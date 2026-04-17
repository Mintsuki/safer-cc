/* safer-cc -- Checked C Compiler Wrapper (standalone C99 implementation)
 *
 * A compile-time source rewriting tool that instruments C code with runtime
 * safety checks. Parses C source (preprocessed) and rewrites arithmetic,
 * pointer, array, and narrowing operations to go through ckd_* macros.
 *
 * Build:  cc -std=c99 -O2 -o safer-cc safer-cc.c
 * Modes:
 *   Compiler wrapper: safer-cc --cc=clang [--handler=file] <flags> -c src.c -o out.o
 *   Filter mode:      safer-cc [--no-preamble] [--handler=file] [input] [-o output]
 */

#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdint.h>
#include <ctype.h>
#include <errno.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>

/* ========================================================================= */
/* Utilities                                                                 */
/* ========================================================================= */

static void die(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("safer-cc: error: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    exit(1);
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) die("out of memory");
    return p;
}

static void *xcalloc(size_t n, size_t sz) {
    void *p = calloc(n ? n : 1, sz ? sz : 1);
    if (!p) die("out of memory");
    return p;
}

static void *xrealloc(void *p, size_t n) {
    p = realloc(p, n ? n : 1);
    if (!p) die("out of memory");
    return p;
}

static char *xstrdup(const char *s) {
    size_t n = strlen(s);
    char *r = xmalloc(n + 1);
    memcpy(r, s, n + 1);
    return r;
}

static char *xstrndup(const char *s, size_t n) {
    char *r = xmalloc(n + 1);
    memcpy(r, s, n);
    r[n] = 0;
    return r;
}

/* ========================================================================= */
/* Dynamic string buffer                                                     */
/* ========================================================================= */

typedef struct {
    char *data;
    size_t len;
    size_t cap;
} Str;

static void str_init(Str *s) {
    s->data = NULL;
    s->len = 0;
    s->cap = 0;
}

static void str_reserve(Str *s, size_t extra) {
    if (s->len + extra + 1 > s->cap) {
        size_t nc = s->cap ? s->cap * 2 : 128;
        while (nc < s->len + extra + 1) nc *= 2;
        s->data = xrealloc(s->data, nc);
        s->cap = nc;
    }
}

static void str_append(Str *s, const char *buf, size_t n) {
    str_reserve(s, n);
    memcpy(s->data + s->len, buf, n);
    s->len += n;
    s->data[s->len] = 0;
}

static void str_append_cstr(Str *s, const char *cstr) {
    str_append(s, cstr, strlen(cstr));
}

static void str_append_ch(Str *s, char c) {
    str_reserve(s, 1);
    s->data[s->len++] = c;
    s->data[s->len] = 0;
}

static void str_appendf(Str *s, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    va_list ap2;
    va_copy(ap2, ap);
    int n = vsnprintf(NULL, 0, fmt, ap);
    va_end(ap);
    if (n < 0) { va_end(ap2); return; }
    str_reserve(s, (size_t)n);
    vsnprintf(s->data + s->len, s->cap - s->len, fmt, ap2);
    va_end(ap2);
    s->len += (size_t)n;
}

static void str_free(Str *s) {
    free(s->data);
    s->data = NULL;
    s->len = s->cap = 0;
}

static char *str_detach(Str *s) {
    char *r = s->data ? s->data : xstrdup("");
    s->data = NULL; s->len = s->cap = 0;
    return r;
}

/* ========================================================================= */
/* Hash-based string set / string-to-pointer map                             */
/* ========================================================================= */

typedef struct StrEntry {
    char *key;
    size_t klen;
    void *val;
    struct StrEntry *next;
} StrEntry;

typedef struct {
    StrEntry **buckets;
    size_t nbuckets;
    size_t count;
} StrMap;

static size_t str_hash(const char *s, size_t n) {
    size_t h = 1469598103934665603ULL;
    for (size_t i = 0; i < n; i++) {
        h ^= (unsigned char)s[i];
        h *= 1099511628211ULL;
    }
    return h;
}

static void smap_init(StrMap *m) {
    m->nbuckets = 16;
    m->buckets = xcalloc(m->nbuckets, sizeof(*m->buckets));
    m->count = 0;
}

static void smap_free_vals(StrMap *m, void (*freefn)(void *)) {
    if (!m->buckets) return;
    for (size_t i = 0; i < m->nbuckets; i++) {
        StrEntry *e = m->buckets[i];
        while (e) {
            StrEntry *n = e->next;
            if (freefn) freefn(e->val);
            free(e->key);
            free(e);
            e = n;
        }
    }
    free(m->buckets);
    m->buckets = NULL;
    m->nbuckets = 0;
    m->count = 0;
}

static void smap_free(StrMap *m) { smap_free_vals(m, NULL); }

static StrEntry *smap_find_e(StrMap *m, const char *key, size_t klen) {
    if (!m->nbuckets) return NULL;
    size_t h = str_hash(key, klen) & (m->nbuckets - 1);
    for (StrEntry *e = m->buckets[h]; e; e = e->next) {
        if (e->klen == klen && memcmp(e->key, key, klen) == 0) return e;
    }
    return NULL;
}

static void smap_resize(StrMap *m, size_t newsz) {
    StrEntry **nb = xcalloc(newsz, sizeof(*nb));
    for (size_t i = 0; i < m->nbuckets; i++) {
        StrEntry *e = m->buckets[i];
        while (e) {
            StrEntry *n = e->next;
            size_t h = str_hash(e->key, e->klen) & (newsz - 1);
            e->next = nb[h];
            nb[h] = e;
            e = n;
        }
    }
    free(m->buckets);
    m->buckets = nb;
    m->nbuckets = newsz;
}

static void smap_put_n(StrMap *m, const char *key, size_t klen, void *val) {
    if (m->count * 2 >= m->nbuckets) smap_resize(m, m->nbuckets * 2);
    StrEntry *e = smap_find_e(m, key, klen);
    if (e) { e->val = val; return; }
    size_t h = str_hash(key, klen) & (m->nbuckets - 1);
    e = xmalloc(sizeof(*e));
    e->key = xstrndup(key, klen);
    e->klen = klen;
    e->val = val;
    e->next = m->buckets[h];
    m->buckets[h] = e;
    m->count++;
}

static void smap_put(StrMap *m, const char *key, void *val) {
    smap_put_n(m, key, strlen(key), val);
}

static void *smap_get_n(StrMap *m, const char *key, size_t klen) {
    StrEntry *e = smap_find_e(m, key, klen);
    return e ? e->val : NULL;
}

static void *smap_get(StrMap *m, const char *key) {
    return smap_get_n(m, key, strlen(key));
}

static int smap_has_n(StrMap *m, const char *key, size_t klen) {
    return smap_find_e(m, key, klen) != NULL;
}

static int smap_has(StrMap *m, const char *key) {
    return smap_has_n(m, key, strlen(key));
}

static void smap_remove(StrMap *m, const char *key) {
    if (!m->nbuckets) return;
    size_t klen = strlen(key);
    size_t h = str_hash(key, klen) & (m->nbuckets - 1);
    StrEntry **pp = &m->buckets[h];
    while (*pp) {
        if ((*pp)->klen == klen && memcmp((*pp)->key, key, klen) == 0) {
            StrEntry *e = *pp;
            *pp = e->next;
            free(e->key);
            free(e);
            m->count--;
            return;
        }
        pp = &(*pp)->next;
    }
}

static void smap_copy(StrMap *dst, StrMap *src) {
    smap_init(dst);
    if (!src->buckets) return;
    for (size_t i = 0; i < src->nbuckets; i++) {
        for (StrEntry *e = src->buckets[i]; e; e = e->next) {
            smap_put_n(dst, e->key, e->klen, e->val);
        }
    }
}

static void smap_copy_dup_strs(StrMap *dst, StrMap *src) {
    /* deep copy where value is a heap-owned char* */
    smap_init(dst);
    if (!src->buckets) return;
    for (size_t i = 0; i < src->nbuckets; i++) {
        for (StrEntry *e = src->buckets[i]; e; e = e->next) {
            char *v = (char *)e->val;
            smap_put_n(dst, e->key, e->klen, v ? xstrdup(v) : NULL);
        }
    }
}

static void free_cstr(void *p) { free(p); }

/* --- StrList: dynamic array of strings ---------------------------------- */

typedef struct {
    char **items;
    size_t len;
    size_t cap;
} StrList;

static void sl_init(StrList *l) { l->items = NULL; l->len = 0; l->cap = 0; }

static void sl_push_n(StrList *l, const char *s, size_t n) {
    if (l->len == l->cap) {
        l->cap = l->cap ? l->cap * 2 : 8;
        l->items = xrealloc(l->items, l->cap * sizeof(*l->items));
    }
    l->items[l->len++] = s ? xstrndup(s, n) : NULL;
}

static void sl_push(StrList *l, const char *s) {
    sl_push_n(l, s, s ? strlen(s) : 0);
}

static void sl_push_null(StrList *l) {
    if (l->len == l->cap) {
        l->cap = l->cap ? l->cap * 2 : 8;
        l->items = xrealloc(l->items, l->cap * sizeof(*l->items));
    }
    l->items[l->len++] = NULL;
}

static void sl_free(StrList *l) {
    for (size_t i = 0; i < l->len; i++) free(l->items[i]);
    free(l->items);
    l->items = NULL; l->len = 0; l->cap = 0;
}

static StrList *sl_new_copy(StrList *src) {
    StrList *dst = xmalloc(sizeof(*dst));
    sl_init(dst);
    for (size_t i = 0; i < src->len; i++) {
        sl_push(dst, src->items[i]);
    }
    return dst;
}

static void free_strlist_val(void *p) {
    if (!p) return;
    StrList *l = (StrList *)p;
    sl_free(l);
    free(l);
}

/* ========================================================================= */
/* Source preprocessing: strip __attribute__, @ markers, #line directives    */
/* ========================================================================= */

typedef struct {
    size_t start;
    size_t end;
} Range;

typedef struct {
    char *stripped;      /* same length as input, with stripped bytes → spaces */
    size_t len;
    size_t *suppressed;  /* byte positions of @ markers (sorted) */
    size_t nsup;
    Range *disabled;     /* byte ranges inside @@@ blocks (sorted) */
    size_t ndis;
} Preprocessed;

static void pp_free(Preprocessed *p) {
    free(p->stripped);
    free(p->suppressed);
    free(p->disabled);
    p->stripped = NULL;
    p->suppressed = NULL;
    p->disabled = NULL;
}

static int is_digit(int c) { return c >= '0' && c <= '9'; }
static int is_alpha(int c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'; }
static int is_alnum(int c) { return is_digit(c) || is_alpha(c); }

/* Preprocess source for tree-sitter-less parsing:
 * - Strip __attribute__((...)) into spaces (preserves byte offsets)
 * - Strip #line directives into spaces
 * - Collect @ suppression marker positions (replace @ with space)
 * - Collect @@@ block-suppression ranges
 */
static Preprocessed preprocess(const char *src, size_t n) {
    Preprocessed r = {0};
    r.stripped = xmalloc(n);
    memcpy(r.stripped, src, n);
    r.len = n;
    size_t sup_cap = 16, sup_len = 0;
    size_t *sup = xmalloc(sup_cap * sizeof(*sup));
    size_t tog_cap = 8, tog_len = 0;
    size_t *togs = xmalloc(tog_cap * sizeof(*togs));

    size_t i = 0;
    while (i < n) {
        /* #line directives: only at start of line */
        if (src[i] == '#' && (i == 0 || src[i-1] == '\n')) {
            size_t j = i + 1;
            while (j < n && (src[j] == ' ' || src[j] == '\t')) j++;
            if (j < n && is_digit((unsigned char)src[j])) {
                /* Replace entire line with spaces (preserve newline) */
                size_t k = i;
                while (k < n && src[k] != '\n') {
                    r.stripped[k] = ' ';
                    k++;
                }
                i = k;
                continue;
            }
        }

        /* __attribute__((...)) stripping */
        if (src[i] == '_' && (
                (i + 13 <= n && memcmp(src + i, "__attribute__", 13) == 0 && !is_alnum((unsigned char)(i+13 < n ? src[i+13] : 0))) ||
                (i + 12 <= n && memcmp(src + i, "__attribute(", 12) == 0))) {
            size_t kwlen;
            if (i + 13 <= n && memcmp(src + i, "__attribute__", 13) == 0) kwlen = 13;
            else kwlen = 11;
            size_t j = i + kwlen;
            while (j < n && (src[j] == ' ' || src[j] == '\t' || src[j] == '\n' || src[j] == '\r')) j++;
            if (j < n && src[j] == '(') {
                int depth = 1;
                size_t k = j + 1;
                while (k < n && depth > 0) {
                    if (src[k] == '(') depth++;
                    else if (src[k] == ')') depth--;
                    k++;
                }
                if (depth == 0) {
                    for (size_t x = i; x < k; x++) r.stripped[x] = ' ';
                    i = k;
                    continue;
                }
            }
        }

        /* String/char literals: skip (don't process @ inside) */
        if (src[i] == '"' || src[i] == '\'') {
            char q = src[i];
            i++;
            while (i < n && src[i] != q) {
                if (src[i] == '\\' && i + 1 < n) {
                    i += 2;
                    continue;
                }
                i++;
            }
            if (i < n) i++;
            continue;
        }

        /* Block suppression markers: @@@ */
        if (i + 3 <= n && src[i] == '@' && src[i+1] == '@' && src[i+2] == '@') {
            if (tog_len == tog_cap) { tog_cap *= 2; togs = xrealloc(togs, tog_cap * sizeof(*togs)); }
            togs[tog_len++] = i;
            /* Also mark the individual @ positions as suppressed (so op checks can see them) */
            for (int d = 0; d < 3; d++) {
                if (sup_len == sup_cap) { sup_cap *= 2; sup = xrealloc(sup, sup_cap * sizeof(*sup)); }
                sup[sup_len++] = i + d;
                r.stripped[i + d] = ' ';
            }
            i += 3;
            continue;
        }

        /* Single @ suppression */
        if (src[i] == '@') {
            if (sup_len == sup_cap) { sup_cap *= 2; sup = xrealloc(sup, sup_cap * sizeof(*sup)); }
            sup[sup_len++] = i;
            r.stripped[i] = ' ';
            i++;
            continue;
        }

        /* Skip comments: line */
        if (i + 2 <= n && src[i] == '/' && src[i+1] == '/') {
            i += 2;
            while (i < n && src[i] != '\n') i++;
            continue;
        }
        /* Skip comments: block */
        if (i + 2 <= n && src[i] == '/' && src[i+1] == '*') {
            i += 2;
            while (i + 1 < n && !(src[i] == '*' && src[i+1] == '/')) i++;
            if (i + 1 < n) i += 2;
            continue;
        }

        i++;
    }

    /* Convert toggle positions into disabled byte ranges (pairs) */
    r.suppressed = sup;
    r.nsup = sup_len;
    /* sort suppressed positions */
    for (size_t a = 1; a < sup_len; a++) {
        size_t v = sup[a];
        size_t b = a;
        while (b > 0 && sup[b-1] > v) { sup[b] = sup[b-1]; b--; }
        sup[b] = v;
    }
    size_t ndis = tog_len / 2;
    int unpaired = (tog_len % 2);
    r.disabled = xmalloc((ndis + (unpaired ? 1 : 0) + 1) * sizeof(*r.disabled));
    r.ndis = 0;
    for (size_t j = 0; j + 1 < tog_len; j += 2) {
        r.disabled[r.ndis].start = togs[j];
        r.disabled[r.ndis].end = togs[j+1] + 3;
        r.ndis++;
    }
    if (unpaired) {
        r.disabled[r.ndis].start = togs[tog_len - 1];
        r.disabled[r.ndis].end = n;
        r.ndis++;
    }
    free(togs);
    return r;
}

/* ========================================================================= */
/* Tokenizer                                                                 */
/* ========================================================================= */

typedef enum {
    TK_EOF = 0,
    TK_IDENT,       /* or keyword — caller disambiguates */
    TK_NUMBER,
    TK_CHAR_LIT,
    TK_STRING_LIT,
    TK_PUNCT        /* operators and punctuation; text is tokens[i].text */
} TokKind;

typedef struct {
    TokKind kind;
    size_t start;   /* byte offset in source */
    size_t end;     /* exclusive */
    const char *text; /* for punct: the operator/keyword text; for ident: pointer to source */
    size_t text_len;
    /* computed lazily */
} Token;

typedef struct {
    Token *items;
    size_t len;
    size_t cap;
    const char *src;
    size_t src_len;
} Tokens;

static int is_ident_start(int c) { return is_alpha(c); }
static int is_ident_cont(int c) { return is_alnum(c); }

static void toks_push(Tokens *t, TokKind k, size_t a, size_t b, const char *text, size_t tlen) {
    if (t->len == t->cap) {
        t->cap = t->cap ? t->cap * 2 : 256;
        t->items = xrealloc(t->items, t->cap * sizeof(*t->items));
    }
    t->items[t->len].kind = k;
    t->items[t->len].start = a;
    t->items[t->len].end = b;
    t->items[t->len].text = text;
    t->items[t->len].text_len = tlen;
    t->len++;
}

/* Tokenize the source. Comments are skipped. String/char literals are single tokens. */
static void tokenize(const char *src, size_t n, Tokens *out) {
    out->items = NULL; out->len = 0; out->cap = 0;
    out->src = src; out->src_len = n;
    size_t i = 0;
    while (i < n) {
        unsigned char c = (unsigned char)src[i];
        if (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' || c == '\f') { i++; continue; }
        /* comments */
        if (c == '/' && i + 1 < n && src[i+1] == '/') {
            i += 2;
            while (i < n && src[i] != '\n') i++;
            continue;
        }
        if (c == '/' && i + 1 < n && src[i+1] == '*') {
            i += 2;
            while (i + 1 < n && !(src[i] == '*' && src[i+1] == '/')) i++;
            if (i + 1 < n) i += 2;
            continue;
        }
        /* # line directives and other preprocessor lines: skip to EOL */
        if (c == '#' && (i == 0 || src[i-1] == '\n' || src[i-1] == ' ' || src[i-1] == '\t')) {
            /* only at start of line in the stripped source (after whitespace) */
            size_t ls = i;
            while (ls > 0 && src[ls-1] != '\n') {
                if (src[ls-1] != ' ' && src[ls-1] != '\t') break;
                ls--;
            }
            if (ls == 0 || src[ls-1] == '\n') {
                /* Skip the entire preprocessor line */
                while (i < n && src[i] != '\n') i++;
                continue;
            }
        }
        /* identifiers / keywords */
        if (is_ident_start(c)) {
            size_t j = i + 1;
            while (j < n && is_ident_cont((unsigned char)src[j])) j++;
            toks_push(out, TK_IDENT, i, j, src + i, j - i);
            i = j;
            continue;
        }
        /* numbers (integer and float) */
        if (is_digit(c) || (c == '.' && i + 1 < n && is_digit((unsigned char)src[i+1]))) {
            size_t j = i;
            /* hex prefix */
            if (c == '0' && j + 1 < n && (src[j+1] == 'x' || src[j+1] == 'X')) {
                j += 2;
                while (j < n && (isxdigit((unsigned char)src[j]) || src[j] == '.' ||
                                 src[j] == 'p' || src[j] == 'P' ||
                                 (j > i + 2 && (src[j] == '+' || src[j] == '-') &&
                                  (src[j-1] == 'p' || src[j-1] == 'P')))) j++;
            } else {
                while (j < n && (is_digit((unsigned char)src[j]) || src[j] == '.' ||
                                 src[j] == 'e' || src[j] == 'E' ||
                                 (j > i && (src[j] == '+' || src[j] == '-') &&
                                  (src[j-1] == 'e' || src[j-1] == 'E')))) j++;
            }
            /* integer suffix (u, l, ll, ul, ull, lu, llu, f, etc.) */
            while (j < n) {
                char s = src[j];
                if (s == 'u' || s == 'U' || s == 'l' || s == 'L' ||
                    s == 'f' || s == 'F' || s == 'z' || s == 'Z') j++;
                else break;
            }
            toks_push(out, TK_NUMBER, i, j, src + i, j - i);
            i = j;
            continue;
        }
        /* string literals (with possible L/u/U/u8 prefix) */
        {
            size_t start = i;
            int is_str = 0, is_char = 0;
            if (c == '"') is_str = 1;
            else if (c == '\'') is_char = 1;
            else if ((c == 'L' || c == 'u' || c == 'U') && i + 1 < n) {
                size_t k = i + 1;
                if (c == 'u' && k < n && src[k] == '8') k++;
                if (k < n && src[k] == '"') { is_str = 1; i = k; }
                else if (k < n && src[k] == '\'') { is_char = 1; i = k; }
            }
            if (is_str || is_char) {
                char q = src[i];
                size_t j = i + 1;
                while (j < n && src[j] != q) {
                    if (src[j] == '\\' && j + 1 < n) { j += 2; continue; }
                    j++;
                }
                if (j < n) j++;
                toks_push(out, is_str ? TK_STRING_LIT : TK_CHAR_LIT,
                          start, j, src + start, j - start);
                i = j;
                continue;
            }
        }
        /* Multi-char operators */
#define PUNCT(LEN, TXT) \
    do { toks_push(out, TK_PUNCT, i, i + (LEN), TXT, (LEN)); i += (LEN); goto next; } while (0)
        if (i + 2 < n) {
            if (src[i] == '.' && src[i+1] == '.' && src[i+2] == '.') PUNCT(3, "...");
            if (src[i] == '<' && src[i+1] == '<' && src[i+2] == '=') PUNCT(3, "<<=");
            if (src[i] == '>' && src[i+1] == '>' && src[i+2] == '=') PUNCT(3, ">>=");
        }
        if (i + 1 < n) {
            char a = src[i], b = src[i+1];
            if (a == '-' && b == '>') PUNCT(2, "->");
            if (a == '+' && b == '+') PUNCT(2, "++");
            if (a == '-' && b == '-') PUNCT(2, "--");
            if (a == '<' && b == '<') PUNCT(2, "<<");
            if (a == '>' && b == '>') PUNCT(2, ">>");
            if (a == '<' && b == '=') PUNCT(2, "<=");
            if (a == '>' && b == '=') PUNCT(2, ">=");
            if (a == '=' && b == '=') PUNCT(2, "==");
            if (a == '!' && b == '=') PUNCT(2, "!=");
            if (a == '&' && b == '&') PUNCT(2, "&&");
            if (a == '|' && b == '|') PUNCT(2, "||");
            if (a == '+' && b == '=') PUNCT(2, "+=");
            if (a == '-' && b == '=') PUNCT(2, "-=");
            if (a == '*' && b == '=') PUNCT(2, "*=");
            if (a == '/' && b == '=') PUNCT(2, "/=");
            if (a == '%' && b == '=') PUNCT(2, "%=");
            if (a == '&' && b == '=') PUNCT(2, "&=");
            if (a == '|' && b == '=') PUNCT(2, "|=");
            if (a == '^' && b == '=') PUNCT(2, "^=");
            if (a == '#' && b == '#') PUNCT(2, "##");
        }
        switch (c) {
        case '(': PUNCT(1, "(");
        case ')': PUNCT(1, ")");
        case '[': PUNCT(1, "[");
        case ']': PUNCT(1, "]");
        case '{': PUNCT(1, "{");
        case '}': PUNCT(1, "}");
        case ',': PUNCT(1, ",");
        case ';': PUNCT(1, ";");
        case ':': PUNCT(1, ":");
        case '?': PUNCT(1, "?");
        case '+': PUNCT(1, "+");
        case '-': PUNCT(1, "-");
        case '*': PUNCT(1, "*");
        case '/': PUNCT(1, "/");
        case '%': PUNCT(1, "%");
        case '&': PUNCT(1, "&");
        case '|': PUNCT(1, "|");
        case '^': PUNCT(1, "^");
        case '~': PUNCT(1, "~");
        case '!': PUNCT(1, "!");
        case '<': PUNCT(1, "<");
        case '>': PUNCT(1, ">");
        case '=': PUNCT(1, "=");
        case '.': PUNCT(1, ".");
        case '#': PUNCT(1, "#");
        default: i++; break;
        }
    next:;
#undef PUNCT
    }
    /* sentinel EOF token to simplify parsing */
    toks_push(out, TK_EOF, n, n, "", 0);
}

static void toks_free(Tokens *t) {
    free(t->items);
    t->items = NULL;
    t->len = t->cap = 0;
}

/* ========================================================================= */
/* AST                                                                       */
/* ========================================================================= */

typedef enum {
    ND_TRANSLATION_UNIT,
    ND_DECLARATION,
    ND_TYPE_DEFINITION,
    ND_FUNCTION_DEFINITION,
    ND_STRUCT_SPECIFIER,
    ND_UNION_SPECIFIER,
    ND_ENUM_SPECIFIER,
    ND_FIELD_DECLARATION_LIST,
    ND_FIELD_DECLARATION,
    ND_BITFIELD_CLAUSE,
    ND_ENUMERATOR,
    ND_INIT_DECLARATOR,
    ND_POINTER_DECLARATOR,
    ND_ABSTRACT_POINTER_DECLARATOR,
    ND_ARRAY_DECLARATOR,
    ND_FUNCTION_DECLARATOR,
    ND_PARENTHESIZED_DECLARATOR,
    ND_PARAMETER_LIST,
    ND_PARAMETER_DECLARATION,
    ND_VARIADIC_PARAMETER,
    ND_TYPE_DESCRIPTOR,
    ND_PRIMITIVE_TYPE,
    ND_SIZED_TYPE_SPECIFIER,
    ND_TYPE_IDENTIFIER,
    ND_IDENTIFIER,
    ND_FIELD_IDENTIFIER,
    ND_NUMBER_LITERAL,
    ND_CHAR_LITERAL,
    ND_STRING_LITERAL,
    ND_CONCATENATED_STRING,
    ND_BINARY_EXPRESSION,
    ND_UNARY_EXPRESSION,
    ND_UPDATE_EXPRESSION,
    ND_ASSIGNMENT_EXPRESSION,
    ND_POINTER_EXPRESSION,
    ND_CAST_EXPRESSION,
    ND_COMPOUND_LITERAL_EXPRESSION,
    ND_PARENTHESIZED_EXPRESSION,
    ND_SUBSCRIPT_EXPRESSION,
    ND_FIELD_EXPRESSION,
    ND_CALL_EXPRESSION,
    ND_ARGUMENT_LIST,
    ND_CONDITIONAL_EXPRESSION,
    ND_COMMA_EXPRESSION,
    ND_SIZEOF_EXPRESSION,
    ND_ALIGNOF_EXPRESSION,
    ND_GENERIC_EXPRESSION,
    ND_COMPOUND_STATEMENT,
    ND_EXPRESSION_STATEMENT,
    ND_IF_STATEMENT,
    ND_FOR_STATEMENT,
    ND_WHILE_STATEMENT,
    ND_DO_STATEMENT,
    ND_SWITCH_STATEMENT,
    ND_CASE_STATEMENT,
    ND_LABELED_STATEMENT,
    ND_RETURN_STATEMENT,
    ND_BREAK_STATEMENT,
    ND_CONTINUE_STATEMENT,
    ND_GOTO_STATEMENT,
    ND_INITIALIZER_LIST,
    ND_INITIALIZER_PAIR,
    ND_SUBSCRIPT_DESIGNATOR,
    ND_FIELD_DESIGNATOR,
    ND_OPERATOR,        /* a token child: +, -, ->, etc. text is in .text */
    ND_KEYWORD,         /* keyword token child: return, for, if, ... */
    ND_PUNCT,           /* punct token child: (, ), [, ], {, }, , , ; */
    ND_STORAGE_CLASS_SPECIFIER,
    ND_TYPE_QUALIFIER,
    ND_FUNCTION_SPECIFIER,
    ND_COMMENT,
    ND_ATTRIBUTE_SPECIFIER,
    ND_ATTRIBUTE_DECLARATION,
    ND_ERROR,
} NodeKind;

typedef struct Node Node;
struct Node {
    NodeKind kind;
    size_t start;
    size_t end;
    size_t line;    /* 0-based */
    size_t col;     /* 0-based */
    Node **children;
    size_t nchildren;
    size_t cap;
    Node *parent;
    const char *text;   /* for operator/keyword/punct/ident nodes */
    size_t text_len;
    unsigned char has_error;
};

static Node *node_new(NodeKind kind) {
    Node *n = xcalloc(1, sizeof(*n));
    n->kind = kind;
    return n;
}

static Node *node_new_tok(NodeKind kind, Token *t) {
    Node *n = node_new(kind);
    n->start = t->start;
    n->end = t->end;
    n->text = t->text;
    n->text_len = t->text_len;
    return n;
}

static void node_add_child(Node *p, Node *c) {
    if (!c) return;
    if (p->nchildren == p->cap) {
        p->cap = p->cap ? p->cap * 2 : 4;
        p->children = xrealloc(p->children, p->cap * sizeof(*p->children));
    }
    c->parent = p;
    p->children[p->nchildren++] = c;
    if (c->has_error) p->has_error = 1;
    if (p->nchildren == 1) { p->start = c->start; p->line = c->line; p->col = c->col; }
    if (c->end > p->end) p->end = c->end;
    if (c->start < p->start) p->start = c->start;
}

static void node_free(Node *n) {
    if (!n) return;
    for (size_t i = 0; i < n->nchildren; i++) node_free(n->children[i]);
    free(n->children);
    free(n);
}

static const char *node_type_name(const Node *n) {
    switch (n->kind) {
    case ND_TRANSLATION_UNIT: return "translation_unit";
    case ND_DECLARATION: return "declaration";
    case ND_TYPE_DEFINITION: return "type_definition";
    case ND_FUNCTION_DEFINITION: return "function_definition";
    case ND_STRUCT_SPECIFIER: return "struct_specifier";
    case ND_UNION_SPECIFIER: return "union_specifier";
    case ND_ENUM_SPECIFIER: return "enum_specifier";
    case ND_FIELD_DECLARATION_LIST: return "field_declaration_list";
    case ND_FIELD_DECLARATION: return "field_declaration";
    case ND_BITFIELD_CLAUSE: return "bitfield_clause";
    case ND_ENUMERATOR: return "enumerator";
    case ND_INIT_DECLARATOR: return "init_declarator";
    case ND_POINTER_DECLARATOR: return "pointer_declarator";
    case ND_ABSTRACT_POINTER_DECLARATOR: return "abstract_pointer_declarator";
    case ND_ARRAY_DECLARATOR: return "array_declarator";
    case ND_FUNCTION_DECLARATOR: return "function_declarator";
    case ND_PARENTHESIZED_DECLARATOR: return "parenthesized_declarator";
    case ND_PARAMETER_LIST: return "parameter_list";
    case ND_PARAMETER_DECLARATION: return "parameter_declaration";
    case ND_VARIADIC_PARAMETER: return "variadic_parameter";
    case ND_TYPE_DESCRIPTOR: return "type_descriptor";
    case ND_PRIMITIVE_TYPE: return "primitive_type";
    case ND_SIZED_TYPE_SPECIFIER: return "sized_type_specifier";
    case ND_TYPE_IDENTIFIER: return "type_identifier";
    case ND_IDENTIFIER: return "identifier";
    case ND_FIELD_IDENTIFIER: return "field_identifier";
    case ND_NUMBER_LITERAL: return "number_literal";
    case ND_CHAR_LITERAL: return "char_literal";
    case ND_STRING_LITERAL: return "string_literal";
    case ND_CONCATENATED_STRING: return "concatenated_string";
    case ND_BINARY_EXPRESSION: return "binary_expression";
    case ND_UNARY_EXPRESSION: return "unary_expression";
    case ND_UPDATE_EXPRESSION: return "update_expression";
    case ND_ASSIGNMENT_EXPRESSION: return "assignment_expression";
    case ND_POINTER_EXPRESSION: return "pointer_expression";
    case ND_CAST_EXPRESSION: return "cast_expression";
    case ND_COMPOUND_LITERAL_EXPRESSION: return "compound_literal_expression";
    case ND_PARENTHESIZED_EXPRESSION: return "parenthesized_expression";
    case ND_SUBSCRIPT_EXPRESSION: return "subscript_expression";
    case ND_FIELD_EXPRESSION: return "field_expression";
    case ND_CALL_EXPRESSION: return "call_expression";
    case ND_ARGUMENT_LIST: return "argument_list";
    case ND_CONDITIONAL_EXPRESSION: return "conditional_expression";
    case ND_COMMA_EXPRESSION: return "comma_expression";
    case ND_SIZEOF_EXPRESSION: return "sizeof_expression";
    case ND_ALIGNOF_EXPRESSION: return "alignof_expression";
    case ND_GENERIC_EXPRESSION: return "generic_expression";
    case ND_COMPOUND_STATEMENT: return "compound_statement";
    case ND_EXPRESSION_STATEMENT: return "expression_statement";
    case ND_IF_STATEMENT: return "if_statement";
    case ND_FOR_STATEMENT: return "for_statement";
    case ND_WHILE_STATEMENT: return "while_statement";
    case ND_DO_STATEMENT: return "do_statement";
    case ND_SWITCH_STATEMENT: return "switch_statement";
    case ND_CASE_STATEMENT: return "case_statement";
    case ND_LABELED_STATEMENT: return "labeled_statement";
    case ND_RETURN_STATEMENT: return "return_statement";
    case ND_BREAK_STATEMENT: return "break_statement";
    case ND_CONTINUE_STATEMENT: return "continue_statement";
    case ND_GOTO_STATEMENT: return "goto_statement";
    case ND_INITIALIZER_LIST: return "initializer_list";
    case ND_INITIALIZER_PAIR: return "initializer_pair";
    case ND_SUBSCRIPT_DESIGNATOR: return "subscript_designator";
    case ND_FIELD_DESIGNATOR: return "field_designator";
    case ND_STORAGE_CLASS_SPECIFIER: return "storage_class_specifier";
    case ND_TYPE_QUALIFIER: return "type_qualifier";
    case ND_FUNCTION_SPECIFIER: return "function_specifier";
    case ND_ATTRIBUTE_SPECIFIER: return "attribute_specifier";
    case ND_ATTRIBUTE_DECLARATION: return "attribute_declaration";
    case ND_ERROR: return "ERROR";
    case ND_OPERATOR:
    case ND_KEYWORD:
    case ND_PUNCT:
    default: return n->text ? n->text : "?";
    }
}

/* A shorthand to test if a node's displayed "type" equals a string. */
static int node_type_is(const Node *n, const char *s) {
    /* OPERATOR/KEYWORD/PUNCT nodes store their token text in ->text */
    if (n->kind == ND_OPERATOR || n->kind == ND_KEYWORD || n->kind == ND_PUNCT) {
        if (!n->text) return 0;
        return strlen(s) == n->text_len && memcmp(n->text, s, n->text_len) == 0;
    }
    return strcmp(node_type_name(n), s) == 0;
}

/* Extract node text from source (use .text if operator/keyword/punct else use start/end). */
static void node_text_range(const Node *n, const char *src, size_t *out_start, size_t *out_end) {
    if (n->kind == ND_OPERATOR || n->kind == ND_KEYWORD || n->kind == ND_PUNCT) {
        *out_start = n->start;
        *out_end = n->end;
    } else {
        *out_start = n->start;
        *out_end = n->end;
    }
    (void)src;
}

static int node_text_equals(const Node *n, const char *src, const char *s) {
    size_t a, b;
    node_text_range(n, src, &a, &b);
    size_t slen = strlen(s);
    if (b - a != slen) return 0;
    return memcmp(src + a, s, slen) == 0;
}

static char *node_text_dup(const Node *n, const char *src) {
    size_t a, b;
    node_text_range(n, src, &a, &b);
    return xstrndup(src + a, b - a);
}

/* ========================================================================= */
/* Parser                                                                    */
/* ========================================================================= */

typedef struct {
    Tokens *toks;
    size_t pos;
    const char *src;
    size_t src_len;
    StrMap typedefs;   /* names that are typedefs → dummy value (char *)1 */
    /* Line table for computing line/col from byte offset */
    size_t *line_starts;
    size_t nlines;
} Parser;

static int cur_is_ident(Parser *p, const char *kw) {
    Token *t = &p->toks->items[p->pos];
    if (t->kind != TK_IDENT) return 0;
    size_t kl = strlen(kw);
    return t->text_len == kl && memcmp(t->text, kw, kl) == 0;
}

static int cur_is_punct(Parser *p, const char *s) {
    Token *t = &p->toks->items[p->pos];
    if (t->kind != TK_PUNCT) return 0;
    size_t kl = strlen(s);
    return t->text_len == kl && memcmp(t->text, s, kl) == 0;
}

static int peek_is_punct(Parser *p, size_t off, const char *s) {
    if (p->pos + off >= p->toks->len) return 0;
    Token *t = &p->toks->items[p->pos + off];
    if (t->kind != TK_PUNCT) return 0;
    size_t kl = strlen(s);
    return t->text_len == kl && memcmp(t->text, s, kl) == 0;
}

static int peek_is_ident(Parser *p, size_t off, const char *kw) {
    if (p->pos + off >= p->toks->len) return 0;
    Token *t = &p->toks->items[p->pos + off];
    if (t->kind != TK_IDENT) return 0;
    size_t kl = strlen(kw);
    return t->text_len == kl && memcmp(t->text, kw, kl) == 0;
}

static Token *cur(Parser *p) { return &p->toks->items[p->pos]; }

/* line/col computation (0-based) */
static void compute_line_col(Parser *p, size_t byte_off, size_t *line, size_t *col) {
    /* binary search */
    size_t lo = 0, hi = p->nlines;
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        if (p->line_starts[mid] <= byte_off) lo = mid + 1;
        else hi = mid;
    }
    /* lo is the first line_start > byte_off; so byte is on line lo-1 */
    size_t li = lo > 0 ? lo - 1 : 0;
    *line = li;
    *col = byte_off - p->line_starts[li];
}

static void build_line_table(Parser *p, const char *src, size_t n) {
    size_t cap = 32, len = 0;
    size_t *arr = xmalloc(cap * sizeof(*arr));
    arr[len++] = 0;
    for (size_t i = 0; i < n; i++) {
        if (src[i] == '\n') {
            if (len == cap) { cap *= 2; arr = xrealloc(arr, cap * sizeof(*arr)); }
            arr[len++] = i + 1;
        }
    }
    p->line_starts = arr;
    p->nlines = len;
}

/* Advance: consume current token, append as child of parent as NDkind (operator/keyword/punct). */
static Node *consume_as(Parser *p, NodeKind kind) {
    Token *t = cur(p);
    Node *n = node_new_tok(kind, t);
    compute_line_col(p, t->start, &n->line, &n->col);
    p->pos++;
    return n;
}

static Node *consume_punct(Parser *p) { return consume_as(p, ND_PUNCT); }
static Node *consume_op(Parser *p) { return consume_as(p, ND_OPERATOR); }
static Node *consume_kw(Parser *p) { return consume_as(p, ND_KEYWORD); }

/* Keyword recognition — these appear as TK_IDENT tokens */
static int is_kw(Token *t, const char *kw) {
    if (t->kind != TK_IDENT) return 0;
    size_t kl = strlen(kw);
    return t->text_len == kl && memcmp(t->text, kw, kl) == 0;
}

static int is_any_kw(Token *t, const char *const kws[], size_t nkws) {
    for (size_t i = 0; i < nkws; i++) if (is_kw(t, kws[i])) return 1;
    return 0;
}

/* Primitive type keywords (includes stdint-style fixed-width types,
 * mirroring tree-sitter-c's predefined primitive_type set). */
static int is_primitive_type_kw(Token *t) {
    static const char *const kws[] = {
        "void", "char", "int", "float", "double", "_Bool", "bool",
        "_Complex", "_Imaginary",
        /* stdint-style */
        "int8_t", "int16_t", "int32_t", "int64_t",
        "uint8_t", "uint16_t", "uint32_t", "uint64_t",
        "intptr_t", "uintptr_t", "size_t", "ssize_t", "ptrdiff_t",
        "intmax_t", "uintmax_t",
        "int_fast8_t", "int_fast16_t", "int_fast32_t", "int_fast64_t",
        "uint_fast8_t", "uint_fast16_t", "uint_fast32_t", "uint_fast64_t",
        "int_least8_t", "int_least16_t", "int_least32_t", "int_least64_t",
        "uint_least8_t", "uint_least16_t", "uint_least32_t", "uint_least64_t",
        "wchar_t", "char8_t", "char16_t", "char32_t",
        "__int8", "__int16", "__int32", "__int64", "__int128",
        "_Float16", "_Float32", "_Float64", "_Float128",
        "__float80", "__float128",
    };
    return is_any_kw(t, kws, sizeof(kws) / sizeof(*kws));
}

static int is_sized_type_kw(Token *t) {
    static const char *const kws[] = {
        "short", "long", "signed", "unsigned"
    };
    return is_any_kw(t, kws, sizeof(kws) / sizeof(*kws));
}

static int is_storage_class_kw(Token *t) {
    static const char *const kws[] = {
        "auto", "register", "static", "extern", "typedef",
        "_Thread_local", "thread_local"
    };
    return is_any_kw(t, kws, sizeof(kws) / sizeof(*kws));
}

static int is_type_qualifier_kw(Token *t) {
    static const char *const kws[] = {
        "const", "volatile", "restrict", "_Atomic",
        "__restrict", "__restrict__", "__const", "__const__",
        "__volatile", "__volatile__",
    };
    return is_any_kw(t, kws, sizeof(kws) / sizeof(*kws));
}

static int is_function_specifier_kw(Token *t) {
    static const char *const kws[] = {
        "inline", "__inline", "__inline__", "_Noreturn", "noreturn",
        "__forceinline"
    };
    return is_any_kw(t, kws, sizeof(kws) / sizeof(*kws));
}

static int is_struct_like_kw(Token *t) {
    return is_kw(t, "struct") || is_kw(t, "union") || is_kw(t, "enum");
}

/* Check if token starts a type specifier (primitive, sized, struct, enum,
 * typedef name, or qualifier).
 */
static int tok_starts_type(Parser *p, size_t off) {
    if (p->pos + off >= p->toks->len) return 0;
    Token *t = &p->toks->items[p->pos + off];
    if (t->kind != TK_IDENT) return 0;
    if (is_primitive_type_kw(t)) return 1;
    if (is_sized_type_kw(t)) return 1;
    if (is_type_qualifier_kw(t)) return 1;
    if (is_storage_class_kw(t)) return 1;
    if (is_function_specifier_kw(t)) return 1;
    if (is_struct_like_kw(t)) return 1;
    if (is_kw(t, "typeof") || is_kw(t, "__typeof") || is_kw(t, "__typeof__")) return 1;
    if (is_kw(t, "__extension__")) return 1;
    /* a typedef name (known via typedef tracking) */
    if (smap_has_n(&p->typedefs, t->text, t->text_len)) return 1;
    return 0;
}

/* Forward decls */
static Node *parse_expression(Parser *p);
static Node *parse_assignment_expression(Parser *p);
static Node *parse_cast_expression(Parser *p);
static Node *parse_unary_expression(Parser *p);
static Node *parse_postfix_expression(Parser *p);
static Node *parse_primary_expression(Parser *p);
static Node *parse_declaration(Parser *p, int allow_fn_def);
static Node *parse_statement(Parser *p);
static Node *parse_compound_statement(Parser *p);
static Node *parse_initializer(Parser *p);
static Node *parse_declarator(Parser *p, int abstract);
static Node *parse_type_name(Parser *p);
static Node *parse_declaration_specifiers(Parser *p, int *out_is_typedef);
static Node *parse_struct_or_union_specifier(Parser *p);
static Node *parse_enum_specifier(Parser *p);
static Node *parse_parameter_list(Parser *p);

/* ----------------------------------------------------------------------- */
/* Expressions                                                             */
/* ----------------------------------------------------------------------- */

/* Precedence (lowest to highest for binary_expression):
 *   comma, assign, conditional, ||, &&, |, ^, &,
 *   == !=, < > <= >=, << >>, + -, * / %, unary, cast, postfix
 */

static Node *wrap_primary_ident(Parser *p, Token *t, int field_ident) {
    Node *n = node_new(field_ident ? ND_FIELD_IDENTIFIER : ND_IDENTIFIER);
    n->start = t->start; n->end = t->end;
    n->text = t->text; n->text_len = t->text_len;
    compute_line_col(p, t->start, &n->line, &n->col);
    return n;
}

/* Try to parse a parenthesized type cast or compound literal or parenthesized expr. */
static int is_type_name_lookahead(Parser *p) {
    /* After a '(', check if we have a type name:
     *  ( TYPE ) -- cast or compound literal
     * vs
     *  ( EXPR ) -- parenthesized expression
     */
    /* Current token must be '(' */
    if (!cur_is_punct(p, "(")) return 0;
    return tok_starts_type(p, 1);
}

static Node *parse_primary_expression(Parser *p) {
    Token *t = cur(p);
    /* __extension__ may precede an expression */
    if (is_kw(t, "__extension__")) { p->pos++; return parse_primary_expression(p); }

    if (t->kind == TK_NUMBER) {
        Node *n = node_new_tok(ND_NUMBER_LITERAL, t);
        compute_line_col(p, t->start, &n->line, &n->col);
        p->pos++;
        return n;
    }
    if (t->kind == TK_CHAR_LIT) {
        Node *n = node_new_tok(ND_CHAR_LITERAL, t);
        compute_line_col(p, t->start, &n->line, &n->col);
        p->pos++;
        return n;
    }
    if (t->kind == TK_STRING_LIT) {
        Node *first = node_new_tok(ND_STRING_LITERAL, t);
        compute_line_col(p, t->start, &first->line, &first->col);
        p->pos++;
        /* Check for concatenated string literals */
        if (cur(p)->kind == TK_STRING_LIT) {
            Node *cat = node_new(ND_CONCATENATED_STRING);
            cat->line = first->line;
            cat->col = first->col;
            node_add_child(cat, first);
            while (cur(p)->kind == TK_STRING_LIT) {
                Token *ct = cur(p);
                Node *s = node_new_tok(ND_STRING_LITERAL, ct);
                compute_line_col(p, ct->start, &s->line, &s->col);
                node_add_child(cat, s);
                p->pos++;
            }
            return cat;
        }
        return first;
    }
    if (t->kind == TK_IDENT) {
        Node *n = wrap_primary_ident(p, t, 0);
        p->pos++;
        return n;
    }
    if (cur_is_punct(p, "(")) {
        /* Parenthesized expression OR statement expression "({...})" — GCC ext */
        if (peek_is_punct(p, 1, "{")) {
            /* statement expression */
            Node *paren = node_new(ND_PARENTHESIZED_EXPRESSION);
            compute_line_col(p, cur(p)->start, &paren->line, &paren->col);
            node_add_child(paren, consume_punct(p));
            Node *cs = parse_compound_statement(p);
            if (cs) node_add_child(paren, cs);
            if (cur_is_punct(p, ")")) node_add_child(paren, consume_punct(p));
            return paren;
        }
        Node *paren = node_new(ND_PARENTHESIZED_EXPRESSION);
        compute_line_col(p, cur(p)->start, &paren->line, &paren->col);
        node_add_child(paren, consume_punct(p));
        Node *inner = parse_expression(p);
        if (inner) node_add_child(paren, inner);
        if (cur_is_punct(p, ")")) node_add_child(paren, consume_punct(p));
        return paren;
    }
    /* Unknown primary — create an error node for a single token */
    Node *err = node_new(ND_ERROR);
    err->start = t->start; err->end = t->end;
    compute_line_col(p, t->start, &err->line, &err->col);
    err->has_error = 1;
    p->pos++;
    return err;
}

static Node *parse_postfix_expression(Parser *p) {
    Node *left = NULL;

    /* Compound literal: (type){ ... } */
    if (cur_is_punct(p, "(") && is_type_name_lookahead(p)) {
        /* Save position to backtrack if needed */
        size_t saved = p->pos;
        Node *lp = consume_punct(p);
        Node *tname = parse_type_name(p);
        if (cur_is_punct(p, ")") && peek_is_punct(p, 1, "{")) {
            Node *rp = consume_punct(p);
            /* Compound literal */
            Node *cl = node_new(ND_COMPOUND_LITERAL_EXPRESSION);
            compute_line_col(p, lp->start, &cl->line, &cl->col);
            node_add_child(cl, lp);
            node_add_child(cl, tname);
            node_add_child(cl, rp);
            Node *init = parse_initializer(p);
            if (init) node_add_child(cl, init);
            left = cl;
        } else {
            /* Cast expression */
            if (!cur_is_punct(p, ")")) {
                /* Couldn't find closing paren; treat as error */
                node_free(tname);
                node_free(lp);
                p->pos = saved;
                left = parse_primary_expression(p);
            } else {
                Node *rp = consume_punct(p);
                Node *cast = node_new(ND_CAST_EXPRESSION);
                compute_line_col(p, lp->start, &cast->line, &cast->col);
                node_add_child(cast, lp);
                node_add_child(cast, tname);
                node_add_child(cast, rp);
                Node *operand = parse_cast_expression(p);
                if (operand) node_add_child(cast, operand);
                /* This is technically a cast expression, returned as left */
                left = cast;
            }
        }
    } else {
        left = parse_primary_expression(p);
    }

    /* Postfix operators */
    while (1) {
        if (cur_is_punct(p, "[")) {
            Node *n = node_new(ND_SUBSCRIPT_EXPRESSION);
            n->line = left->line; n->col = left->col;
            node_add_child(n, left);
            node_add_child(n, consume_punct(p));
            Node *idx = parse_expression(p);
            if (idx) node_add_child(n, idx);
            if (cur_is_punct(p, "]")) node_add_child(n, consume_punct(p));
            left = n;
            continue;
        }
        if (cur_is_punct(p, "(")) {
            Node *call = node_new(ND_CALL_EXPRESSION);
            call->line = left->line; call->col = left->col;
            node_add_child(call, left);
            Node *args = node_new(ND_ARGUMENT_LIST);
            compute_line_col(p, cur(p)->start, &args->line, &args->col);
            node_add_child(args, consume_punct(p));
            while (!cur_is_punct(p, ")") && cur(p)->kind != TK_EOF) {
                Node *a = parse_assignment_expression(p);
                if (a) node_add_child(args, a);
                if (cur_is_punct(p, ",")) node_add_child(args, consume_punct(p));
                else break;
            }
            if (cur_is_punct(p, ")")) node_add_child(args, consume_punct(p));
            node_add_child(call, args);
            left = call;
            continue;
        }
        if (cur_is_punct(p, ".") || cur_is_punct(p, "->")) {
            Node *n = node_new(ND_FIELD_EXPRESSION);
            n->line = left->line; n->col = left->col;
            node_add_child(n, left);
            node_add_child(n, consume_op(p));
            if (cur(p)->kind == TK_IDENT) {
                Token *t = cur(p);
                Node *fi = wrap_primary_ident(p, t, 1);
                p->pos++;
                node_add_child(n, fi);
            }
            left = n;
            continue;
        }
        if (cur_is_punct(p, "++") || cur_is_punct(p, "--")) {
            Node *n = node_new(ND_UPDATE_EXPRESSION);
            n->line = left->line; n->col = left->col;
            node_add_child(n, left);
            node_add_child(n, consume_op(p));
            left = n;
            continue;
        }
        break;
    }
    return left;
}

static Node *parse_unary_expression(Parser *p) {
    Token *t = cur(p);

    if (is_kw(t, "__extension__")) { p->pos++; return parse_unary_expression(p); }

    /* sizeof / _Alignof / __alignof__ */
    if (is_kw(t, "sizeof") || is_kw(t, "_Alignof") || is_kw(t, "alignof") ||
        is_kw(t, "__alignof__") || is_kw(t, "__alignof")) {
        int is_align = !is_kw(t, "sizeof");
        Node *n = node_new(is_align ? ND_ALIGNOF_EXPRESSION : ND_SIZEOF_EXPRESSION);
        compute_line_col(p, t->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, "(")) {
            if (is_type_name_lookahead(p)) {
                node_add_child(n, consume_punct(p));
                Node *tn = parse_type_name(p);
                if (tn) node_add_child(n, tn);
                if (cur_is_punct(p, ")")) node_add_child(n, consume_punct(p));
                return n;
            }
        }
        Node *u = parse_unary_expression(p);
        if (u) node_add_child(n, u);
        return n;
    }

    if (cur_is_punct(p, "++") || cur_is_punct(p, "--")) {
        Node *n = node_new(ND_UPDATE_EXPRESSION);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_op(p));
        Node *u = parse_unary_expression(p);
        if (u) node_add_child(n, u);
        return n;
    }
    if (cur_is_punct(p, "&") || cur_is_punct(p, "*")) {
        Node *n = node_new(ND_POINTER_EXPRESSION);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_op(p));
        Node *u = parse_cast_expression(p);
        if (u) node_add_child(n, u);
        return n;
    }
    if (cur_is_punct(p, "+") || cur_is_punct(p, "-") ||
        cur_is_punct(p, "!") || cur_is_punct(p, "~")) {
        Node *n = node_new(ND_UNARY_EXPRESSION);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_op(p));
        Node *u = parse_cast_expression(p);
        if (u) node_add_child(n, u);
        /* Mirror tree-sitter-c: a trailing postfix ++/-- after the unary's
         * operand attaches to the outer unary. Detect this by unwrapping one
         * level of update_expression whose operator is ++/--. */
        if (u && u->kind == ND_UPDATE_EXPRESSION && u->nchildren >= 2) {
            Node *lst = u->children[u->nchildren - 1];
            Node *first = u->children[0];
            if (lst->kind == ND_OPERATOR && lst->text_len == 2 &&
                (memcmp(lst->text, "++", 2) == 0 || memcmp(lst->text, "--", 2) == 0) &&
                /* only if the operand of update was a primary/postfix-like node */
                (first->kind == ND_IDENTIFIER || first->kind == ND_SUBSCRIPT_EXPRESSION ||
                 first->kind == ND_FIELD_EXPRESSION || first->kind == ND_PARENTHESIZED_EXPRESSION ||
                 first->kind == ND_POINTER_EXPRESSION || first->kind == ND_CALL_EXPRESSION)) {
                /* Remove u from n's children; replace with first. */
                n->children[n->nchildren - 1] = first;
                first->parent = n;
                /* Wrap in update_expression */
                Node *upd = node_new(ND_UPDATE_EXPRESSION);
                upd->line = n->line; upd->col = n->col;
                node_add_child(upd, n);
                node_add_child(upd, lst);
                /* Clear u's child refs and free u shell */
                u->nchildren = 0;
                free(u->children);
                u->children = NULL;
                free(u);
                return upd;
            }
        }
        return n;
    }
    /* __builtin_offsetof, __builtin_choose_expr, __builtin_va_arg treated as calls */
    return parse_postfix_expression(p);
}

static Node *parse_cast_expression(Parser *p) {
    /* Check for cast: ( type ) cast-expression */
    if (cur_is_punct(p, "(") && is_type_name_lookahead(p)) {
        size_t saved = p->pos;
        Node *lp = consume_punct(p);
        Node *tname = parse_type_name(p);
        if (!cur_is_punct(p, ")")) {
            /* Can't complete cast, backtrack */
            node_free(tname);
            node_free(lp);
            p->pos = saved;
            return parse_unary_expression(p);
        }
        /* If followed by '{', this is a compound literal: handle in postfix */
        if (peek_is_punct(p, 1, "{")) {
            node_free(tname);
            node_free(lp);
            p->pos = saved;
            return parse_unary_expression(p);
        }
        Node *rp = consume_punct(p);
        Node *cast = node_new(ND_CAST_EXPRESSION);
        compute_line_col(p, lp->start, &cast->line, &cast->col);
        node_add_child(cast, lp);
        node_add_child(cast, tname);
        node_add_child(cast, rp);
        Node *operand = parse_cast_expression(p);
        if (operand) node_add_child(cast, operand);
        /* Apply postfix operators on cast (for compound literals already handled) */
        return cast;
    }
    return parse_unary_expression(p);
}

/* Binary precedence table */
typedef struct {
    const char *op;
    int prec;   /* higher = tighter binding */
} BinOpInfo;

static BinOpInfo BINOPS[] = {
    {"*", 13}, {"/", 13}, {"%", 13},
    {"+", 12}, {"-", 12},
    {"<<", 11}, {">>", 11},
    {"<", 10}, {">", 10}, {"<=", 10}, {">=", 10},
    {"==", 9}, {"!=", 9},
    {"&", 8},
    {"^", 7},
    {"|", 6},
    {"&&", 5},
    {"||", 4},
};

static int binop_prec(Token *t) {
    if (t->kind != TK_PUNCT) return 0;
    for (size_t i = 0; i < sizeof(BINOPS)/sizeof(*BINOPS); i++) {
        if (t->text_len == strlen(BINOPS[i].op) &&
            memcmp(t->text, BINOPS[i].op, t->text_len) == 0)
            return BINOPS[i].prec;
    }
    return 0;
}

static Node *parse_binary_expression(Parser *p, int min_prec) {
    Node *left = parse_cast_expression(p);
    while (1) {
        Token *t = cur(p);
        int prec = binop_prec(t);
        if (prec < min_prec) break;
        Node *op = consume_op(p);
        Node *right = parse_binary_expression(p, prec + 1);
        Node *bin = node_new(ND_BINARY_EXPRESSION);
        bin->line = left->line; bin->col = left->col;
        node_add_child(bin, left);
        node_add_child(bin, op);
        if (right) node_add_child(bin, right);
        left = bin;
    }
    return left;
}

static Node *parse_conditional_expression(Parser *p) {
    Node *cond = parse_binary_expression(p, 1);
    if (cur_is_punct(p, "?")) {
        Node *n = node_new(ND_CONDITIONAL_EXPRESSION);
        n->line = cond->line; n->col = cond->col;
        node_add_child(n, cond);
        node_add_child(n, consume_op(p));
        Node *mid = parse_expression(p);
        if (mid) node_add_child(n, mid);
        if (cur_is_punct(p, ":")) node_add_child(n, consume_op(p));
        Node *rhs = parse_conditional_expression(p);
        if (rhs) node_add_child(n, rhs);
        return n;
    }
    return cond;
}

static int is_assignment_op(Token *t) {
    if (t->kind != TK_PUNCT) return 0;
    static const char *const ops[] = {
        "=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "&=", "|=", "^="
    };
    for (size_t i = 0; i < sizeof(ops)/sizeof(*ops); i++) {
        if (t->text_len == strlen(ops[i]) &&
            memcmp(t->text, ops[i], t->text_len) == 0) return 1;
    }
    return 0;
}

static Node *parse_assignment_expression(Parser *p) {
    /* Assignment is right-associative; parse conditional then see if assign op */
    Node *left = parse_conditional_expression(p);
    if (is_assignment_op(cur(p))) {
        Node *n = node_new(ND_ASSIGNMENT_EXPRESSION);
        n->line = left->line; n->col = left->col;
        node_add_child(n, left);
        node_add_child(n, consume_op(p));
        Node *right = parse_assignment_expression(p);
        if (right) node_add_child(n, right);
        return n;
    }
    return left;
}

static Node *parse_expression(Parser *p) {
    Node *e = parse_assignment_expression(p);
    if (cur_is_punct(p, ",")) {
        Node *n = node_new(ND_COMMA_EXPRESSION);
        n->line = e->line; n->col = e->col;
        node_add_child(n, e);
        while (cur_is_punct(p, ",")) {
            node_add_child(n, consume_op(p));
            Node *rhs = parse_assignment_expression(p);
            if (rhs) node_add_child(n, rhs);
        }
        return n;
    }
    return e;
}

/* Parse an initializer (expression or brace-enclosed initializer list).
 * Supports designated initializers: .field = expr, [index] = expr.
 */
static Node *parse_initializer(Parser *p) {
    if (cur_is_punct(p, "{")) {
        Node *n = node_new(ND_INITIALIZER_LIST);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_punct(p));
        while (!cur_is_punct(p, "}") && cur(p)->kind != TK_EOF) {
            /* Check for designator */
            if (cur_is_punct(p, ".") || cur_is_punct(p, "[")) {
                Node *pair = node_new(ND_INITIALIZER_PAIR);
                compute_line_col(p, cur(p)->start, &pair->line, &pair->col);
                while (cur_is_punct(p, ".") || cur_is_punct(p, "[")) {
                    if (cur_is_punct(p, ".")) {
                        Node *des = node_new(ND_FIELD_DESIGNATOR);
                        compute_line_col(p, cur(p)->start, &des->line, &des->col);
                        node_add_child(des, consume_op(p));
                        if (cur(p)->kind == TK_IDENT) {
                            Node *fi = wrap_primary_ident(p, cur(p), 1);
                            p->pos++;
                            node_add_child(des, fi);
                        }
                        node_add_child(pair, des);
                    } else {
                        /* [idx] or [a ... b] */
                        Node *des = node_new(ND_SUBSCRIPT_DESIGNATOR);
                        compute_line_col(p, cur(p)->start, &des->line, &des->col);
                        node_add_child(des, consume_punct(p));
                        Node *e = parse_expression(p);
                        if (e) node_add_child(des, e);
                        if (cur_is_punct(p, "]")) node_add_child(des, consume_punct(p));
                        node_add_child(pair, des);
                    }
                }
                if (cur_is_punct(p, "=")) node_add_child(pair, consume_op(p));
                Node *v = parse_initializer(p);
                if (v) node_add_child(pair, v);
                node_add_child(n, pair);
            } else {
                Node *v = parse_initializer(p);
                if (v) node_add_child(n, v);
            }
            if (cur_is_punct(p, ",")) node_add_child(n, consume_punct(p));
            else break;
        }
        if (cur_is_punct(p, "}")) node_add_child(n, consume_punct(p));
        return n;
    }
    return parse_assignment_expression(p);
}

/* ----------------------------------------------------------------------- */
/* Declarations                                                            */
/* ----------------------------------------------------------------------- */

/* Parse a struct-or-union-specifier: struct|union [IDENT] [{ field_list }] */
static Node *parse_struct_or_union_specifier(Parser *p) {
    int is_union = is_kw(cur(p), "union");
    Node *n = node_new(is_union ? ND_UNION_SPECIFIER : ND_STRUCT_SPECIFIER);
    compute_line_col(p, cur(p)->start, &n->line, &n->col);
    node_add_child(n, consume_kw(p));
    /* optional attribute */
    /* (attributes are already stripped in preprocess) */
    if (cur(p)->kind == TK_IDENT && !is_kw(cur(p), "if") && !is_kw(cur(p), "else") &&
        !tok_starts_type(p, 0)) {
        /* tag name */
        Token *t = cur(p);
        Node *id = node_new_tok(ND_TYPE_IDENTIFIER, t);
        compute_line_col(p, t->start, &id->line, &id->col);
        p->pos++;
        node_add_child(n, id);
    } else if (cur(p)->kind == TK_IDENT) {
        /* simple check: if next is '{' or ';' or ',' or ')' treat as tag */
        Token *t = cur(p);
        size_t saved = p->pos;
        p->pos++;
        if (cur_is_punct(p, "{") || cur_is_punct(p, ";") || cur_is_punct(p, ",") ||
            cur_is_punct(p, ")") || cur_is_punct(p, "*") || cur(p)->kind == TK_IDENT) {
            /* It's a tag */
            Node *id = node_new_tok(ND_TYPE_IDENTIFIER, t);
            compute_line_col(p, t->start, &id->line, &id->col);
            node_add_child(n, id);
        } else {
            p->pos = saved;
        }
    }
    if (cur_is_punct(p, "{")) {
        Node *flist = node_new(ND_FIELD_DECLARATION_LIST);
        compute_line_col(p, cur(p)->start, &flist->line, &flist->col);
        node_add_child(flist, consume_punct(p));
        while (!cur_is_punct(p, "}") && cur(p)->kind != TK_EOF) {
            /* Field declaration: decl-specs init-declarator-list[? with bitfields] ; */
            Node *fd = node_new(ND_FIELD_DECLARATION);
            compute_line_col(p, cur(p)->start, &fd->line, &fd->col);
            int is_typedef = 0;
            Node *specs = parse_declaration_specifiers(p, &is_typedef);
            if (specs) {
                /* Splice specs children into fd */
                for (size_t i = 0; i < specs->nchildren; i++) {
                    node_add_child(fd, specs->children[i]);
                }
                free(specs->children);
                free(specs);
            }
            /* Comma-separated declarators possibly with bitfield : width */
            if (!cur_is_punct(p, ";")) {
                while (1) {
                    Node *decl = parse_declarator(p, 0);
                    if (decl) node_add_child(fd, decl);
                    if (cur_is_punct(p, ":")) {
                        Node *bf = node_new(ND_BITFIELD_CLAUSE);
                        compute_line_col(p, cur(p)->start, &bf->line, &bf->col);
                        node_add_child(bf, consume_punct(p));
                        Node *w = parse_conditional_expression(p);
                        if (w) node_add_child(bf, w);
                        node_add_child(fd, bf);
                    }
                    if (cur_is_punct(p, ",")) {
                        node_add_child(fd, consume_punct(p));
                        continue;
                    }
                    break;
                }
            }
            if (cur_is_punct(p, ";")) node_add_child(fd, consume_punct(p));
            else {
                /* skip until ; or } to recover */
                while (!cur_is_punct(p, ";") && !cur_is_punct(p, "}") &&
                       cur(p)->kind != TK_EOF) p->pos++;
                if (cur_is_punct(p, ";")) node_add_child(fd, consume_punct(p));
            }
            node_add_child(flist, fd);
        }
        if (cur_is_punct(p, "}")) node_add_child(flist, consume_punct(p));
        node_add_child(n, flist);
    }
    return n;
}

static Node *parse_enum_specifier(Parser *p) {
    Node *n = node_new(ND_ENUM_SPECIFIER);
    compute_line_col(p, cur(p)->start, &n->line, &n->col);
    node_add_child(n, consume_kw(p));
    if (cur(p)->kind == TK_IDENT) {
        Token *t = cur(p);
        Node *id = node_new_tok(ND_TYPE_IDENTIFIER, t);
        compute_line_col(p, t->start, &id->line, &id->col);
        p->pos++;
        node_add_child(n, id);
    }
    if (cur_is_punct(p, "{")) {
        Node *body = node_new(ND_FIELD_DECLARATION_LIST);
        compute_line_col(p, cur(p)->start, &body->line, &body->col);
        node_add_child(body, consume_punct(p));
        while (!cur_is_punct(p, "}") && cur(p)->kind != TK_EOF) {
            if (cur(p)->kind == TK_IDENT) {
                Node *e = node_new(ND_ENUMERATOR);
                compute_line_col(p, cur(p)->start, &e->line, &e->col);
                Node *id = wrap_primary_ident(p, cur(p), 0);
                p->pos++;
                node_add_child(e, id);
                if (cur_is_punct(p, "=")) {
                    node_add_child(e, consume_op(p));
                    Node *v = parse_conditional_expression(p);
                    if (v) node_add_child(e, v);
                }
                node_add_child(body, e);
            } else p->pos++;
            if (cur_is_punct(p, ",")) node_add_child(body, consume_punct(p));
            else break;
        }
        if (cur_is_punct(p, "}")) node_add_child(body, consume_punct(p));
        node_add_child(n, body);
    }
    return n;
}

/* Parse declaration specifiers: storage-class / type qualifier / type specifier /
 * function specifier, in any order. Stops when no more specifiers.
 */
static Node *parse_declaration_specifiers(Parser *p, int *out_is_typedef) {
    Node *list = node_new(ND_DECLARATION);  /* placeholder; caller splices children */
    compute_line_col(p, cur(p)->start, &list->line, &list->col);
    int got_type = 0;
    int got_primitive = 0;
    while (1) {
        Token *t = cur(p);
        if (is_kw(t, "__extension__")) { p->pos++; continue; }
        if (is_storage_class_kw(t)) {
            if (is_kw(t, "typedef") && out_is_typedef) *out_is_typedef = 1;
            Node *c = consume_as(p, ND_STORAGE_CLASS_SPECIFIER);
            node_add_child(list, c);
            continue;
        }
        if (is_type_qualifier_kw(t)) {
            Node *c = consume_as(p, ND_TYPE_QUALIFIER);
            node_add_child(list, c);
            continue;
        }
        if (is_function_specifier_kw(t)) {
            Node *c = consume_as(p, ND_FUNCTION_SPECIFIER);
            node_add_child(list, c);
            continue;
        }
        if (is_primitive_type_kw(t)) {
            /* Only one primitive allowed. */
            if (got_primitive) break;
            /* If a primitive follows another type spec AND is followed by a
             * declarator-terminating token (;,=,[,(), treat it as the
             * declarator name rather than a specifier. This handles
             * typedef/declarations like "typedef unsigned short uint16_t;"
             * where uint16_t is the name but matches primitive_type_kw. */
            if (got_type && p->pos + 1 < p->toks->len) {
                Token *nx = &p->toks->items[p->pos + 1];
                if (nx->kind == TK_PUNCT &&
                    (nx->text_len == 1 && (nx->text[0] == ';' || nx->text[0] == ',' ||
                                           nx->text[0] == '=' || nx->text[0] == '[' ||
                                           nx->text[0] == '('))) {
                    /* Exception: "int" and "char" after sized are normal
                     * (e.g. "long int x;" where x is followed by ';'). These
                     * are true primitive completions. */
                    int is_canonical = (t->text_len == 3 && memcmp(t->text, "int", 3) == 0) ||
                                       (t->text_len == 4 && memcmp(t->text, "char", 4) == 0) ||
                                       (t->text_len == 5 && memcmp(t->text, "short", 5) == 0) ||
                                       (t->text_len == 4 && memcmp(t->text, "long", 4) == 0) ||
                                       (t->text_len == 4 && memcmp(t->text, "void", 4) == 0) ||
                                       (t->text_len == 5 && memcmp(t->text, "float", 5) == 0) ||
                                       (t->text_len == 6 && memcmp(t->text, "double", 6) == 0) ||
                                       (t->text_len == 5 && memcmp(t->text, "_Bool", 5) == 0);
                    if (!is_canonical) break;
                }
            }
            Node *c = consume_as(p, ND_PRIMITIVE_TYPE);
            node_add_child(list, c);
            got_type = 1;
            got_primitive = 1;
            continue;
        }
        if (is_sized_type_kw(t)) {
            Node *c = consume_as(p, ND_SIZED_TYPE_SPECIFIER);
            node_add_child(list, c);
            got_type = 1;
            continue;
        }
        if (is_struct_like_kw(t)) {
            if (is_kw(t, "enum")) node_add_child(list, parse_enum_specifier(p));
            else node_add_child(list, parse_struct_or_union_specifier(p));
            got_type = 1;
            continue;
        }
        if ((is_kw(t, "typeof") || is_kw(t, "__typeof") || is_kw(t, "__typeof__")) &&
            peek_is_punct(p, 1, "(")) {
            /* typeof(...) — treat as a sized_type_specifier surrounding the call */
            Node *c = node_new(ND_SIZED_TYPE_SPECIFIER);
            compute_line_col(p, t->start, &c->line, &c->col);
            node_add_child(c, consume_kw(p));
            node_add_child(c, consume_punct(p));
            int depth = 1;
            while (cur(p)->kind != TK_EOF && depth > 0) {
                if (cur_is_punct(p, "(")) depth++;
                else if (cur_is_punct(p, ")")) { depth--; if (depth == 0) break; }
                Node *cc = consume_as(p, ND_PUNCT);
                node_add_child(c, cc);
            }
            if (cur_is_punct(p, ")")) node_add_child(c, consume_punct(p));
            node_add_child(list, c);
            got_type = 1;
            continue;
        }
        if (t->kind == TK_IDENT && !got_type &&
            smap_has_n(&p->typedefs, t->text, t->text_len)) {
            Node *c = consume_as(p, ND_TYPE_IDENTIFIER);
            node_add_child(list, c);
            got_type = 1;
            continue;
        }
        break;
    }
    return list;
}

/* Parse a declarator (possibly pointer/array/function). Abstract = no name. */
static Node *parse_direct_declarator(Parser *p, int abstract);

static Node *parse_declarator(Parser *p, int abstract) {
    /* Chain of pointer declarators */
    if (cur_is_punct(p, "*")) {
        Node *ptr = node_new(abstract ? ND_ABSTRACT_POINTER_DECLARATOR : ND_POINTER_DECLARATOR);
        compute_line_col(p, cur(p)->start, &ptr->line, &ptr->col);
        node_add_child(ptr, consume_op(p));
        /* qualifiers after * */
        while (cur(p)->kind == TK_IDENT && is_type_qualifier_kw(cur(p))) {
            node_add_child(ptr, consume_as(p, ND_TYPE_QUALIFIER));
        }
        Node *inner = parse_declarator(p, abstract);
        if (inner) node_add_child(ptr, inner);
        return ptr;
    }
    return parse_direct_declarator(p, abstract);
}

static Node *parse_direct_declarator(Parser *p, int abstract) {
    Node *core = NULL;
    if (cur_is_punct(p, "(")) {
        /* Either (declarator) or (parameter-list)-suffix */
        /* If followed by ')' or types, it's a parameter list on an abstract declarator */
        size_t saved = p->pos;
        /* Heuristic: if next token is ')' or starts a type, treat as function declarator suffix
         *  That only applies when we have no name (abstract) or we've already consumed the name.
         *  So here, parenthesized declarator means: ( declarator )
         *  We'll try parenthesized_declarator first; if parse_declarator fails to find one, backtrack.
         */
        if (abstract && (peek_is_punct(p, 1, ")") || tok_starts_type(p, 1))) {
            /* abstract function declarator: ( parameter-list ) */
            goto after_core;
        }
        Node *lp = consume_punct(p);
        Node *inner = parse_declarator(p, abstract);
        if (cur_is_punct(p, ")")) {
            Node *paren = node_new(ND_PARENTHESIZED_DECLARATOR);
            compute_line_col(p, lp->start, &paren->line, &paren->col);
            node_add_child(paren, lp);
            if (inner) node_add_child(paren, inner);
            node_add_child(paren, consume_punct(p));
            core = paren;
        } else {
            node_free(inner);
            node_free(lp);
            p->pos = saved;
            /* abstract function declarator fallthrough */
        }
    } else if (cur(p)->kind == TK_IDENT && !is_type_qualifier_kw(cur(p)) &&
               !is_storage_class_kw(cur(p)) && !is_function_specifier_kw(cur(p))) {
        /* ident: the declarator name */
        Token *t = cur(p);
        Node *id = node_new_tok(ND_IDENTIFIER, t);
        compute_line_col(p, t->start, &id->line, &id->col);
        p->pos++;
        core = id;
    }
after_core:;
    /* Suffix: [..] (params) */
    while (1) {
        if (cur_is_punct(p, "[")) {
            Node *arr = node_new(ND_ARRAY_DECLARATOR);
            if (core) { arr->line = core->line; arr->col = core->col; }
            else compute_line_col(p, cur(p)->start, &arr->line, &arr->col);
            if (core) node_add_child(arr, core);
            node_add_child(arr, consume_punct(p));
            /* optional qualifiers / static */
            while (cur(p)->kind == TK_IDENT &&
                   (is_type_qualifier_kw(cur(p)) || is_kw(cur(p), "static"))) {
                node_add_child(arr, consume_as(p, is_kw(cur(p), "static") ? ND_KEYWORD : ND_TYPE_QUALIFIER));
            }
            if (!cur_is_punct(p, "]")) {
                Node *e = parse_assignment_expression(p);
                if (e) node_add_child(arr, e);
            }
            if (cur_is_punct(p, "]")) node_add_child(arr, consume_punct(p));
            core = arr;
            continue;
        }
        if (cur_is_punct(p, "(")) {
            /* function declarator: followed by parameter list */
            Node *fd = node_new(ND_FUNCTION_DECLARATOR);
            if (core) { fd->line = core->line; fd->col = core->col; }
            else compute_line_col(p, cur(p)->start, &fd->line, &fd->col);
            if (core) node_add_child(fd, core);
            Node *pl = parse_parameter_list(p);
            if (pl) node_add_child(fd, pl);
            core = fd;
            continue;
        }
        break;
    }
    if (!core) {
        /* Abstract declarator with no inner — synthesize empty node at cur position */
        core = node_new(abstract ? ND_ABSTRACT_POINTER_DECLARATOR : ND_IDENTIFIER);
        core->start = cur(p)->start;
        core->end = cur(p)->start;
        compute_line_col(p, cur(p)->start, &core->line, &core->col);
    }
    return core;
}

static Node *parse_parameter_list(Parser *p) {
    Node *pl = node_new(ND_PARAMETER_LIST);
    compute_line_col(p, cur(p)->start, &pl->line, &pl->col);
    if (!cur_is_punct(p, "(")) return pl;
    node_add_child(pl, consume_punct(p));
    while (!cur_is_punct(p, ")") && cur(p)->kind != TK_EOF) {
        if (cur_is_punct(p, "...")) {
            Node *v = consume_as(p, ND_VARIADIC_PARAMETER);
            node_add_child(pl, v);
            break;
        }
        Node *pd = node_new(ND_PARAMETER_DECLARATION);
        compute_line_col(p, cur(p)->start, &pd->line, &pd->col);
        int is_typedef = 0;
        Node *specs = parse_declaration_specifiers(p, &is_typedef);
        if (specs) {
            for (size_t i = 0; i < specs->nchildren; i++)
                node_add_child(pd, specs->children[i]);
            free(specs->children);
            free(specs);
        }
        /* Optional declarator (abstract or named) */
        if (!cur_is_punct(p, ",") && !cur_is_punct(p, ")")) {
            /* Decide if abstract: we can try parse_declarator; if no ident found, it's abstract */
            /* Heuristic: if current token is '*', '(' (followed by type/ptr/')') or '[', it's abstract start */
            int abstract = 0;
            if (cur_is_punct(p, "*") || cur_is_punct(p, "[")) abstract = 0; /* could be either */
            Node *d = parse_declarator(p, abstract);
            if (d) node_add_child(pd, d);
        }
        node_add_child(pl, pd);
        if (cur_is_punct(p, ",")) node_add_child(pl, consume_punct(p));
        else break;
    }
    if (cur_is_punct(p, ")")) node_add_child(pl, consume_punct(p));
    return pl;
}

static Node *parse_type_name(Parser *p) {
    Node *tn = node_new(ND_TYPE_DESCRIPTOR);
    compute_line_col(p, cur(p)->start, &tn->line, &tn->col);
    int is_td = 0;
    Node *specs = parse_declaration_specifiers(p, &is_td);
    if (specs) {
        for (size_t i = 0; i < specs->nchildren; i++)
            node_add_child(tn, specs->children[i]);
        free(specs->children);
        free(specs);
    }
    if (!cur_is_punct(p, ")")) {
        /* abstract declarator */
        Node *d = parse_declarator(p, 1);
        if (d) node_add_child(tn, d);
    }
    return tn;
}

/* ----------------------------------------------------------------------- */
/* Statements                                                              */
/* ----------------------------------------------------------------------- */

static int starts_declaration(Parser *p) {
    return tok_starts_type(p, 0);
}

/* Extract identifier name from a declarator subtree */
static const char *declarator_name_ref(Node *n, size_t *out_len) {
    if (!n) return NULL;
    if (n->kind == ND_IDENTIFIER || n->kind == ND_FIELD_IDENTIFIER ||
        n->kind == ND_TYPE_IDENTIFIER) {
        *out_len = n->text_len;
        return n->text;
    }
    if (n->kind == ND_STRUCT_SPECIFIER || n->kind == ND_UNION_SPECIFIER ||
        n->kind == ND_ENUM_SPECIFIER || n->kind == ND_FIELD_DECLARATION_LIST)
        return NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        const char *r = declarator_name_ref(n->children[i], out_len);
        if (r) return r;
    }
    return NULL;
}

static int has_function_declarator_in(Node *n) {
    if (!n) return 0;
    if (n->kind == ND_FUNCTION_DECLARATOR) return 1;
    for (size_t i = 0; i < n->nchildren; i++) {
        if (has_function_declarator_in(n->children[i])) return 1;
    }
    return 0;
}

/* Try to parse a declaration, possibly a function definition if allow_fn_def. */
static Node *parse_declaration(Parser *p, int allow_fn_def) {
    Node *d = node_new(ND_DECLARATION);
    compute_line_col(p, cur(p)->start, &d->line, &d->col);
    int is_typedef = 0;
    Node *specs = parse_declaration_specifiers(p, &is_typedef);
    if (specs) {
        for (size_t i = 0; i < specs->nchildren; i++)
            node_add_child(d, specs->children[i]);
        free(specs->children);
        free(specs);
    }
    /* Empty decl (just ';') is valid for struct forward decl */
    if (cur_is_punct(p, ";")) {
        node_add_child(d, consume_punct(p));
        return d;
    }
    /* Comma-separated init-declarators */
    StrList decl_names; sl_init(&decl_names);
    int first = 1;
    int is_fn_def = 0;
    while (1) {
        Node *decl = parse_declarator(p, 0);
        size_t nl;
        const char *nm = decl ? declarator_name_ref(decl, &nl) : NULL;
        if (nm) sl_push_n(&decl_names, nm, nl);
        else sl_push_null(&decl_names);

        /* If first declarator is a function, check for function definition */
        if (first && allow_fn_def && decl && has_function_declarator_in(decl) &&
            cur_is_punct(p, "{")) {
            /* It's a function definition */
            Node *fd = node_new(ND_FUNCTION_DEFINITION);
            fd->line = d->line; fd->col = d->col;
            /* Move all children of d (specs) into fd, plus the declarator */
            for (size_t i = 0; i < d->nchildren; i++)
                node_add_child(fd, d->children[i]);
            free(d->children);
            d->children = NULL; d->nchildren = 0; d->cap = 0;
            node_free(d);
            node_add_child(fd, decl);
            /* Parameters shadow typedefs for the duration of the body.
             * Save the outer typedef set, remove any typedef name that also
             * names a parameter, parse the body, then restore. */
            StrMap saved_fn_typedefs;
            smap_copy(&saved_fn_typedefs, &p->typedefs);
            /* Walk the declarator's parameter list to collect parameter names. */
            Node *funcd = NULL;
            for (size_t i = 0; i < decl->nchildren; i++) {
                if (decl->children[i]->kind == ND_FUNCTION_DECLARATOR) {
                    funcd = decl->children[i]; break;
                }
            }
            if (!funcd && decl->kind == ND_FUNCTION_DECLARATOR) funcd = decl;
            if (funcd) {
                for (size_t i = 0; i < funcd->nchildren; i++) {
                    Node *pl = funcd->children[i];
                    if (pl->kind != ND_PARAMETER_LIST) continue;
                    for (size_t j = 0; j < pl->nchildren; j++) {
                        Node *pd = pl->children[j];
                        if (pd->kind != ND_PARAMETER_DECLARATION) continue;
                        /* Extract name only from declarator-side children,
                         * skipping type specifiers (ND_TYPE_IDENTIFIER etc). */
                        for (size_t k = 0; k < pd->nchildren; k++) {
                            Node *pc = pd->children[k];
                            if (pc->kind != ND_IDENTIFIER &&
                                pc->kind != ND_POINTER_DECLARATOR &&
                                pc->kind != ND_ARRAY_DECLARATOR &&
                                pc->kind != ND_FUNCTION_DECLARATOR &&
                                pc->kind != ND_PARENTHESIZED_DECLARATOR)
                                continue;
                            size_t nl;
                            const char *nm = declarator_name_ref(pc, &nl);
                            if (nm) {
                                char *key = xstrndup(nm, nl);
                                smap_remove(&p->typedefs, key);
                                free(key);
                            }
                            break;
                        }
                    }
                }
            }
            Node *body = parse_compound_statement(p);
            if (body) node_add_child(fd, body);
            /* Restore typedefs to outer state (re-adding params' typedef
             * shadows and undoing any body-escaped changes). */
            smap_free(&p->typedefs);
            p->typedefs = saved_fn_typedefs;
            is_fn_def = 1;
            /* typedef names don't apply to function definitions */
            sl_free(&decl_names);
            return fd;
        }
        if (decl) node_add_child(d, decl);
        if (cur_is_punct(p, "=")) {
            /* init_declarator: wrap decl + "=" + initializer */
            /* Replace decl with an init_declarator containing decl, =, init */
            Node *id = node_new(ND_INIT_DECLARATOR);
            id->line = decl->line; id->col = decl->col;
            /* Pop decl from d's children */
            d->nchildren--;
            node_add_child(id, decl);
            node_add_child(id, consume_op(p));
            Node *init = parse_initializer(p);
            if (init) node_add_child(id, init);
            node_add_child(d, id);
        }
        if (cur_is_punct(p, ",")) {
            node_add_child(d, consume_punct(p));
            first = 0;
            continue;
        }
        break;
    }
    if (cur_is_punct(p, ";")) node_add_child(d, consume_punct(p));
    /* Register typedef names, or remove shadowed typedefs for plain variables.
     * Enclosing compound_statement save/restore re-creates outer typedefs at
     * block exit, so removing here only affects the current scope. */
    if (is_typedef && !is_fn_def) {
        for (size_t i = 0; i < decl_names.len; i++) {
            if (decl_names.items[i])
                smap_put(&p->typedefs, decl_names.items[i], (void *)1);
        }
    } else if (!is_fn_def) {
        for (size_t i = 0; i < decl_names.len; i++) {
            if (decl_names.items[i])
                smap_remove(&p->typedefs, decl_names.items[i]);
        }
    }
    sl_free(&decl_names);
    /* Convert to type_definition if typedef */
    if (is_typedef && !is_fn_def) d->kind = ND_TYPE_DEFINITION;
    return d;
}

static Node *parse_compound_statement(Parser *p) {
    Node *n = node_new(ND_COMPOUND_STATEMENT);
    compute_line_col(p, cur(p)->start, &n->line, &n->col);
    if (!cur_is_punct(p, "{")) return n;
    node_add_child(n, consume_punct(p));
    /* Block-scope typedef names: snapshot current typedef set, let inner
     * declarations extend it, then restore on exit. */
    StrMap saved_typedefs;
    smap_copy(&saved_typedefs, &p->typedefs);
    while (!cur_is_punct(p, "}") && cur(p)->kind != TK_EOF) {
        Node *s = NULL;
        if (starts_declaration(p)) s = parse_declaration(p, 0);
        else s = parse_statement(p);
        if (s) node_add_child(n, s);
        else break;
    }
    if (cur_is_punct(p, "}")) node_add_child(n, consume_punct(p));
    smap_free(&p->typedefs);
    p->typedefs = saved_typedefs;
    return n;
}

static Node *parse_expression_statement(Parser *p) {
    Node *n = node_new(ND_EXPRESSION_STATEMENT);
    compute_line_col(p, cur(p)->start, &n->line, &n->col);
    if (!cur_is_punct(p, ";")) {
        Node *e = parse_expression(p);
        if (e) node_add_child(n, e);
    }
    if (cur_is_punct(p, ";")) node_add_child(n, consume_punct(p));
    return n;
}

static Node *parse_statement(Parser *p) {
    Token *t = cur(p);
    if (cur_is_punct(p, "{")) return parse_compound_statement(p);
    if (cur_is_punct(p, ";")) {
        Node *es = node_new(ND_EXPRESSION_STATEMENT);
        compute_line_col(p, cur(p)->start, &es->line, &es->col);
        node_add_child(es, consume_punct(p));
        return es;
    }
    if (is_kw(t, "if")) {
        Node *n = node_new(ND_IF_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, "(")) node_add_child(n, consume_punct(p));
        Node *e = parse_expression(p);
        if (e) node_add_child(n, e);
        if (cur_is_punct(p, ")")) node_add_child(n, consume_punct(p));
        Node *s = parse_statement(p);
        if (s) node_add_child(n, s);
        if (is_kw(cur(p), "else")) {
            node_add_child(n, consume_kw(p));
            Node *s2 = parse_statement(p);
            if (s2) node_add_child(n, s2);
        }
        return n;
    }
    if (is_kw(t, "for")) {
        Node *n = node_new(ND_FOR_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, "(")) node_add_child(n, consume_punct(p));
        /* init clause */
        if (!cur_is_punct(p, ";")) {
            if (starts_declaration(p)) {
                Node *d = parse_declaration(p, 0);
                if (d) node_add_child(n, d);
            } else {
                Node *es = parse_expression_statement(p);
                if (es) node_add_child(n, es);
            }
        } else node_add_child(n, consume_punct(p));
        /* cond clause */
        if (!cur_is_punct(p, ";")) {
            Node *e = parse_expression(p);
            if (e) node_add_child(n, e);
        }
        if (cur_is_punct(p, ";")) node_add_child(n, consume_punct(p));
        /* update clause */
        if (!cur_is_punct(p, ")")) {
            Node *e = parse_expression(p);
            if (e) node_add_child(n, e);
        }
        if (cur_is_punct(p, ")")) node_add_child(n, consume_punct(p));
        Node *s = parse_statement(p);
        if (s) node_add_child(n, s);
        return n;
    }
    if (is_kw(t, "while")) {
        Node *n = node_new(ND_WHILE_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, "(")) node_add_child(n, consume_punct(p));
        Node *e = parse_expression(p);
        if (e) node_add_child(n, e);
        if (cur_is_punct(p, ")")) node_add_child(n, consume_punct(p));
        Node *s = parse_statement(p);
        if (s) node_add_child(n, s);
        return n;
    }
    if (is_kw(t, "do")) {
        Node *n = node_new(ND_DO_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        Node *s = parse_statement(p);
        if (s) node_add_child(n, s);
        if (is_kw(cur(p), "while")) node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, "(")) node_add_child(n, consume_punct(p));
        Node *e = parse_expression(p);
        if (e) node_add_child(n, e);
        if (cur_is_punct(p, ")")) node_add_child(n, consume_punct(p));
        if (cur_is_punct(p, ";")) node_add_child(n, consume_punct(p));
        return n;
    }
    if (is_kw(t, "switch")) {
        Node *n = node_new(ND_SWITCH_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, "(")) node_add_child(n, consume_punct(p));
        Node *e = parse_expression(p);
        if (e) node_add_child(n, e);
        if (cur_is_punct(p, ")")) node_add_child(n, consume_punct(p));
        Node *s = parse_statement(p);
        if (s) node_add_child(n, s);
        return n;
    }
    if (is_kw(t, "case") || is_kw(t, "default")) {
        Node *n = node_new(ND_CASE_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (!is_kw(t, "default")) {
            Node *e = parse_conditional_expression(p);
            if (e) node_add_child(n, e);
        }
        if (cur_is_punct(p, ":")) node_add_child(n, consume_punct(p));
        /* optional statement attached */
        while (!cur_is_punct(p, "}") && !is_kw(cur(p), "case") && !is_kw(cur(p), "default") &&
               cur(p)->kind != TK_EOF) {
            Node *s;
            if (starts_declaration(p)) s = parse_declaration(p, 0);
            else s = parse_statement(p);
            if (s) node_add_child(n, s);
            else break;
        }
        return n;
    }
    if (is_kw(t, "return")) {
        Node *n = node_new(ND_RETURN_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (!cur_is_punct(p, ";")) {
            Node *e = parse_expression(p);
            if (e) node_add_child(n, e);
        }
        if (cur_is_punct(p, ";")) node_add_child(n, consume_punct(p));
        return n;
    }
    if (is_kw(t, "break")) {
        Node *n = node_new(ND_BREAK_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, ";")) node_add_child(n, consume_punct(p));
        return n;
    }
    if (is_kw(t, "continue")) {
        Node *n = node_new(ND_CONTINUE_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur_is_punct(p, ";")) node_add_child(n, consume_punct(p));
        return n;
    }
    if (is_kw(t, "goto")) {
        Node *n = node_new(ND_GOTO_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        node_add_child(n, consume_kw(p));
        if (cur(p)->kind == TK_IDENT) {
            Node *id = wrap_primary_ident(p, cur(p), 0);
            p->pos++;
            node_add_child(n, id);
        }
        if (cur_is_punct(p, ";")) node_add_child(n, consume_punct(p));
        return n;
    }
    /* labeled statement: IDENT : stmt */
    if (t->kind == TK_IDENT && peek_is_punct(p, 1, ":") &&
        !tok_starts_type(p, 0)) {
        Node *n = node_new(ND_LABELED_STATEMENT);
        compute_line_col(p, cur(p)->start, &n->line, &n->col);
        Node *id = wrap_primary_ident(p, cur(p), 0);
        p->pos++;
        node_add_child(n, id);
        node_add_child(n, consume_punct(p));
        Node *s = parse_statement(p);
        if (s) node_add_child(n, s);
        return n;
    }
    /* declaration inside block is handled in parse_compound_statement. Here we only get exprs. */
    return parse_expression_statement(p);
}

static Node *parse_translation_unit(Parser *p) {
    Node *tu = node_new(ND_TRANSLATION_UNIT);
    tu->start = 0;
    tu->end = p->src_len;
    while (cur(p)->kind != TK_EOF) {
        Node *d = NULL;
        if (starts_declaration(p)) d = parse_declaration(p, 1);
        else {
            /* Allow stray ';' or expression statements at top level */
            if (cur_is_punct(p, ";")) {
                Node *es = node_new(ND_EXPRESSION_STATEMENT);
                compute_line_col(p, cur(p)->start, &es->line, &es->col);
                node_add_child(es, consume_punct(p));
                d = es;
            } else {
                /* Skip unknown token */
                p->pos++;
                continue;
            }
        }
        if (d) node_add_child(tu, d);
    }
    if (tu->nchildren > 0) tu->end = tu->children[tu->nchildren - 1]->end;
    return tu;
}

/* ========================================================================= */
/* Pointer / type tracker                                                    */
/* ========================================================================= */

/* Narrow integer types (from Python NARROW_TYPES set) */
static int is_narrow_type_text(const char *s, size_t n) {
    static const char *const nts[] = {
        "char", "signed char", "unsigned char",
        "short", "unsigned short", "short int", "unsigned short int",
        "int", "signed", "signed int", "unsigned", "unsigned int",
        "long", "signed long", "unsigned long", "long int", "unsigned long int",
        "long long", "signed long long", "unsigned long long",
        "long long int", "unsigned long long int",
    };
    for (size_t i = 0; i < sizeof(nts)/sizeof(*nts); i++) {
        size_t l = strlen(nts[i]);
        if (l == n && memcmp(nts[i], s, l) == 0) return 1;
    }
    return 0;
}

/* Struct field info */
typedef struct {
    char *name;         /* field name */
    char *narrow_type;  /* narrow type string or NULL */
} FieldInfo;

typedef struct {
    FieldInfo *items;
    size_t len;
    size_t cap;
} FieldList;

static void fl_init(FieldList *l) { l->items = NULL; l->len = 0; l->cap = 0; }
static void fl_push(FieldList *l, const char *name, const char *nt) {
    if (l->len == l->cap) {
        l->cap = l->cap ? l->cap * 2 : 4;
        l->items = xrealloc(l->items, l->cap * sizeof(*l->items));
    }
    l->items[l->len].name = xstrdup(name);
    l->items[l->len].narrow_type = nt ? xstrdup(nt) : NULL;
    l->len++;
}
static void fl_free(FieldList *l) {
    for (size_t i = 0; i < l->len; i++) {
        free(l->items[i].name);
        free(l->items[i].narrow_type);
    }
    free(l->items);
    l->items = NULL; l->len = 0; l->cap = 0;
}
static FieldList *fl_clone(FieldList *src) {
    FieldList *d = xmalloc(sizeof(*d));
    fl_init(d);
    for (size_t i = 0; i < src->len; i++) fl_push(d, src->items[i].name, src->items[i].narrow_type);
    return d;
}
static void free_fieldlist_val(void *p) {
    if (!p) return;
    FieldList *l = (FieldList *)p;
    fl_free(l);
    free(l);
}

/* PointerTracker — mirrors the Python class */
typedef struct {
    StrMap pointer_names;     /* name -> (void*)1 */
    StrMap array_names;
    StrMap array_sizes;       /* name -> StrList* of dim strings or NULL entries */
    StrMap var_types;         /* name -> char* declared type */
    StrMap deep_pointer_names;
    StrMap pointer_type_names; /* typedef names that are pointer/array types */
    StrMap narrow_type_names;  /* typedef names that are narrow integer types */
    StrMap pointer_returning_funcs;
    StrMap pointer_fields;    /* global pointer field names */
    StrMap struct_pointer_fields; /* struct name -> StrMap* of field names */
    StrMap struct_narrow_fields;  /* struct name -> StrMap* of field name -> char* type */
    StrMap typedef_struct_names;  /* typedef name -> struct name (char*) */
    StrMap var_struct_types;      /* variable name -> struct name (char*) */
    StrMap func_param_narrow;     /* func name -> StrList* (NULL or type per param) */
    StrMap bitfield_fields;
    StrMap struct_bitfield_fields; /* struct name -> StrMap* of bitfield names */
    StrMap struct_fields_ordered;  /* struct name -> FieldList* */
    char *func_return_type;       /* owned or NULL */
} Tracker;

static void tracker_init(Tracker *t) {
    smap_init(&t->pointer_names);
    smap_init(&t->array_names);
    smap_init(&t->array_sizes);
    smap_init(&t->var_types);
    smap_init(&t->deep_pointer_names);
    smap_init(&t->pointer_type_names);
    smap_init(&t->narrow_type_names);
    smap_init(&t->pointer_returning_funcs);
    smap_init(&t->pointer_fields);
    smap_init(&t->struct_pointer_fields);
    smap_init(&t->struct_narrow_fields);
    smap_init(&t->typedef_struct_names);
    smap_init(&t->var_struct_types);
    smap_init(&t->func_param_narrow);
    smap_init(&t->bitfield_fields);
    smap_init(&t->struct_bitfield_fields);
    smap_init(&t->struct_fields_ordered);
    t->func_return_type = NULL;
}

static void smap_free_nested_smap(void *p) {
    if (!p) return;
    StrMap *m = (StrMap *)p;
    smap_free_vals(m, free_cstr);
    free(m);
}

static void smap_free_nested_smap_nov(void *p) {
    if (!p) return;
    StrMap *m = (StrMap *)p;
    smap_free(m);
    free(m);
}

static void tracker_free(Tracker *t) {
    smap_free(&t->pointer_names);
    smap_free(&t->array_names);
    smap_free_vals(&t->array_sizes, free_strlist_val);
    smap_free_vals(&t->var_types, free_cstr);
    smap_free(&t->deep_pointer_names);
    smap_free(&t->pointer_type_names);
    smap_free(&t->narrow_type_names);
    smap_free(&t->pointer_returning_funcs);
    smap_free(&t->pointer_fields);
    smap_free_vals(&t->struct_pointer_fields, smap_free_nested_smap_nov);
    smap_free_vals(&t->struct_narrow_fields, smap_free_nested_smap);
    smap_free_vals(&t->typedef_struct_names, free_cstr);
    smap_free_vals(&t->var_struct_types, free_cstr);
    smap_free_vals(&t->func_param_narrow, free_strlist_val);
    smap_free(&t->bitfield_fields);
    smap_free_vals(&t->struct_bitfield_fields, smap_free_nested_smap_nov);
    smap_free_vals(&t->struct_fields_ordered, free_fieldlist_val);
    free(t->func_return_type);
    t->func_return_type = NULL;
}

/* Copy constructor (deep where needed so nested maps aren't aliased) */
static void tracker_copy(Tracker *dst, Tracker *src) {
    smap_copy(&dst->pointer_names, &src->pointer_names);
    smap_copy(&dst->array_names, &src->array_names);
    /* array_sizes: values are StrList*, clone them */
    smap_init(&dst->array_sizes);
    for (size_t i = 0; i < src->array_sizes.nbuckets; i++) {
        for (StrEntry *e = src->array_sizes.buckets[i]; e; e = e->next) {
            StrList *cloned = sl_new_copy((StrList *)e->val);
            smap_put_n(&dst->array_sizes, e->key, e->klen, cloned);
        }
    }
    smap_copy_dup_strs(&dst->var_types, &src->var_types);
    smap_copy(&dst->deep_pointer_names, &src->deep_pointer_names);
    smap_copy(&dst->pointer_type_names, &src->pointer_type_names);
    smap_copy(&dst->narrow_type_names, &src->narrow_type_names);
    smap_copy(&dst->pointer_returning_funcs, &src->pointer_returning_funcs);
    smap_copy(&dst->pointer_fields, &src->pointer_fields);
    smap_init(&dst->struct_pointer_fields);
    for (size_t i = 0; i < src->struct_pointer_fields.nbuckets; i++) {
        for (StrEntry *e = src->struct_pointer_fields.buckets[i]; e; e = e->next) {
            StrMap *orig = (StrMap *)e->val;
            StrMap *nm = xmalloc(sizeof(*nm));
            smap_copy(nm, orig);
            smap_put_n(&dst->struct_pointer_fields, e->key, e->klen, nm);
        }
    }
    smap_init(&dst->struct_narrow_fields);
    for (size_t i = 0; i < src->struct_narrow_fields.nbuckets; i++) {
        for (StrEntry *e = src->struct_narrow_fields.buckets[i]; e; e = e->next) {
            StrMap *orig = (StrMap *)e->val;
            StrMap *nm = xmalloc(sizeof(*nm));
            smap_copy_dup_strs(nm, orig);
            smap_put_n(&dst->struct_narrow_fields, e->key, e->klen, nm);
        }
    }
    smap_copy_dup_strs(&dst->typedef_struct_names, &src->typedef_struct_names);
    smap_copy_dup_strs(&dst->var_struct_types, &src->var_struct_types);
    smap_init(&dst->func_param_narrow);
    for (size_t i = 0; i < src->func_param_narrow.nbuckets; i++) {
        for (StrEntry *e = src->func_param_narrow.buckets[i]; e; e = e->next) {
            StrList *cloned = sl_new_copy((StrList *)e->val);
            smap_put_n(&dst->func_param_narrow, e->key, e->klen, cloned);
        }
    }
    smap_copy(&dst->bitfield_fields, &src->bitfield_fields);
    smap_init(&dst->struct_bitfield_fields);
    for (size_t i = 0; i < src->struct_bitfield_fields.nbuckets; i++) {
        for (StrEntry *e = src->struct_bitfield_fields.buckets[i]; e; e = e->next) {
            StrMap *orig = (StrMap *)e->val;
            StrMap *nm = xmalloc(sizeof(*nm));
            smap_copy(nm, orig);
            smap_put_n(&dst->struct_bitfield_fields, e->key, e->klen, nm);
        }
    }
    smap_init(&dst->struct_fields_ordered);
    for (size_t i = 0; i < src->struct_fields_ordered.nbuckets; i++) {
        for (StrEntry *e = src->struct_fields_ordered.buckets[i]; e; e = e->next) {
            FieldList *cloned = fl_clone((FieldList *)e->val);
            smap_put_n(&dst->struct_fields_ordered, e->key, e->klen, cloned);
        }
    }
    dst->func_return_type = src->func_return_type ? xstrdup(src->func_return_type) : NULL;
}

/* ----- AST helpers --------------------------------------------------- */

static int has_pointer_declarator(Node *n) {
    if (!n) return 0;
    if (n->kind == ND_POINTER_DECLARATOR || n->kind == ND_ABSTRACT_POINTER_DECLARATOR) return 1;
    /* Don't recurse into value-producing expressions */
    if (n->kind == ND_SIZEOF_EXPRESSION || n->kind == ND_ALIGNOF_EXPRESSION ||
        n->kind == ND_CALL_EXPRESSION || n->kind == ND_BINARY_EXPRESSION ||
        n->kind == ND_UNARY_EXPRESSION || n->kind == ND_CONDITIONAL_EXPRESSION ||
        n->kind == ND_NUMBER_LITERAL || n->kind == ND_STRING_LITERAL ||
        n->kind == ND_PARENTHESIZED_EXPRESSION) return 0;
    for (size_t i = 0; i < n->nchildren; i++)
        if (has_pointer_declarator(n->children[i])) return 1;
    return 0;
}

static int has_array_declarator(Node *n) {
    if (!n) return 0;
    if (n->kind == ND_ARRAY_DECLARATOR) return 1;
    for (size_t i = 0; i < n->nchildren; i++)
        if (has_array_declarator(n->children[i])) return 1;
    return 0;
}

static int has_nested_pointer_declarator(Node *n) {
    if (!n) return 0;
    if (n->kind == ND_POINTER_DECLARATOR || n->kind == ND_ABSTRACT_POINTER_DECLARATOR) {
        for (size_t i = 0; i < n->nchildren; i++)
            if (has_pointer_declarator(n->children[i])) return 1;
        return 0;
    }
    for (size_t i = 0; i < n->nchildren; i++)
        if (has_nested_pointer_declarator(n->children[i])) return 1;
    return 0;
}

/* Return pointer to name within the source and its length */
static char *extract_declarator_name(Node *n, const char *src) {
    size_t l;
    const char *p = declarator_name_ref(n, &l);
    if (!p) return NULL;
    (void)src;
    return xstrndup(p, l);
}

/* Extract array dimensions (outermost to innermost) from a declarator subtree.
 * Returns StrList* or NULL if no dims at all. NULL entries = unsized.
 */
static StrList *extract_array_dims(Node *n, const char *src) {
    if (!n) return NULL;
    if (n->kind == ND_ARRAY_DECLARATOR) {
        /* size is inside this array_declarator, between [ and ] */
        char *size_str = NULL;
        Node *inner = NULL;
        int in_brackets = 0;
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_PUNCT && c->text_len == 1 && c->text[0] == '[') { in_brackets = 1; continue; }
            if (c->kind == ND_PUNCT && c->text_len == 1 && c->text[0] == ']') { in_brackets = 0; continue; }
            if (in_brackets) {
                /* Only take the expression child, not qualifiers */
                if (c->kind == ND_TYPE_QUALIFIER || c->kind == ND_KEYWORD) continue;
                size_t a = c->start, b = c->end;
                free(size_str);
                size_str = xstrndup(src + a, b - a);
                /* strip leading/trailing whitespace */
                while (size_str[0] && isspace((unsigned char)size_str[0])) memmove(size_str, size_str + 1, strlen(size_str));
                size_t l = strlen(size_str);
                while (l > 0 && isspace((unsigned char)size_str[l-1])) size_str[--l] = 0;
                continue;
            }
            if (c->kind == ND_ARRAY_DECLARATOR) inner = c;
        }
        StrList *inner_dims = inner ? extract_array_dims(inner, src) : NULL;
        StrList *r = NULL;
        if (inner_dims) {
            r = inner_dims;
            sl_push(r, size_str);
        } else {
            r = xmalloc(sizeof(*r));
            sl_init(r);
            sl_push(r, size_str);
        }
        free(size_str);
        return r;
    }
    if (n->kind == ND_INIT_DECLARATOR || n->kind == ND_POINTER_DECLARATOR ||
        n->kind == ND_PARENTHESIZED_DECLARATOR || n->kind == ND_ABSTRACT_POINTER_DECLARATOR) {
        for (size_t i = 0; i < n->nchildren; i++) {
            StrList *r = extract_array_dims(n->children[i], src);
            if (r) return r;
        }
    }
    return NULL;
}

static char *find_enclosing_struct_name(Node *n, const char *src) {
    Node *p = n->parent;
    while (p) {
        if (p->kind == ND_STRUCT_SPECIFIER || p->kind == ND_UNION_SPECIFIER) {
            for (size_t i = 0; i < p->nchildren; i++) {
                if (p->children[i]->kind == ND_TYPE_IDENTIFIER) {
                    return xstrndup(src + p->children[i]->start,
                                    p->children[i]->end - p->children[i]->start);
                }
            }
            /* anonymous: check if inside typedef; use typedef declarator name */
            if (p->parent && p->parent->kind == ND_TYPE_DEFINITION) {
                char *nm = extract_declarator_name(p->parent, src);
                if (nm) return nm;
            }
            char buf[64];
            snprintf(buf, sizeof(buf), "__anon_%zu", p->start);
            return xstrdup(buf);
        }
        p = p->parent;
    }
    return NULL;
}

/* Tracker scan — visits nodes to populate symbol tables */
static void tracker_visit(Tracker *t, Node *n, const char *src, int skip_fn_bodies,
                          int skip_nested_blocks, Node *root);

/* Determine if a parameter_declaration is NOT inside a function_definition's params */
static int inside_funcptr_type(Node *n) {
    Node *p = n->parent;
    while (p) {
        if (p->kind == ND_FUNCTION_DEFINITION) return 0;
        p = p->parent;
    }
    return 1;
}

static char *find_func_name_in(Node *n, const char *src) {
    if (!n) return NULL;
    if (n->kind == ND_FUNCTION_DECLARATOR) {
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_IDENTIFIER)
                return xstrndup(src + c->start, c->end - c->start);
            if (c->kind == ND_PARENTHESIZED_DECLARATOR) {
                char *r = extract_declarator_name(c, src);
                if (r) return r;
            }
        }
    }
    for (size_t i = 0; i < n->nchildren; i++) {
        char *r = find_func_name_in(n->children[i], src);
        if (r) return r;
    }
    return NULL;
}

/* Extract the type-specifier text from a declaration's children (primitive or
 * sized_type_specifier or type_identifier), possibly joined for sized specs. */
static char *extract_type_specifier_text(Node *n, const char *src) {
    /* Look for a primitive/sized/type_identifier child. For sized specs,
       concatenate consecutive ones (e.g. "unsigned long"). */
    Str out; str_init(&out);
    int found = 0;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER ||
            c->kind == ND_TYPE_IDENTIFIER) {
            if (found) str_append_ch(&out, ' ');
            str_append(&out, src + c->start, c->end - c->start);
            found = 1;
        }
    }
    if (!found) { str_free(&out); return NULL; }
    return str_detach(&out);
}

static void extract_struct_type_name(Node *n, const char *src, char **out) {
    *out = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_STRUCT_SPECIFIER || c->kind == ND_UNION_SPECIFIER) {
            for (size_t j = 0; j < c->nchildren; j++) {
                Node *g = c->children[j];
                if (g->kind == ND_TYPE_IDENTIFIER) {
                    *out = xstrndup(src + g->start, g->end - g->start);
                    return;
                }
            }
            char buf[64];
            snprintf(buf, sizeof(buf), "__anon_%zu", c->start);
            *out = xstrdup(buf);
            return;
        }
    }
}

/* Called on declaration / parameter_declaration / field_declaration */
static void check_declaration(Tracker *t, Node *n, const char *src) {
    /* Extract type info */
    char *type_text = NULL;
    char *struct_name = NULL;
    int is_ptr_typedef = 0;

    /* First pass: scan children for type info (not declarators) */
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER) {
            /* Concatenate into type_text */
            if (!type_text) type_text = xstrndup(src + c->start, c->end - c->start);
            else {
                Str s; str_init(&s);
                str_append_cstr(&s, type_text);
                str_append_ch(&s, ' ');
                str_append(&s, src + c->start, c->end - c->start);
                free(type_text);
                type_text = str_detach(&s);
            }
        } else if (c->kind == ND_TYPE_IDENTIFIER) {
            if (!type_text) type_text = xstrndup(src + c->start, c->end - c->start);
            /* Check pointer typedef */
            if (smap_has(&t->pointer_type_names, type_text))
                is_ptr_typedef = 1;
        } else if (c->kind == ND_STRUCT_SPECIFIER || c->kind == ND_UNION_SPECIFIER) {
            int found_tag = 0;
            for (size_t j = 0; j < c->nchildren; j++) {
                Node *g = c->children[j];
                if (g->kind == ND_TYPE_IDENTIFIER) {
                    struct_name = xstrndup(src + g->start, g->end - g->start);
                    found_tag = 1;
                    break;
                }
            }
            if (!found_tag) {
                char buf[64];
                snprintf(buf, sizeof(buf), "__anon_%zu", c->start);
                struct_name = xstrdup(buf);
            }
        }
    }

    /* Second pass: each declarator */
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind != ND_INIT_DECLARATOR && c->kind != ND_POINTER_DECLARATOR &&
            c->kind != ND_ARRAY_DECLARATOR && c->kind != ND_FUNCTION_DECLARATOR &&
            c->kind != ND_IDENTIFIER && c->kind != ND_PARENTHESIZED_DECLARATOR)
            continue;
        char *name = extract_declarator_name(c, src);
        if (!name) continue;
        /* Shadow previous */
        smap_remove(&t->pointer_names, name);
        smap_remove(&t->array_names, name);
        {
            StrEntry *e = smap_find_e(&t->array_sizes, name, strlen(name));
            if (e) {
                sl_free((StrList *)e->val);
                free(e->val);
                smap_remove(&t->array_sizes, name);
            }
        }
        smap_remove(&t->deep_pointer_names, name);
        {
            StrEntry *e = smap_find_e(&t->var_types, name, strlen(name));
            if (e) { free(e->val); smap_remove(&t->var_types, name); }
        }
        {
            StrEntry *e = smap_find_e(&t->var_struct_types, name, strlen(name));
            if (e) { free(e->val); smap_remove(&t->var_struct_types, name); }
        }
        if (has_pointer_declarator(c)) {
            smap_put(&t->pointer_names, name, (void *)1);
            if (has_array_declarator(c) || has_nested_pointer_declarator(c))
                smap_put(&t->deep_pointer_names, name, (void *)1);
        }
        if (has_array_declarator(c)) {
            smap_put(&t->array_names, name, (void *)1);
        }
        StrList *dims = extract_array_dims(c, src);
        if (dims) smap_put(&t->array_sizes, name, dims);
        if (is_ptr_typedef) smap_put(&t->pointer_names, name, (void *)1);
        if (type_text) smap_put(&t->var_types, name, xstrdup(type_text));
        if (struct_name) smap_put(&t->var_struct_types, name, xstrdup(struct_name));
        else if (type_text) {
            char *sn = smap_get(&t->typedef_struct_names, type_text);
            if (sn) smap_put(&t->var_struct_types, name, xstrdup(sn));
        }
        free(name);
    }
    free(type_text);
    free(struct_name);
}

static void check_typedef(Tracker *t, Node *n, const char *src) {
    /* Find the name being defined */
    char *name = NULL;
    /* Look for a declarator identifier */
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_INIT_DECLARATOR || c->kind == ND_POINTER_DECLARATOR ||
            c->kind == ND_ARRAY_DECLARATOR || c->kind == ND_FUNCTION_DECLARATOR ||
            c->kind == ND_IDENTIFIER || c->kind == ND_PARENTHESIZED_DECLARATOR) {
            name = extract_declarator_name(c, src);
            if (name) break;
        }
    }
    if (!name) return;

    /* Pointer/array typedef */
    int is_ptr_or_arr = 0;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (has_pointer_declarator(c) || has_array_declarator(c)) { is_ptr_or_arr = 1; break; }
    }
    if (is_ptr_or_arr) {
        smap_put(&t->pointer_type_names, name, (void *)1);
    } else {
        /* Chain: typedef resolves to another typedef that's a pointer */
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_TYPE_IDENTIFIER) {
                char *tt = xstrndup(src + c->start, c->end - c->start);
                if (strcmp(tt, name) != 0 && smap_has(&t->pointer_type_names, tt)) {
                    smap_put(&t->pointer_type_names, name, (void *)1);
                }
                free(tt);
            }
        }
        /* Narrow typedef */
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER ||
                c->kind == ND_TYPE_IDENTIFIER) {
                char *tt = xstrndup(src + c->start, c->end - c->start);
                if (strcmp(tt, name) == 0) { free(tt); continue; }
                if (is_narrow_type_text(tt, strlen(tt)) || smap_has(&t->narrow_type_names, tt)) {
                    smap_put(&t->narrow_type_names, name, (void *)1);
                    free(tt);
                    break;
                }
                free(tt);
            }
        }
    }
    /* typedef struct */
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_STRUCT_SPECIFIER || c->kind == ND_UNION_SPECIFIER) {
            char *snm = NULL;
            for (size_t j = 0; j < c->nchildren; j++) {
                Node *g = c->children[j];
                if (g->kind == ND_TYPE_IDENTIFIER) {
                    snm = xstrndup(src + g->start, g->end - g->start);
                    break;
                }
            }
            if (!snm) snm = xstrdup(name);
            smap_put(&t->typedef_struct_names, name, snm);
            break;
        }
    }
    free(name);
}

static void check_func_return(Tracker *t, Node *n, const char *src) {
    /* pointer-returning function: TYPE *name(...) */
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_POINTER_DECLARATOR) {
            char *nm = find_func_name_in(c, src);
            if (nm) {
                smap_put(&t->pointer_returning_funcs, nm, (void *)1);
                free(nm);
            }
        }
    }
}

static void check_func_params(Tracker *t, Node *n, const char *src) {
    /* Find function_declarator */
    Node *fd = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_FUNCTION_DECLARATOR) { fd = c; break; }
        if (c->kind == ND_POINTER_DECLARATOR) {
            /* pointer-returning function */
            for (size_t j = 0; j < c->nchildren; j++) {
                if (c->children[j]->kind == ND_FUNCTION_DECLARATOR) {
                    fd = c->children[j]; break;
                }
                if (c->children[j]->kind == ND_POINTER_DECLARATOR) {
                    /* nested pointer declarator */
                    for (size_t k = 0; k < c->children[j]->nchildren; k++)
                        if (c->children[j]->children[k]->kind == ND_FUNCTION_DECLARATOR) {
                            fd = c->children[j]->children[k]; break;
                        }
                }
            }
            if (fd) break;
        }
    }
    if (!fd) return;
    /* Extract func name */
    char *fname = NULL;
    Node *pl = NULL;
    for (size_t i = 0; i < fd->nchildren; i++) {
        Node *c = fd->children[i];
        if (c->kind == ND_IDENTIFIER) fname = xstrndup(src + c->start, c->end - c->start);
        else if (c->kind == ND_PARENTHESIZED_DECLARATOR) fname = extract_declarator_name(c, src);
        else if (c->kind == ND_PARAMETER_LIST) pl = c;
    }
    if (!fname || !pl) { free(fname); return; }

    StrList *ptypes = xmalloc(sizeof(*ptypes));
    sl_init(ptypes);
    int any = 0;
    for (size_t i = 0; i < pl->nchildren; i++) {
        Node *pd = pl->children[i];
        if (pd->kind == ND_VARIADIC_PARAMETER) break;
        if (pd->kind != ND_PARAMETER_DECLARATION) continue;
        int is_ptr = has_pointer_declarator(pd);
        int is_arr = has_array_declarator(pd);
        char *tt = NULL;
        for (size_t j = 0; j < pd->nchildren; j++) {
            Node *c = pd->children[j];
            if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER) {
                if (!tt) tt = xstrndup(src + c->start, c->end - c->start);
                else {
                    Str s; str_init(&s);
                    str_append_cstr(&s, tt);
                    str_append_ch(&s, ' ');
                    str_append(&s, src + c->start, c->end - c->start);
                    free(tt);
                    tt = str_detach(&s);
                }
            } else if (c->kind == ND_TYPE_IDENTIFIER) {
                if (!tt) tt = xstrndup(src + c->start, c->end - c->start);
            }
        }
        if (is_ptr || is_arr || !tt) sl_push_null(ptypes);
        else if (is_narrow_type_text(tt, strlen(tt)) || smap_has(&t->narrow_type_names, tt)) {
            sl_push(ptypes, tt);
            any = 1;
        } else sl_push_null(ptypes);
        free(tt);
    }
    if (any) {
        StrEntry *e = smap_find_e(&t->func_param_narrow, fname, strlen(fname));
        if (e) { sl_free((StrList *)e->val); free(e->val); }
        smap_put(&t->func_param_narrow, fname, ptypes);
    } else {
        sl_free(ptypes);
        free(ptypes);
    }
    free(fname);
}

static void check_field(Tracker *t, Node *n, const char *src) {
    /* Extract field name */
    char *name = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_INIT_DECLARATOR || c->kind == ND_POINTER_DECLARATOR ||
            c->kind == ND_ARRAY_DECLARATOR || c->kind == ND_FUNCTION_DECLARATOR ||
            c->kind == ND_IDENTIFIER || c->kind == ND_PARENTHESIZED_DECLARATOR ||
            c->kind == ND_FIELD_IDENTIFIER) {
            if (!name) name = extract_declarator_name(c, src);
        }
    }
    if (!name) return;

    char *struct_name = find_enclosing_struct_name(n, src);

    /* Bit-field? */
    int is_bf = 0;
    for (size_t i = 0; i < n->nchildren; i++) {
        if (n->children[i]->kind == ND_BITFIELD_CLAUSE) { is_bf = 1; break; }
    }
    if (is_bf) {
        smap_put(&t->bitfield_fields, name, (void *)1);
        if (struct_name) {
            StrMap *m = smap_get(&t->struct_bitfield_fields, struct_name);
            if (!m) {
                m = xmalloc(sizeof(*m));
                smap_init(m);
                smap_put(&t->struct_bitfield_fields, struct_name, m);
            }
            smap_put(m, name, (void *)1);
        }
    }

    /* Pointer/array field? */
    int is_pa = 0;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if ((c->kind == ND_POINTER_DECLARATOR || c->kind == ND_ARRAY_DECLARATOR ||
             c->kind == ND_FUNCTION_DECLARATOR) &&
            (has_pointer_declarator(c) || has_array_declarator(c))) {
            is_pa = 1; break;
        }
        if (c->kind == ND_TYPE_IDENTIFIER) {
            char *tt = xstrndup(src + c->start, c->end - c->start);
            if (smap_has(&t->pointer_type_names, tt)) is_pa = 1;
            free(tt);
            if (is_pa) break;
        }
    }
    if (is_pa) {
        smap_put(&t->pointer_fields, name, (void *)1);
        if (struct_name) {
            StrMap *m = smap_get(&t->struct_pointer_fields, struct_name);
            if (!m) {
                m = xmalloc(sizeof(*m));
                smap_init(m);
                smap_put(&t->struct_pointer_fields, struct_name, m);
            }
            smap_put(m, name, (void *)1);
        }
    }

    /* Narrow type? */
    char *narrow_type = NULL;
    if (!is_pa && struct_name) {
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER ||
                c->kind == ND_TYPE_IDENTIFIER) {
                char *tt = xstrndup(src + c->start, c->end - c->start);
                /* join consecutive sized specs */
                size_t j = i + 1;
                while (j < n->nchildren) {
                    Node *g = n->children[j];
                    if (g->kind == ND_SIZED_TYPE_SPECIFIER || g->kind == ND_PRIMITIVE_TYPE) {
                        Str s; str_init(&s);
                        str_append_cstr(&s, tt);
                        str_append_ch(&s, ' ');
                        str_append(&s, src + g->start, g->end - g->start);
                        free(tt);
                        tt = str_detach(&s);
                        j++;
                    } else break;
                }
                if (is_narrow_type_text(tt, strlen(tt)) || smap_has(&t->narrow_type_names, tt)) {
                    narrow_type = tt;
                    StrMap *m = smap_get(&t->struct_narrow_fields, struct_name);
                    if (!m) {
                        m = xmalloc(sizeof(*m));
                        smap_init(m);
                        smap_put(&t->struct_narrow_fields, struct_name, m);
                    }
                    smap_put(m, name, xstrdup(narrow_type));
                    break;
                }
                free(tt);
            }
        }
    }

    if (struct_name) {
        FieldList *fl = smap_get(&t->struct_fields_ordered, struct_name);
        if (!fl) {
            fl = xmalloc(sizeof(*fl));
            fl_init(fl);
            smap_put(&t->struct_fields_ordered, struct_name, fl);
        }
        fl_push(fl, name, narrow_type);
    }
    free(name);
    free(narrow_type);
    free(struct_name);
}

static void tracker_visit(Tracker *t, Node *n, const char *src, int skip_fn_bodies,
                          int skip_nested_blocks, Node *root) {
    if (!n) return;
    if (skip_fn_bodies && n->kind == ND_FUNCTION_DEFINITION) {
        check_func_return(t, n, src);
        check_func_params(t, n, src);
        /* Still recurse into declarator (struct specifiers) but not body */
        for (size_t i = 0; i < n->nchildren; i++) {
            if (n->children[i]->kind != ND_COMPOUND_STATEMENT)
                tracker_visit(t, n->children[i], src, skip_fn_bodies, skip_nested_blocks, root);
        }
        return;
    }
    if (skip_nested_blocks && (n->kind == ND_COMPOUND_STATEMENT || n->kind == ND_FOR_STATEMENT)
        && n != root) return;

    if (n->kind == ND_DECLARATION || n->kind == ND_PARAMETER_DECLARATION ||
        n->kind == ND_FIELD_DECLARATION) {
        if (n->kind != ND_PARAMETER_DECLARATION || !inside_funcptr_type(n)) {
            check_declaration(t, n, src);
        }
    }
    if (n->kind == ND_TYPE_DEFINITION) check_typedef(t, n, src);
    if (n->kind == ND_FUNCTION_DEFINITION || n->kind == ND_DECLARATION) {
        check_func_return(t, n, src);
        check_func_params(t, n, src);
    }
    if (n->kind == ND_FIELD_DECLARATION) check_field(t, n, src);

    for (size_t i = 0; i < n->nchildren; i++)
        tracker_visit(t, n->children[i], src, skip_fn_bodies, skip_nested_blocks, root);
}

static void tracker_scan(Tracker *t, Node *root, const char *src, int global_only, int skip_nested_blocks) {
    tracker_visit(t, root, src, global_only, skip_nested_blocks, root);
}

/* ========================================================================= */
/* Rewriter                                                                  */
/* ========================================================================= */

typedef struct {
    const char *src;
    size_t src_len;
    size_t *suppressed;
    size_t nsup;
    Range *disabled;
    size_t ndis;
} Rewriter;

static int rw_is_disabled(Rewriter *r, Node *n) {
    for (size_t i = 0; i < r->ndis; i++) {
        if (n->start >= r->disabled[i].start && n->end <= r->disabled[i].end)
            return 1;
    }
    return 0;
}

/* Return 1 if a @ marker appears just before the operator token of this node. */
static int rw_is_suppressed_at(Rewriter *r, Node *n, size_t op_start) {
    for (size_t i = 0; i < r->nsup; i++) {
        size_t pos = r->suppressed[i];
        size_t lo = n->start > 0 ? n->start - 1 : 0;
        if (pos < op_start && pos >= lo) {
            /* between pos+1 and op_start, only whitespace allowed */
            int ok = 1;
            for (size_t j = pos + 1; j < op_start; j++) {
                char c = r->src[j];
                if (c != ' ' && c != '\t') { ok = 0; break; }
            }
            if (ok) return 1;
        }
    }
    return 0;
}

static int rw_is_suppressed(Rewriter *r, Node *n, const char *const ops[], size_t nops) {
    /* find the operator child of n */
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_OPERATOR || c->kind == ND_KEYWORD || c->kind == ND_PUNCT) {
            for (size_t k = 0; k < nops; k++) {
                size_t ol = strlen(ops[k]);
                if (c->text_len == ol && memcmp(c->text, ops[k], ol) == 0) {
                    return rw_is_suppressed_at(r, n, c->start);
                }
            }
        }
    }
    return 0;
}

/* Copy source[start:end], stripping @ at suppressed positions */
static void strip_markers_into(Rewriter *r, size_t start, size_t end, Str *out) {
    size_t i = start;
    for (size_t k = 0; k < r->nsup; k++) {
        size_t sp = r->suppressed[k];
        if (sp < i) continue;
        if (sp >= end) break;
        if (sp > i) str_append(out, r->src + i, sp - i);
        i = sp + 1;
    }
    if (i < end) str_append(out, r->src + i, end - i);
}

static char *strip_markers(Rewriter *r, size_t start, size_t end) {
    Str s; str_init(&s);
    strip_markers_into(r, start, end, &s);
    if (!s.data) return xstrdup("");
    return str_detach(&s);
}

/* Forward decl */
static char *transform(Node *n, Rewriter *r, Tracker *t);
static char *transform_children(Node *n, Rewriter *r, Tracker *t);
static char *try_rewrite(Node *n, Rewriter *r, Tracker *t);

/* Floating-point detection */
static int is_float_expr(Node *n, const char *src) {
    if (!n) return 0;
    if (n->kind == ND_NUMBER_LITERAL) {
        char *text = xstrndup(src + n->start, n->end - n->start);
        int fl = 0;
        size_t l = strlen(text);
        if (strchr(text, '.')) fl = 1;
        else {
            /* e/E exponent but not hex */
            if (text[0] != '0' || (l > 1 && text[1] != 'x' && text[1] != 'X')) {
                if (strchr(text, 'e') || strchr(text, 'E')) fl = 1;
            }
            char last = l ? text[l-1] : 0;
            if ((last == 'f' || last == 'F') && !(text[0] == '0' && l > 1 && (text[1] == 'x' || text[1] == 'X'))) fl = 1;
        }
        free(text);
        return fl;
    }
    if (n->kind == ND_CAST_EXPRESSION) {
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_TYPE_DESCRIPTOR) {
                for (size_t j = 0; j < c->nchildren; j++) {
                    Node *g = c->children[j];
                    if (g->kind == ND_PRIMITIVE_TYPE || g->kind == ND_SIZED_TYPE_SPECIFIER) {
                        char *tt = xstrndup(src + g->start, g->end - g->start);
                        int fl = 0;
                        if (strcmp(tt, "float") == 0 || strcmp(tt, "double") == 0 ||
                            strcmp(tt, "long double") == 0 ||
                            strcmp(tt, "_Float16") == 0 || strcmp(tt, "_Float32") == 0 ||
                            strcmp(tt, "_Float64") == 0 || strcmp(tt, "_Float128") == 0) fl = 1;
                        free(tt);
                        if (fl) return 1;
                    }
                }
            }
        }
    }
    if (n->kind == ND_PARENTHESIZED_EXPRESSION) {
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind != ND_PUNCT && c->kind != ND_OPERATOR)
                return is_float_expr(c, src);
        }
    }
    if (n->kind == ND_BINARY_EXPRESSION && n->nchildren >= 3) {
        return is_float_expr(n->children[0], src) || is_float_expr(n->children[2], src);
    }
    return 0;
}

/* Is a node a compile-time constant expression? */
static int is_const_expr(Node *n, const char *src) {
    if (!n) return 0;
    if (n->kind == ND_NUMBER_LITERAL || n->kind == ND_CHAR_LITERAL) return 1;
    if (n->kind == ND_PARENTHESIZED_EXPRESSION) {
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind != ND_PUNCT) return is_const_expr(c, src);
        }
        return 0;
    }
    if (n->kind == ND_UNARY_EXPRESSION && n->nchildren >= 2) {
        Node *op = n->children[0];
        if (op->kind == ND_OPERATOR && op->text_len == 1 &&
            (op->text[0] == '+' || op->text[0] == '-' || op->text[0] == '~' || op->text[0] == '!')) {
            return is_const_expr(n->children[1], src);
        }
    }
    if (n->kind == ND_CAST_EXPRESSION) {
        /* skip pointer cast */
        if (has_pointer_declarator(n)) return 0;
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind != ND_PUNCT && c->kind != ND_TYPE_DESCRIPTOR)
                return is_const_expr(c, src);
        }
    }
    if (n->kind == ND_BINARY_EXPRESSION && n->nchildren == 3) {
        return is_const_expr(n->children[0], src) && is_const_expr(n->children[2], src);
    }
    if (n->kind == ND_SIZEOF_EXPRESSION) return 1;
    return 0;
}

/* Is a node inside a function body? (detects where statement expressions are valid) */
static int inside_function(Node *n) {
    Node *p = n->parent;
    while (p) {
        if (p->kind == ND_COMPOUND_STATEMENT) return 1;
        if (p->kind == ND_TRANSLATION_UNIT) return 0;
        p = p->parent;
    }
    return 0;
}

/* Extract cast target type from a cast_expression */
static char *extract_cast_type(Node *n, const char *src) {
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_TYPE_DESCRIPTOR) {
            Str out; str_init(&out);
            int any = 0;
            for (size_t j = 0; j < c->nchildren; j++) {
                Node *g = c->children[j];
                if (g->kind == ND_PRIMITIVE_TYPE || g->kind == ND_SIZED_TYPE_SPECIFIER ||
                    g->kind == ND_TYPE_IDENTIFIER) {
                    if (any) str_append_ch(&out, ' ');
                    str_append(&out, src + g->start, g->end - g->start);
                    any = 1;
                }
            }
            if (!any) { str_free(&out); return NULL; }
            return str_detach(&out);
        }
    }
    return NULL;
}

/* Type of an assignment LHS for narrowing (or NULL) */
static char *get_lhs_narrow_type(Node *left, const char *src, Tracker *t) {
    if (left->kind == ND_IDENTIFIER) {
        char *name = xstrndup(src + left->start, left->end - left->start);
        if (!smap_has(&t->pointer_names, name)) {
            char *vt = smap_get(&t->var_types, name);
            if (vt && (is_narrow_type_text(vt, strlen(vt)) || smap_has(&t->narrow_type_names, vt))) {
                free(name);
                return xstrdup(vt);
            }
        }
        free(name);
    } else if (left->kind == ND_SUBSCRIPT_EXPRESSION && left->nchildren >= 1) {
        Node *base = left->children[0];
        if (base->kind == ND_IDENTIFIER) {
            char *name = xstrndup(src + base->start, base->end - base->start);
            if (smap_has(&t->deep_pointer_names, name)) { free(name); return NULL; }
            char *vt = smap_get(&t->var_types, name);
            if (vt && (is_narrow_type_text(vt, strlen(vt)) || smap_has(&t->narrow_type_names, vt))) {
                free(name);
                return xstrdup(vt);
            }
            free(name);
        }
    } else if (left->kind == ND_POINTER_EXPRESSION && left->nchildren == 2) {
        Node *op = left->children[0];
        if (op->kind == ND_OPERATOR && op->text_len == 1 && op->text[0] == '*') {
            Node *inner = left->children[1];
            if (inner->kind == ND_IDENTIFIER) {
                char *name = xstrndup(src + inner->start, inner->end - inner->start);
                if (!smap_has(&t->deep_pointer_names, name)) {
                    char *vt = smap_get(&t->var_types, name);
                    if (vt && (is_narrow_type_text(vt, strlen(vt)) || smap_has(&t->narrow_type_names, vt))) {
                        free(name);
                        return xstrdup(vt);
                    }
                }
                free(name);
            }
        }
    } else if (left->kind == ND_FIELD_EXPRESSION) {
        Node *base = NULL, *fi = NULL;
        for (size_t i = 0; i < left->nchildren; i++) {
            Node *c = left->children[i];
            if (c->kind == ND_OPERATOR && i + 1 < left->nchildren) {
                fi = left->children[i+1];
                base = i > 0 ? left->children[i-1] : NULL;
                break;
            }
        }
        if (base && fi && fi->kind == ND_FIELD_IDENTIFIER && base->kind == ND_IDENTIFIER) {
            char *bn = xstrndup(src + base->start, base->end - base->start);
            char *sn = smap_get(&t->var_struct_types, bn);
            free(bn);
            if (sn) {
                StrMap *nf = smap_get(&t->struct_narrow_fields, sn);
                if (nf) {
                    char *fn = xstrndup(src + fi->start, fi->end - fi->start);
                    char *tt = smap_get(nf, fn);
                    free(fn);
                    if (tt) return xstrdup(tt);
                }
            }
        }
    }
    return NULL;
}

/* is_pointer_expr — mirrors Python's PointerTracker.is_pointer_expr */
static int is_pointer_expr(Node *n, const char *src, Tracker *t) {
    if (!n) return 0;
    if (n->kind == ND_IDENTIFIER) {
        char *name = xstrndup(src + n->start, n->end - n->start);
        int r = smap_has(&t->pointer_names, name) || smap_has(&t->array_names, name);
        free(name);
        return r;
    }
    if (n->kind == ND_STRING_LITERAL || n->kind == ND_CONCATENATED_STRING) return 1;
    if (n->kind == ND_POINTER_EXPRESSION && n->nchildren == 2) {
        Node *op = n->children[0];
        Node *inner = n->children[1];
        if (op->kind == ND_OPERATOR && op->text_len == 1 && op->text[0] == '&') return 1;
        if (op->kind == ND_OPERATOR && op->text_len == 1 && op->text[0] == '*' &&
            inner->kind == ND_IDENTIFIER) {
            char *nm = xstrndup(src + inner->start, inner->end - inner->start);
            int r = smap_has(&t->deep_pointer_names, nm);
            free(nm);
            if (r) return 1;
        }
    }
    if (n->kind == ND_SUBSCRIPT_EXPRESSION && n->nchildren >= 1) {
        Node *base = n->children[0];
        if (base->kind == ND_IDENTIFIER) {
            char *nm = xstrndup(src + base->start, base->end - base->start);
            int r = smap_has(&t->deep_pointer_names, nm);
            free(nm);
            if (r) return 1;
        }
    }
    if (n->kind == ND_CAST_EXPRESSION) {
        if (has_pointer_declarator(n)) return 1;
    }
    if (n->kind == ND_CALL_EXPRESSION && n->nchildren >= 1) {
        Node *fn = n->children[0];
        if (fn->kind == ND_IDENTIFIER) {
            char *nm = xstrndup(src + fn->start, fn->end - fn->start);
            int r = smap_has(&t->pointer_returning_funcs, nm);
            free(nm);
            if (r) return 1;
        }
    }
    if (n->kind == ND_FIELD_EXPRESSION) {
        Node *base = NULL, *fi = NULL;
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_OPERATOR && i + 1 < n->nchildren) {
                fi = n->children[i+1];
                base = i > 0 ? n->children[i-1] : NULL;
                break;
            }
        }
        if (fi && fi->kind == ND_FIELD_IDENTIFIER) {
            char *fn = xstrndup(src + fi->start, fi->end - fi->start);
            if (base && base->kind == ND_IDENTIFIER) {
                char *bn = xstrndup(src + base->start, base->end - base->start);
                char *sn = smap_get(&t->var_struct_types, bn);
                free(bn);
                if (sn) {
                    StrMap *m = smap_get(&t->struct_pointer_fields, sn);
                    if (m && smap_has(m, fn)) { free(fn); return 1; }
                    free(fn);
                    return 0;  /* known struct, field not pointer */
                }
            }
            int r = smap_has(&t->pointer_fields, fn);
            free(fn);
            if (r) return 1;
        }
    }
    if (n->kind == ND_BINARY_EXPRESSION) {
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_OPERATOR) continue;
            if (is_pointer_expr(c, src, t)) return 1;
        }
    }
    if (n->kind == ND_PARENTHESIZED_EXPRESSION) {
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind != ND_PUNCT) return is_pointer_expr(c, src, t);
        }
    }
    if (n->kind == ND_CONDITIONAL_EXPRESSION) {
        /* ? expr1 : expr2 — the non-op non-punct children after '?' */
        Node *mid = NULL, *rhs = NULL;
        int seen_q = 0, seen_c = 0;
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_OPERATOR && c->text_len == 1 && c->text[0] == '?') { seen_q = 1; continue; }
            if (c->kind == ND_OPERATOR && c->text_len == 1 && c->text[0] == ':') { seen_c = 1; continue; }
            if (seen_c) rhs = c;
            else if (seen_q) mid = c;
        }
        if ((mid && is_pointer_expr(mid, src, t)) || (rhs && is_pointer_expr(rhs, src, t))) return 1;
    }
    if (n->kind == ND_COMMA_EXPRESSION) {
        if (n->nchildren > 0) return is_pointer_expr(n->children[n->nchildren - 1], src, t);
    }
    return 0;
}

static int is_bitfield_expr(Node *n, const char *src, Tracker *t) {
    if (n->kind != ND_FIELD_EXPRESSION) return 0;
    Node *base = NULL, *fi = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_OPERATOR && i + 1 < n->nchildren) {
            fi = n->children[i+1];
            base = i > 0 ? n->children[i-1] : NULL;
            break;
        }
    }
    if (!fi || fi->kind != ND_FIELD_IDENTIFIER) return 0;
    char *fn = xstrndup(src + fi->start, fi->end - fi->start);
    if (base && base->kind == ND_IDENTIFIER) {
        char *bn = xstrndup(src + base->start, base->end - base->start);
        char *sn = smap_get(&t->var_struct_types, bn);
        free(bn);
        if (sn) {
            StrMap *m = smap_get(&t->struct_bitfield_fields, sn);
            if (m && smap_has(m, fn)) { free(fn); return 1; }
            free(fn);
            return 0;
        }
    }
    int r = smap_has(&t->bitfield_fields, fn);
    free(fn);
    return r;
}

/* Helper: the text (rewritten if needed) for a child */
static char *child_text(Node *c, Rewriter *r, Tracker *t) {
    char *s = transform(c, r, t);
    if (s) return s;
    return strip_markers(r, c->start, c->end);
}

/* col: Python uses node.start_point[1] + 1 (1-based column) */
static size_t col_of(Node *n) { return n->col + 1; }

/* ----- Specific rewrite handlers ------------------------------------ */

static int binop_is_arith(const char *op, size_t l) {
    static const char *const ops[] = {"+", "-", "*", "/", "%", "<<", ">>"};
    for (size_t i = 0; i < sizeof(ops)/sizeof(*ops); i++) {
        if (strlen(ops[i]) == l && memcmp(ops[i], op, l) == 0) return 1;
    }
    return 0;
}

static const char *int_macro_for(const char *op, size_t l) {
    if (l == 1) {
        if (op[0] == '+') return "ckd_add";
        if (op[0] == '-') return "ckd_sub";
        if (op[0] == '*') return "ckd_mul";
        if (op[0] == '/') return "ckd_div";
        if (op[0] == '%') return "ckd_mod";
    }
    if (l == 2) {
        if (op[0] == '<' && op[1] == '<') return "ckd_shl";
        if (op[0] == '>' && op[1] == '>') return "ckd_shr";
    }
    return NULL;
}

static const char *ptr_macro_for(const char *op, size_t l) {
    if (l == 1) {
        if (op[0] == '+') return "ckd_ptr_add";
        if (op[0] == '-') return "ckd_ptr_sub";
    }
    return NULL;
}

static char *try_rewrite_binary(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 3 || n->has_error) return NULL;
    /* Find operator child */
    Node *op = NULL, *left = NULL, *right = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        if (n->children[i]->kind == ND_OPERATOR) {
            op = n->children[i];
            left = i > 0 ? n->children[i-1] : NULL;
            right = i + 1 < n->nchildren ? n->children[i+1] : NULL;
            break;
        }
    }
    if (!op || !left || !right) return NULL;
    if (!binop_is_arith(op->text, op->text_len)) return NULL;
    static const char *const ops[] = {"+", "-", "*", "/", "%", "<<", ">>"};
    if (rw_is_suppressed(r, n, ops, 7)) return NULL;
    if (is_const_expr(left, r->src) && is_const_expr(right, r->src)) return NULL;
    if (is_float_expr(left, r->src) || is_float_expr(right, r->src)) return NULL;
    if (!inside_function(n)) return NULL;

    int left_is_ptr = is_pointer_expr(left, r->src, t);
    int right_is_ptr = is_pointer_expr(right, r->src, t);

    if (left_is_ptr && right_is_ptr && op->text_len == 1 && op->text[0] == '-') {
        size_t col = col_of(n);
        char *lt = child_text(left, r, t);
        char *rt = child_text(right, r, t);
        Str out; str_init(&out);
        str_appendf(&out, "ckd_ptr_diff(%s, %s, %zu)", lt, rt, col);
        free(lt); free(rt);
        return str_detach(&out);
    }

    int is_ptr = left_is_ptr || right_is_ptr;
    const char *macro = NULL;
    if (is_ptr) {
        macro = ptr_macro_for(op->text, op->text_len);
        if (!macro) return NULL;
    } else {
        macro = int_macro_for(op->text, op->text_len);
        if (!macro) return NULL;
    }

    size_t col = col_of(n);
    char *lt = child_text(left, r, t);
    char *rt = child_text(right, r, t);
    /* Swap if ptr + int reversed: int + ptr case needs swap for ckd_ptr_add */
    if (is_ptr && op->text_len == 1 && op->text[0] == '+' && right_is_ptr && !left_is_ptr) {
        char *tmp = lt; lt = rt; rt = tmp;
    }

    /* Known-size array: use ckd_array_ptr for + */
    if (is_ptr && op->text_len == 1 && op->text[0] == '+') {
        Node *arr = left_is_ptr ? left : right;
        if (arr->kind == ND_IDENTIFIER) {
            char *nm = xstrndup(r->src + arr->start, arr->end - arr->start);
            StrList *dims = smap_get(&t->array_sizes, nm);
            free(nm);
            if (dims && dims->len > 0 && dims->items[0]) {
                Str out; str_init(&out);
                str_appendf(&out, "ckd_array_ptr(%s, %s, %s, %zu)", lt, rt, dims->items[0], col);
                free(lt); free(rt);
                return str_detach(&out);
            }
        }
    }

    Str out; str_init(&out);
    str_appendf(&out, "%s(%s, %s, %zu)", macro, lt, rt, col);
    free(lt); free(rt);
    return str_detach(&out);
}

static int has_call_expr_in(Node *n) {
    if (!n) return 0;
    if (n->kind == ND_CALL_EXPRESSION) return 1;
    for (size_t i = 0; i < n->nchildren; i++)
        if (has_call_expr_in(n->children[i])) return 1;
    return 0;
}

static int bf_base_has_side_effects(Node *n) {
    if (n->kind != ND_FIELD_EXPRESSION || n->nchildren == 0) return 0;
    return has_call_expr_in(n->children[0]);
}

static int update_result_discarded(Node *n) {
    Node *p = n->parent;
    if (!p) return 0;
    if (p->kind == ND_EXPRESSION_STATEMENT) return 1;
    if (p->kind == ND_FOR_STATEMENT) return 1;
    if (p->kind == ND_COMMA_EXPRESSION) return update_result_discarded(p);
    return 0;
}

/* Compound assignment / plain = narrowing */
static char *try_rewrite_assignment(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 3 || n->has_error) return NULL;
    Node *op = NULL, *left = NULL, *right = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        if (n->children[i]->kind == ND_OPERATOR) {
            op = n->children[i];
            left = i > 0 ? n->children[i-1] : NULL;
            right = i + 1 < n->nchildren ? n->children[i+1] : NULL;
            break;
        }
    }
    if (!op || !left || !right) return NULL;
    static const char *const all_ops[] = {"=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>="};
    if (rw_is_suppressed(r, n, all_ops, 8)) return NULL;

    /* Plain = : check narrowing only */
    if (op->text_len == 1 && op->text[0] == '=') {
        if (is_const_expr(right, r->src)) return NULL;
        char *decl_type = get_lhs_narrow_type(left, r->src, t);
        if (!decl_type) return NULL;
        /* Skip if right is cast to same type */
        if (right->kind == ND_CAST_EXPRESSION) {
            char *ct = extract_cast_type(right, r->src);
            if (ct && strcmp(ct, decl_type) == 0) {
                free(ct);
                free(decl_type);
                return NULL;
            }
            free(ct);
        }
        size_t col = col_of(right);
        char *rt = child_text(right, r, t);
        char *lt = child_text(left, r, t);
        Str out; str_init(&out);
        str_appendf(&out, "%s = ckd_narrow(%s, %s, %zu)", lt, rt, decl_type, col);
        free(lt); free(rt); free(decl_type);
        return str_detach(&out);
    }

    /* Compound op */
    static const char *const cops[] = {"+=", "-=", "*=", "/=", "%=", "<<=", ">>="};
    int found = 0;
    char binop_str[4] = {0};
    for (size_t i = 0; i < sizeof(cops)/sizeof(*cops); i++) {
        size_t ol = strlen(cops[i]);
        if (op->text_len == ol && memcmp(op->text, cops[i], ol) == 0) {
            memcpy(binop_str, cops[i], ol - 1);
            binop_str[ol - 1] = 0;
            found = 1;
            break;
        }
    }
    if (!found) return NULL;
    if (is_const_expr(left, r->src) && is_const_expr(right, r->src)) return NULL;

    const char *int_m = int_macro_for(binop_str, strlen(binop_str));
    const char *ptr_m = ptr_macro_for(binop_str, strlen(binop_str));
    if (!int_m) return NULL;

    int is_ptr = is_pointer_expr(left, r->src, t);
    const char *macro = is_ptr ? ptr_m : int_m;
    if (is_ptr && !ptr_m) return NULL;

    size_t col = col_of(n);
    int is_bf = is_bitfield_expr(left, r->src, t);
    if (is_bf && bf_base_has_side_effects(left)) return NULL;

    char *lt = child_text(left, r, t);
    char *rt = child_text(right, r, t);

    if (!is_ptr) {
        char *decl_type = get_lhs_narrow_type(left, r->src, t);
        if (decl_type) {
            Str out; str_init(&out);
            if (is_bf)
                str_appendf(&out, "ckd_bf_compound_narrow(%s, %s, %s, %s, %zu)",
                            lt, macro, rt, decl_type, col);
            else
                str_appendf(&out, "ckd_compound_narrow(%s, %s, %s, %s, %zu)",
                            lt, macro, rt, decl_type, col);
            free(lt); free(rt); free(decl_type);
            return str_detach(&out);
        }
    }
    Str out; str_init(&out);
    if (is_bf)
        str_appendf(&out, "ckd_bf_compound(%s, %s, %s, %zu)", lt, macro, rt, col);
    else
        str_appendf(&out, "ckd_compound(%s, %s, %s, %zu)", lt, macro, rt, col);
    free(lt); free(rt);
    return str_detach(&out);
}

static char *try_rewrite_update(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 2 || n->has_error) return NULL;
    static const char *const ops[] = {"++", "--"};
    if (rw_is_suppressed(r, n, ops, 2)) return NULL;

    /* Identify prefix or postfix */
    Node *opn = NULL, *operand = NULL;
    int is_prefix = 0;
    if (n->children[0]->kind == ND_OPERATOR &&
        (n->children[0]->text_len == 2) &&
        (memcmp(n->children[0]->text, "++", 2) == 0 || memcmp(n->children[0]->text, "--", 2) == 0)) {
        opn = n->children[0];
        operand = n->children[1];
        is_prefix = 1;
    } else {
        Node *lst = n->children[n->nchildren - 1];
        if (lst->kind == ND_OPERATOR && lst->text_len == 2 &&
            (memcmp(lst->text, "++", 2) == 0 || memcmp(lst->text, "--", 2) == 0)) {
            opn = lst;
            operand = n->children[0];
            is_prefix = 0;
        } else return NULL;
    }
    if (!operand) return NULL;
    /* Accept only certain operand kinds */
    if (operand->kind != ND_IDENTIFIER && operand->kind != ND_FIELD_EXPRESSION &&
        operand->kind != ND_SUBSCRIPT_EXPRESSION && operand->kind != ND_PARENTHESIZED_EXPRESSION &&
        operand->kind != ND_POINTER_EXPRESSION) return NULL;

    int is_plus = (opn->text[0] == '+');
    int is_ptr = is_pointer_expr(operand, r->src, t);
    int is_bf = is_bitfield_expr(operand, r->src, t);
    if (is_bf && bf_base_has_side_effects(operand)) return NULL;

    size_t col = col_of(n);
    char *otxt = child_text(operand, r, t);

    if (is_bf) {
        int discarded = update_result_discarded(n) || is_prefix;
        const char *macro;
        if (discarded) macro = is_plus ? "ckd_bf_preinc" : "ckd_bf_predec";
        else macro = is_plus ? "ckd_bf_postinc" : "ckd_bf_postdec";
        Str out; str_init(&out);
        str_appendf(&out, "%s(%s, %zu)", macro, otxt, col);
        free(otxt);
        return str_detach(&out);
    }

    const char *macro = NULL;
    int discarded = update_result_discarded(n);
    if (discarded || is_prefix) {
        if (is_ptr) macro = is_plus ? "ckd_ptr_preinc" : "ckd_ptr_predec";
        else macro = is_plus ? "ckd_preinc" : "ckd_predec";
    } else {
        if (is_ptr) macro = is_plus ? "ckd_ptr_postinc" : "ckd_ptr_postdec";
        else macro = is_plus ? "ckd_postinc" : "ckd_postdec";
    }
    Str out; str_init(&out);
    str_appendf(&out, "%s(%s, %zu)", macro, otxt, col);
    free(otxt);
    return str_detach(&out);
}

/* Walk subscript chain to find (arrname, depth) */
static int resolve_subscript_chain(Node *n, const char *src, Tracker *t,
                                    char **out_name, int *out_depth) {
    if (n->kind == ND_IDENTIFIER) {
        char *nm = xstrndup(src + n->start, n->end - n->start);
        if (smap_has(&t->array_sizes, nm)) {
            *out_name = nm;
            *out_depth = 0;
            return 1;
        }
        free(nm);
        return 0;
    }
    if (n->kind == ND_SUBSCRIPT_EXPRESSION && n->nchildren >= 1) {
        if (resolve_subscript_chain(n->children[0], src, t, out_name, out_depth)) {
            (*out_depth)++;
            return 1;
        }
    }
    return 0;
}

static char *try_rewrite_subscript(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 4 || n->has_error) return NULL;
    static const char *const ops[] = {"["};
    if (rw_is_suppressed(r, n, ops, 1)) return NULL;

    /* subscript_expression: base '[' index ']' */
    Node *base = n->children[0];
    Node *index = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_PUNCT && c->text_len == 1 && (c->text[0] == '[' || c->text[0] == ']')) continue;
        if (c != base) { index = c; break; }
    }
    if (!base || !index) return NULL;

    char *aname = NULL;
    int depth = 0;
    char *size = NULL;
    if (resolve_subscript_chain(base, r->src, t, &aname, &depth)) {
        StrList *dims = smap_get(&t->array_sizes, aname);
        if (dims && (size_t)depth < dims->len && dims->items[depth])
            size = xstrdup(dims->items[depth]);
        free(aname);
    }
    if (!size) return NULL;

    size_t col = col_of(n);
    char *bt = child_text(base, r, t);
    char *it = child_text(index, r, t);
    Str out; str_init(&out);
    str_appendf(&out, "ckd_bounds(%s, %s, %s, %zu)", bt, it, size, col);
    free(bt); free(it); free(size);
    return str_detach(&out);
}

/* Get declared type from parent declaration */
static char *get_declaration_type(Node *n, const char *src) {
    Node *p = n->parent;
    if (!p) return NULL;
    if (p->kind != ND_DECLARATION && p->kind != ND_PARAMETER_DECLARATION) return NULL;
    Str out; str_init(&out);
    int any = 0;
    for (size_t i = 0; i < p->nchildren; i++) {
        Node *c = p->children[i];
        if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER ||
            c->kind == ND_TYPE_IDENTIFIER) {
            if (any) str_append_ch(&out, ' ');
            str_append(&out, src + c->start, c->end - c->start);
            any = 1;
        }
    }
    if (!any) { str_free(&out); return NULL; }
    return str_detach(&out);
}

static char *get_struct_type_for_decl(Node *n, const char *src, Tracker *t) {
    Node *p = n->parent;
    if (!p || p->kind != ND_DECLARATION) return NULL;
    for (size_t i = 0; i < p->nchildren; i++) {
        Node *c = p->children[i];
        if (c->kind == ND_STRUCT_SPECIFIER || c->kind == ND_UNION_SPECIFIER) {
            for (size_t j = 0; j < c->nchildren; j++) {
                Node *g = c->children[j];
                if (g->kind == ND_TYPE_IDENTIFIER)
                    return xstrndup(src + g->start, g->end - g->start);
            }
            char buf[64];
            snprintf(buf, sizeof(buf), "__anon_%zu", c->start);
            return xstrdup(buf);
        }
        if (c->kind == ND_TYPE_IDENTIFIER) {
            char *tt = xstrndup(src + c->start, c->end - c->start);
            char *sn = smap_get(&t->typedef_struct_names, tt);
            free(tt);
            if (sn) return xstrdup(sn);
        }
    }
    return NULL;
}

/* Struct-initializer-list rewriting for init_declarator */
static char *rewrite_struct_init_list(Node *init_node, FieldList *fields,
                                      Rewriter *r, Tracker *t) {
    /* Determine if any element needs narrowing */
    int any_narrow = 0;
    size_t fi_idx = 0;
    for (size_t i = 0; i < init_node->nchildren; i++) {
        Node *c = init_node->children[i];
        if (c->kind == ND_PUNCT) continue;
        if (c->kind == ND_INITIALIZER_LIST) { fi_idx++; continue; }
        if (fi_idx < fields->len && fields->items[fi_idx].narrow_type &&
            !is_const_expr(c, r->src)) { any_narrow = 1; break; }
        fi_idx++;
    }
    if (!any_narrow) return NULL;

    Str parts; str_init(&parts);
    size_t prev_end = init_node->start;
    fi_idx = 0;
    for (size_t i = 0; i < init_node->nchildren; i++) {
        Node *c = init_node->children[i];
        strip_markers_into(r, prev_end, c->start, &parts);
        if (c->kind == ND_PUNCT) {
            strip_markers_into(r, c->start, c->end, &parts);
        } else {
            const char *nt = NULL;
            if (fi_idx < fields->len && c->kind != ND_INITIALIZER_LIST)
                nt = fields->items[fi_idx].narrow_type;
            fi_idx++;
            if (nt && !is_const_expr(c, r->src)) {
                size_t col = col_of(c);
                char *et = child_text(c, r, t);
                str_appendf(&parts, "ckd_narrow(%s, %s, %zu)", et, nt, col);
                free(et);
            } else {
                char *et = transform(c, r, t);
                if (et) { str_append_cstr(&parts, et); free(et); }
                else strip_markers_into(r, c->start, c->end, &parts);
            }
        }
        prev_end = c->end;
    }
    strip_markers_into(r, prev_end, init_node->end, &parts);
    return str_detach(&parts);
}

static char *try_rewrite_init_narrow(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 3 || n->has_error) return NULL;
    static const char *const ops[] = {"="};
    if (rw_is_suppressed(r, n, ops, 1)) return NULL;
    if (!inside_function(n)) return NULL;

    /* Find '=' */
    int eq_idx = -1;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_OPERATOR && c->text_len == 1 && c->text[0] == '=') {
            eq_idx = (int)i;
            break;
        }
    }
    if (eq_idx < 0 || (size_t)eq_idx + 1 >= n->nchildren) return NULL;
    Node *init_node = n->children[eq_idx + 1];

    /* Struct init list special case */
    if (init_node->kind == ND_INITIALIZER_LIST && !has_pointer_declarator(n) &&
        !has_array_declarator(n)) {
        char *sn = get_struct_type_for_decl(n, r->src, t);
        if (sn) {
            FieldList *fl = smap_get(&t->struct_fields_ordered, sn);
            if (fl) {
                /* Skip if designated initializers */
                int designated = 0;
                for (size_t i = 0; i < init_node->nchildren; i++)
                    if (init_node->children[i]->kind == ND_INITIALIZER_PAIR) { designated = 1; break; }
                if (!designated) {
                    char *rewritten = rewrite_struct_init_list(init_node, fl, r, t);
                    if (rewritten) {
                        /* Splice back into parent */
                        Str out; str_init(&out);
                        size_t prev_end = n->start;
                        for (size_t i = 0; i < n->nchildren; i++) {
                            Node *c = n->children[i];
                            strip_markers_into(r, prev_end, c->start, &out);
                            if (c == init_node) str_append_cstr(&out, rewritten);
                            else {
                                char *ct = transform(c, r, t);
                                if (ct) { str_append_cstr(&out, ct); free(ct); }
                                else strip_markers_into(r, c->start, c->end, &out);
                            }
                            prev_end = c->end;
                        }
                        strip_markers_into(r, prev_end, n->end, &out);
                        free(rewritten);
                        free(sn);
                        return str_detach(&out);
                    }
                }
            }
            free(sn);
        }
    }

    char *decl_type = get_declaration_type(n, r->src);
    int is_narrow = decl_type && (is_narrow_type_text(decl_type, strlen(decl_type)) ||
                                   smap_has(&t->narrow_type_names, decl_type));
    if (!is_narrow) { free(decl_type); return NULL; }
    if (has_pointer_declarator(n)) { free(decl_type); return NULL; }
    if (is_const_expr(init_node, r->src)) { free(decl_type); return NULL; }
    if (init_node->kind == ND_CAST_EXPRESSION) {
        char *ct = extract_cast_type(init_node, r->src);
        if (ct && strcmp(ct, decl_type) == 0) {
            free(ct); free(decl_type);
            return NULL;
        }
        free(ct);
    }

    /* Array declaration with init-list: wrap each non-constant element */
    if (has_array_declarator(n)) {
        if (init_node->kind != ND_INITIALIZER_LIST) { free(decl_type); return NULL; }
        /* Wrap each non-const element */
        Str parts; str_init(&parts);
        size_t prev_end = init_node->start;
        int any_changed = 0;
        for (size_t i = 0; i < init_node->nchildren; i++) {
            Node *c = init_node->children[i];
            strip_markers_into(r, prev_end, c->start, &parts);
            if (c->kind != ND_PUNCT && c->kind != ND_INITIALIZER_LIST &&
                !is_const_expr(c, r->src)) {
                size_t col = col_of(c);
                char *et = child_text(c, r, t);
                str_appendf(&parts, "ckd_narrow(%s, %s, %zu)", et, decl_type, col);
                free(et);
                any_changed = 1;
            } else {
                char *ct = transform(c, r, t);
                if (ct) { str_append_cstr(&parts, ct); free(ct); any_changed = 1; }
                else strip_markers_into(r, c->start, c->end, &parts);
            }
            prev_end = c->end;
        }
        strip_markers_into(r, prev_end, init_node->end, &parts);
        if (!any_changed) { str_free(&parts); free(decl_type); return NULL; }
        /* Now rebuild the full init_declarator around the new init list */
        Str full; str_init(&full);
        size_t pe = n->start;
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            strip_markers_into(r, pe, c->start, &full);
            if (c == init_node) str_append_cstr(&full, parts.data ? parts.data : "");
            else {
                char *ct = transform(c, r, t);
                if (ct) { str_append_cstr(&full, ct); free(ct); }
                else strip_markers_into(r, c->start, c->end, &full);
            }
            pe = c->end;
        }
        strip_markers_into(r, pe, n->end, &full);
        str_free(&parts);
        free(decl_type);
        return str_detach(&full);
    }

    size_t col = col_of(init_node);
    char *it = child_text(init_node, r, t);
    Str out; str_init(&out);
    size_t prev_end = n->start;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        strip_markers_into(r, prev_end, c->start, &out);
        if ((int)i == eq_idx + 1)
            str_appendf(&out, "ckd_narrow(%s, %s, %zu)", it, decl_type, col);
        else strip_markers_into(r, c->start, c->end, &out);
        prev_end = c->end;
    }
    strip_markers_into(r, prev_end, n->end, &out);
    free(it); free(decl_type);
    return str_detach(&out);
}

static char *try_rewrite_return(Node *n, Rewriter *r, Tracker *t) {
    if (!t->func_return_type) return NULL;
    if (n->has_error) return NULL;
    static const char *const ops[] = {"return"};
    if (rw_is_suppressed(r, n, ops, 1)) return NULL;
    Node *expr = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_KEYWORD) continue;
        if (c->kind == ND_PUNCT && c->text_len == 1 && c->text[0] == ';') continue;
        expr = c;
        break;
    }
    if (!expr) return NULL;
    if (is_const_expr(expr, r->src)) return NULL;
    if (expr->kind == ND_CAST_EXPRESSION) {
        char *ct = extract_cast_type(expr, r->src);
        if (ct && strcmp(ct, t->func_return_type) == 0) { free(ct); return NULL; }
        free(ct);
    }
    size_t col = col_of(expr);
    char *et = child_text(expr, r, t);
    Str out; str_init(&out);
    size_t prev_end = n->start;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        strip_markers_into(r, prev_end, c->start, &out);
        if (c == expr)
            str_appendf(&out, "ckd_narrow(%s, %s, %zu)", et, t->func_return_type, col);
        else strip_markers_into(r, c->start, c->end, &out);
        prev_end = c->end;
    }
    strip_markers_into(r, prev_end, n->end, &out);
    free(et);
    return str_detach(&out);
}

static char *try_rewrite_cast(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 4 || n->has_error) return NULL;
    static const char *const ops[] = {"("};
    if (rw_is_suppressed(r, n, ops, 1)) return NULL;
    if (!inside_function(n)) return NULL;

    Node *td = NULL, *operand = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_TYPE_DESCRIPTOR) td = c;
        else if (c->kind != ND_PUNCT && td) { operand = c; break; }
    }
    if (!td || !operand) return NULL;

    /* Skip pointer casts */
    for (size_t i = 0; i < td->nchildren; i++) {
        if (td->children[i]->kind == ND_ABSTRACT_POINTER_DECLARATOR) return NULL;
    }
    /* Extract cast target type */
    char *ct = NULL;
    {
        Str s; str_init(&s);
        int any = 0;
        for (size_t i = 0; i < td->nchildren; i++) {
            Node *c = td->children[i];
            if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER ||
                c->kind == ND_TYPE_IDENTIFIER) {
                if (any) str_append_ch(&s, ' ');
                str_append(&s, r->src + c->start, c->end - c->start);
                any = 1;
            }
        }
        ct = any ? str_detach(&s) : NULL;
        if (!any) str_free(&s);
    }
    if (!ct) return NULL;
    int is_narrow = is_narrow_type_text(ct, strlen(ct)) || smap_has(&t->narrow_type_names, ct);
    if (!is_narrow) { free(ct); return NULL; }
    if (is_const_expr(operand, r->src)) { free(ct); return NULL; }
    size_t col = col_of(n);
    char *ot = child_text(operand, r, t);
    Str out; str_init(&out);
    str_appendf(&out, "ckd_narrow(%s, %s, %zu)", ot, ct, col);
    free(ot); free(ct);
    return str_detach(&out);
}

static char *try_rewrite_compound_literal(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 3 || n->has_error) return NULL;
    Node *td = NULL, *init = NULL;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        if (c->kind == ND_TYPE_DESCRIPTOR) td = c;
        else if (c->kind == ND_INITIALIZER_LIST) init = c;
    }
    if (!td || !init) return NULL;

    /* Find struct name */
    char *sn = NULL;
    for (size_t i = 0; i < td->nchildren; i++) {
        Node *c = td->children[i];
        if (c->kind == ND_STRUCT_SPECIFIER || c->kind == ND_UNION_SPECIFIER) {
            for (size_t j = 0; j < c->nchildren; j++) {
                Node *g = c->children[j];
                if (g->kind == ND_TYPE_IDENTIFIER) {
                    sn = xstrndup(r->src + g->start, g->end - g->start);
                    break;
                }
            }
            if (!sn) {
                char buf[64];
                snprintf(buf, sizeof(buf), "__anon_%zu", c->start);
                sn = xstrdup(buf);
            }
            break;
        }
        if (c->kind == ND_TYPE_IDENTIFIER) {
            char *tt = xstrndup(r->src + c->start, c->end - c->start);
            char *s2 = smap_get(&t->typedef_struct_names, tt);
            if (s2) sn = xstrdup(s2);
            free(tt);
            if (sn) break;
        }
    }
    if (!sn) return NULL;
    FieldList *fl = smap_get(&t->struct_fields_ordered, sn);
    free(sn);
    if (!fl) return NULL;

    /* Skip designated */
    for (size_t i = 0; i < init->nchildren; i++)
        if (init->children[i]->kind == ND_INITIALIZER_PAIR) return NULL;

    char *rewritten = rewrite_struct_init_list(init, fl, r, t);
    if (!rewritten) return NULL;

    Str out; str_init(&out);
    size_t prev_end = n->start;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        strip_markers_into(r, prev_end, c->start, &out);
        if (c == init) str_append_cstr(&out, rewritten);
        else {
            char *ct = transform(c, r, t);
            if (ct) { str_append_cstr(&out, ct); free(ct); }
            else strip_markers_into(r, c->start, c->end, &out);
        }
        prev_end = c->end;
    }
    strip_markers_into(r, prev_end, n->end, &out);
    free(rewritten);
    return str_detach(&out);
}

static char *try_rewrite_call(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 2 || n->has_error) return NULL;
    Node *fn = n->children[0];
    if (fn->kind != ND_IDENTIFIER) return NULL;
    char *fname = xstrndup(r->src + fn->start, fn->end - fn->start);
    StrList *params = smap_get(&t->func_param_narrow, fname);
    free(fname);
    if (!params) return NULL;

    Node *args = NULL;
    for (size_t i = 0; i < n->nchildren; i++)
        if (n->children[i]->kind == ND_ARGUMENT_LIST) { args = n->children[i]; break; }
    if (!args) return NULL;

    /* Collect actual args */
    size_t arg_idx = 0;
    int any_narrow = 0;
    for (size_t i = 0; i < args->nchildren; i++) {
        Node *c = args->children[i];
        if (c->kind == ND_PUNCT) continue;
        if (arg_idx < params->len && params->items[arg_idx] && !is_const_expr(c, r->src)) {
            any_narrow = 1;
            break;
        }
        arg_idx++;
    }
    if (!any_narrow) return NULL;

    Str parts; str_init(&parts);
    size_t prev_end = args->start;
    arg_idx = 0;
    for (size_t i = 0; i < args->nchildren; i++) {
        Node *c = args->children[i];
        strip_markers_into(r, prev_end, c->start, &parts);
        if (c->kind == ND_PUNCT) {
            strip_markers_into(r, c->start, c->end, &parts);
        } else {
            const char *dt = NULL;
            if (arg_idx < params->len) dt = params->items[arg_idx];
            arg_idx++;
            int skip = 0;
            if (dt && c->kind == ND_CAST_EXPRESSION) {
                char *ct = extract_cast_type(c, r->src);
                if (ct && strcmp(ct, dt) == 0) skip = 1;
                free(ct);
            }
            if (dt && !is_const_expr(c, r->src) && !skip) {
                size_t col = col_of(c);
                char *at = child_text(c, r, t);
                str_appendf(&parts, "ckd_narrow(%s, %s, %zu)", at, dt, col);
                free(at);
            } else {
                char *ct = transform(c, r, t);
                if (ct) { str_append_cstr(&parts, ct); free(ct); }
                else strip_markers_into(r, c->start, c->end, &parts);
            }
        }
        prev_end = c->end;
    }
    strip_markers_into(r, prev_end, args->end, &parts);

    Str out; str_init(&out);
    strip_markers_into(r, fn->start, fn->end, &out);
    strip_markers_into(r, fn->end, args->start, &out);
    str_append_cstr(&out, parts.data ? parts.data : "");
    str_free(&parts);
    return str_detach(&out);
}

static char *try_rewrite_unary_neg(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren < 2 || n->has_error) return NULL;
    static const char *const ops[] = {"-"};
    if (rw_is_suppressed(r, n, ops, 1)) return NULL;
    Node *op = n->children[0];
    if (op->kind != ND_OPERATOR || op->text_len != 1 || op->text[0] != '-') return NULL;
    Node *operand = n->children[1];
    if (is_const_expr(operand, r->src)) return NULL;
    if (is_float_expr(operand, r->src)) return NULL;

    size_t col = col_of(n);
    char *ot = child_text(operand, r, t);
    Str out; str_init(&out);
    str_appendf(&out, "ckd_neg(%s, %zu)", ot, col);
    free(ot);
    return str_detach(&out);
}

static char *try_rewrite(Node *n, Rewriter *r, Tracker *t) {
    switch (n->kind) {
    case ND_BINARY_EXPRESSION: return try_rewrite_binary(n, r, t);
    case ND_ASSIGNMENT_EXPRESSION: return try_rewrite_assignment(n, r, t);
    case ND_UPDATE_EXPRESSION: return try_rewrite_update(n, r, t);
    case ND_UNARY_EXPRESSION: return try_rewrite_unary_neg(n, r, t);
    case ND_SUBSCRIPT_EXPRESSION: return try_rewrite_subscript(n, r, t);
    case ND_INIT_DECLARATOR: return try_rewrite_init_narrow(n, r, t);
    case ND_RETURN_STATEMENT: return try_rewrite_return(n, r, t);
    case ND_CALL_EXPRESSION: return try_rewrite_call(n, r, t);
    case ND_CAST_EXPRESSION: return try_rewrite_cast(n, r, t);
    case ND_COMPOUND_LITERAL_EXPRESSION: return try_rewrite_compound_literal(n, r, t);
    default: return NULL;
    }
}

/* Main recursive transform */
static char *transform(Node *n, Rewriter *r, Tracker *t) {
    if (!n) return NULL;
    if (rw_is_disabled(r, n)) return NULL;
    if (n->kind == ND_SIZEOF_EXPRESSION || n->kind == ND_ALIGNOF_EXPRESSION ||
        n->kind == ND_ERROR || n->has_error) return NULL;

    if (n->kind == ND_FUNCTION_DEFINITION) {
        Tracker local;
        tracker_copy(&local, t);
        /* Scan declarator (parameters) */
        int has_ptr_return = 0;
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_FUNCTION_DECLARATOR || c->kind == ND_POINTER_DECLARATOR) {
                tracker_scan(&local, c, r->src, 0, 0);
            }
            if (c->kind == ND_POINTER_DECLARATOR) has_ptr_return = 1;
        }
        /* Return type */
        if (!has_ptr_return) {
            for (size_t i = 0; i < n->nchildren; i++) {
                Node *c = n->children[i];
                if (c->kind == ND_PRIMITIVE_TYPE || c->kind == ND_SIZED_TYPE_SPECIFIER) {
                    /* Build "sized type" string by joining consecutive specs */
                    Str s; str_init(&s);
                    str_append(&s, r->src + c->start, c->end - c->start);
                    size_t j = i + 1;
                    while (j < n->nchildren) {
                        Node *g = n->children[j];
                        if (g->kind == ND_SIZED_TYPE_SPECIFIER || g->kind == ND_PRIMITIVE_TYPE) {
                            str_append_ch(&s, ' ');
                            str_append(&s, r->src + g->start, g->end - g->start);
                            j++;
                        } else break;
                    }
                    char *tt = str_detach(&s);
                    if (is_narrow_type_text(tt, strlen(tt)) || smap_has(&local.narrow_type_names, tt)) {
                        free(local.func_return_type);
                        local.func_return_type = tt;
                    } else free(tt);
                    break;
                }
                if (c->kind == ND_TYPE_IDENTIFIER) {
                    char *tt = xstrndup(r->src + c->start, c->end - c->start);
                    if (is_narrow_type_text(tt, strlen(tt)) || smap_has(&local.narrow_type_names, tt)) {
                        free(local.func_return_type);
                        local.func_return_type = tt;
                    } else free(tt);
                    break;
                }
            }
        }
        char *result = transform_children(n, r, &local);
        tracker_free(&local);
        return result;
    }

    if (n->kind == ND_COMPOUND_STATEMENT) {
        Tracker local;
        tracker_copy(&local, t);
        tracker_scan(&local, n, r->src, 0, 1);
        char *result = transform_children(n, r, &local);
        tracker_free(&local);
        return result;
    }

    if (n->kind == ND_FOR_STATEMENT) {
        Tracker local;
        tracker_copy(&local, t);
        for (size_t i = 0; i < n->nchildren; i++) {
            Node *c = n->children[i];
            if (c->kind == ND_DECLARATION) {
                tracker_scan(&local, c, r->src, 0, 0);
                break;
            }
        }
        char *result = transform_children(n, r, &local);
        tracker_free(&local);
        return result;
    }

    char *rewritten = try_rewrite(n, r, t);
    if (rewritten) return rewritten;

    /* Fall back to child transforms */
    return transform_children(n, r, t);
}

static char *transform_children(Node *n, Rewriter *r, Tracker *t) {
    if (n->nchildren == 0) return NULL;
    char **results = xcalloc(n->nchildren, sizeof(*results));
    int any = 0;
    for (size_t i = 0; i < n->nchildren; i++) {
        results[i] = transform(n->children[i], r, t);
        if (results[i]) any = 1;
    }
    if (!any) {
        free(results);
        return NULL;
    }
    Str out; str_init(&out);
    size_t prev_end = n->start;
    for (size_t i = 0; i < n->nchildren; i++) {
        Node *c = n->children[i];
        strip_markers_into(r, prev_end, c->start, &out);
        if (results[i]) {
            str_append_cstr(&out, results[i]);
            free(results[i]);
        } else {
            strip_markers_into(r, c->start, c->end, &out);
        }
        prev_end = c->end;
    }
    strip_markers_into(r, prev_end, n->end, &out);
    free(results);
    return str_detach(&out);
}

/* ========================================================================= */
/* Preamble                                                                  */
/* ========================================================================= */

static const char *PREAMBLE_PREFIX =
"\n"
"/* --- safer-cc: checked arithmetic preamble --- */\n"
"\n"
"#ifndef SAFER_CC_PREAMBLE_\n"
"#define SAFER_CC_PREAMBLE_\n"
"\n"
"/* Token pasting helpers for __COUNTER__-based unique names.\n"
"   Double indirection forces __COUNTER__ expansion before paste. */\n"
"#define ckd_paste_(a, b) a##b\n"
"#define ckd_paste(a, b) ckd_paste_(a, b)\n"
"\n"
"/* Overflow handler — invoked when a checked operation overflows.\n"
"   Parameters: op = string literal (\"add\", \"sub\", \"mul\", \"ptr add\", \"ptr sub\"),\n"
"               col = integer literal for column offset in original source.\n"
"   Override by passing --handler <file> to safer-cc. */\n"
"#define ckd_overflow_handler_(op, col) ";

static const char *PREAMBLE_SUFFIX =
"\n"
"\n"
"/* --- Core checked integer arithmetic (uses __builtin_*_overflow) --- */\n"
"\n"
"#define ckd_add(a, b, col) ckd_add_(a, b, col, __COUNTER__)\n"
"#define ckd_add_(a, b, col, c) ckd_add_impl_(a, b, col, c)\n"
"#define ckd_add_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    typeof(ckd_paste(ckd_a_, c) + ckd_paste(ckd_b_, c)) ckd_paste(ckd_r_, c); \\\n"
"    if (__builtin_add_overflow(ckd_paste(ckd_a_, c), ckd_paste(ckd_b_, c), \\\n"
"                               &ckd_paste(ckd_r_, c))) \\\n"
"        ckd_overflow_handler_(\"addition\", col); \\\n"
"    ckd_paste(ckd_r_, c); \\\n"
"})\n"
"\n"
"#define ckd_sub(a, b, col) ckd_sub_(a, b, col, __COUNTER__)\n"
"#define ckd_sub_(a, b, col, c) ckd_sub_impl_(a, b, col, c)\n"
"#define ckd_sub_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    typeof(ckd_paste(ckd_a_, c) - ckd_paste(ckd_b_, c)) ckd_paste(ckd_r_, c); \\\n"
"    if (__builtin_sub_overflow(ckd_paste(ckd_a_, c), ckd_paste(ckd_b_, c), \\\n"
"                               &ckd_paste(ckd_r_, c))) \\\n"
"        ckd_overflow_handler_(\"subtraction\", col); \\\n"
"    ckd_paste(ckd_r_, c); \\\n"
"})\n"
"\n"
"#define ckd_mul(a, b, col) ckd_mul_(a, b, col, __COUNTER__)\n"
"#define ckd_mul_(a, b, col, c) ckd_mul_impl_(a, b, col, c)\n"
"#define ckd_mul_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    typeof(ckd_paste(ckd_a_, c) * ckd_paste(ckd_b_, c)) ckd_paste(ckd_r_, c); \\\n"
"    if (__builtin_mul_overflow(ckd_paste(ckd_a_, c), ckd_paste(ckd_b_, c), \\\n"
"                               &ckd_paste(ckd_r_, c))) \\\n"
"        ckd_overflow_handler_(\"multiplication\", col); \\\n"
"    ckd_paste(ckd_r_, c); \\\n"
"})\n"
"\n"
"/* --- Pointer arithmetic (null + wrap detection) --- */\n"
"\n"
"#define ckd_nullptr_check_(val, col) \\\n"
"    if (__builtin_classify_type(val) == 5 && !(val)) \\\n"
"        ckd_overflow_handler_(\"null pointer arithmetic\", col)\n"
"\n"
"#define ckd_ptr_add(p, i, col) ckd_ptr_add_(p, i, col, __COUNTER__)\n"
"#define ckd_ptr_add_(p, i, col, c) ckd_ptr_add_impl_(p, i, col, c)\n"
"#define ckd_ptr_add_impl_(p, i, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_p_, c) = (p); \\\n"
"    __auto_type ckd_paste(ckd_i_, c) = (i); \\\n"
"    ckd_nullptr_check_(ckd_paste(ckd_p_, c), col); \\\n"
"    typeof(ckd_paste(ckd_p_, c) + ckd_paste(ckd_i_, c)) ckd_paste(ckd_r_, c) = \\\n"
"        ckd_paste(ckd_p_, c) + ckd_paste(ckd_i_, c); \\\n"
"    if ((__INTPTR_TYPE__)ckd_paste(ckd_i_, c) >= 0 \\\n"
"        ? (__UINTPTR_TYPE__)ckd_paste(ckd_r_, c) < (__UINTPTR_TYPE__)ckd_paste(ckd_p_, c) \\\n"
"        : (__UINTPTR_TYPE__)ckd_paste(ckd_r_, c) > (__UINTPTR_TYPE__)ckd_paste(ckd_p_, c)) \\\n"
"        ckd_overflow_handler_(\"pointer addition\", col); \\\n"
"    ckd_paste(ckd_r_, c); \\\n"
"})\n"
"\n"
"#define ckd_ptr_sub(p, i, col) ckd_ptr_sub_(p, i, col, __COUNTER__)\n"
"#define ckd_ptr_sub_(p, i, col, c) ckd_ptr_sub_impl_(p, i, col, c)\n"
"#define ckd_ptr_sub_impl_(p, i, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_p_, c) = (p); \\\n"
"    __auto_type ckd_paste(ckd_i_, c) = (i); \\\n"
"    ckd_nullptr_check_(ckd_paste(ckd_p_, c), col); \\\n"
"    typeof(ckd_paste(ckd_p_, c) - ckd_paste(ckd_i_, c)) ckd_paste(ckd_r_, c) = \\\n"
"        ckd_paste(ckd_p_, c) - ckd_paste(ckd_i_, c); \\\n"
"    if ((__INTPTR_TYPE__)ckd_paste(ckd_i_, c) >= 0 \\\n"
"        ? (__UINTPTR_TYPE__)ckd_paste(ckd_r_, c) > (__UINTPTR_TYPE__)ckd_paste(ckd_p_, c) \\\n"
"        : (__UINTPTR_TYPE__)ckd_paste(ckd_r_, c) < (__UINTPTR_TYPE__)ckd_paste(ckd_p_, c)) \\\n"
"        ckd_overflow_handler_(\"pointer subtraction\", col); \\\n"
"    ckd_paste(ckd_r_, c); \\\n"
"})\n"
"\n"
"#define ckd_ptr_diff(a, b, col) ckd_ptr_diff_(a, b, col, __COUNTER__)\n"
"#define ckd_ptr_diff_(a, b, col, c) ckd_ptr_diff_impl_(a, b, col, c)\n"
"#define ckd_ptr_diff_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    ckd_nullptr_check_(ckd_paste(ckd_a_, c), col); \\\n"
"    ckd_nullptr_check_(ckd_paste(ckd_b_, c), col); \\\n"
"    __PTRDIFF_TYPE__ ckd_paste(ckd_r_, c) = ckd_paste(ckd_a_, c) - ckd_paste(ckd_b_, c); \\\n"
"    if ((__UINTPTR_TYPE__)ckd_paste(ckd_a_, c) >= (__UINTPTR_TYPE__)ckd_paste(ckd_b_, c) \\\n"
"        ? ckd_paste(ckd_r_, c) < 0 \\\n"
"        : ckd_paste(ckd_r_, c) > 0) \\\n"
"        ckd_overflow_handler_(\"pointer subtraction overflow\", col); \\\n"
"    ckd_paste(ckd_r_, c); \\\n"
"})\n"
"\n"
"#define ckd_div(a, b, col) ckd_div_(a, b, col, __COUNTER__)\n"
"#define ckd_div_(a, b, col, c) ckd_div_impl_(a, b, col, c)\n"
"#define ckd_div_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    if (ckd_paste(ckd_b_, c) == 0) \\\n"
"        ckd_overflow_handler_(\"division by zero\", col); \\\n"
"    if ((typeof(ckd_paste(ckd_b_, c)))(-1) < 0 && ckd_paste(ckd_b_, c) == -1 && \\\n"
"        __builtin_sub_overflow((typeof(ckd_paste(ckd_a_, c)))0, ckd_paste(ckd_a_, c), \\\n"
"                               &(typeof(ckd_paste(ckd_a_, c))){0})) \\\n"
"        ckd_overflow_handler_(\"signed division overflow\", col); \\\n"
"    ckd_paste(ckd_a_, c) / ckd_paste(ckd_b_, c); \\\n"
"})\n"
"\n"
"#define ckd_mod(a, b, col) ckd_mod_(a, b, col, __COUNTER__)\n"
"#define ckd_mod_(a, b, col, c) ckd_mod_impl_(a, b, col, c)\n"
"#define ckd_mod_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    if (ckd_paste(ckd_b_, c) == 0) \\\n"
"        ckd_overflow_handler_(\"division by zero\", col); \\\n"
"    if ((typeof(ckd_paste(ckd_b_, c)))(-1) < 0 && ckd_paste(ckd_b_, c) == -1 && \\\n"
"        __builtin_sub_overflow((typeof(ckd_paste(ckd_a_, c)))0, ckd_paste(ckd_a_, c), \\\n"
"                               &(typeof(ckd_paste(ckd_a_, c))){0})) \\\n"
"        ckd_overflow_handler_(\"signed division overflow\", col); \\\n"
"    ckd_paste(ckd_a_, c) % ckd_paste(ckd_b_, c); \\\n"
"})\n"
"\n"
"#define ckd_shl(a, b, col) ckd_shl_(a, b, col, __COUNTER__)\n"
"#define ckd_shl_(a, b, col, c) ckd_shl_impl_(a, b, col, c)\n"
"#define ckd_shl_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    if (ckd_paste(ckd_b_, c) < 0 || \\\n"
"        (__SIZE_TYPE__)ckd_paste(ckd_b_, c) >= \\\n"
"            sizeof(typeof(ckd_paste(ckd_a_, c) << ckd_paste(ckd_b_, c))) * 8) \\\n"
"        ckd_overflow_handler_(\"shift out of range\", col); \\\n"
"    ckd_paste(ckd_a_, c) << ckd_paste(ckd_b_, c); \\\n"
"})\n"
"\n"
"#define ckd_shr(a, b, col) ckd_shr_(a, b, col, __COUNTER__)\n"
"#define ckd_shr_(a, b, col, c) ckd_shr_impl_(a, b, col, c)\n"
"#define ckd_shr_impl_(a, b, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    __auto_type ckd_paste(ckd_b_, c) = (b); \\\n"
"    if (ckd_paste(ckd_b_, c) < 0 || \\\n"
"        (__SIZE_TYPE__)ckd_paste(ckd_b_, c) >= \\\n"
"            sizeof(typeof(ckd_paste(ckd_a_, c) >> ckd_paste(ckd_b_, c))) * 8) \\\n"
"        ckd_overflow_handler_(\"shift out of range\", col); \\\n"
"    ckd_paste(ckd_a_, c) >> ckd_paste(ckd_b_, c); \\\n"
"})\n"
"\n"
"#define ckd_neg(a, col) ckd_neg_(a, col, __COUNTER__)\n"
"#define ckd_neg_(a, col, c) ckd_neg_impl_(a, col, c)\n"
"#define ckd_neg_impl_(a, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_a_, c) = (a); \\\n"
"    typeof(-ckd_paste(ckd_a_, c)) ckd_paste(ckd_r_, c); \\\n"
"    if (__builtin_sub_overflow( \\\n"
"            (typeof(ckd_paste(ckd_a_, c)))0, ckd_paste(ckd_a_, c), \\\n"
"            &ckd_paste(ckd_r_, c)) && \\\n"
"        (typeof(ckd_paste(ckd_a_, c)))(-1) < 0) \\\n"
"        ckd_overflow_handler_(\"negation overflow\", col); \\\n"
"    ckd_paste(ckd_r_, c); \\\n"
"})\n"
"\n"
"#define ckd_narrow(val, target_type, col) ckd_narrow_(val, target_type, col, __COUNTER__)\n"
"#define ckd_narrow_(val, target_type, col, c) ckd_narrow_impl_(val, target_type, col, c)\n"
"#define ckd_narrow_impl_(val, target_type, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_v_, c) = (val); \\\n"
"    if ((typeof(ckd_paste(ckd_v_, c)))(target_type)(ckd_paste(ckd_v_, c)) \\\n"
"        != ckd_paste(ckd_v_, c)) \\\n"
"        ckd_overflow_handler_(\"narrowing conversion\", col); \\\n"
"    (target_type)(ckd_paste(ckd_v_, c)); \\\n"
"})\n"
"\n"
"#define ckd_bounds(arr, idx, size, col) ckd_bounds_(arr, idx, size, col, __COUNTER__)\n"
"#define ckd_bounds_(arr, idx, size, col, c) ckd_bounds_impl_(arr, idx, size, col, c)\n"
"#define ckd_bounds_impl_(arr, idx, size, col, c) (*__extension__({ \\\n"
"    __auto_type ckd_paste(ckd_i_, c) = (idx); \\\n"
"    if ((__SIZE_TYPE__)ckd_paste(ckd_i_, c) >= (__SIZE_TYPE__)(size)) \\\n"
"        ckd_overflow_handler_(\"array out of bounds\", col); \\\n"
"    &(arr)[ckd_paste(ckd_i_, c)]; \\\n"
"}))\n"
"\n"
"#define ckd_array_ptr(arr, idx, size, col) ckd_array_ptr_(arr, idx, size, col, __COUNTER__)\n"
"#define ckd_array_ptr_(arr, idx, size, col, c) ckd_array_ptr_impl_(arr, idx, size, col, c)\n"
"#define ckd_array_ptr_impl_(arr, idx, size, col, c) __extension__({ \\\n"
"    __auto_type ckd_paste(ckd_i_, c) = (idx); \\\n"
"    if ((__SIZE_TYPE__)ckd_paste(ckd_i_, c) > (__SIZE_TYPE__)(size)) \\\n"
"        ckd_overflow_handler_(\"array out of bounds\", col); \\\n"
"    &(arr)[ckd_paste(ckd_i_, c)]; \\\n"
"})\n"
"\n"
"#define ckd_compound(lhs, op, rhs, col) ckd_compound__(lhs, op, rhs, col, __COUNTER__)\n"
"#define ckd_compound__(lhs, op, rhs, col, c) ckd_compound_impl_(lhs, op, rhs, col, c)\n"
"#define ckd_compound_impl_(lhs, op, rhs, col, c) __extension__({ \\\n"
"    typeof(&(lhs)) ckd_paste(ckd_p_, c) = &(lhs); \\\n"
"    *ckd_paste(ckd_p_, c) = op(*ckd_paste(ckd_p_, c), (rhs), col); \\\n"
"})\n"
"\n"
"#define ckd_compound_narrow(lhs, op, rhs, type, col) \\\n"
"    ckd_compound_narrow__(lhs, op, rhs, type, col, __COUNTER__)\n"
"#define ckd_compound_narrow__(lhs, op, rhs, type, col, c) \\\n"
"    ckd_compound_narrow_impl_(lhs, op, rhs, type, col, c)\n"
"#define ckd_compound_narrow_impl_(lhs, op, rhs, type, col, c) __extension__({ \\\n"
"    typeof(&(lhs)) ckd_paste(ckd_p_, c) = &(lhs); \\\n"
"    *ckd_paste(ckd_p_, c) = ckd_narrow(op(*ckd_paste(ckd_p_, c), (rhs), col), type, col); \\\n"
"})\n"
"\n"
"#define ckd_bf_compound(lhs, op, rhs, col) ((void)((lhs) = op((lhs), (rhs), col)))\n"
"#define ckd_bf_compound_narrow(lhs, op, rhs, type, col) \\\n"
"    ((void)((lhs) = ckd_narrow(op((lhs), (rhs), col), type, col)))\n"
"\n"
"#define ckd_bf_preinc(a, col) ckd_bf_compound(a, ckd_add, 1, col)\n"
"#define ckd_bf_predec(a, col) ckd_bf_compound(a, ckd_sub, 1, col)\n"
"\n"
"#define ckd_bf_postinc(a, col) ckd_bf_postinc_(a, col, __COUNTER__)\n"
"#define ckd_bf_postinc_(a, col, c) ckd_bf_postinc_impl_(a, col, c)\n"
"#define ckd_bf_postinc_impl_(a, col, c) __extension__({ \\\n"
"    typeof(a) ckd_paste(ckd_old_, c) = (a); \\\n"
"    (a) = ckd_add((a), 1, col); \\\n"
"    ckd_paste(ckd_old_, c); \\\n"
"})\n"
"\n"
"#define ckd_bf_postdec(a, col) ckd_bf_postdec_(a, col, __COUNTER__)\n"
"#define ckd_bf_postdec_(a, col, c) ckd_bf_postdec_impl_(a, col, c)\n"
"#define ckd_bf_postdec_impl_(a, col, c) __extension__({ \\\n"
"    typeof(a) ckd_paste(ckd_old_, c) = (a); \\\n"
"    (a) = ckd_sub((a), 1, col); \\\n"
"    ckd_paste(ckd_old_, c); \\\n"
"})\n"
"\n"
"#define ckd_preinc(a, col) ckd_compound(a, ckd_add, 1, col)\n"
"#define ckd_predec(a, col) ckd_compound(a, ckd_sub, 1, col)\n"
"\n"
"#define ckd_postinc(a, col) ckd_postinc_(a, col, __COUNTER__)\n"
"#define ckd_postinc_(a, col, c) ckd_postinc_impl_(a, col, c)\n"
"#define ckd_postinc_impl_(a, col, c) __extension__({ \\\n"
"    typeof(&(a)) ckd_paste(ckd_pp_, c) = &(a); \\\n"
"    __auto_type ckd_paste(ckd_old_, c) = *ckd_paste(ckd_pp_, c); \\\n"
"    *ckd_paste(ckd_pp_, c) = ckd_add(*ckd_paste(ckd_pp_, c), 1, col); \\\n"
"    ckd_paste(ckd_old_, c); \\\n"
"})\n"
"\n"
"#define ckd_postdec(a, col) ckd_postdec_(a, col, __COUNTER__)\n"
"#define ckd_postdec_(a, col, c) ckd_postdec_impl_(a, col, c)\n"
"#define ckd_postdec_impl_(a, col, c) __extension__({ \\\n"
"    typeof(&(a)) ckd_paste(ckd_pp_, c) = &(a); \\\n"
"    __auto_type ckd_paste(ckd_old_, c) = *ckd_paste(ckd_pp_, c); \\\n"
"    *ckd_paste(ckd_pp_, c) = ckd_sub(*ckd_paste(ckd_pp_, c), 1, col); \\\n"
"    ckd_paste(ckd_old_, c); \\\n"
"})\n"
"\n"
"#define ckd_ptr_preinc(a, col) ckd_compound(a, ckd_ptr_add, 1, col)\n"
"#define ckd_ptr_predec(a, col) ckd_compound(a, ckd_ptr_sub, 1, col)\n"
"\n"
"#define ckd_ptr_postinc(a, col) ckd_ptr_postinc_(a, col, __COUNTER__)\n"
"#define ckd_ptr_postinc_(a, col, c) ckd_ptr_postinc_impl_(a, col, c)\n"
"#define ckd_ptr_postinc_impl_(a, col, c) __extension__({ \\\n"
"    typeof(&(a)) ckd_paste(ckd_pp_, c) = &(a); \\\n"
"    __auto_type ckd_paste(ckd_old_, c) = *ckd_paste(ckd_pp_, c); \\\n"
"    *ckd_paste(ckd_pp_, c) = ckd_ptr_add(*ckd_paste(ckd_pp_, c), 1, col); \\\n"
"    ckd_paste(ckd_old_, c); \\\n"
"})\n"
"\n"
"#define ckd_ptr_postdec(a, col) ckd_ptr_postdec_(a, col, __COUNTER__)\n"
"#define ckd_ptr_postdec_(a, col, c) ckd_ptr_postdec_impl_(a, col, c)\n"
"#define ckd_ptr_postdec_impl_(a, col, c) __extension__({ \\\n"
"    typeof(&(a)) ckd_paste(ckd_pp_, c) = &(a); \\\n"
"    __auto_type ckd_paste(ckd_old_, c) = *ckd_paste(ckd_pp_, c); \\\n"
"    *ckd_paste(ckd_pp_, c) = ckd_ptr_sub(*ckd_paste(ckd_pp_, c), 1, col); \\\n"
"    ckd_paste(ckd_old_, c); \\\n"
"})\n"
"\n"
"#endif /* SAFER_CC_PREAMBLE_ */\n"
"/* --- end safer-cc preamble --- */\n"
"\n";

static const char *DEFAULT_HANDLER = "__builtin_trap()";

static void emit_preamble(const char *handler, Str *out) {
    str_append_cstr(out, PREAMBLE_PREFIX);
    str_append_cstr(out, handler);
    str_append_cstr(out, PREAMBLE_SUFFIX);
}

/* ========================================================================= */
/* Top-level process                                                         */
/* ========================================================================= */

static char *process_source(const char *src, size_t n, int emit_pre, const char *handler) {
    Preprocessed pp = preprocess(src, n);

    Tokens toks;
    tokenize(pp.stripped, pp.len, &toks);

    Parser P;
    P.toks = &toks;
    P.pos = 0;
    P.src = pp.stripped;
    P.src_len = pp.len;
    smap_init(&P.typedefs);
    build_line_table(&P, pp.stripped, pp.len);

    Node *root = parse_translation_unit(&P);

    Tracker global;
    tracker_init(&global);
    tracker_scan(&global, root, src, 1, 0);

    Rewriter rw;
    rw.src = src;
    rw.src_len = n;
    rw.suppressed = pp.suppressed;
    rw.nsup = pp.nsup;
    rw.disabled = pp.disabled;
    rw.ndis = pp.ndis;

    char *body = transform(root, &rw, &global);
    Str result_body; str_init(&result_body);
    if (body) {
        /* Include any prefix/suffix source bytes */
        strip_markers_into(&rw, 0, root->start, &result_body);
        str_append_cstr(&result_body, body);
        strip_markers_into(&rw, root->end, n, &result_body);
        free(body);
    } else {
        strip_markers_into(&rw, 0, n, &result_body);
    }

    Str out; str_init(&out);
    if (emit_pre) emit_preamble(handler, &out);
    if (result_body.data) str_append_cstr(&out, result_body.data);
    str_free(&result_body);

    node_free(root);
    tracker_free(&global);
    smap_free(&P.typedefs);
    free(P.line_starts);
    toks_free(&toks);
    pp_free(&pp);

    if (!out.data) out.data = xstrdup("");
    return str_detach(&out);
}

/* ========================================================================= */
/* File I/O                                                                  */
/* ========================================================================= */

static char *read_whole_file(const char *path, size_t *out_len) {
    FILE *f;
    if (!path || strcmp(path, "-") == 0) f = stdin;
    else f = fopen(path, "rb");
    if (!f) die("cannot open %s: %s", path ? path : "-", strerror(errno));
    size_t cap = 4096, len = 0;
    char *buf = xmalloc(cap);
    for (;;) {
        if (len + 4096 > cap) { cap *= 2; buf = xrealloc(buf, cap); }
        size_t r = fread(buf + len, 1, cap - len, f);
        if (r == 0) break;
        len += r;
    }
    if (f != stdin) fclose(f);
    *out_len = len;
    return buf;
}

static void write_whole_file(const char *path, const char *data, size_t len) {
    FILE *f;
    if (!path || strcmp(path, "-") == 0) f = stdout;
    else f = fopen(path, "wb");
    if (!f) die("cannot open %s: %s", path ? path : "-", strerror(errno));
    if (fwrite(data, 1, len, f) != len) die("write failed");
    if (f != stdout) fclose(f);
}

static char *read_handler_file(const char *path) {
    size_t n;
    char *s = read_whole_file(path, &n);
    /* Trim trailing whitespace */
    while (n > 0 && (s[n-1] == '\n' || s[n-1] == '\r' || s[n-1] == ' ' || s[n-1] == '\t')) n--;
    /* Trim leading whitespace */
    size_t st = 0;
    while (st < n && (s[st] == ' ' || s[st] == '\t')) st++;
    char *r = xstrndup(s + st, n - st);
    free(s);
    return r;
}

/* ========================================================================= */
/* CLI                                                                       */
/* ========================================================================= */

static int main_filter(int argc, char **argv) {
    const char *input = "-";
    const char *output = "-";
    int no_preamble = 0;
    char *handler = NULL;
    int have_input = 0;
    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        if (strcmp(a, "--no-preamble") == 0) no_preamble = 1;
        else if (strcmp(a, "--handler") == 0 && i + 1 < argc) {
            handler = read_handler_file(argv[++i]);
        } else if (strncmp(a, "--handler=", 10) == 0) {
            handler = read_handler_file(a + 10);
        } else if (strcmp(a, "-o") == 0 && i + 1 < argc) {
            output = argv[++i];
        } else if (strncmp(a, "-o", 2) == 0 && strlen(a) > 2) {
            output = a + 2;
        } else if (strcmp(a, "--output") == 0 && i + 1 < argc) {
            output = argv[++i];
        } else if (strncmp(a, "--output=", 9) == 0) {
            output = a + 9;
        } else if (!have_input) {
            input = a;
            have_input = 1;
        }
    }
    size_t n;
    char *src = read_whole_file(input, &n);
    const char *hdl = handler ? handler : DEFAULT_HANDLER;
    char *result = process_source(src, n, !no_preamble, hdl);
    write_whole_file(output, result, strlen(result));
    free(src);
    free(result);
    free(handler);
    return 0;
}

static int run_cmd(char **argv) {
    pid_t pid = fork();
    if (pid < 0) die("fork failed: %s", strerror(errno));
    if (pid == 0) {
        execvp(argv[0], argv);
        fprintf(stderr, "safer-cc: exec %s failed: %s\n", argv[0], strerror(errno));
        _exit(127);
    }
    int status = 0;
    while (waitpid(pid, &status, 0) < 0) {
        if (errno != EINTR) die("waitpid failed: %s", strerror(errno));
    }
    if (WIFSIGNALED(status)) return 128 + WTERMSIG(status);
    return WEXITSTATUS(status);
}

static int str_ends_with(const char *s, const char *suf) {
    size_t sl = strlen(s), fl = strlen(suf);
    if (sl < fl) return 0;
    return memcmp(s + sl - fl, suf, fl) == 0;
}

static int main_cc(int argc, char **argv) {
    const char *cc = NULL;
    char *handler = NULL;
    char **cc_args = xcalloc(argc + 8, sizeof(*cc_args));
    int ncc_args = 0;
    for (int i = 1; i < argc; i++) {
        const char *a = argv[i];
        if (strncmp(a, "--cc=", 5) == 0) cc = a + 5;
        else if (strcmp(a, "--cc") == 0 && i + 1 < argc) cc = argv[++i];
        else if (strncmp(a, "--handler=", 10) == 0) handler = read_handler_file(a + 10);
        else if (strcmp(a, "--handler") == 0 && i + 1 < argc) handler = read_handler_file(argv[++i]);
        else cc_args[ncc_args++] = (char *)a;
    }
    if (!cc) die("--cc=<compiler> is required");

    /* Find source file, -o output, -c flag */
    const char *source_file = NULL;
    const char *output_file = NULL;
    int has_c = 0;
    char **other = xcalloc(ncc_args + 4, sizeof(*other));
    int nother = 0;
    for (int i = 0; i < ncc_args; i++) {
        const char *a = cc_args[i];
        if (strcmp(a, "-o") == 0 && i + 1 < ncc_args) {
            output_file = cc_args[++i];
            continue;
        }
        if (strcmp(a, "-c") == 0) { has_c = 1; continue; }
        if (a[0] != '-' && (str_ends_with(a, ".c") || str_ends_with(a, ".h") || str_ends_with(a, ".i"))) {
            source_file = a;
            continue;
        }
        other[nother++] = (char *)a;
    }
    if (!source_file) die("no source file found in arguments");
    if (!has_c) die("-c flag required (safer-cc only does compilation, not linking)");
    char *derived_out = NULL;
    if (!output_file) {
        const char *dot = strrchr(source_file, '.');
        size_t sl = dot ? (size_t)(dot - source_file) : strlen(source_file);
        derived_out = xmalloc(sl + 3);
        memcpy(derived_out, source_file, sl);
        derived_out[sl] = '.';
        derived_out[sl+1] = 'o';
        derived_out[sl+2] = 0;
        output_file = derived_out;
    }

    char tmpdir_tmpl[] = "/tmp/safer-cc-XXXXXX";
    if (!mkdtemp(tmpdir_tmpl)) die("mkdtemp failed: %s", strerror(errno));
    char pp_file[256]; snprintf(pp_file, sizeof(pp_file), "%s/pp.i", tmpdir_tmpl);
    char rewritten_file[256]; snprintf(rewritten_file, sizeof(rewritten_file), "%s/rewritten.c", tmpdir_tmpl);

    /* Separate dep-generation flags */
    static const char *dep_flags[] = {"-MMD", "-MD", "-MP", "-MG"};
    static const char *dep_with_arg[] = {"-MF", "-MQ", "-MT"};

    char **pp_args = xcalloc(nother + 16, sizeof(*pp_args));
    int npp_args = 0;
    char **compile_args = xcalloc(nother + 16, sizeof(*compile_args));
    int ncompile_args = 0;
    int has_dep_gen = 0;
    for (int i = 0; i < nother; i++) {
        const char *a = other[i];
        pp_args[npp_args++] = (char *)a;
        int is_dep = 0;
        for (size_t j = 0; j < sizeof(dep_flags)/sizeof(*dep_flags); j++)
            if (strcmp(a, dep_flags[j]) == 0) { is_dep = 1; break; }
        if (is_dep) {
            if (strcmp(a, "-MMD") == 0 || strcmp(a, "-MD") == 0) has_dep_gen = 1;
            continue;
        }
        int skip_next = 0;
        for (size_t j = 0; j < sizeof(dep_with_arg)/sizeof(*dep_with_arg); j++) {
            if (strcmp(a, dep_with_arg[j]) == 0) { skip_next = 1; break; }
            size_t pl = strlen(dep_with_arg[j]);
            if (strncmp(a, dep_with_arg[j], pl) == 0) { is_dep = 1; break; }
        }
        if (skip_next) {
            if (i + 1 < nother) i++;
            continue;
        }
        if (is_dep) continue;
        compile_args[ncompile_args++] = (char *)a;
    }
    char *dep_mt = NULL;
    if (has_dep_gen) {
        /* Derive .d path */
        const char *dot = strrchr(output_file, '.');
        size_t sl = dot ? (size_t)(dot - output_file) : strlen(output_file);
        char *dep_file = xmalloc(sl + 3);
        memcpy(dep_file, output_file, sl);
        dep_file[sl] = '.'; dep_file[sl+1] = 'd'; dep_file[sl+2] = 0;
        pp_args[npp_args++] = (char *)"-MF";
        pp_args[npp_args++] = dep_file;
        pp_args[npp_args++] = (char *)"-MT";
        pp_args[npp_args++] = (char *)output_file;
        dep_mt = dep_file;
    }

    /* Step 1: preprocess */
    char **pp_cmd = xcalloc(npp_args + 8, sizeof(*pp_cmd));
    int n0 = 0;
    pp_cmd[n0++] = (char *)cc;
    for (int i = 0; i < npp_args; i++) pp_cmd[n0++] = pp_args[i];
    pp_cmd[n0++] = (char *)"-E";
    pp_cmd[n0++] = (char *)source_file;
    pp_cmd[n0++] = (char *)"-o";
    pp_cmd[n0++] = pp_file;
    pp_cmd[n0] = NULL;
    int rc = run_cmd(pp_cmd);
    if (rc != 0) exit(rc);
    free(pp_cmd);

    /* Step 2: rewrite */
    size_t n;
    char *src = read_whole_file(pp_file, &n);
    const char *hdl = handler ? handler : DEFAULT_HANDLER;
    char *result = process_source(src, n, 1, hdl);
    write_whole_file(rewritten_file, result, strlen(result));
    free(src);
    free(result);

    /* Step 3: compile */
    char **compile_cmd = xcalloc(ncompile_args + 16, sizeof(*compile_cmd));
    int n1 = 0;
    compile_cmd[n1++] = (char *)cc;
    for (int i = 0; i < ncompile_args; i++) compile_cmd[n1++] = compile_args[i];
    compile_cmd[n1++] = (char *)"-c";
    compile_cmd[n1++] = (char *)"-x";
    compile_cmd[n1++] = (char *)"c";
    compile_cmd[n1++] = rewritten_file;
    compile_cmd[n1++] = (char *)"-o";
    compile_cmd[n1++] = (char *)output_file;
    compile_cmd[n1] = NULL;
    rc = run_cmd(compile_cmd);
    free(compile_cmd);

    /* Cleanup */
    unlink(pp_file);
    unlink(rewritten_file);
    rmdir(tmpdir_tmpl);

    free(derived_out);
    free(pp_args);
    free(compile_args);
    free(other);
    free(cc_args);
    free(dep_mt);
    free(handler);
    return rc;
}

int main(int argc, char **argv) {
    for (int i = 1; i < argc; i++) {
        if (strncmp(argv[i], "--cc", 4) == 0) return main_cc(argc, argv);
    }
    return main_filter(argc, argv);
}
