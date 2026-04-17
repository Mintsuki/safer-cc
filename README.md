# safer-cc

A compile-time C source rewriting tool that instruments code with runtime safety checks. It parses C source with a built-in C99 parser and rewrites arithmetic, pointer, array, and type conversion operations to include overflow, bounds, and narrowing checks.

safer-cc can be used as a drop-in compiler wrapper or as a standalone source filter. It is distributed as a single self-contained C99 source file with no external dependencies.

## Build

```sh
cc -std=c99 -O2 -o safer-cc safer-cc.c
```

## Checks

| Category | Operations | Detection |
|---|---|---|
| Arithmetic overflow | `+`, `-`, `*` | `__builtin_*_overflow` |
| Division | `/`, `%` | Division by zero + signed `TYPE_MIN / -1` |
| Shifts | `<<`, `>>` | Shift amount out of range (uses promoted type width) |
| Negation | `-x` | Signed overflow (`-INT_MIN`) |
| Pointer arithmetic | `ptr + i`, `ptr - i` | Null pointer + address wrap detection |
| Pointer difference | `ptr1 - ptr2` | `ptrdiff_t` overflow |
| Array bounds | `arr[i]` | Index vs known size (fixed, multi-dim, VLA, parameter arrays) |
| Narrowing | assignment, init, return, compound, cast, call arg | Round-trip cast detects truncation on all integer types |
| Compound assignment | `+=`, `-=`, `*=`, `/=`, `%=`, `<<=`, `>>=` | Single-evaluation of LHS + arithmetic check + narrowing |
| Increment/decrement | `++`, `--` | Single-evaluation, checked (integer and pointer) |

## Skips

- Both operands are compile-time constants
- Expressions inside `sizeof()` / `_Alignof()`
- File-scope initializers (statement expressions are invalid there)
- Operations marked with `@` suppression

## Usage

### Compiler wrapper

```sh
safer-cc --cc=clang --handler handler.txt [cc flags] -c source.c -o output.o
```

The tool preprocesses the source, rewrites it, and compiles the result. The `--handler` file contains C code that is invoked when a check fails, receiving `op` (string literal describing the operation) and `col` (column number in the original source).

### Filter mode

```sh
safer-cc [--no-preamble] [--handler handler.txt] [input.c] [-o output.c]
```

Rewrites source from stdin or a file and writes to stdout or a file. With `--no-preamble`, the macro definitions are omitted (useful for testing).

### Build system integration

Example Makefile integration:

```makefile
SAFER_CC := safer-cc --cc=$(CC) --handler handler.txt
$(SAFER_CC) $(CFLAGS) -c source.c -o output.o
```

## Suppression

Prefix any operator with `@` to suppress the check for that specific operation:

```c
sum @+= byte;          // suppress compound assignment check
buf@[i] = val;          // suppress bounds check
char c = @(char)wide;   // suppress cast narrowing check
@return val;            // suppress return narrowing check
x @= val;              // suppress assignment narrowing check
```

The `@` marker is removed during preprocessing and does not affect the compiled output.

## Handler

The `--handler` flag specifies a file containing the C code to execute when a check fails. The handler receives two parameters:

- `op` — a string literal describing the failed check (e.g. `"addition"`, `"array out of bounds"`, `"narrowing conversion"`)
- `col` — an integer literal for the column number in the original source

Example handler:

```c
do { \
    extern _Noreturn void panic(_Bool, const char *, ...); \
    extern _Bool recoverable; \
    panic(recoverable, "%s at %s:%d:%d", op, __FILE__, __LINE__, col); \
} while (0)
```

If no handler is specified, `__builtin_trap()` is used.

## Requirements

- A C99 compiler to build `safer-cc` itself (any modern `cc`).
- GCC or Clang to compile the generated code (for `__extension__`, `__auto_type`, `typeof`, `__builtin_*_overflow`, `__COUNTER__`).

## Testing

```sh
cd tests && bash run.sh
```

Test files use a simple format:

```
=== test name ===
input C code
---
expected output
```

## License

BSD 2-Clause. See [LICENSE](LICENSE).
