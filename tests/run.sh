#!/bin/sh
# safer-cc test runner
#
# Test file format (.test):
#   === test name ===
#   <input C code>
#   ---
#   <exact expected output>
#
# The runner passes each input through safer-cc --no-preamble and
# compares the output byte-for-byte against the expected output.

set -e

CKDOPSPP="$(dirname "$0")/../safer-cc"
PASS=0
FAIL=0
ERRORS=""

run_test() {
    name="$1"
    input="$2"
    expected="$3"

    actual="$(printf '%s' "$input" | python3 "$CKDOPSPP" --no-preamble 2>&1)" || {
        FAIL=$((FAIL + 1))
        ERRORS="${ERRORS}\nFAIL: ${name} (safer-cc crashed)"
        return
    }

    # Trim trailing whitespace/newlines for comparison
    actual="$(printf '%s' "$actual" | sed 's/[[:space:]]*$//')"
    expected="$(printf '%s' "$expected" | sed 's/[[:space:]]*$//')"

    if [ "$actual" != "$expected" ]; then
        FAIL=$((FAIL + 1))
        diff_out="$(diff <(printf '%s\n' "$expected") <(printf '%s\n' "$actual") || true)"
        ERRORS="${ERRORS}\nFAIL: ${name}\n${diff_out}\n"
        return
    fi

    PASS=$((PASS + 1))
}

for testfile in "$(dirname "$0")"/*.test; do
    [ -f "$testfile" ] || continue
    category="$(basename "$testfile" .test)"

    current_name=""
    current_input=""
    current_expected=""
    in_expected=0

    while IFS= read -r line || [ -n "$line" ]; do
        case "$line" in
            '=== '*)
                if [ -n "$current_name" ]; then
                    run_test "${category}/${current_name}" "$current_input" "$current_expected"
                fi
                current_name="$(echo "$line" | sed 's/^=== //;s/ ===$//')"
                current_input=""
                current_expected=""
                in_expected=0
                ;;
            '---')
                in_expected=1
                ;;
            *)
                if [ "$in_expected" -eq 1 ]; then
                    if [ -n "$current_expected" ]; then
                        current_expected="${current_expected}
${line}"
                    else
                        current_expected="$line"
                    fi
                else
                    if [ -n "$current_input" ]; then
                        current_input="${current_input}
${line}"
                    else
                        current_input="$line"
                    fi
                fi
                ;;
        esac
    done < "$testfile"

    if [ -n "$current_name" ]; then
        run_test "${category}/${current_name}" "$current_input" "$current_expected"
    fi
done

total=$((PASS + FAIL))
echo "Ran ${total} tests: ${PASS} passed, ${FAIL} failed"

if [ "$FAIL" -gt 0 ]; then
    printf '%b\n' "$ERRORS"
    exit 1
fi
