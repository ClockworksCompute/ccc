#!/usr/bin/env bash
#
# scripts/corpus.sh — CVE regression corpus scoreboard for CCC's verifier.
#
# For every subdirectory of test/corpus/, runs `ccc` (verify-only, no
# linking) against both vulnerable.c and fixed.c and classifies the pair:
#
#   detected       vulnerable.c REJECTED (a violation reported) AND
#                  fixed.c ACCEPTED (no violation reported)
#   missed         vulnerable.c ACCEPTED -- the real bug slipped through
#   false-positive vulnerable.c REJECTED but fixed.c is ALSO REJECTED --
#                  the verifier flagged the demonstrably-safe post-fix code
#   parse-failed   ccc could not parse or emit assembly for one of the two
#                  files (unrelated to verifier precision -- see
#                  CCC/Preprocess/Preprocess.lean's limited header/feature
#                  support)
#   timeout        ccc did not finish within TIMEOUT_SECS on one of the two
#                  files
#
# NOTE ON EXIT CODES: `ccc` in verify-only mode currently exits 0 even when
# it reports memory-safety violations, because "force-emit" still produces
# assembly for unsafe programs (see FEL-40). This script therefore reads the
# printed report text, not the process exit code, to determine the verdict.
#
# This is a measurement script, not a CI gate: it always exits 0. The
# checked-in baseline snapshot lives at docs/corpus-results.md.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CORPUS_DIR="$REPO_ROOT/test/corpus"
CCC_BIN="$REPO_ROOT/.lake/build/bin/ccc"
TIMEOUT_SECS=20

if [ ! -x "$CCC_BIN" ]; then
    echo "error: $CCC_BIN not found or not executable." >&2
    echo "       Build it first: (cd '$REPO_ROOT' && lake build ccc)" >&2
    exit 0
fi

if [ ! -d "$CORPUS_DIR" ]; then
    echo "error: $CORPUS_DIR does not exist." >&2
    exit 0
fi

# run_with_timeout <seconds> <outfile> <cmd...> -> exit status of <cmd>, or
# 124 if it had to be killed. Polls every 0.5s; no dependency on GNU
# coreutils `timeout`, which is not present on macOS by default (confirmed
# absent on the machine this baseline was measured on: `which timeout` ->
# "not found"). Using the real `timeout(1)` here silently broke every
# verdict to "accepted" (the shell's own "command not found" text doesn't
# match any of run_ccc's grep patterns, so it fell through to the default
# case) -- so this portable polling loop is required, not just a style
# preference.
run_with_timeout() {
    local secs="$1" outfile="$2"
    shift 2
    "$@" >"$outfile" 2>&1 &
    local pid=$!
    local max=$((secs * 2)) i=0
    while kill -0 "$pid" 2>/dev/null; do
        sleep 0.5
        i=$((i + 1))
        if [ "$i" -ge "$max" ]; then
            kill -9 "$pid" 2>/dev/null
            wait "$pid" 2>/dev/null
            return 124
        fi
    done
    wait "$pid"
    return $?
}

# run_ccc <file>
# Sets RC_VERDICT to one of: accepted, rejected, parse-failed, timeout
# Sets RC_LINE to the first reported violation line, or "-"
run_ccc() {
    local file="$1"
    local out status outfile

    outfile="$(mktemp)"
    run_with_timeout "$TIMEOUT_SECS" "$outfile" "$CCC_BIN" "$file"
    status=$?
    out="$(cat "$outfile")"
    rm -f "$outfile"

    if [ "$status" -eq 124 ] || [ "$status" -eq 137 ]; then
        RC_VERDICT="timeout"
        RC_LINE="-"
        return
    fi

    if printf '%s\n' "$out" | grep -q "ERROR: Parse error\|ERROR: Emission error"; then
        RC_VERDICT="parse-failed"
        RC_LINE="-"
        return
    fi

    if printf '%s\n' "$out" | grep -q "memory safety violation(s) found"; then
        RC_VERDICT="rejected"
        RC_LINE=$(printf '%s\n' "$out" | grep -o "violation at line [0-9]*" | head -1 | grep -o "[0-9]*$")
        [ -z "$RC_LINE" ] && RC_LINE="?"
        return
    fi

    RC_VERDICT="accepted"
    RC_LINE="-"
}

n_total=0
n_detected=0
n_missed=0
n_false_positive=0
n_parse_failed=0
n_timeout=0
n_unsound=0

printf '%-34s %-11s %-11s %-16s %s\n' "ENTRY" "VULN" "FIXED" "CLASS" "NOTES"
printf -- '--------------------------------------------------------------------------------------------\n'

for entry_dir in "$CORPUS_DIR"/*/; do
    [ -d "$entry_dir" ] || continue
    entry_name="$(basename "$entry_dir")"
    vuln_file="$entry_dir/vulnerable.c"
    fixed_file="$entry_dir/fixed.c"

    if [ ! -f "$vuln_file" ] || [ ! -f "$fixed_file" ]; then
        printf '%-34s %-11s %-11s %-16s %s\n' "$entry_name" "-" "-" "skipped" "missing vulnerable.c/fixed.c"
        continue
    fi

    n_total=$((n_total + 1))

    run_ccc "$vuln_file"
    vuln_verdict="$RC_VERDICT"
    vuln_line="$RC_LINE"

    run_ccc "$fixed_file"
    fixed_verdict="$RC_VERDICT"
    fixed_line="$RC_LINE"

    notes="-"
    if [ "$vuln_verdict" = "parse-failed" ] || [ "$fixed_verdict" = "parse-failed" ]; then
        class="parse-failed"
        n_parse_failed=$((n_parse_failed + 1))
    elif [ "$vuln_verdict" = "timeout" ] || [ "$fixed_verdict" = "timeout" ]; then
        class="timeout"
        n_timeout=$((n_timeout + 1))
    elif [ "$vuln_verdict" = "accepted" ]; then
        class="missed"
        n_missed=$((n_missed + 1))
        notes="bug not flagged"
    elif [ "$vuln_verdict" = "rejected" ] && [ "$fixed_verdict" = "accepted" ]; then
        # Provisionally "detected" on the vulnerable/fixed pair alone -- but
        # that pair is a single data point. FEL-64: a mechanism can reject
        # vulnerable.c and accept fixed.c for reasons that have nothing to
        # do with soundly modelling the bug, and still accept a handful of
        # one-line mutants of fixed.c that reintroduce the exact same class
        # of overflow. So a "detected" verdict is only trustworthy once
        # every file under this entry's must-reject/ directory (variants
        # that are KNOWN, ASan-confirmed, to overflow) is also rejected.
        must_reject_dir="$entry_dir/must-reject"
        unsound_file=""
        if [ -d "$must_reject_dir" ]; then
            for mr_file in "$must_reject_dir"/*.c; do
                [ -f "$mr_file" ] || continue
                run_ccc "$mr_file"
                if [ "$RC_VERDICT" != "rejected" ]; then
                    unsound_file="$(basename "$mr_file")"
                    break
                fi
            done
        fi
        if [ -n "$unsound_file" ]; then
            class="false-positive"
            n_false_positive=$((n_false_positive + 1))
            n_unsound=$((n_unsound + 1))
            notes="UNSOUND: must-reject/$unsound_file was accepted (FEL-64)"
        else
            class="detected"
            n_detected=$((n_detected + 1))
            notes="violation at line $vuln_line"
            if [ -d "$must_reject_dir" ]; then
                notes="$notes; must-reject/ variants all rejected"
            fi
        fi
    else
        # vuln rejected, fixed also rejected
        class="false-positive"
        n_false_positive=$((n_false_positive + 1))
        notes="fixed.c flagged at line $fixed_line"
    fi

    printf '%-34s %-11s %-11s %-16s %s\n' "$entry_name" "$vuln_verdict" "$fixed_verdict" "$class" "$notes"
done

printf -- '--------------------------------------------------------------------------------------------\n'
echo
echo "SUMMARY: $n_total entries -- detected=$n_detected missed=$n_missed false-positive=$n_false_positive parse-failed=$n_parse_failed timeout=$n_timeout (of which unsound-detected=$n_unsound: rejected the vuln/fixed pair but accepted a known-bad must-reject/ mutant, see FEL-64)"

if [ "$n_detected" -eq "$n_total" ] && [ "$n_total" -gt 0 ]; then
    echo "PASS: all $n_total corpus entries detected"
else
    echo "FAIL: $((n_total - n_detected))/$n_total corpus entries not detected (see table above) -- expected while the verifier lacks integer-overflow/pointer-arithmetic tracking (FEL-42..48); this script is a scoreboard, not a gate, and always exits 0"
fi

if [ "$n_unsound" -gt 0 ]; then
    echo "NOTE: $n_unsound entr$([ "$n_unsound" -eq 1 ] && echo y || echo ies) would have scored 'detected' on the vuln/fixed pair alone but failed a must-reject/ mutant -- see FEL-64. Reported as false-positive above, which is the honest, conservative call."
fi

exit 0
