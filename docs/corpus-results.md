# CVE regression corpus — baseline results

**Measured:** 2026-09-19
**Against commit:** `cf2f0a503c0269d47bc6467e088dd8681570944c` (branch
`epic/libheif-class-detection`, the tip before this corpus was added)
**Command:** `lake build ccc && bash scripts/corpus.sh` — run to completion,
output captured verbatim below.

This is a snapshot, not a target: it records what CCC's verifier actually
does today against a small set of real-world CVE shapes, so future changes
to the verifier (FEL-42/43/44/46/47/48/56/57/58 and friends) can be
measured against it instead of against CCC's own self-authored demos. See
`test/corpus/*/README.md` for each entry's CVE/commit background and
`scripts/corpus.sh` for how the scoreboard works; FEL-54/FEL-61 in Linear
for the full context.

## Result

```
ENTRY                              VULN        FIXED       CLASS            NOTES
--------------------------------------------------------------------------------------------
libheif-overlay-85e21ad            accepted    accepted    missed           bug not flagged
libpng-cve-2015-8126               rejected    rejected    false-positive   fixed.c flagged at line 33
libpng-cve-2018-13785              accepted    accepted    missed           bug not flagged
libwebp-cve-2023-4863              rejected    rejected    false-positive   fixed.c flagged at line 78
--------------------------------------------------------------------------------------------

SUMMARY: 4 entries -- detected=0 missed=2 false-positive=2 parse-failed=0 timeout=0
FAIL: 4/4 corpus entries not detected (see table above) -- expected while the verifier lacks integer-overflow/pointer-arithmetic tracking (FEL-42..48); this script is a scoreboard, not a gate, and always exits 0
```

**0 of 4 entries detected.** This is the expected baseline, not a bug in
the corpus: as of this snapshot the verifier has no integer-overflow
tracking, no negative-index detection, and treats most pointer arithmetic
as either fully unchecked (silently accepted) or flagged in a blanket,
input-independent way that can't distinguish a fixed program from a
vulnerable one. Every `vulnerable.c` in this corpus was independently
confirmed (outside `ccc`, with plain `cc`/`clang`) to actually misbehave
under the trigger in its `trigger.txt`:

- `libheif-overlay-85e21ad`: `cc -fsanitize=address -g vulnerable.c -o v
  && ./v` -> AddressSanitizer heap-buffer-overflow (READ), 0 bytes after
  the overlay-plane allocation; `fixed.c` exits 0 clean.
- `libwebp-cve-2023-4863`: same ASan recipe -> heap-buffer-overflow
  (WRITE) in the second-level Huffman table write; `fixed.c` exits 0
  clean.
- `libpng-cve-2015-8126`: same ASan recipe -> heap-buffer-overflow
  (WRITE) into the fixed 256-entry palette array; `fixed.c` exits 0
  clean.
- `libpng-cve-2018-13785`: the `row_factor` computation wraps to exactly
  0 for the documented trigger (confirmed by direct calculation), which
  is a genuine SIGFPE divide-by-zero on the x86 hardware libpng actually
  ships on; on this (ARM64) measurement machine integer division by zero
  does not trap (`UDIV` returns 0 instead of faulting), so the crash
  itself isn't reproducible here, but the wrap -- the actual defect -- is
  confirmed. `fixed.c`'s `row_factor` for the same inputs is a nonzero
  2^32, so the division stays safe on any architecture.

So the "0 detected" result is a real, if disappointing, finding about the
verifier, not an artifact of a bad corpus.

## Breakdown by outcome

- **missed (2/4): `libheif-overlay-85e21ad`, `libpng-cve-2018-13785`.**
  `ccc` reports "0 memory safety violations" for both the vulnerable and
  fixed versions. For the libheif entry, this is exactly the failure mode
  the epic (FEL-54) predicted: the bug lives in pointer arithmetic
  (computed array-index writes into a plane buffer) that isn't a bare
  local-variable dereference, which the verifier currently treats as
  unchecked/accepted (FEL-44). For the libpng row_factor entry, the bug
  is pure integer arithmetic (a 32-bit multiply/add that wraps to 0) with
  no pointer access at all near the wrap — there is currently no
  integer-overflow domain to catch it (FEL-46).

- **false-positive (2/4): `libpng-cve-2015-8126`, `libwebp-cve-2023-4863`.**
  `ccc` rejects *both* the vulnerable and the fixed version, with the
  identical violation ("cannot verify dynamic index is within bounds", or
  an unresolvable pointer-arithmetic write inside a helper function) on
  both. This is a real positive signal that CCC's bounds checker does
  look at some of these array/pointer accesses — but because it has no
  relational reasoning between a runtime-computed count and a fixed-size
  buffer, and no interprocedural facts about a clamp applied a few lines
  (or one call frame) earlier (FEL-47/FEL-48), it can't distinguish the
  version with the missing clamp from the version with the clamp added.
  Both get flagged identically, so as far as a scoreboard verdict is
  concerned this measures as a false positive on the fixed program, even
  though the underlying instinct ("this access needs a bounds proof") is
  correct.

- **detected (0/4).** None yet. This is the number this corpus exists to
  move.

- **parse-failed / timeout (0/4 each).** All four entries parse and
  compile within the front-end's current (self-contained, `#include`-stub)
  C subset, and all four verify well within the 20s-per-file budget
  (all 8 files together take a few seconds).

## Re-running

```bash
lake build ccc
bash scripts/corpus.sh
```

`scripts/corpus.sh` always exits 0 (it is a measurement script, not a CI
gate) and prints a `PASS`/`FAIL`-style summary line in addition to the
table above. Note: the script uses a portable, dependency-free polling
loop for its per-file timeout rather than GNU coreutils `timeout`, which
is not installed by default on macOS (confirmed absent — `which timeout`
fails — on the machine this baseline was measured on); an earlier draft
that shelled out to `timeout` silently misclassified every entry as
"accepted" here, because the shell's own "command not found" text didn't
match any of the script's verdict patterns and fell through to the
default case. If you see every entry come back "accepted" on a fresh
machine, check that first.
