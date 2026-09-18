# CVE regression corpus — baseline results

## 2026-09-19 (second update) — after FEL-59 (real --harden), the div-by-zero
## check, and the typedef-struct-field parser fix

**Against commit:** `13649a043f75aa1a8ff6b9ac4a2df4347e24217b` (branch
`epic/libheif-class-detection`).

```
ENTRY                              VULN        FIXED       CLASS            NOTES
--------------------------------------------------------------------------------------------
libheif-overlay-85e21ad            rejected    rejected    false-positive   fixed.c flagged at line 130
libpng-cve-2015-8126               rejected    rejected    false-positive   fixed.c flagged at line 52
libpng-cve-2018-13785              rejected    rejected    false-positive   fixed.c flagged at line 26
libwebp-cve-2023-4863              accepted    accepted    missed           bug not flagged
--------------------------------------------------------------------------------------------

SUMMARY: 4 entries -- detected=0 missed=1 false-positive=3 parse-failed=0 timeout=0
```

Still 0/4 strictly *detected*. What changed since the update immediately
below this one:

- **`libpng-cve-2018-13785` moved from `missed` to `false-positive`.** A
  new, sound division-by-zero check (a tractable, self-contained slice of
  FEL-56 — this entry's bug is pure integer arithmetic, no pointer or
  interprocedural complexity at all) now flags `vulnerable.c`'s
  `row_factor` division directly — the actual CVE. `fixed.c` is also
  flagged: its `row_factor` is widened to `size_t` and provably nonzero
  in reality (`product + 1 + ...`, and 1 makes any non-negative sum
  positive), but proving that needs "sum of non-negative terms plus a
  positive literal is positive" reasoning this pass doesn't implement, so
  it isn't recognized as safe yet. Real, verified progress (the
  previously-invisible bug is now visible) short of the full "detected"
  bar.
- **`libwebp-cve-2023-4863` moved from `parse-failed` to `missed`.** Fixed
  a real, independently-significant, previously-unknown parser bug found
  while testing this corpus entry: `typedef struct HuffmanCode { ... }
  HuffmanCode;` (a struct typedef'd under its own tag name — extremely
  common in real C) had its field list silently discarded by the parser,
  so ANY value of the type failed at code emission with "unknown field"
  the instant a field was touched — nothing to do with this CVE's actual
  bug. Fixed at the parser level (now parses fields exactly like a bare
  `struct NAME {...};` already did). The file now parses, verifies, and
  compiles cleanly for both versions — but the actual OOB write (a
  computed index into a `HuffmanCode` array) isn't caught by the verifier
  yet, so this is a `missed`, not yet a `detected`.
- **`libheif-overlay-85e21ad` and `libpng-cve-2015-8126` unchanged**
  (still `false-positive`, same underlying reasons as the update below).

Also landed alongside this measurement, not visible in the scoreboard
table itself but directly relevant to the epic's Definition of Done:
**`ccc --harden` now does real, verified runtime instrumentation**, not
just a plumbed-through escape hatch. Every array subscript through a
pointer-typed base gets a runtime bounds check (a new allocation-size
registry in `runtime/ccc_runtime.c` + `ccc_check_index`, inserted by the
emitter only when `--harden` is passed). Confirmed against the actual DoD
acceptance test: `ccc --harden test/corpus/libheif-overlay-85e21ad/vulnerable.c`
aborts at runtime with the real bounds violation (reading past the
overlay plane, exactly the CVE's overflow) on the corpus's trigger input;
the `fixed.c` version runs clean under the same `--harden` build. See
`test/HardenTest.lean` (5/5) and Linear FEL-59 for the full story,
including what building this uncovered: a real, previously-unknown,
independently-significant emitter bug (`resolveType` not stripping
`const`/`volatile`/`restrict` before checking for a typedef, silently
corrupting the indexing stride of every `const uint8_t *`-shaped access —
found because `--harden`'s runtime check fired on a memory-safe access
in `fixed.c` with a visibly wrong `elem_size`).

## 2026-09-19 (first update) — measured after the FEL-40..49 verifier fixes

**Against commit:** `a1e70438e097713bfed3a8db998d86478ec0866f` (branch
`epic/libheif-class-detection`, after the force-emit removal, range/bounds
domain, struct-field pointer tracking, and malloc/calloc/realloc tracking
landed). The section below this one is the ORIGINAL baseline (measured
before those fixes, against `cf2f0a5`) — kept for comparison, since the
whole point of this corpus is to make exactly this kind of before/after
comparison possible.

```
ENTRY                              VULN          FIXED         CLASS            NOTES
------------------------------------------------------------------------------------------
libheif-overlay-85e21ad            rejected      rejected      false-positive   fixed.c flagged at line 130
libpng-cve-2015-8126               rejected      rejected      false-positive   fixed.c flagged at line 52
libpng-cve-2018-13785              accepted      accepted      missed           bug not flagged
libwebp-cve-2023-4863              parse-failed  parse-failed  parse-failed     -
------------------------------------------------------------------------------------------

SUMMARY: 4 entries -- detected=0 missed=1 false-positive=2 parse-failed=1 timeout=0
```

Still 0/4 *detected* by the scoreboard's strict definition (reject the
vulnerable version AND accept the fixed one) — that's expected: the
CVE-relevant bugs here are integer-overflow and pointer-arithmetic shaped,
and the FEL-56/57/58 work (relational/overflow-aware ranges, a real
`(base,offset)` pointer model, interprocedural summaries) hasn't landed
yet. But three things changed, and they're worth spelling out because
"still 0/4" undersells what actually moved:

- **`libheif-overlay-85e21ad` moved from `missed` to `false-positive`.**
  The verifier now genuinely rejects BOTH files — but for the WRONG
  reason: it flags `out_p[i] = 0;`/`in_p[i] = 1;` (buffer-init loops) as a
  possible null-pointer dereference, because FEL-47 now correctly tracks
  `malloc(out_w*out_h)` (a non-constant size) as a `nullable` pointer that
  needs a null check — and this synthetic test harness's `main()`, like a
  lot of throwaway test code, never bothers null-checking its `malloc`
  calls. That's a *real* finding (these mallocs genuinely aren't
  null-checked), just not *the* CVE-relevant one (the overlay clipping
  arithmetic), and it fires identically on both files so the scoreboard
  can't credit it as a detection. This is a legitimate before/after
  improvement in the verifier (FEL-47 working as intended) that the
  scoreboard's coarse detected/missed/false-positive taxonomy doesn't have
  a label for; a future refinement could distinguish "rejected, but for a
  provably different reason on each file" from "rejected identically".
- **`libpng-cve-2015-8126` stayed `false-positive`** (same identical
  violation on both — `fixed.c` flagged at line 52 now instead of line 33,
  because the range/bounds rewrite changed which check fires first, not
  because the underlying gap closed).
- **`libwebp-cve-2023-4863` moved from `false-positive` to `parse-failed`.**
  This is NOT a parser regression from this work — it surfaces a
  pre-existing, unrelated front-end gap: `typedef struct HuffmanCode {
  ... } HuffmanCode;` (a struct typedef'd under its own tag name) is
  parsed by skipping the field list entirely (`CCC/Parse/Parse.lean`'s
  `parseTypedefDecl` only records the tag as an opaque `struct_` type for
  this shape; a bare `struct HuffmanCode { ... };` without the typedef
  wrapper does NOT have this problem). Previously the file was rejected by
  the verifier before ever reaching code generation, so the emitter's
  resulting "unknown field 'bits'" error was silently swallowed by the
  old force-emit fallback (`Pipeline.lean`'s pre-FEL-40 code discarded a
  *second* error from the force-emit attempt and kept showing the
  verifier's original violation text). FEL-47's more accurate tracking
  means THIS file's actual bug is no longer flagged by the verifier at
  all (a miss, same underlying cause as the libheif entry above — the
  real overlow bug is pointer-arithmetic shaped, FEL-44/57), so it now
  proceeds to code generation for real and the pre-existing struct-field
  gap becomes visible instead of masked. Tracked as a front-end
  completeness gap under FEL-55.

## Original baseline (measured 2026-09-19, before the FEL-40..49 fixes)

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
