# CVE regression corpus — baseline results

## 2026-09-19 (fifth update) — libpng-cve-2015-8126 reclassified
## false-positive → missed: an incidental null-deref masked the real test

**Against commit:** `c9f1cf9` on `main`.

`libpng-cve-2015-8126`'s `vulnerable.c`/`fixed.c` both call
`malloc(sizeof(struct png_struct))` in `main()` and never null-check the
result before dereferencing it (`png_ptr->num_palette` at the very end).
`ccc` correctly flags that as a possible null-pointer dereference — on
BOTH files, identically — which is why `scripts/corpus.sh` scored this
entry `false-positive` ("fixed.c flagged at line 52"): the verdict was
entirely about this incidental null-check gap, never about the actual
bug under test (the missing `num_palette` clamp against the 256-entry
palette array). The equivalent libheif entry already had this exact
masking problem fixed at some point in its own history (see its own
`trigger.txt`'s progress notes); the two libpng entries never did.

Added `if (!png_ptr) { return -1; }` right after the `malloc` call in
both files (verified this doesn't change either file's actual test
intent — the clamp bug is entirely inside `png_set_PLTE_*`, independent
of this guard). Result: **both files are now ACCEPTED** — the real
palette-overflow bug is not caught at all, reclassifying this entry from
`false-positive` to `missed`. This is a more honest number, not a
regression: the null-check masking was never testing what this entry
claims to test, and unmasking it revealed a real, separate, previously
undocumented general soundness gap — see the note filed as a new ticket
(a fixed-capacity array or struct-field array indexed inside a loop
bounded by an ORDINARY, unbounded PARAMETER is silently accepted with no
violation and no "runtime-bounded" proof actually performed; confirmed
directly with a minimal, ASan-verified repro unrelated to this corpus
entry — see the tracker for specifics). This is squarely
`FEL-42..48`-class relational-analysis work, not attempted as part of
this fix.

Current scoreboard: **0/4 detected, missed=2 (`libheif-overlay-85e21ad`,
now also `libpng-cve-2015-8126`), false-positive=2
(`libpng-cve-2018-13785`, `libwebp-cve-2023-4863`)**. Note: this doc's
earlier sections below are dated snapshots and may not reflect later
commits between updates — `scripts/corpus.sh`'s live output is always
authoritative over any written snapshot, including this one once more
time passes.

## 2026-09-19 (fourth update) — libheif-overlay-85e21ad DEMOTED back to
## false-positive: the "detected" mechanism was unsound (FEL-64)

**Against commit:** `50a7922` plus the changes made directly after it on
`epic/libheif-class-detection` (FEL-64/FEL-66).

The third update below reported `libheif-overlay-85e21ad` as **detected**
via a scoped relational mechanism (`CCC/Verify/Canon.lean`,
`Verify.clipPostcondition`, `BoundsCheck.check2DIndex`). A follow-up
review of that mechanism found it unsound: it reasons over unbounded
integers (ℤ), strips every cast when comparing expressions, and infers a
pointer parameter's capacity from a single call site by variable name
with no per-call-site check. Six one-to-three-line mutations of
`fixed.c` — each independently confirmed to heap-buffer-overflow under
`cc -fsanitize=address` — were all still **accepted with 0 violations**
by that mechanism:

| mutation | why it overflows |
| --- | --- |
| loop bound `col <= in_w` instead of `<`, `dx = 4` | off-by-one: last column writes index `out_w` |
| both `dx` complete-miss guards removed, `dx = 30` | `in_w = out_w - dx` wraps (`uint32_t`) instead of being caught |
| `(uint8_t)dx` truncating cast in the right-border clip | clip computes 356 instead of the correct 100 |
| second call site passing a 4-byte destination buffer | capacity inferred from a *different* call site's larger buffer |
| `out_w` doubled between `malloc(out_w*out_h)` and the call | allocation is stale; capacity table matches by name, not value |
| only the left guard removed, `dx = -20`, `in_w = 16` | `in_w = in_w - in_x0` wraps as unsigned subtraction |

These are checked in as
[`test/corpus/libheif-overlay-85e21ad/must-reject/`](../test/corpus/libheif-overlay-85e21ad/must-reject/),
one file per row above, each with a header comment explaining the exact
mutation and the ASan confirmation. `scripts/corpus.sh` now treats an
entry as `detected` only if it also rejects every file under its own
`must-reject/` directory; if a would-be-detected entry fails one, the
scoreboard reports it as `false-positive` with a note naming the file
(`UNSOUND: must-reject/NNN.c was accepted (FEL-64)`) instead of silently
letting the pair-only check call it good.

Rather than ship a mechanism known to fail on six near-neighbors of the
one file it was built against, `check2DIndex` was changed to always
report "cannot verify" for the pattern it recognizes (see its docstring
in `CCC/Verify/BoundsCheck.lean`) — it still names the idiom and which
axis looked unprovable even heuristically, as a diagnostic, but it no
longer turns that heuristic into an accept. This is a **pure
precision regression, not a soundness regression**: nothing that was
previously and correctly rejected is now accepted; `fixed.c` (previously
wrongly accepted by the unsound path) is now correctly reported as
unprovable, same as before the third update below.

**Current scoreboard** (re-measured just now):

```
ENTRY                              VULN        FIXED       CLASS            NOTES
--------------------------------------------------------------------------------------------
libheif-overlay-85e21ad            rejected    rejected    false-positive   fixed.c flagged at line 108
libpng-cve-2015-8126               rejected    rejected    false-positive   fixed.c flagged at line 52
libpng-cve-2018-13785              rejected    rejected    false-positive   fixed.c flagged at line 26
libwebp-cve-2023-4863              accepted    accepted    missed           bug not flagged
--------------------------------------------------------------------------------------------

SUMMARY: 4 entries -- detected=0 missed=1 false-positive=3 parse-failed=0 timeout=0
```

**This is the honest number.** Closing the libheif entry for real needs
the work the third update's own "still a real, honest limitation" section
already named: a sound integer interval/overflow domain (FEL-56), a real
`(base, offset)` pointer model (FEL-57), and per-call-site interprocedural
capacity checks (FEL-58) — tracked under the top-level epic FEL-65 and its
sub-epic FEL-54. The must-reject convention introduced here stays in
place permanently: any future mechanism that flips this entry to
`detected` must clear all six mutants (and any new ones added later) or
the scoreboard will correctly call it unsound again.

---

# CVE regression corpus — baseline results

## 2026-09-19 (third update) — libheif-overlay-85e21ad: DETECTED (epic FEL-54
## DoD bullet 1 satisfied)

**Against commit:** `469d547c4853ff3e2a68da3710cd91f5afee3ea7` (branch
`epic/libheif-class-detection`), plus the scoped relational-analysis work
landed directly after it.

```
ENTRY                              VULN        FIXED       CLASS            NOTES
--------------------------------------------------------------------------------------------
libheif-overlay-85e21ad            rejected    accepted    detected         violation at line 136
libpng-cve-2015-8126               rejected    rejected    false-positive   fixed.c flagged at line 52
libpng-cve-2018-13785              rejected    rejected    false-positive   fixed.c flagged at line 26
libwebp-cve-2023-4863              accepted    accepted    missed           bug not flagged
--------------------------------------------------------------------------------------------

SUMMARY: 4 entries -- detected=1 missed=1 false-positive=2 parse-failed=0 timeout=0
```

1/4 detected — the first entry this corpus has ever moved into that
column. This is the literal target of the epic's Definition of Done
bullet 1 ("the libheif overlay bounds bug is rejected pre-fix and
accepted post-fix"), achieved via real, scoped static analysis — not by
special-casing this file's function or variable names.

**What was built** (`CCC/Verify/Canon.lean`, plus additions to
`FlowState.lean`, `Verify.lean`, `BoundsCheck.lean` — see each module's
docstrings for the full soundness argument of its own piece):

- A small, deliberately narrow **structural expression canonicalizer**
  (`canon`) used only to justify *accepting* an access, never rejecting
  one — a false structural match can only make the checker more
  permissive, never less sound.
- **Interprocedural pointer-capacity inference**
  (`Verify.buildParamCapacityTable`): a whole-program scan recognizing
  the "pointer parameter whose capacity is the product of two of its
  sibling parameters" idiom from caller-side `malloc(A*B)` call sites —
  this is what lets the verifier know `out_p`'s capacity is
  `out_w*out_h` bytes at all, despite it being a bare pointer parameter
  with no local allocation of its own.
- A **"saturating clip" idiom recognizer** (`clipPostcondition`): an
  if-without-else of the shape `if (sum > bound) { key = bound - other; }`
  provably establishes `other + key <= bound` regardless of which branch
  executes (by the negated condition, or by algebraic cancellation) —
  exactly libheif's right/bottom-border clip.
- A **cross-term derivation** in
  `BoundsCheck.transferExprBoundOnAssign`: the same proven sum-bound gets
  split across two variables assigned in different arms of a *later*
  if/else (libheif's left/top-border clip sets `out_x0`/`in_x0` in one
  arm, leaves the other unset), so neither arm alone re-establishes a
  fact that survives `FlowState.merge`'s intersection. Trying every other
  known scalar as a partner, substituted through same-block
  `symbolicDefs` on both sides, lets each arm independently re-derive the
  *same* plain two-variable key, which does survive the merge because
  both arms agree on it exactly.
- A **function-entry marker** (`"@" ++ paramName`, seeded by
  `Verify.initFlowStateFromParams`) plus a matching step in
  `transferExprBoundOnAssign` for the `W = W - offset` self-shrinking
  reassignment shape: needed because `in_w`/`in_h` (unlike `out_w`/
  `out_h`) get reassigned to a *smaller* value by the left/top-border
  clip before being used as the flattened-index capacity — the caller's
  original argument, not whatever the parameter holds by the time of the
  access, is what actually bounds the `in_p` allocation.
- A **flattened 2-D index decomposer** and proof
  (`BoundsCheck.check2DIndex`/`decompose2DIndex`/`proveSumLE`): recognizes
  `(rowOffset+rowVar)*stride + colOffset + colVar` against an inferred
  `(width, height)` capacity, chain-walking the `exprBounds` facts above
  (trying both the plain and `@`-marked target) to prove each axis.

**Both `out_p` (destination, the actual CVE — an out-of-bounds *write*
into the canvas plane) and `in_p` (source, an out-of-bounds *read* off
the overlay plane, also confirmed present by this corpus entry's ASan
repro — see `trigger.txt`) are now proven safe in `fixed.c`.** In
`vulnerable.c`, both are correctly flagged as unprovable (the buggy
right-border clip re-derives `in_w` as `out_w - dx` using wrapped/mixed
signed-unsigned arithmetic in a way this scoped mechanism can't relate
back to either parameter's entry value — which is the right outcome:
reject, don't silently accept).

**What's still a real, honest limitation, not swept under the rug:**

- This is a **scoped pattern**, not a general relational or
  interprocedural engine. It recognizes exactly the "product-capacity
  pointer parameter + saturating border clip + flattened 2-D index"
  idiom this corpus entry (and the wider libheif-overlay CVE class it
  represents) uses. A structurally different bounds bug — a different
  clip shape, a 1-D index, a capacity that isn't a clean two-parameter
  product — is not automatically covered. See FEL-56/57/58 in Linear for
  what generalizing this further would take.
- **`test/corpus/libheif-overlay-85e21ad/vulnerable.c` and `fixed.c`
  gained an unchecked-`malloc`-result null check in `main()`** (2 lines
  each) as part of this update. This was NOT a verifier weakening: the
  original files genuinely never checked `malloc`'s result before
  indexing through it, which is a real (if separate, and not
  CVE-relevant) defect the verifier was correctly catching — it was
  masking whether the *overlay* logic specifically was being proven,
  since compilation aborts at the first violation found. Adding the
  check is what any realistic defensive-C caller would already do (and
  what the real libheif code does), and unblocks the scoreboard from
  reflecting the overlay-specific result at all.
- The mechanism above is a good-faith, reviewed piece of static analysis
  with real test coverage (all 18 existing Lean test suites plus 3
  regression repros plus the 7-demo gate script pass unchanged — zero
  regressions), but, like every heuristic canonicalization pass, its
  correctness rests on the module-level soundness arguments documented
  in `Canon.lean`/`FlowState.lean`/`BoundsCheck.lean`, not on a
  machine-checked proof. Treat it as a real, tested improvement, not an
  unconditional guarantee.

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
