#!/usr/bin/env python3
"""
scripts/generated_fuzz.py — Generated-program differential fuzzer (FEL-69,
item 2: "a small generator producing programs with arrays, loops, integer
arithmetic and heap allocation").

Unlike scripts/mutation_fuzz.py (which perturbs the EXISTING CVE corpus),
this generates fresh, small, parameterized C programs from a fixed set of
templates covering the array/loop/heap-allocation shapes real C libraries
use constantly (and the shape FEL-76 found unsound: a fixed-capacity
buffer written in a loop bounded by an ordinary, unbounded parameter).
Each template is instantiated many times with randomized buffer sizes,
loop bounds, and overflow margins, so "safe" and "unsafe" instances of
the same shape are both exercised.

Differential oracle, same as scripts/mutation_fuzz.py: `cc
-fsanitize=address -fsanitize=undefined` is ground truth, `ccc
--report=json` (verify-only) is the candidate. A generated program the
sanitizer flags as broken but `ccc` still ACCEPTS is a soundness bug —
reported loudly (this script does not know which corpus entry, if any, a
finding belongs to, so it cannot auto-file into a specific must-reject/
directory the way the mutation fuzzer does; it writes the failing
source to a local scratch file instead and prints the path).

FEL-69 item 3 ("emitter differential ... extends SignednessTest to
random programs, this is how the FEL-50 class of bugs is found
automatically"): for every instance in the well-defined-behavior "ok"
bucket (ccc accepts it AND the sanitizer run completed without a
crash — i.e. a program where comparing exact runtime behavior is
actually meaningful, unlike an "unsound"/overflow instance whose
behavior is UB and where CCC's and cc's outputs are both equally
"correct" nonsense), this ALSO compiles the same source with `ccc
... -o` (the real emitter, not just the verifier) and runs the
resulting binary, comparing its exit code against the already-executed
sanitizer binary's exit code. A mismatch means CCC's emitter computed
a different answer than a real C compiler for an accepted, well-defined
program — a correctness bug, not a soundness one, but exactly the
class FEL-50 (signed sub-word loads always zero-extended) was in
before it was found by hand.

Run with a fixed instance count (default) or `--duration-secs N` for a
sustained run (FEL-69's own design calls for a nightly multi-hour run
and an eventual 24h clean run — this flag is what makes that possible;
reaching an actual "24h clean" claim needs that duration to actually
elapse without a finding, which is a property of repeated runs over
real time, not a single invocation).
"""
import argparse
import random
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CCC_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "ccc"
TIMEOUT_SECS = 10


def run(cmd, timeout=TIMEOUT_SECS):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None


def is_sanitizer_crash(proc) -> bool:
    if proc is None:
        return False
    err = proc.stderr or ""
    return (
        "ERROR: AddressSanitizer" in err
        or "ERROR: UndefinedBehaviorSanitizer" in err
        or "runtime error:" in err
    )


def ccc_accepts(src_path: Path) -> bool:
    """True iff ccc --report=json says summary.safe (parse errors, or a
    missing/unparseable report, count as NOT accepted -- conservative:
    a template bug producing invalid C must never look like a soundness
    finding)."""
    proc = run([str(CCC_BIN), "--report=json", str(src_path)])
    if proc is None or proc.returncode not in (0, 1):
        return False
    return '"safe":true' in (proc.stdout or "")


# ── Templates ────────────────────────────────────────────────────────
# Each returns (source, description, expect_unsafe: bool | None).
# expect_unsafe is the GENERATOR's own intent, used only for the
# "ok"/"caught" bucketing labels in the summary -- the sanitizer's
# actual verdict is always what decides "crashed" for the oracle.

def tmpl_local_array(rng: random.Random):
    size = rng.randint(4, 64)
    overflow = rng.choice([0, 0, 0, rng.randint(1, 8)])  # mostly safe, sometimes not
    bound = size + overflow
    src = f"""
void fill(int arr[{size}], int n) {{
  int i;
  for (i = 0; i < n; i = i + 1) {{
    arr[i] = i;
  }}
}}
int main() {{
  int arr[{size}];
  fill(arr, {bound});
  return arr[0];
}}
"""
    return src, f"local_array(size={size},bound={bound})", overflow > 0


def tmpl_heap_array(rng: random.Random):
    size = rng.randint(4, 64)
    overflow = rng.choice([0, 0, 0, rng.randint(1, 8)])
    bound = size + overflow
    src = f"""
typedef unsigned long size_t;
void *malloc(size_t sz);
void fill(int *arr, int n) {{
  int i;
  for (i = 0; i < n; i = i + 1) {{
    arr[i] = i;
  }}
}}
int main() {{
  int *arr = malloc({size} * sizeof(int));
  if (!arr) {{ return -1; }}
  fill(arr, {bound});
  return arr[0];
}}
"""
    return src, f"heap_array(size={size},bound={bound})", overflow > 0


def tmpl_struct_field_array(rng: random.Random):
    size = rng.randint(4, 64)
    overflow = rng.choice([0, 0, 0, rng.randint(1, 8)])
    bound = size + overflow
    src = f"""
struct S {{ int arr[{size}]; int tag; }};
void fill(struct S *s, int n) {{
  int i;
  for (i = 0; i < n; i = i + 1) {{
    s->arr[i] = i;
  }}
}}
int main() {{
  struct S s;
  s.tag = 0;
  fill(&s, {bound});
  return s.arr[0];
}}
"""
    return src, f"struct_field_array(size={size},bound={bound})", overflow > 0


def tmpl_copy_loop(rng: random.Random):
    dst_size = rng.randint(4, 64)
    src_size = rng.randint(4, 64)
    overflow = rng.choice([0, 0, 0, rng.randint(1, 8)])
    count = min(dst_size, src_size) + overflow
    src = f"""
typedef unsigned long size_t;
void *malloc(size_t sz);
void copy_n(int *dst, int *src, int n) {{
  int i;
  for (i = 0; i < n; i = i + 1) {{
    dst[i] = src[i];
  }}
}}
int main() {{
  int *dst = malloc({dst_size} * sizeof(int));
  int *src = malloc({src_size} * sizeof(int));
  if (!dst || !src) {{ return -1; }}
  int i;
  for (i = 0; i < {src_size}; i = i + 1) {{ src[i] = i; }}
  copy_n(dst, src, {count});
  return dst[0];
}}
"""
    overflows_dst = count > dst_size
    overflows_src = count > src_size
    return (
        src,
        f"copy_loop(dst={dst_size},src={src_size},count={count})",
        overflows_dst or overflows_src,
    )


TEMPLATES = [tmpl_local_array, tmpl_heap_array, tmpl_struct_field_array, tmpl_copy_loop]


def emitter_diff(src_path: Path, tmp_dir: Path, idx: int, ref_exit: int):
    """FEL-69 item 3: compile the same (already-accepted, well-defined)
    source with ccc's real emitter (not just --report=json) and compare
    its exit code against `ref_exit` (the sanitizer binary's own exit
    code for this instance, already known not to have crashed). Returns
    (verdict, detail) where verdict is "match", "mismatch", or
    "ccc_compile_failed" (ccc's CLI refused to compile something its own
    --report=json just called safe -- a gate inconsistency, not an
    emitter bug, but worth surfacing separately rather than silently
    treating as a match)."""
    ccc_bin = tmp_dir / f"gen_{idx}_ccc_bin"
    compile_proc = run([str(CCC_BIN), str(src_path), "-o", str(ccc_bin)])
    if compile_proc is None or compile_proc.returncode != 0 or not ccc_bin.exists():
        detail = (compile_proc.stderr if compile_proc else "timeout") or ""
        return "ccc_compile_failed", detail.strip()[:200]
    run_proc = run([str(ccc_bin)])
    if run_proc is None:
        return "ccc_compile_failed", "ccc-emitted binary timed out"
    ccc_exit = run_proc.returncode
    if ccc_exit == ref_exit:
        return "match", None
    return "mismatch", f"cc exit={ref_exit} ccc exit={ccc_exit}"


def run_one(rng: random.Random, tmp_dir: Path, idx: int):
    template = rng.choice(TEMPLATES)
    src, desc, expect_unsafe = template(rng)
    src_path = tmp_dir / f"gen_{idx}.c"
    bin_path = tmp_dir / f"gen_{idx}_bin"
    src_path.write_text(src)

    compile_proc = run(
        ["cc", "-fsanitize=address", "-fsanitize=undefined", "-g",
         "-o", str(bin_path), str(src_path)]
    )
    if compile_proc is None or compile_proc.returncode != 0:
        return "inconclusive", desc, expect_unsafe, None

    run_proc = run([str(bin_path)])
    crashed = is_sanitizer_crash(run_proc)
    accepted = ccc_accepts(src_path)

    if crashed and accepted:
        return "unsound", desc, expect_unsafe, src
    elif crashed and not accepted:
        return "caught", desc, expect_unsafe, None
    elif not crashed and not accepted:
        return "fp_candidate", desc, expect_unsafe, None
    else:
        # "ok" bucket: accepted, well-defined behavior -- the only bucket
        # where an emitter differential is actually meaningful.
        ediff_verdict, ediff_detail = emitter_diff(src_path, tmp_dir, idx, run_proc.returncode)
        if ediff_verdict == "mismatch":
            return "emitter_mismatch", f"{desc} ({ediff_detail})", expect_unsafe, src
        elif ediff_verdict == "ccc_compile_failed":
            return "emitter_inconsistent", f"{desc} ({ediff_detail})", expect_unsafe, src
        return "ok", desc, expect_unsafe, None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--iterations", type=int, default=200,
                     help="number of generated programs (default 200)")
    ap.add_argument("--duration-secs", type=int, default=None,
                     help="run for this many seconds instead of a fixed iteration count")
    ap.add_argument("--seed", type=int, default=None, help="RNG seed for reproducibility")
    args = ap.parse_args()

    if not CCC_BIN.exists():
        print(f"error: {CCC_BIN} not found. Build it first: lake build ccc", file=sys.stderr)
        return 0

    seed = args.seed if args.seed is not None else random.randrange(2**32)
    rng = random.Random(seed)
    print("GENERATED-PROGRAM FUZZER (FEL-69, items 2+3)")
    print(f"seed={seed}" + (f" duration={args.duration_secs}s" if args.duration_secs else f" iterations={args.iterations}"))
    print("=" * 78)

    counts = {"ok": 0, "caught": 0, "fp_candidate": 0, "unsound": 0, "inconclusive": 0,
              "emitter_mismatch": 0, "emitter_inconsistent": 0}
    unsound_findings = []
    emitter_findings = []
    start = time.time()
    i = 0
    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        while True:
            if args.duration_secs is not None:
                if time.time() - start >= args.duration_secs:
                    break
            else:
                if i >= args.iterations:
                    break
            verdict, desc, expect_unsafe, src = run_one(rng, tdp, i)
            counts[verdict] += 1
            if verdict == "unsound":
                # Written outside the repo (a fresh finding, not yet triaged
                # into a specific corpus entry's must-reject/ directory —
                # unlike scripts/mutation_fuzz.py, this generator has no
                # single existing entry to file into) so a run never risks
                # leaving stray files for a later `git add -A` to pick up.
                out_dir = Path(tempfile.gettempdir()) / "ccc_generated_fuzz_findings"
                out_dir.mkdir(exist_ok=True)
                out_path = out_dir / f"finding_{i}.c"
                out_path.write_text(src)
                unsound_findings.append((desc, out_path))
            elif verdict in ("emitter_mismatch", "emitter_inconsistent"):
                out_dir = Path(tempfile.gettempdir()) / "ccc_generated_fuzz_findings"
                out_dir.mkdir(exist_ok=True)
                out_path = out_dir / f"emitter_finding_{i}.c"
                out_path.write_text(src)
                emitter_findings.append((verdict, desc, out_path))
            i += 1

    total = sum(counts.values())
    print(f"ran {total} generated programs in {time.time() - start:.1f}s")
    print(f"ok={counts['ok']} caught={counts['caught']} fp_candidate={counts['fp_candidate']} "
          f"inconclusive={counts['inconclusive']} UNSOUND={counts['unsound']} "
          f"EMITTER_MISMATCH={counts['emitter_mismatch']} emitter_inconsistent={counts['emitter_inconsistent']}")
    print("=" * 78)
    if unsound_findings:
        for desc, path in unsound_findings:
            print(f"::warning::generated_fuzz.py found a soundness bug: {desc} -- saved to {path}")
        print(f"SOUNDNESS BUGS FOUND: {len(unsound_findings)} — see file paths listed above.")
    else:
        print("No new soundness bugs found this run.")
    if emitter_findings:
        for verdict, desc, path in emitter_findings:
            print(f"::warning::generated_fuzz.py found an emitter differential ({verdict}): {desc} -- saved to {path}")
        print(f"EMITTER DIFFERENTIALS FOUND: {len(emitter_findings)} — see file paths listed above.")
    else:
        print("No emitter differentials found this run.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
