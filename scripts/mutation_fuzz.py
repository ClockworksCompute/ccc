#!/usr/bin/env python3
"""
scripts/mutation_fuzz.py — Mutation-fuzzing harness over the CVE corpus
(FEL-69, first mutation class).

FEL-64 was found by HAND-mutating one corpus file six times; each mutation
was a 1-3 line edit and each one fooled the verifier. This script makes that
a machine's job: for every corpus entry's `fixed.c` (the demonstrably-safe,
post-fix version), it generates every single-comparison-operator-flip
mutant (`<` <-> `<=`, `>` <-> `>=`, one flip per mutant, everything else
unchanged) and runs a differential oracle on each:

  - ground truth: compile with `cc -fsanitize=address -fsanitize=undefined`
    and run it; a sanitizer report means the mutation reintroduced a real
    bug.
  - candidate: run `ccc` verify-only on the same mutant.

A mutant the sanitizer flags as broken but `ccc` still ACCEPTS (0 memory
safety violations) is a soundness bug — auto-filed into
`test/corpus/<entry>/must-reject/NNN_<description>.c` with a header
explaining the exact mutation, matching the convention `scripts/corpus.sh`
already checks (every entry marked "detected" must also reject everything
under its own `must-reject/`).

Only the comparison-operator-flip mutation class is implemented here — the
first of the seven-item catalogue in the FEL-69 ticket (flip <->, delete a
guard, narrow a cast, +-1/x2 a literal, swap statements, a second smaller
call site, reassign a size variable). The others need real C-aware
transformations (balanced-brace guard deletion, tracking which literals are
size-related) that a token-regex mutator can't do safely — left as
follow-up work under the same ticket rather than attempted here at reduced
reliability.

This is a differential SCOREBOARD, like `scripts/corpus.sh` — it always
exits 0 (never fails CI on its own) and prints what it found; a genuine new
finding is filed to disk, and the run summary flags it loudly so a human
notices in review.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CORPUS_DIR = REPO_ROOT / "test" / "corpus"
CCC_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "ccc"
TIMEOUT_SECS = 15

# Matches (in priority order so <<, >>, -> never get misread as < or >):
# <=, >=, <<, >>, ->, then bare < or >.
TOKEN_RE = re.compile(r"<=|>=|<<|>>|->|<|>")

FLIP = {"<": "<=", "<=": "<", ">": ">=", ">=": ">"}


def gen_mutants(src: str):
    """Yield (mutated_source, description, line_no) for every single
    comparison-operator flip. Skips <<, >>, -> (not comparisons)."""
    for m in TOKEN_RE.finditer(src):
        tok = m.group(0)
        if tok not in FLIP:
            continue
        line_no = src.count("\n", 0, m.start()) + 1
        mutated = src[: m.start()] + FLIP[tok] + src[m.end() :]
        desc = f"line {line_no}: `{tok}` -> `{FLIP[tok]}`"
        yield mutated, desc, line_no


def run(cmd, cwd=None, timeout=TIMEOUT_SECS):
    try:
        return subprocess.run(
            cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return None


def is_sanitizer_crash(proc) -> bool:
    if proc is None:
        return False  # timeout: treat as inconclusive, not a crash
    err = proc.stderr or ""
    return (
        "ERROR: AddressSanitizer" in err
        or "ERROR: UndefinedBehaviorSanitizer" in err
        or "runtime error:" in err
        or "SUMMARY: " in err
        and "Sanitizer" in err
    )


def ccc_rejects(proc) -> bool:
    if proc is None:
        return False  # timeout: inconclusive, don't claim either verdict
    out = proc.stdout or ""
    return "memory safety violation" in out and "0 memory safety violations" not in out


def next_must_reject_index(must_reject_dir: Path) -> int:
    existing = list(must_reject_dir.glob("*.c")) if must_reject_dir.exists() else []
    nums = []
    for p in existing:
        m = re.match(r"(\d+)_", p.name)
        if m:
            nums.append(int(m.group(1)))
    return (max(nums) + 1) if nums else 1


def already_filed(must_reject_dir: Path, mutated: str) -> bool:
    if not must_reject_dir.exists():
        return False
    for p in must_reject_dir.glob("*.c"):
        text = p.read_text()
        body = text.split("*/\n", 1)[-1] if "*/\n" in text else text
        if body.strip() == mutated.strip():
            return True
    return False


def fuzz_entry(entry_dir: Path) -> dict:
    fixed_c = entry_dir / "fixed.c"
    src = fixed_c.read_text()
    counts = {"ok": 0, "caught": 0, "false_positive_candidate": 0, "unsound": 0, "inconclusive": 0}
    new_files = []

    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        for mutated, desc, _line_no in gen_mutants(src):
            mutant_c = tdp / "mutant.c"
            mutant_bin = tdp / "mutant_bin"
            mutant_c.write_text(mutated)

            compile_proc = run(
                ["cc", "-fsanitize=address", "-fsanitize=undefined", "-g",
                 "-o", str(mutant_bin), str(mutant_c)]
            )
            if compile_proc is None or compile_proc.returncode != 0:
                counts["inconclusive"] += 1
                continue
            run_proc = run([str(mutant_bin)])
            crashed = is_sanitizer_crash(run_proc)

            ccc_proc = run([str(CCC_BIN), str(mutant_c)])
            rejected = ccc_rejects(ccc_proc)
            if ccc_proc is None:
                counts["inconclusive"] += 1
                continue

            if crashed and not rejected:
                counts["unsound"] += 1
                mr_dir = entry_dir / "must-reject"
                mr_dir.mkdir(exist_ok=True)
                if already_filed(mr_dir, mutated):
                    continue
                idx = next_must_reject_index(mr_dir)
                slug = re.sub(r"[^a-z0-9]+", "_", desc.lower()).strip("_")[:50]
                out_path = mr_dir / f"{idx:02d}_autofuzz_{slug}.c"
                header = (
                    f"/*\n"
                    f" * {out_path.name} — auto-discovered by scripts/mutation_fuzz.py "
                    f"(FEL-69)\n"
                    f" *\n"
                    f" * Single mutation from {entry_dir.name}/fixed.c: {desc}\n"
                    f" *\n"
                    f" * Ground truth: cc -fsanitize=address -fsanitize=undefined "
                    f"reported a real\n"
                    f" * violation running this mutant (see the run output where this "
                    f"was found).\n"
                    f" * CCC must reject this file; if it doesn't, the entry's "
                    f"\"detected\" verdict\n"
                    f" * is unsound (see scripts/corpus.sh's must-reject/ convention).\n"
                    f" */\n"
                )
                out_path.write_text(header + mutated)
                new_files.append(out_path)
            elif crashed and rejected:
                counts["caught"] += 1
            elif not crashed and rejected:
                counts["false_positive_candidate"] += 1
            else:
                counts["ok"] += 1

    return {"counts": counts, "new_files": new_files}


def main() -> int:
    if not CCC_BIN.exists():
        print(f"error: {CCC_BIN} not found. Build it first: lake build ccc", file=sys.stderr)
        return 0

    entries = sorted(p for p in CORPUS_DIR.iterdir() if (p / "fixed.c").exists())
    if not entries:
        print("no corpus entries with fixed.c found.", file=sys.stderr)
        return 0

    print("MUTATION FUZZER — comparison-operator-flip class (FEL-69)")
    print("=" * 78)
    any_unsound = False
    for entry in entries:
        result = fuzz_entry(entry)
        c = result["counts"]
        total = sum(c.values())
        print(
            f"{entry.name:30s} mutants={total:3d} ok={c['ok']:3d} "
            f"caught={c['caught']:3d} fp-candidate={c['false_positive_candidate']:3d} "
            f"inconclusive={c['inconclusive']:3d} UNSOUND={c['unsound']:3d}"
        )
        for f in result["new_files"]:
            any_unsound = True
            print(f"  -> NEW must-reject file filed: {f.relative_to(REPO_ROOT)}")

    print("=" * 78)
    if any_unsound:
        print("SOUNDNESS BUGS FOUND — new must-reject/ files were filed above.")
        print("Re-run scripts/corpus.sh to confirm the affected entries now fail")
        print("their must-reject check (they should, until the verifier is fixed).")
        # GitHub Actions annotation: makes a new finding visible in the CI UI
        # without failing the build — matches scripts/corpus.sh's own
        # "measurement, not a gate" philosophy, but a genuinely NEW
        # soundness bug (as opposed to the corpus's existing known
        # missed/false-positive entries) is worth a human noticing directly.
        print("::warning::mutation_fuzz.py found a new soundness bug — see must-reject/ files added in this run")
    else:
        print("No new soundness bugs found by this mutation class this run.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
