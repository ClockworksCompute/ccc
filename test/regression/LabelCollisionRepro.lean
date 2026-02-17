/-
  test/regression/LabelCollisionRepro.lean
  CCC-BUG-001: Detects duplicate labels in emitted x86 assembly.
  Must FAIL before fix, PASS after fix.
-/
import CCC

def main : IO Unit := do
  let src := "
int max_val(int x, int y) {
    if (x > y) { return x; } else { return y; }
}

int clamp(int val, int lo, int hi) {
    if (val < lo) { return lo; }
    if (val > hi) { return hi; }
    return val;
}

int main() {
    int a = clamp(50, 0, 100);
    int b = clamp(200, 0, 100);
    int result = max_val(a, b);
    return result;
}
"
  let result := CCC.compile src "label_collision_repro.c"
  match result.assembly with
  | some asm =>
    let lines := asm.splitOn "\n"
    let labelLines := lines.filter (fun l =>
      l.length > 0 && l.endsWith ":" && (l.startsWith ".L_"))
    -- Check for duplicates
    let rec findDupes (remaining seen dupes : List String) : List String :=
      match remaining with
      | [] => dupes
      | l :: rest =>
        if seen.any (· == l) then findDupes rest seen (if dupes.any (· == l) then dupes else l :: dupes)
        else findDupes rest (l :: seen) dupes
    let dupes := findDupes labelLines [] []
    if dupes.isEmpty then
      IO.println "✓ PASS  LabelCollisionRepro — no duplicate labels"
    else
      IO.eprintln s!"✗ FAIL  LabelCollisionRepro — duplicate labels: {dupes}"
      IO.Process.exit 1
  | none =>
    IO.eprintln s!"✗ FAIL  LabelCollisionRepro — compilation failed: {result.report}"
    IO.Process.exit 1
