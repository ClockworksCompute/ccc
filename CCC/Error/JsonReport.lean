/-
  CCC/Error/JsonReport.lean — Machine-readable verification report (FEL-70)

  `CCC/Error/Report.lean` formats a `ProgramVerifyResult` as prose for
  humans. Everything that needs to consume a verification result
  PROGRAMMATICALLY — `scripts/corpus.sh` (previously grepping the prose
  for "memory safety violation(s) found", which is exactly how FEL-40's
  exit-code bug went unnoticed for a while), the mutation fuzzer, an
  eventual patch-synthesis loop, IDE integration — deserves real
  structured data instead of scraping text meant for a terminal.

  This is a first slice, not the full SARIF 2.1 format the FEL-70 ticket
  describes: it emits a CCC-native JSON shape (function name, status,
  per-violation property/location/message/context/suggestion, and a
  program-level summary) built directly from the SAME `SafetyViolation`/
  `FunVerifyResult`/`ProgramVerifyResult` data `Report.lean` already
  formats — no new verifier-side data collection. Each checker's
  "witness" (the specific facts it had and what it needed, e.g. `col <
  in_w`, needed `out_x0 + col < out_w`) is NOT captured as structured
  data anywhere in the verifier today — `SafetyViolation.message` is
  already a formatted-for-humans string that happens to contain this
  information in prose, not a separate structured field a checker
  populates. Splitting that out into a real `Witness` type each checker
  fills in, and full SARIF-schema compliance (`runs[].results[]`,
  `ruleId`, `properties.witness`), are both left for follow-up under the
  same ticket — this slice unblocks every consumer that just needs
  "which functions/violations, where, why" without more prose-scraping.
-/

import CCC.Syntax.PtrState
import Lean.Data.Json

namespace CCC.Error

open CCC.Syntax
open Lean (Json)

def ruleIdOf : SafetyProperty → String
  | .bufferBounds     => "buffer-bounds"
  | .noUseAfterFree    => "use-after-free"
  | .noDoubleFree      => "double-free"
  | .noNullDeref       => "null-deref"
  | .noStackOverflow   => "stack-overflow"
  | .noDivByZero       => "div-by-zero"

def statusTagOf : VerifyStatus → String
  | .verified   => "verified"
  | .degraded   => "degraded"
  | .exempt     => "exempt"
  | .parseError => "parse-error"

def locToJson (loc : Loc) : Json :=
  let line : Nat := loc.line
  let col : Nat := loc.col
  Json.mkObj [("line", line), ("col", col)]

def violationToJson (v : SafetyViolation) : Json :=
  Json.mkObj [
    ("property", Json.str (ruleIdOf v.property)),
    ("loc", locToJson v.loc),
    ("expr", Json.str v.expr),
    ("message", Json.str v.message),
    ("context", Json.arr (v.context.map Json.str).toArray),
    ("suggestion", match v.suggestion with
      | some s => Json.str s
      | none => Json.null)
  ]

/-- `Main.degradeReasons`-equivalent, kept structured instead of prose. -/
def degradeReasonsJson (r : FunVerifyResult) : List Json :=
  r.evidence.filterMap fun e =>
    match e with
    | .degradedBy feature reason loc =>
        some (Json.mkObj [
          ("feature", Json.str feature),
          ("reason", Json.str reason),
          ("loc", locToJson loc)
        ])
    | _ => none

def funResultToJson (r : FunVerifyResult) : Json :=
  Json.mkObj [
    ("name", Json.str r.funName),
    ("status", Json.str (statusTagOf r.status)),
    ("violations", Json.arr (r.violations.map violationToJson).toArray),
    ("degradedReasons", Json.arr (degradeReasonsJson r).toArray)
  ]

/-- The full program report as JSON. Skips the synthetic "program" entry
    `Verify.verifyProgramReport` adds, matching `--verify-report`'s own
    per-function loop in `Main.lean`. -/
def programReportToJson (filename : String) (report : ProgramVerifyResult) : Json :=
  let fns := report.results.filter (·.funName != "program")
  let totalViolations : Nat := (fns.map (·.violations.length)).foldl (·+·) 0
  let verified : Nat := (fns.filter (·.status == .verified)).length
  let degraded : Nat := (fns.filter (·.status == .degraded)).length
  let exempt : Nat := (fns.filter (·.status == .exempt)).length
  let totalFunctions : Nat := fns.length
  Json.mkObj [
    ("file", Json.str filename),
    ("functions", Json.arr (fns.map funResultToJson).toArray),
    ("summary", Json.mkObj [
      ("totalFunctions", totalFunctions),
      ("verified", verified),
      ("degraded", degraded),
      ("exempt", exempt),
      ("totalViolations", totalViolations),
      ("safe", Json.bool (totalViolations == 0))
    ])
  ]

end CCC.Error
