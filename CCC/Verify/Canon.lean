/-
  CCC/Verify/Canon.lean — structural expression canonicalization for the
  scoped symbolic-bounds mechanism (FEL-56/57/58, libheif-class detection).

  This is deliberately NOT a general symbolic-algebra engine. It performs a
  small, fixed set of structure-preserving normalizations sufficient to
  recognize a handful of well-known, generalizable idioms:

    - casts are layout-transparent for value comparison, so they're
      stripped (`(uint32_t)x` compares equal to `x`);
    - addition is commutative, so operands are sorted before joining, and
      `A - (-B)` is rewritten to the same canonical form as `A + B` (so a
      subtraction of an already-known-negative quantity composes with a
      later addition of the "same" quantity elsewhere);
    - a call to a "negation-wrapper" function — a function whose body,
      after stripping an initial special-case branch (INT_MIN-style
      overflow guards are common here), returns exactly `-x` for its own
      single parameter `x` — canonicalizes the SAME as a literal negation
      of its argument. This is a real, if narrow, generalization: it lets
      `negate_negative_int32(dx)` (libheif's own helper, needed because
      negating `INT32_MIN` is UB) compose algebraically with `dx` itself,
      without CCC needing to model INT_MIN/UB specially — it only needs to
      recognize the SHAPE "this function computes a negation".

  Two expressions with the same canonical string are asserted equal for
  the purposes of the `FlowState.exprBounds` fact table (see
  `CCC/Verify/Verify.lean`'s `clipPostcondition` and
  `CCC/Verify/BoundsCheck.lean`'s canon-based assignment transfer) — NOT
  proven equal by any general procedure. A false "equal" here could only
  make the checker WRONGLY ACCEPT something (the checks built on top only
  ever use canon-equality to justify accepting an access, never to justify
  rejecting one), so keep this list of normalizations short, exact, and
  reviewed; do not casually extend it.
-/

import CCC.Syntax.AST

namespace CCC.Verify

private partial def stripCast : Syntax.Expr → Syntax.Expr
  | .cast _ inner _ => stripCast inner
  | e => e

/-- Collect every expression appearing in a `return e;` anywhere in a
    statement (including nested blocks/branches/loops). -/
private partial def collectReturnExprs (s : Syntax.Stmt) : List Syntax.Expr :=
  match s with
  | .ret (some e) _ => [e]
  | .ret none _ => []
  | .block ss _ => (ss.map collectReturnExprs).flatten
  | .ifElse _ t e _ => (t.map collectReturnExprs).flatten ++ (e.map collectReturnExprs).flatten
  | .while_ _ b _ => (b.map collectReturnExprs).flatten
  | .for_ _ _ _ b _ => (b.map collectReturnExprs).flatten
  | .switch_ _ cases _ => (cases.map (fun c => (c.2.1.map collectReturnExprs).flatten)).flatten
  | .doWhile b _ _ => (b.map collectReturnExprs).flatten
  | .label_ _ body _ => collectReturnExprs body
  | _ => []

/-- Is `fnName` (in `prog`) a "negation-wrapper": exactly one parameter,
    and SOME reachable `return` expression is (after stripping casts)
    exactly `-<that parameter>`? See the module docstring. -/
def negationWrapperParam? (prog : Syntax.Program) (fnName : String) : Option String :=
  match prog.functions.find? (·.name == fnName) with
  | none => none
  | some f =>
      match f.params with
      | [p] =>
          let rets := (f.body.map collectReturnExprs).flatten
          if rets.any (fun e =>
              match stripCast e with
              | .unOp .neg (.var name _) _ => name == p.name
              | _ => false)
          then some p.name
          else none
      | _ => none

/-- Commutative join for canonicalized addition operands (`+0` is its own
    identity, both for readability of the resulting keys and because
    `BoundsCheck.proveSumLE` relies on it to treat a zero offset as "no
    offset at all" when chaining a bound through a sum). Exported (not
    `private`) since `proveSumLE` builds candidate sum-keys directly from
    already-canonicalized strings, without an `Expr` to re-canonicalize. -/
def joinAdd (a b : String) : String :=
  if a == "0" then b
  else if b == "0" then a
  else if a < b then "(" ++ a ++ "+" ++ b ++ ")" else "(" ++ b ++ "+" ++ a ++ ")"

/-- If `s` is exactly `neg(X)` (our own canonical negation wrapper),
    return `X`. -/
private def unwrapNeg (s : String) : Option String :=
  if s.startsWith "neg(" && s.endsWith ")" then
    some (((s.drop 4).dropRight 1).toString)
  else none

/-- Structural canonicalization — see the module docstring for exactly
    what this does and does not prove. `prog` is needed to resolve
    negation-wrapper function calls.

    `defs` is an optional, CALLER-PROVIDED symbolic-substitution
    environment (typically `FlowState.symbolicDefs`): when canonicalizing
    `.var name`, if `name` has an entry, its DEFINING expression is
    canonicalized instead (recursively, bounded by `fuel` so a def that
    happens to be self-referential or cyclic can only ever make this
    function return a less-precise (still SOUND — see the module
    docstring) result, never loop). This is what lets `in_w - in_x0`
    recognize `in_x0`'s definition `negate_negative_int32(dx)` as `-dx`
    and simplify to `in_w + dx`, matching a fact already established about
    `dx + in_w` elsewhere in the same straight-line block. -/
partial def canon (prog : Syntax.Program) (e : Syntax.Expr)
    (defs : List (String × Syntax.Expr) := []) (fuel : Nat := 3) : String :=
  match e with
  | .var name _ =>
      if fuel == 0 then name else
      match defs.find? (·.1 == name) with
      | some (_, def_) => canon prog def_ defs (fuel - 1)
      | none => name
  | .intLit v _ => toString v
  | .charLit c _ => toString c.toNat
  | .cast _ inner _ => canon prog inner defs fuel
  | .unOp .neg inner _ => "neg(" ++ canon prog inner defs fuel ++ ")"
  | .binOp .add a b _ => joinAdd (canon prog a defs fuel) (canon prog b defs fuel)
  | .binOp .sub a b _ =>
      let cb := canon prog b defs fuel
      match unwrapNeg cb with
      | some inner => joinAdd (canon prog a defs fuel) inner  -- A - (-B)  ≡  A + B
      | none => "(" ++ canon prog a defs fuel ++ "-" ++ cb ++ ")"
  | .call fnName [arg] _ =>
      match negationWrapperParam? prog fnName with
      | some _ => "neg(" ++ canon prog arg defs fuel ++ ")"
      | none => "call:" ++ fnName ++ "(" ++ canon prog arg defs fuel ++ ")"
  | _ => reprStr e

end CCC.Verify
