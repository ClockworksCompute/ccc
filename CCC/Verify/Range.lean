/-
  CCC/Verify/Range.lean — Integer interval domain for the verifier

  Tracks a per-key inclusive lower bound / exclusive upper bound over ℤ.
  `none` in either slot means "unknown" (not "unbounded" — we do not assume
  -∞/+∞ soundly cover anything; callers decide what "unknown" means for their
  check, e.g. an unsigned type gives an implicit lo=0 even when `lo = none`).

  This is the shared foundation for:
    - FEL-42 (kill/shift bounds on write)
    - FEL-46 (lower bound + width/signedness aware bounds)
    - FEL-56 (symbolic/relational bounds — later extension point)
-/

namespace CCC.Verify

/-- `lo` inclusive, `hi` exclusive. `none` = not known. -/
structure IRange where
  lo : Option Int := none
  hi : Option Int := none
  deriving Repr, Inhabited, BEq

namespace IRange

/-- Nothing known about this value. -/
def unknown : IRange := {}

/-- The value is known to be exactly `v`. -/
def point (v : Int) : IRange := { lo := some v, hi := some (v + 1) }

/-- Tighten (intersect) the lower bound with a new inclusive lower bound. -/
def withLo (r : IRange) (v : Int) : IRange :=
  { r with lo := some (match r.lo with | some l => max l v | none => v) }

/-- Tighten (intersect) the upper bound with a new exclusive upper bound. -/
def withHiExclusive (r : IRange) (v : Int) : IRange :=
  { r with hi := some (match r.hi with | some h => min h v | none => v) }

/-- Shift both ends by a constant delta (used for `i = i + k` / `i++` / `i--`). -/
def shift (r : IRange) (d : Int) : IRange :=
  { lo := r.lo.map (· + d), hi := r.hi.map (· + d) }

/-- Join (widen) two ranges: the result must contain both possibilities.
    Only produces a known bound when both sides know that bound. -/
def merge (a b : IRange) : IRange :=
  { lo := match a.lo, b.lo with
      | some x, some y => some (min x y)
      | _, _ => none
    hi := match a.hi, b.hi with
      | some x, some y => some (max x y)
      | _, _ => none }

/-- Inclusive upper bound, if known (hi - 1). -/
def hiInclusive (r : IRange) : Option Int := r.hi.map (· - 1)

/-- Is this range known to be entirely ≥ 0? -/
def knownNonNeg (r : IRange) : Bool :=
  match r.lo with
  | some l => l ≥ 0
  | none => false

/-- Is this range known to possibly be negative (lo known and < 0)? -/
def knownNeg (r : IRange) : Bool :=
  match r.lo with
  | some l => l < 0
  | none => false

end IRange

end CCC.Verify
