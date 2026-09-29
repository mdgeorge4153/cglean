import Mathlib.Data.Sign.Basic

/-!
# Orientation systems

Knuth's axiomatisation of orientation from *Axioms and Hulls*, stated for a
three-valued orientation rather than for a relation. `orientation p q r` reports
`.pos` for a counterclockwise turn, `.neg` for a clockwise one, and `.zero` when
the three points are collinear, so degenerate configurations are described
rather than assumed away.

Taking the sign as primitive buys three things. Two of Knuth's five axioms
become plain equations, true of collinear triples as well as of turns. The
remaining two each split into a strict form, which is Knuth's, and a non-strict
form permitting collinearity, which is what degenerate-tolerant algorithms need.
And an orientation is data, so it can be computed; the relation `ccw` derived
from it is a `Prop` and cannot be.

Knuth's third axiom, non-degeneracy, is absent. It asserts that no three points
are collinear, and assuming it would exclude exactly the configurations this is
meant to handle. In the language of oriented matroids these laws describe a
rank-3 chirotope — `swap` is the alternating law and `plucker` in
`CGLean/Geometry/Orientation.lean` is a Grassmann–Plücker relation — with
Knuth's CC systems the uniform case, that is the case with no zeros. That
correspondence is a lead worth checking against the literature, not something
verified here.

The strict laws are not consequences of the non-strict ones: `≠ .neg` leaves
`.zero` open, so both are carried.
-/

namespace CGLean

/-- A three-valued orientation on triples, satisfying those of Knuth's axioms
that hold of points in the plane.

Collinear triples are permitted throughout, and are exactly those sent to
`.zero`. Non-degeneracy is deliberately not assumed. -/
class OrientationSystem (P : Type) where
  /-- Which way the plane turns at `p q r`, with `p` as the pivot: `.pos`
  counterclockwise, `.neg` clockwise, `.zero` collinear. -/
  orientation : P → P → P → SignType
  /-- Knuth's axiom 1, as an equation: the orientation depends on the cyclic
  order of its arguments, not on which is written first. -/
  cyclic (p q r : P) : orientation q r p = orientation p q r
  /-- Knuth's axiom 2, as an equation: exchanging the two points seen from the
  pivot negates the orientation. Collinear triples are included, both sides
  being `.zero`. -/
  swap (p q r : P) : orientation p r q = -orientation p q r
  /-- Knuth's axiom 4 without strictness: a point `t` that no edge of `p q r`
  sees to its right — it may lie *on* an edge — leaves `p q r` not turning
  right either. -/
  interiority {p q r t : P} :
    orientation t q r ≠ .neg → orientation p t r ≠ .neg → orientation p q t ≠ .neg →
    orientation p q r ≠ .neg
  /-- Knuth's axiom 4: a point `t` strictly inside `p q r` forces it to turn
  counterclockwise. -/
  interiority_pos {p q r t : P} :
    orientation t q r = .pos → orientation p t r = .pos → orientation p q t = .pos →
    orientation p q r = .pos
  /-- Knuth's axiom 5 without strictness. Only the premise placing `q` off the
  line `t s` stays strict; it is what the conclusion is divided through by, and
  the result fails without it. -/
  transitivity {p q r s t : P} :
    orientation t s p ≠ .neg → orientation t s q = .pos → orientation t s r ≠ .neg →
    orientation t p q ≠ .neg → orientation t q r ≠ .neg →
    orientation t p r ≠ .neg
  /-- Knuth's axiom 5: seen from `t`, the order is transitive on points confined
  to one side of the line `t s` by the three premises naming `s`. -/
  transitivity_pos {p q r s t : P} :
    orientation t s p = .pos → orientation t s q = .pos → orientation t s r = .pos →
    orientation t p q = .pos → orientation t q r = .pos →
    orientation t p r = .pos

export OrientationSystem (orientation)

variable {P : Type} [OrientationSystem P]

/-- `p`, `q`, `r` make a counterclockwise turn, with `p` as the pivot. This is
Knuth's relation; the axioms governing it are the `CCW` lemmas below. -/
def CCW (p q r : P) : Prop := orientation p q r = .pos

/-- Knuth's axiom 1. -/
theorem CCW.cyclic {p q r : P} (h : CCW p q r) : CCW q r p := by
  unfold CCW at h ⊢
  rw [OrientationSystem.cyclic]; exact h

/-- Knuth's axiom 2. -/
theorem CCW.antisymm {p q r : P} (h : CCW p q r) : ¬ CCW p r q := by
  unfold CCW at h ⊢
  rw [OrientationSystem.swap, h]
  decide

/-- Knuth's axiom 4. -/
theorem CCW.interiority {p q r t : P}
    (h₁ : CCW t q r) (h₂ : CCW p t r) (h₃ : CCW p q t) : CCW p q r :=
  OrientationSystem.interiority_pos h₁ h₂ h₃

/-- Knuth's axiom 5. -/
theorem CCW.transitivity {p q r s t : P}
    (hsp : CCW t s p) (hsq : CCW t s q) (hsr : CCW t s r)
    (hpq : CCW t p q) (hqr : CCW t q r) : CCW t p r :=
  OrientationSystem.transitivity_pos hsp hsq hsr hpq hqr

end CGLean
