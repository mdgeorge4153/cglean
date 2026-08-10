import CGLean.Geometry.Point2D
import CGLean.Classes.CCWSystem
import CGLean.Algebra.Signed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Orientation of a triple of points

Which way the plane turns, as the sign of a determinant. Because the sign is
three-valued, collinearity is reported rather than excluded: `orientation` is
`.zero` exactly when the three points lie on a line, and no general-position
assumption is needed anywhere below.

Cyclic symmetry and antisymmetry hold at this level as equations between signs,
true of collinear triples as well. Knuth's axioms, which speak only of turns
that are counterclockwise, follow as corollaries and are packaged as the
`CCWSystem` instance at the end.

Two polynomial identities carry all the work. Interiority comes from the
signed areas about an interior point summing to the whole, and transitivity
from the three-term Plücker relation, which turns five positive determinants
into a positive product.
-/

open Signed

variable {k : Type} [SignedRing k]

namespace CGLean

/-- Twice the signed area of the triangle `p q r`, positive exactly when the
three points are traversed counterclockwise and zero exactly when they are
collinear. -/
def det (p q r : Point k) : k :=
  (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x)

/-- Which way the plane turns at `p q r`: `.pos` counterclockwise, `.neg`
clockwise, `.zero` collinear. -/
def orientation (p q r : Point k) : SignType := sign (det p q r)

/-- `p`, `q`, `r` make a counterclockwise turn, with `p` as the pivot. -/
def CCW (p q r : Point k) : Prop := orientation p q r = .pos

/-! ## The identities -/

/-- The determinant depends on the cyclic order of its arguments only. -/
theorem det_cyclic (p q r : Point k) : det q r p = det p q r := by
  simp only [det, Point.x, Point.y]; ring

/-- Exchanging the two points seen from the pivot negates the determinant. -/
theorem det_swap (p q r : Point k) : det p r q = -det p q r := by
  simp only [det, Point.x, Point.y]; ring

/-- The three triangles on `t` and an edge of `p q r` have signed areas summing
to that of `p q r`, for any `t` whatsoever. -/
theorem det_sum (p q r t : Point k) :
    det p q r = det t q r + det p t r + det p q t := by
  simp only [det, Point.x, Point.y]; ring

/-- The three-term Plücker relation among the determinants at a common pivot
`t`. Read with `s` fixed, it expresses `det t p r` in terms of the steps
`p → q` and `q → r`. -/
theorem det_plucker (p q r s t : Point k) :
    det t p r * det t s q = det t s p * det t q r + det t p q * det t s r := by
  simp only [det, Point.x, Point.y]; ring

/-! ## Orientation -/

/-- A counterclockwise turn is a positive determinant. -/
theorem ccw_iff_det_pos {p q r : Point k} : CCW p q r ↔ 0 < det p q r :=
  SignedRing.sign_eq_pos_iff

/-- Cyclic symmetry, as an equation between signs: it holds of collinear
triples too, not only of turns. -/
theorem orientation_cyclic (p q r : Point k) :
    orientation q r p = orientation p q r := by
  unfold orientation
  rw [det_cyclic]

/-- Antisymmetry, as an equation between signs: exchanging the two points seen
from the pivot negates the orientation, collinear triples included, where both
sides are `.zero`. -/
theorem orientation_swap (p q r : Point k) :
    orientation p r q = -orientation p q r := by
  unfold orientation
  rw [det_swap, SignedRing.sign_neg]

/-! ## Knuth's axioms -/

/-- Knuth's axiom 1. -/
theorem CCW.cyclic {p q r : Point k} (h : CCW p q r) : CCW q r p := by
  rwa [CCW, orientation_cyclic]

/-- Knuth's axiom 2. -/
theorem CCW.antisymm {p q r : Point k} (h : CCW p q r) : ¬ CCW p r q := by
  intro hc
  rw [ccw_iff_det_pos, det_swap] at hc
  rw [ccw_iff_det_pos] at h
  linarith

/-- Knuth's axiom 4: a point `t` seeing all three edges of `p q r` the same way
lies inside it, so `p q r` turns counterclockwise. -/
theorem CCW.interiority {p q r t : Point k}
    (h₁ : CCW t q r) (h₂ : CCW p t r) (h₃ : CCW p q t) : CCW p q r := by
  rw [ccw_iff_det_pos] at h₁ h₂ h₃ ⊢
  rw [det_sum p q r t]
  exact add_pos (add_pos h₁ h₂) h₃

/-- Knuth's axiom 5: seen from `t`, the order is transitive on points confined
to one side of the line `t s` by the first three hypotheses. -/
theorem CCW.transitivity {p q r s t : Point k}
    (hsp : CCW t s p) (hsq : CCW t s q) (hsr : CCW t s r)
    (hpq : CCW t p q) (hqr : CCW t q r) : CCW t p r := by
  rw [ccw_iff_det_pos] at hsp hsq hsr hpq hqr ⊢
  have hprod : 0 < det t p r * det t s q := by
    rw [det_plucker p q r s t]
    exact add_pos (mul_pos hsp hqr) (mul_pos hpq hsr)
  rcases mul_pos_iff.mp hprod with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd hsq (not_lt.mpr h.le)

instance : CCWSystem (Point k) where
  ccw := CCW
  cyclic := CCW.cyclic
  antisymm := CCW.antisymm
  interiority := CCW.interiority
  transitivity := CCW.transitivity

/-! ## The three values, on concrete points

The degenerate cases are the reason `orientation` is not a `Prop`: a collinear
triple is reported rather than excluded, and so is a repeated point. -/

example : orientation (toLex (0, 0) : Point Int) (toLex (1, 0)) (toLex (0, 1)) = .pos := by decide
example : orientation (toLex (0, 0) : Point Int) (toLex (0, 1)) (toLex (1, 0)) = .neg := by decide
example : orientation (toLex (0, 0) : Point Int) (toLex (1, 1)) (toLex (2, 2)) = .zero := by decide
example : orientation (toLex (5, 5) : Point Int) (toLex (5, 5)) (toLex (1, 2)) = .zero := by decide

end CGLean
