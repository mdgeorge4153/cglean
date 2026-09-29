import CGLean.Geometry.Point2D
import CGLean.Classes.OrientationSystem
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Orientation of a triple of points

Points with coordinates in an ordered ring form an `OrientationSystem`, the
orientation of a triple being the sign of a determinant. Since the sign is
three-valued, collinearity is reported rather than excluded, and no
general-position assumption appears anywhere below.

Two polynomial identities carry all the work, and each axiom is a law of
`SignType.sign` applied to one of them. Interiority comes from the signed areas about
a fourth point summing to the whole, together with closure of the non-negative
elements under addition; transitivity from the three-term Plücker relation,
together with the sign of a product. Cyclic symmetry
and antisymmetry are the identities themselves, under `sign_neg`.
-/

open SignType (sign)

variable {k : Type} [CommRing k] [LinearOrder k] [IsStrictOrderedRing k]

namespace CGLean

private theorem nonneg_iff {a : k} : 0 ≤ a ↔ sign a ≠ .neg := by
  rw [Ne, SignType.neg_eq_neg_one, sign_eq_neg_one_iff, not_lt]

private theorem sign_eq_pos_iff {a : k} : sign a = .pos ↔ 0 < a := by
  rw [SignType.pos_eq_one, sign_eq_one_iff]

/-- Twice the signed area of the triangle `p q r`, positive exactly when the
three points are traversed counterclockwise and zero exactly when they are
collinear. -/
def det (p q r : Point k) : k :=
  (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x)

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

/-! ## The instance

Each field is stated here against `sign (det ..)` so that the proofs are about
the determinant rather than about a structure projection. -/

private theorem sign_det_cyclic (p q r : Point k) :
    sign (det q r p) = sign (det p q r) := by rw [det_cyclic]

private theorem sign_det_swap (p q r : Point k) :
    sign (det p r q) = -sign (det p q r) := by
  rw [det_swap, Left.sign_neg]

private theorem sign_det_interiority {p q r t : Point k}
    (h₁ : sign (det t q r) ≠ .neg) (h₂ : sign (det p t r) ≠ .neg)
    (h₃ : sign (det p q t) ≠ .neg) : sign (det p q r) ≠ .neg := by
  rw [← nonneg_iff] at h₁ h₂ h₃ ⊢
  rw [det_sum p q r t]
  exact add_nonneg (add_nonneg h₁ h₂) h₃

private theorem sign_det_interiority_pos {p q r t : Point k}
    (h₁ : sign (det t q r) = .pos) (h₂ : sign (det p t r) = .pos)
    (h₃ : sign (det p q t) = .pos) : sign (det p q r) = .pos := by
  rw [sign_eq_pos_iff] at h₁ h₂ h₃ ⊢
  rw [det_sum p q r t]
  exact add_pos (add_pos h₁ h₂) h₃

private theorem sign_det_transitivity {p q r s t : Point k}
    (hsp : sign (det t s p) ≠ .neg) (hsq : sign (det t s q) = .pos)
    (hsr : sign (det t s r) ≠ .neg) (hpq : sign (det t p q) ≠ .neg)
    (hqr : sign (det t q r) ≠ .neg) : sign (det t p r) ≠ .neg := by
  rw [← nonneg_iff] at hsp hsr hpq hqr ⊢
  rw [sign_eq_pos_iff] at hsq
  have hprod : 0 ≤ det t p r * det t s q := by
    rw [det_plucker p q r s t]
    exact add_nonneg (mul_nonneg hsp hqr) (mul_nonneg hpq hsr)
  by_contra hc
  rw [not_le] at hc
  nlinarith

private theorem sign_det_transitivity_pos {p q r s t : Point k}
    (hsp : sign (det t s p) = .pos) (hsq : sign (det t s q) = .pos)
    (hsr : sign (det t s r) = .pos) (hpq : sign (det t p q) = .pos)
    (hqr : sign (det t q r) = .pos) : sign (det t p r) = .pos := by
  rw [sign_eq_pos_iff] at hsp hsq hsr hpq hqr ⊢
  have hprod : 0 < det t p r * det t s q := by
    rw [det_plucker p q r s t]
    exact add_pos (mul_pos hsp hqr) (mul_pos hpq hsr)
  rcases mul_pos_iff.mp hprod with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd hsq (not_lt.mpr h.le)

instance : OrientationSystem (Point k) where
  orientation p q r := sign (det p q r)
  cyclic := sign_det_cyclic
  swap := sign_det_swap
  interiority := sign_det_interiority
  interiority_pos := sign_det_interiority_pos
  transitivity := sign_det_transitivity
  transitivity_pos := sign_det_transitivity_pos

/-- The orientation of a triple of points is the sign of its determinant. -/
theorem orientation_eq_sign_det (p q r : Point k) :
    orientation p q r = sign (det p q r) := rfl

/-- A counterclockwise turn is a positive determinant. -/
theorem ccw_iff_det_pos {p q r : Point k} : CCW p q r ↔ 0 < det p q r :=
  sign_eq_pos_iff

/-! ## The three values, on concrete points

The degenerate cases are the reason an orientation is not a `Prop`: a collinear
triple is reported rather than excluded, and so is a repeated point. -/

example : orientation (toLex (0, 0) : Point Int) (toLex (1, 0)) (toLex (0, 1)) = .pos := by decide
example : orientation (toLex (0, 0) : Point Int) (toLex (0, 1)) (toLex (1, 0)) = .neg := by decide
example : orientation (toLex (0, 0) : Point Int) (toLex (1, 1)) (toLex (2, 2)) = .zero := by decide
example : orientation (toLex (5, 5) : Point Int) (toLex (5, 5)) (toLex (1, 2)) = .zero := by decide

end CGLean
