import Mathlib.Analysis.Real.Sqrt
import CGLean.Data.AdjoinSqrt

/-!
# The real value of an element of `A[√n]`

`toReal` sends `a₁ + aₙ√n` to a real number, given a real value for each element
of `A`. It is the embedding that fixes `√n` as the positive root; the conjugate
embedding is obtained by negating `aₙ`.

Its homomorphism properties are what `FilteredReal` requires of the function it
is parameterised by, since an interval containing `f x` can only be built from
intervals containing the parts of `x` when `f` respects the operations.
-/

namespace AdjoinSqrt

variable {R : Type} {n : R}

/-- The real value of `a₁ + aₙ√n`, given a real value for each element of `R`.
Noncomputable, since it lands in `ℝ`: this exists to state the homomorphism
properties of the embedding, not to be evaluated. -/
noncomputable def toReal (f : R → ℝ) (x : AdjoinSqrt R n) : ℝ :=
  f x.a₁ + f x.aₙ * Real.sqrt (f n)

section Hom

variable [CommRing R] (f : R →+* ℝ) (hn : 0 ≤ f n)

@[simp] theorem toReal_zero : toReal f (0 : AdjoinSqrt R n) = 0 := by
  simp [toReal]

@[simp] theorem toReal_one : toReal f (1 : AdjoinSqrt R n) = 1 := by
  simp [toReal]

@[simp] theorem toReal_add (x y : AdjoinSqrt R n) :
    toReal f (x + y) = toReal f x + toReal f y := by
  have ha : (x + y).a₁ = x.a₁ + y.a₁ := rfl
  have hb : (x + y).aₙ = x.aₙ + y.aₙ := rfl
  simp only [toReal, ha, hb, map_add]; ring

@[simp] theorem toReal_neg (x : AdjoinSqrt R n) :
    toReal f (-x) = -toReal f x := by
  have ha : (-x).a₁ = -x.a₁ := rfl
  have hb : (-x).aₙ = -x.aₙ := rfl
  simp only [toReal, ha, hb, map_neg]; ring

include hn in
/-- `toReal` is multiplicative. This is where `0 ≤ f n` is needed: the cross
terms cancel only because `√(f n)` squares back to `f n`. -/
theorem toReal_mul (x y : AdjoinSqrt R n) :
    toReal f (x * y) = toReal f x * toReal f y := by
  have hs : Real.sqrt (f n) * Real.sqrt (f n) = f n := Real.mul_self_sqrt hn
  have ha : (x * y).a₁ = x.a₁ * y.a₁ + n * x.aₙ * y.aₙ := rfl
  have hb : (x * y).aₙ = x.a₁ * y.aₙ + x.aₙ * y.a₁ := rfl
  simp only [toReal, ha, hb, map_add, map_mul]
  linear_combination (-(f x.aₙ * f y.aₙ)) * hs

end Hom

section OrderHom

/-- Real-arithmetic core of the first case: if `A` is non-negative and dominates
`sB` in square, it dominates it outright. -/
private lemma add_nonneg_of_sq_le {A B t : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A)
    (h : 0 ≤ A * A - t * t * (B * B)) : 0 ≤ A + B * t := by
  by_contra hc
  push_neg at hc
  have hBt : B * t < 0 := by linarith
  nlinarith [mul_pos (neg_pos.mpr hc) (show (0:ℝ) < A - B * t by linarith)]

/-- Real-arithmetic core of the second case: if `B` is non-negative and `sB`
dominates `A` in square, the sum is non-negative. -/
private lemma add_nonneg_of_sq_ge {A B t : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (h : A * A - t * t * (B * B) ≤ 0) : 0 ≤ A + B * t := by
  by_contra hc
  push_neg at hc
  have hBt : 0 ≤ B * t := mul_nonneg hB ht
  nlinarith [mul_pos (show (0:ℝ) < -A - B * t by linarith)
    (show (0:ℝ) < -A + B * t by linarith)]

variable [SignedField R] [Nonsquare R n] [Pos R n] (f : R →+* ℝ) (hf : Monotone f)

include hf in
/-- `toReal` sends non-negative elements to non-negative reals. Unlike the
corresponding statement inside `A`, this one is straightforward: `√(f n)` really
exists in `ℝ`, so each disjunct of the criterion can be compared directly. -/
theorem toReal_nonneg (x : AdjoinSqrt R n) (hx : (0 : AdjoinSqrt R n) ≤ x) :
    0 ≤ toReal f x := by
  have hn0 : (0 : R) < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hfn : 0 ≤ f n := by simpa using hf hn0.le
  have hs : Real.sqrt (f n) * Real.sqrt (f n) = f n := Real.mul_self_sqrt hfn
  have hs0 : (0:ℝ) ≤ Real.sqrt (f n) := Real.sqrt_nonneg _
  simp only [toReal]
  rcases (nonneg_iff x).mp (by rw [SignedRing.nonneg_iff] at hx; simpa using hx)
    with ⟨h1, hN⟩ | ⟨h1, hN⟩
  · have a1 : 0 ≤ f x.a₁ := by simpa using hf h1
    have aN : 0 ≤ f (norm x) := by simpa using hf hN
    simp only [norm, map_sub, map_mul] at aN
    exact add_nonneg_of_sq_le hs0 a1 (by rw [hs]; linarith)
  · have aN : 0 ≤ f x.aₙ := by simpa using hf h1
    have a1 : f (norm x) ≤ 0 := by simpa using hf hN
    simp only [norm, map_sub, map_mul] at a1
    exact add_nonneg_of_sq_ge hs0 aN (by rw [hs]; linarith)

include hf in
/-- Hence `toReal` is monotone: it is an ordered ring homomorphism. -/
theorem toReal_monotone : Monotone (toReal (n := n) f) := by
  intro x y hxy
  have h := toReal_nonneg f hf (y - x) (sub_nonneg.mpr hxy)
  have hsub : toReal f (y - x) = toReal f y - toReal f x := by
    rw [sub_eq_add_neg, toReal_add, toReal_neg]; ring
  rw [hsub] at h
  linarith

end OrderHom

end AdjoinSqrt
