import Mathlib.Analysis.Real.Sqrt
import CGLean.Data.AdjoinSqrt

/-! # The real value of an element of `A[√n]` -/

namespace AdjoinSqrt

variable {R : Type} {n : R}
variable {F : Type*} [FunLike F R ℝ] (f : F)

/-- The natural embedding from `AdjoinSqrt R n` to `ℝ` (with positive `√n`). -/
@[simp] noncomputable def toReal (x : AdjoinSqrt R n) : ℝ := f x.a₁ + f x.aₙ * Real.sqrt (f n)

section Hom

variable [CommRing R] [RingHomClass F R ℝ]

/-- `toReal` bundled as a ring hom -/
@[simps] noncomputable def toRealHom (hn : 0 ≤ f n) : AdjoinSqrt R n →+* ℝ where
  toFun := toReal f
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp; ring
  map_mul' := by
    intros x y; simp; linear_combination -(f x.aₙ * f y.aₙ) * (Real.mul_self_sqrt hn)

end Hom

section OrderHom

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Fact (¬ IsSquare n)] [pos : Fact (0 < n)]
  [RingHomClass F R ℝ] [OrderHomClass F R ℝ]

omit [IsStrictOrderedRing R] [Fact (¬ IsSquare n)] in
lemma map_n_nonneg : 0 ≤ f n := by
  simpa using OrderHomClass.monotone f pos.out.le

omit [Fact (¬ IsSquare n)] in
/-- `toReal` preserves nonnegativity -/
-- TODO: maybe restate in terms of toReal instead of toRealHom, and also below
lemma toReal_nonneg {a : AdjoinSqrt R n} (ha : IsNonneg a) :
    0 ≤ toRealHom f (map_n_nonneg f) a := by
  have hsq (c : ℝ) : (c * √(f n)) ^ 2 = f n * c * c := by
    rw [mul_pow, Real.sq_sqrt (map_n_nonneg f)]; ring
  simp only [toRealHom_apply, toReal]
  rcases ha with ⟨h1, hN⟩ | ⟨h1, hN⟩
    <;> replace h1 := OrderHomClass.monotone f h1
    <;> replace hN := OrderHomClass.monotone f hN
    <;> simp [norm] at h1 hN
    <;> nlinarith [hsq (f a.aₙ), mul_nonneg h1 (Real.sqrt_nonneg (f n))]

/-- `toReal` is monotone -/
lemma toReal_monotone : Monotone (toRealHom (n := n) f (map_n_nonneg f)) := by
  intro a b hab
  have h := toReal_nonneg f ((nonneg_iff _).mp (sub_nonneg.mpr hab))
  rwa [map_sub, sub_nonneg] at h

/-- Adds monotonicity to `toRealHom`. -/
noncomputable def toRealOrderHom : AdjoinSqrt R n →+*o ℝ :=
  { toRealHom f (map_n_nonneg f) with monotone' := toReal_monotone f }

end OrderHom

end AdjoinSqrt
