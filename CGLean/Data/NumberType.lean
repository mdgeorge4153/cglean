import Mathlib.Data.Rat.Sqrt
import CGLean.Data.AdjoinSqrt.Filtered

/-!
# The number type `FilteredReal ℚ[√2][√3]`

The instances that make `ℚ[√2][√3]` a linearly ordered field, and the filtered
version of it.

`ℚ` carries two orders here: Mathlib's, and the one derived from its sign
function through `SignedRing`. The tower is built on the second, so the
embedding of `ℚ` into `ℝ` is shown to be strictly monotone for that one.
-/

namespace CGLean.NumberType

open AdjoinSqrt

/-! ## `ℚ` -/

instance : SignedField ℚ := { (inferInstance : SignedRing ℚ), (inferInstance : Field ℚ) with }

/-- The order `ℚ` gets from its sign function is Mathlib's. -/
theorem signed_le_iff (a b : ℚ) :
    @LE.le ℚ (@instLinearOrderOfSignedRing ℚ SignedField.toSignedRing).toLE a b ↔ a ≤ b := by
  rw [SignedRing.le_iff]
  show SignType.sign (b - a) ≠ .neg ↔ _
  rw [SignType.neg_eq_neg_one, ne_eq, sign_eq_neg_one_iff, not_lt, sub_nonneg]

theorem signed_lt_iff (a b : ℚ) :
    @LT.lt ℚ (@instLinearOrderOfSignedRing ℚ SignedField.toSignedRing).toLT a b ↔ a < b := by
  rw [@lt_iff_le_not_ge ℚ (@instLinearOrderOfSignedRing ℚ SignedField.toSignedRing).toPreorder, signed_le_iff,
    signed_le_iff, ← lt_iff_le_not_ge]

/-- Whether `q` is a square in `ℚ` is decided by `Rat.sqrt`. -/
theorem nonsquare_of_sqrt {q : ℚ} (h : Rat.sqrt q * Rat.sqrt q ≠ q) : ∀ x : ℚ, x * x ≠ q :=
  fun x hx => h ((Rat.exists_mul_self q).mp ⟨x, hx⟩)

instance : Nonsquare ℚ 2 := ⟨nonsquare_of_sqrt (by decide +kernel)⟩
instance : Pos ℚ 2 := ⟨show SignType.sign (2 : ℚ) = .pos from sign_pos (by norm_num)⟩

instance : Fact (@StrictMono ℚ ℝ (@instLinearOrderOfSignedRing ℚ SignedField.toSignedRing).toPreorder _
    RealApprox.rat.toRingHom) :=
  ⟨fun a b h => (Fact.out : StrictMono RealApprox.rat.toRingHom) ((signed_lt_iff a b).mp h)⟩

/-! ## `ℚ[√2]` -/

abbrev K := AdjoinSqrt ℚ 2

instance : SignedField K where
  __ := AdjoinSqrt.instSignedRing
  __ := AdjoinSqrt.instField

theorem three_eq : (3 : K) = ⟨3, 0⟩ := by
  rw [← map_ofNat (@algebraMap ℚ K _ _ AdjoinSqrt.instAlgebra) 3]
  ext
  · show (OfNat.ofNat 3 : ℚ) = 3; norm_num
  · rfl

/-- `3` is not a square in `ℚ[√2]`: `(a + b√2)² = 3` forces `ab = 0`, and then
`a² = 3` or `2b² = 3`, neither of which has a rational solution. -/
instance : Nonsquare K 3 where
  not_square x h := by
    rw [three_eq] at h
    have h₁ : x.a₁ * x.a₁ + 2 * x.aₙ * x.aₙ = 3 := by
      simpa using congrArg AdjoinSqrt.a₁ h
    have hₙ : x.a₁ * x.aₙ + x.aₙ * x.a₁ = 0 := by
      simpa using congrArg AdjoinSqrt.aₙ h
    rcases mul_eq_zero.mp (show x.a₁ * x.aₙ = 0 by linarith) with ha | hb
    · exact nonsquare_of_sqrt (q := 6) (by decide +kernel) (2 * x.aₙ) (by rw [ha] at h₁; linarith)
    · exact nonsquare_of_sqrt (q := 3) (by decide +kernel) x.a₁ (by rw [hb] at h₁; linarith)

instance : Pos K 3 where
  n_pos := by
    rw [three_eq]
    show (match SignType.sign ((3 : ℚ) * 3 + -(2 * 0 * 0)) with
      | .neg => SignType.sign (0 : ℚ) | _ => SignType.sign (3 : ℚ)) = .pos
    rw [sign_pos (by norm_num : (0 : ℚ) < 3 * 3 + -(2 * 0 * 0))]
    exact sign_pos (by norm_num)

/-! ## The embeddings -/

theorem two_nonneg : 0 ≤ RealApprox.rat.toRingHom (2 : ℚ) := by
  rw [RealApprox.toRingHom, RealApprox.rat, Erased.out_mk]; norm_num

/-- `ℚ[√2]`, bracketed. -/
abbrev approxK : RealApprox K := realApprox RealApprox.rat two_nonneg

theorem three_nonneg : 0 ≤ approxK.toRingHom (3 : K) := by
  rw [map_ofNat]; norm_num

abbrev L := AdjoinSqrt K 3

/-- `ℚ[√2][√3]`, bracketed. -/
abbrev approxL : RealApprox L := realApprox approxK three_nonneg

/-! ## The number type -/

/-- `ℚ[√2][√3]` with filtered arithmetic. -/
abbrev Filtered := FilteredReal approxL

instance : Field Filtered := FilteredReal.instField

instance : LinearOrder Filtered :=
  @FilteredReal.instLinearOrder L AdjoinSqrt.instCommRing instLinearOrderOfSignedRing approxL _

/-- `FilteredReal ℚ[√2][√3]` is a linearly ordered field. -/
theorem isStrictOrderedRing : IsStrictOrderedRing Filtered :=
  @FilteredReal.instIsStrictOrderedRing L AdjoinSqrt.instCommRing instLinearOrderOfSignedRing
    approxL _ instIsStrictOrderedRingOfSignedRing

end CGLean.NumberType
