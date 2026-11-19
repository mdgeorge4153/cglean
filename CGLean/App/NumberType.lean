import Mathlib.Data.Rat.Sqrt
import CGLean.Data.AdjoinSqrt.Filtered
import CGLean.Data.Interval

/-!
# The number type `Filtered ℚ[√2][√3]`

The instances that make `ℚ[√2][√3]` a linearly ordered field, and the filtered
version of it: that `2` and `3` are positive non-squares in `ℚ` and `ℚ[√2]`, and
that values are approximated by dyadic intervals.
-/

namespace CGLean.NumberType

open AdjoinSqrt

/-! ## `ℚ` -/

/-- Approximate by dyadic intervals; the tower above inherits this. -/
instance : ApproxStrategy ℚ LeanCert.Core.IntervalDyadic := .ratInterval

/-- Whether `q` is a square in `ℚ` is decided by `Rat.sqrt`. -/
theorem nonsquare_of_sqrt {q : ℚ} (h : Rat.sqrt q * Rat.sqrt q ≠ q) : ∀ x : ℚ, x * x ≠ q :=
  fun x hx => h ((Rat.exists_mul_self q).mp ⟨x, hx⟩)

instance : Fact (¬ IsSquare (2 : ℚ)) :=
  ⟨fun ⟨x, h⟩ => nonsquare_of_sqrt (by decide +kernel) x h.symm⟩
instance : Fact ((0 : ℚ) < 2) := ⟨by norm_num⟩

/-! ## `ℚ[√2]` -/

abbrev K := AdjoinSqrt ℚ 2

theorem three_eq : (3 : K) = ⟨3, 0⟩ := by
  rw [← map_ofNat (@algebraMap ℚ K _ _ AdjoinSqrt.algebra) 3]
  ext
  · show (OfNat.ofNat 3 : ℚ) = 3; norm_num
  · rfl

/-- `3` is not a square in `ℚ[√2]`: `(a + b√2)² = 3` forces `ab = 0`, and then
`a² = 3` or `2b² = 3`, neither of which has a rational solution. -/
instance : Fact (¬ IsSquare (3 : K)) where
  out := by
    rintro ⟨x, h⟩
    rw [three_eq] at h
    replace h := h.symm
    have h₁ : x.a₁ * x.a₁ + 2 * x.aₙ * x.aₙ = 3 := by
      simpa using congrArg AdjoinSqrt.a₁ h
    have hₙ : x.a₁ * x.aₙ + x.aₙ * x.a₁ = 0 := by
      simpa using congrArg AdjoinSqrt.aₙ h
    rcases mul_eq_zero.mp (show x.a₁ * x.aₙ = 0 by linarith) with ha | hb
    · exact nonsquare_of_sqrt (q := 6) (by decide +kernel) (2 * x.aₙ) (by rw [ha] at h₁; linarith)
    · exact nonsquare_of_sqrt (q := 3) (by decide +kernel) x.a₁ (by rw [hb] at h₁; linarith)

instance : Fact ((0 : K) < 3) := ⟨by norm_num⟩

abbrev L := AdjoinSqrt K 3

/-! ## The number type -/

/-- `ℚ[√2][√3]` with filtered arithmetic. -/
abbrev Num := Filtered L

instance : Field Num := inferInstance
instance : LinearOrder Num := inferInstance

/-- `Filtered ℚ[√2][√3]` is a linearly ordered field. -/
theorem isStrictOrderedRing : IsStrictOrderedRing Num := inferInstance

end CGLean.NumberType
