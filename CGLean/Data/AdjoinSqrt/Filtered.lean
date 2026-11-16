import CGLean.Data.AdjoinSqrt
import CGLean.Data.FilteredEmbedding

/-!
# Filtering `A[√n]`

A `RealApprox` for `A[√n]`, built from one for `A`: `a₁ + aₙ√n` is bracketed by
combining intervals for `a₁`, `aₙ` and `√n`. Nesting this gives filtered
arithmetic on towers of square roots over `ℚ`.
-/

namespace AdjoinSqrt

open CGLean LeanCert.Core

variable {R : Type} {n : R}

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fact (¬ IsSquare n)] [Fact (0 < n)]

/-- `e`'s embedding, with its monotonicity bundled, as `toRealHom` expects. -/
noncomputable def baseOrderHom (e : RealApprox R) : R →+*o ℝ :=
  { e.toRingHom with monotone' := e.strictMono'.monotone }

/-- Bracket `a₁ + aₙ√n` from brackets for `a₁`, `aₙ` and `n`. -/
instance realApprox [e : RealApprox R] : RealApprox (AdjoinSqrt R n) where
  hom := Erased.mk (toRealHom (baseOrderHom e) (map_n_nonneg _))
  strictMono := by
    rw [Erased.out_mk]
    exact Monotone.strictMono_of_injective (toReal_monotone _) (RingHom.injective _)
  -- `√n` is bracketed once, not on every call
  approx := let s := sqrt (e.approx n)
    fun x => trim ((e.approx x.a₁).add (trim ((e.approx x.aₙ).mul s)))
  mem_approx x := by
    rw [Erased.out_mk]
    exact mem_trim (IntervalDyadic.mem_add (e.mem_approx' _)
      (mem_trim (IntervalDyadic.mem_mul (e.mem_approx' _) (mem_sqrt (e.mem_approx' _)))))

end AdjoinSqrt
