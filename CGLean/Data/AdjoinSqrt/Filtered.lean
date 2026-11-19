module

public import Mathlib.RingTheory.SimpleRing.Basic
public import CGLean.Data.AdjoinSqrt
public import CGLean.Data.Filtered

/-!
# Filtering `R[√n]`

An approximation strategy for `R[√n]`, built from one for `R`: `a₁ + aₙ√n` is
approximated by combining approximations of `a₁`, `aₙ` and `√n`. Nesting this
gives filtered arithmetic on towers of square roots over `ℚ`.
-/

@[expose] public section

namespace AdjoinSqrt

open CGLean

variable {R : Type} {n : R} {α : Type} [RealApprox α]

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fact (¬ IsSquare n)] [Fact (0 < n)]

/-- `e`'s embedding, with its monotonicity bundled, as `toRealHom` expects. -/
noncomputable def baseOrderHom (e : ApproxStrategy R α) : R →+*o ℝ :=
  { e.toRingHom with monotone' := e.strictMono'.monotone }

/-- Approximate `a₁ + aₙ√n` from approximations of `a₁`, `aₙ` and `√n`. -/
instance approxStrategy [e : ApproxStrategy R α] [sq : ApproxSqrt n] :
    ApproxStrategy (AdjoinSqrt R n) α where
  hom := Erased.mk (toRealHom (baseOrderHom e) (map_n_nonneg _))
  strictMono := by
    rw [Erased.out_mk]
    exact Monotone.strictMono_of_injective (toReal_monotone _) (RingHom.injective _)
  approx x := e.approx x.a₁ + e.approx x.aₙ * sq.sqrt
  mem_approx x := by
    rw [Erased.out_mk]
    exact RealApprox.mem_add (e.mem_approx' _)
      (RealApprox.mem_mul (e.mem_approx' _) sq.mem_sqrt)

end AdjoinSqrt
