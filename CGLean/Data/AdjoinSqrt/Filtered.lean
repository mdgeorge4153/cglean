module

public import Mathlib.RingTheory.SimpleRing.Basic
public import CGLean.Data.AdjoinSqrt
public import CGLean.Data.Filtered

/-!
# Filtering `A[√n]`

An approximation strategy for `A[√n]`, built from one for `A`: `a₁ + aₙ√n` is
approximated by combining approximations of `a₁`, `aₙ` and `√n`. Nesting this
gives filtered arithmetic on towers of square roots over `ℚ`.
-/

@[expose] public section

namespace AdjoinSqrt

open CGLean

variable {R : Type} {n : R} {A : Type} [RealApprox A]

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fact (¬ IsSquare n)] [Fact (0 < n)]

/-- `e`'s embedding, with its monotonicity bundled, as `toRealHom` expects. -/
noncomputable def baseOrderHom (e : ApproxStrategy R A) : R →+*o ℝ :=
  { e.toRingHom with monotone' := e.strictMono'.monotone }

/-- Approximate `a₁ + aₙ√n` from approximations of `a₁`, `aₙ` and `√n`. -/
instance approxStrategy [e : ApproxStrategy R A] [sq : ApproxSqrt n] :
    ApproxStrategy (AdjoinSqrt R n) A where
  hom := Erased.mk (toRealHom (baseOrderHom e) (map_n_nonneg _))
  strictMono := by
    rw [Erased.out_mk]
    exact Monotone.strictMono_of_injective (toReal_monotone _) (RingHom.injective _)
  -- `√n` is approximated once, not on every call
  approx := let s := sq.sqrt
    fun x => e.approx x.a₁ + e.approx x.aₙ * s
  mem_approx x := by
    rw [Erased.out_mk]
    exact RealApprox.mem_add (e.mem_approx' _)
      (RealApprox.mem_mul (e.mem_approx' _) sq.mem_sqrt)

end AdjoinSqrt
