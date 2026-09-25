import CGLean.Data.AdjoinSqrt.ToReal
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

/-- `toReal` as a ring homomorphism. -/
noncomputable def toRealHom [CommRing R] (f : R →+* ℝ) (hn : 0 ≤ f n) :
    AdjoinSqrt R n →+* ℝ where
  toFun := toReal f
  map_zero' := toReal_zero f
  map_one' := toReal_one f
  map_add' := toReal_add f
  map_mul' := toReal_mul f hn

/-- Bracket `a₁ + aₙ√n` from brackets for `a₁`, `aₙ` and `n`. -/
def realApprox [CommRing R] (e : RealApprox R) (hn : 0 ≤ e.toRingHom n) :
    RealApprox (AdjoinSqrt R n) where
  hom := Erased.mk (toRealHom e.toRingHom hn)
  -- `√n` is bracketed once, not on every call
  approx := let s := sqrt (e.approx n)
    fun x => trim ((e.approx x.a₁).add (trim ((e.approx x.aₙ).mul s)))
  mem_approx x := by
    rw [Erased.out_mk]
    exact mem_trim (IntervalDyadic.mem_add (e.mem_approx' _)
      (mem_trim (IntervalDyadic.mem_mul (e.mem_approx' _) (mem_sqrt (e.mem_approx' _)))))

theorem realApprox_toRingHom [CommRing R] (e : RealApprox R) (hn : 0 ≤ e.toRingHom n) :
    (realApprox e hn).toRingHom = toRealHom e.toRingHom hn :=
  Erased.out_mk _

/-- The embedding is strictly monotone for the order on `A[√n]`, given that the
one on `A` is. -/
instance [SignedField R] [Nonsquare R n] [Pos R n] (e : RealApprox R) (hn : 0 ≤ e.toRingHom n)
    [he : Fact (StrictMono e.toRingHom)] :
    Fact (StrictMono (realApprox e hn).toRingHom) := by
  constructor
  rw [realApprox_toRingHom]
  exact Monotone.strictMono_of_injective (toReal_monotone _ he.out.monotone)
    (RingHom.injective _)

end AdjoinSqrt
