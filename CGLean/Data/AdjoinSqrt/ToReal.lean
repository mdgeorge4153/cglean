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
