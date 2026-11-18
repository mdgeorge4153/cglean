module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Approximations of real numbers

An instance of `RealApprox A` makes the elements of `A` approximations of real
numbers: each `X : A` stands for the set of reals `x` with `x ∈ X`, and the
operations on `A` are sound, so they map approximations of the inputs to an
approximation of the output.

Nothing requires these sets to be intervals, although intervals are the instance
used in practice (`CGLean.Data.Interval`). Square roots are a separate class,
`RealApproxSqrt`, since only towers of square roots need them.
-/

@[expose] public section

namespace CGLean

/-- `A` approximates real numbers: each element stands for a set of reals, and
the operations are sound. -/
class RealApprox (A : Type) extends Membership ℝ A, Add A, Neg A, Sub A, Mul A, Pow A ℕ where
  /-- An approximation of the reciprocal of every member of `X`, or `none`
  (for instance when `X` may contain zero). -/
  inv? : A → Option A
  /-- The common order of every member of `X` with every member of `Y`, or
  `none` when the approximations don't determine it. -/
  compare? : A → A → Option Ordering
  mem_add {x y : ℝ} {X Y : A} : x ∈ X → y ∈ Y → x + y ∈ X + Y
  mem_neg {x : ℝ} {X : A} : x ∈ X → -x ∈ -X
  mem_sub {x y : ℝ} {X Y : A} : x ∈ X → y ∈ Y → x - y ∈ X - Y
  mem_mul {x y : ℝ} {X Y : A} : x ∈ X → y ∈ Y → x * y ∈ X * Y
  mem_pow {x : ℝ} {X : A} : x ∈ X → ∀ n : ℕ, x ^ n ∈ X ^ n
  mem_inv? {x : ℝ} {X Y : A} : x ∈ X → inv? X = some Y → x⁻¹ ∈ Y
  compare_of_compare? {X Y : A} {o : Ordering} :
    compare? X Y = some o → ∀ x ∈ X, ∀ y ∈ Y, compare x y = o

/-- Square roots of approximations. -/
class RealApproxSqrt (A : Type) [RealApprox A] where
  /-- An approximation of the square root of every member of `X`. -/
  sqrt : A → A
  mem_sqrt {x : ℝ} {X : A} : x ∈ X → Real.sqrt x ∈ sqrt X

end CGLean
