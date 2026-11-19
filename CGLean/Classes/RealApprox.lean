module

public import Mathlib.Basic.Real.Basic

/-!
# Approximations of real numbers

An instance of `RealApprox α` makes the elements of `α` approximations of real
numbers: each `X : α` stands for the set of reals `x` with `x ∈ X`, and the
operations on `α` are sound, so they map approximations of the inputs to an
approximation of the output.

Nothing requires these sets to be intervals, although intervals are the instance
used in practice (`CGLean.Data.Interval`).
-/

@[expose] public section

namespace CGLean

/-- `α` approximates real numbers: each element stands for a set of reals, and
the operations are sound. -/
class RealApprox (α : Type) extends Membership ℝ α, Add α, Neg α, Sub α, Mul α, Pow α ℕ where
  /-- An approximation of the reciprocal of every member of `X`, or `none`
  (for instance when `X` may contain zero). -/
  inv? : α → Option α
  /-- The common order of every member of `X` with every member of `Y`, or
  `none` when the approximations don't determine it. -/
  compare? : α → α → Option Ordering
  mem_add {x y : ℝ} {X Y : α} : x ∈ X → y ∈ Y → x + y ∈ X + Y
  mem_neg {x : ℝ} {X : α} : x ∈ X → -x ∈ -X
  mem_sub {x y : ℝ} {X Y : α} : x ∈ X → y ∈ Y → x - y ∈ X - Y
  mem_mul {x y : ℝ} {X Y : α} : x ∈ X → y ∈ Y → x * y ∈ X * Y
  mem_pow {x : ℝ} {X : α} : x ∈ X → ∀ n : ℕ, x ^ n ∈ X ^ n
  mem_inv? {x : ℝ} {X Y : α} : x ∈ X → inv? X = some Y → x⁻¹ ∈ Y
  compare_of_compare? {X Y : α} {o : Ordering} :
    compare? X Y = some o → ∀ x ∈ X, ∀ y ∈ Y, compare x y = o

/-- The partial operations of `α` are complete: `inv?` fails only when `X`
contains zero, and `compare?` only when the members of `X` and `Y` don't all
compare the same way. (Complete as a decision procedure, not in the sense of
`CompleteSpace` or a complete lattice.) -/
class RealApprox.IsComplete (α : Type) [RealApprox α] : Prop where
  zero_mem_of_inv?_eq_none {X : α} : RealApprox.inv? X = none → (0 : ℝ) ∈ X
  exists_ne_of_compare?_eq_none {X Y : α} : RealApprox.compare? X Y = none →
    ∃ x₁ ∈ X, ∃ y₁ ∈ Y, ∃ x₂ ∈ X, ∃ y₂ ∈ Y, compare x₁ y₁ ≠ compare x₂ y₂

end CGLean
