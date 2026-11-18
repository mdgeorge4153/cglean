module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Erased
public import Mathlib.Basic.Real.Basic
public import CGLean.Classes.RealApprox

/-!
# Approximating the elements of an ordered ring

An instance of `ApproxStrategy α A` is an approximation strategy for `α`: an
order-preserving ring homomorphism `α →+* ℝ`, together with an approximation in
`A` of the image of each element. It is what `FilteredReal α` is built from.
-/

@[expose] public section

namespace CGLean

/-- An approximation strategy for `α`: an order-preserving ring homomorphism into
`ℝ`, together with an approximation in `A` of the image of each element.

The homomorphism is determined by the order when `α` is archimedean, but the
approximations are a choice: the instance is the default strategy, and another
can be passed explicitly, as in `FilteredReal α (e := other)`.

The homomorphism is `Erased`: it lands in `ℝ` and is used only in proofs. -/
class ApproxStrategy (α : Type) [Ring α] [Preorder α] (A : outParam Type) [RealApprox A] where
  hom : Erased (α →+* ℝ)
  strictMono : StrictMono hom.out
  approx : α → A
  mem_approx : ∀ a, hom.out a ∈ approx a

namespace ApproxStrategy

variable {α A : Type} [Ring α] [Preorder α] [RealApprox A]

/-- The embedding into `ℝ`. -/
noncomputable def toRingHom (e : ApproxStrategy α A) : α →+* ℝ := e.hom.out

theorem mem_approx' (e : ApproxStrategy α A) (a : α) : e.toRingHom a ∈ e.approx a :=
  e.mem_approx a

theorem strictMono' (e : ApproxStrategy α A) : StrictMono e.toRingHom := e.strictMono

end ApproxStrategy

end CGLean
