module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Erased
public import Mathlib.Basic.Real.Basic
public import CGLean.Classes.RealApprox

/-!
# Approximating the elements of an ordered subring of real numbers

An instance of `ApproxStrategy α A` is a strategy for approximating the exact but
slow number representation `α` by a fast but imprecise representation `A`. It
requires that the comparison and ring operations on `α`, `A`, and `ℝ` are
compatible.

Since there is only one order embedding from `α` to `ℝ`, we think of `α` as a
subring of real numbers. However, even though the embedding of `α` is unique,
there may be many corresponding approximations. For example, intervals could be
rounded to different precisions, or represented by balls around a midpoint
instead of endpoints. An `instance` defines a default approximation for a type,
but it can be overridden with a different strategy (e.g. `FilteredReal α
(strategy := other)`).
-/

@[expose] public section

namespace CGLean

/-- An approximation strategy for `α`: an order embedding into
`ℝ`, together with an approximation in `A` of the image of each element.

The comparison and ring operations on `α`, `A`, and `ℝ` must be compatible:
 - `hom : α → ℝ` must be an order embedding so that `α` and `ℝ`
   operations are compatible
 - `A` must be a `RealApprox`, which means the operations on `A` and `ℝ` are
   compatible
 - `approx` must map an element of `α` to an approximation in `A` that actually
   contains it

The homomorphism is `Erased`: it lands in `ℝ` and is used only in proofs.
-/
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
