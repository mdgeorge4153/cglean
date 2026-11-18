module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Erased
public import Mathlib.Analysis.Real.Sqrt
public import CGLean.Classes.RealApprox

/-!
# Approximating the elements of an ordered subring of real numbers

An instance of `ApproxStrategy A α` is a strategy for approximating the exact but
slow number representation `A` by a fast but imprecise representation `α`. It
requires that the comparison and ring operations on `A`, `α`, and `ℝ` are
compatible.

Since there is only one order embedding from `A` to `ℝ`, we think of `A` as a
subring of real numbers. However, even though the embedding of `A` is unique,
there may be many corresponding approximations. For example, intervals could be
rounded to different precisions, or represented by balls around a midpoint
instead of endpoints. An `instance` defines a default approximation for a type,
but it can be overridden with a different strategy (e.g. `Filtered A
(strategy := other)`).
-/

@[expose] public section

namespace CGLean

/-- An approximation strategy for `A`: an order embedding into
`ℝ`, together with an approximation in `α` of the image of each element.

The comparison and ring operations on `A`, `α`, and `ℝ` must be compatible:
 - `hom : A → ℝ` must be an order embedding so that `A` and `ℝ`
   operations are compatible
 - `α` must be a `RealApprox`, which means the operations on `α` and `ℝ` are
   compatible
 - `approx` must map an element of `A` to an approximation in `α` that actually
   contains it

The homomorphism is `Erased`: it lands in `ℝ` and is used only in proofs.
-/
class ApproxStrategy (A : Type) [Ring A] [Preorder A] (α : outParam Type) [RealApprox α] where
  hom : Erased (A →+* ℝ)
  strictMono : StrictMono hom.out
  approx : A → α
  mem_approx : ∀ a, hom.out a ∈ approx a

namespace ApproxStrategy

variable {A α : Type} [Ring A] [Preorder A] [RealApprox α]

/-- The embedding into `ℝ`. -/
noncomputable def toRingHom (e : ApproxStrategy A α) : A →+* ℝ := e.hom.out

theorem mem_approx' (e : ApproxStrategy A α) (a : A) : e.toRingHom a ∈ e.approx a :=
  e.mem_approx a

theorem strictMono' (e : ApproxStrategy A α) : StrictMono e.toRingHom := e.strictMono

end ApproxStrategy

/-- An approximation of `√n`, for approximating `A[√n]`. -/
class ApproxSqrt {A α : Type} [Ring A] [Preorder A] [RealApprox α] [e : ApproxStrategy A α]
    (n : A) where
  sqrt : α
  mem_sqrt : Real.sqrt (e.toRingHom n) ∈ sqrt

end CGLean
