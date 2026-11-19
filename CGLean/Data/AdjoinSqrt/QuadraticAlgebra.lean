module

public import CGLean.Data.AdjoinSqrt
public import Mathlib.Algebra.QuadraticAlgebra.Defs

/-!
# `R[√n]` as Mathlib's `QuadraticAlgebra`

Mathlib's `QuadraticAlgebra R a b` has elements `re + im ω` with `ω² = a + b ω`,
so `QuadraticAlgebra R n 0` is `R[√n]`: both are pairs, with the same
operations. This file records the equivalence of `R`-algebras.

The `R`-algebra structure on `AdjoinSqrt R n` is not an instance (see
`AdjoinSqrt.algebra`), so it is a local instance here, and the equivalence is
used with `letI := AdjoinSqrt.algebra`.
-/

@[expose] public section

namespace AdjoinSqrt

variable {R : Type} [CommSemiring R] {n : R}

attribute [local instance] AdjoinSqrt.algebra

/-- `R[√n]` is Mathlib's `QuadraticAlgebra R n 0`, coordinate by coordinate. -/
def quadraticAlgebraEquiv : AdjoinSqrt R n ≃ₐ[R] QuadraticAlgebra R n 0 where
  toFun x := ⟨x.a₁, x.aₙ⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by ext <;> simp [mul_assoc]
  map_add' x y := by ext <;> simp
  commutes' _ := by ext <;> rfl

@[simp] lemma quadraticAlgebraEquiv_apply_re (x : AdjoinSqrt R n) :
    (quadraticAlgebraEquiv x).re = x.a₁ := rfl

@[simp] lemma quadraticAlgebraEquiv_apply_im (x : AdjoinSqrt R n) :
    (quadraticAlgebraEquiv x).im = x.aₙ := rfl

@[simp] lemma quadraticAlgebraEquiv_symm_apply_a₁ (z : QuadraticAlgebra R n 0) :
    (quadraticAlgebraEquiv.symm z).a₁ = z.re := rfl

@[simp] lemma quadraticAlgebraEquiv_symm_apply_aₙ (z : QuadraticAlgebra R n 0) :
    (quadraticAlgebraEquiv.symm z).aₙ = z.im := rfl

end AdjoinSqrt
