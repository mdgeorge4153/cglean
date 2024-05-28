/-
Copyright (c) 2024 Michael D. George. All rights reserved.
TODO: choose a license
Author: Michael D. George.
-/
import Mathlib.Data.Real.Basic
import Ray.Approx.Interval.Around
import Ray.Approx.Interval.Mul

/-!
# Filtered Real Numbers

The `FilteredEmbedding f` type is intended to be a drop-in replacement for a
type `α` that encapsulates a subset of the real numbers (which is provided by
`f : α → ℝ`). It attempts to improve computational performance by maintaining
floating point intervals that bound the real values of the encapsulated `α`
values.

Operations that produce `FilteredEmbedding f` values (like `+` and `*`) are
evaluated lazily on the underlying `α` type; the underlying operations on the
`α` type are only evaluated if and when the floating-point approximations are
insufficiently precise to evaluate comparisons (like `=` and `≤`).

NOTE: The current implementation is just a proof of concept based on the
`Ray.Approx` floating-point approximation library, which uses software floating
point instead of hardware floating point. It is therefore unlikely to provide
an actual performance improvement.

TODO: The hope is that we are only comparing numbers that are far away from each
other, but comparing equal points for equality is also likely to be a common
operation, and it will always fall back on the slow implementation (unless the
FP approximations are exact). It is worth looking into the paper on reference
equality optimizations (or even some kind of union-find structure) to see if
this can be improved.

## Implementation note

Since a `FilteredEmbedding f` value must contain a proof that the
floating-point interval contains the real value, we can only implement
operations if we know that `f` is well-behaved. For example, to implement `Zero
(FilteredEmbedding f)`, we not only need a `Zero α`, but we need to know that
`f 0 = 0` (i.e. that `f` is a 0-homomorphism).

This means that when constructing your `FilteredEmbedding f`, `f` should be a
homomorphism for the operations that you want to be able to perform. For
example, if you need an instance of `Zero`, you need `f` to be a `ZeroHom`:

```
def exampleWithZero : ZeroHom example ℝ where
  toFun x   := ...
  map_zero' := ...

abbrev ExampleFiltered : Type := FilteredEmbedding exampleWithZero

example : ExampleFiltered := 0
```

-/

open Pointwise

attribute [simp] Thunk.get

structure FilteredEmbedding (f : α → ℝ) where
  value  : Thunk α
  range  : Around (f value.get)

@[simp] def FilteredEmbedding.toReal (x : FilteredEmbedding f) : ℝ := f x.value.get

/-! ## Zero -------------------------------------------------------------------/

@[simps] instance [Zero α] [FunLike F α ℝ] [ZeroHomClass F α ℝ] (f : F): Zero (FilteredEmbedding f) where
  zero := {
    value := (0 : α)
    range := ⟨0, by simp [map_zero]⟩
  }

def toZeroHom [Zero α] [FunLike F α ℝ] [ZeroHomClass F α ℝ] (f : F): ZeroHom (FilteredEmbedding f) ℝ where
  toFun     := FilteredEmbedding.toReal
  map_zero' := by simp

def ratToReal : ZeroHom ℚ ℝ where
  toFun q   := q
  map_zero' := by simp

abbrev FilteredRat : Type := FilteredEmbedding ratToReal

example : FilteredRat := 0

/-! ## One --------------------------------------------------------------------/

@[simps] instance [One α] [FunLike F α ℝ] [OneHomClass F α ℝ] (f : F): One (FilteredEmbedding f) where
  one := {
    value := (1 : α)
    range := ⟨1, by simp [map_one]⟩
  }

def toOneHom [One α] [FunLike F α ℝ] [OneHomClass F α ℝ] (f : F): OneHom (FilteredEmbedding f) ℝ where
  toFun    := FilteredEmbedding.toReal
  map_one' := by simp

/-! ## Add --------------------------------------------------------------------/

@[simps] instance [Add α] [FunLike F α ℝ] [AddHomClass F α ℝ] (f : F): Add (FilteredEmbedding f) where
  add x y := {
    value := x.value.get + y.value.get
    range := ⟨x.range.i + y.range.i, by simp [map_add]; mono⟩
  }

def toAddHom [Add α] [FunLike F α ℝ] [AddHomClass F α ℝ] (f : F): AddHom (FilteredEmbedding f) ℝ where
  toFun := FilteredEmbedding.toReal
  map_add' := by simp

/-! ## Mul --------------------------------------------------------------------/

@[simps] instance [Mul α] [FunLike F α ℝ] [MulHomClass F α ℝ] (f : F): Mul (FilteredEmbedding f) where
  mul x y := {
    value := x.value.get * y.value.get
    range := ⟨x.range.i * y.range.i, by simp [map_mul]; mono⟩
  }

def toMulHom [Mul α] [FunLike F α ℝ] [MulHomClass F α ℝ] (f : F): MulHom (FilteredEmbedding f) ℝ where
  toFun := FilteredEmbedding.toReal
  map_mul' := by simp


/-! ## Equality ---------------------------------------------------------------/

instance same_value : Setoid (FilteredEmbedding f) where
  r     := InvImage (· = ·) (λ x ↦ x.value.get)
  iseqv := InvImage.equivalence _ _ eq_equivalence

-- TODO: equality and comparisons

