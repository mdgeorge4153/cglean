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

The `FilteredReal α` type is intended to be a drop-in replacement for a type
`α` that encapsulates a subset of the real numbers (which is provided using a
`Coe α ℝ` instance). It attempts to improve computational performance by
maintaining floating point intervals that bound the real values of the
encapsulated `α` values.

Operations that produce `FilteredReal α` values (like `+` and `*`) are evaluated
lazily on the underlying `α` type; the underlying operations on the `α` type are
only evaluated if and when the floating-point approximations are insufficiently
precise to evaluate comparisons (like `=` and `≤`).

NOTE: The current implementation is just a proof of concept based on the `Ray.Approx`
floating-point approximation library, which uses software floating point
instead of hardware floating point. It is therefore unlikely to provide an
actual performance improvement.

TODO: The hope is that we are only comparing numbers that are far away from each
other, but comparing equal points for equality is also likely to be a common
operation, and it will always fall back on the slow implementation (unless the
FP approximations are exact). It is worth looking into the paper on reference
equality optimizations (or even some kind of union-find structure) to see if
this can be improved.

## Implementation note

Since a `FilteredReal α` value must contain a proof that the floating-point
interval contains the real value, we can only implement operations if we know
that the `Coe α ℝ` instance is well-behaved. For example, to implement
`Zero (FilteredReal α)`, we not only need a `Zero α`, but we need to know that
`((0 : α) : ℝ) = 0 : ℝ`.

These requirements are encapsulated by the `Lawful<Op>Coe` classes (e.g.
`LawfulZeroCoe`, `LawfulAddCoe`, etc.).

TODO: these `Lawful*Coe` classes should maybe be `IsZeroHom coe`, `IsAddHom
coe`, etc. These unbundled classes are deprecated in mathlib; I should
understand why and whether there is something new that I should be using
instead. I don't see an easy way to reuse the bundled `*Hom` classes for this
purpose.

-/

open Pointwise

structure FilteredReal (α : Type) [Coe α ℝ] where
  value  : Thunk α
  range  : Around (value.get)

@[simps] instance [Coe α ℝ] : Coe (FilteredReal α) ℝ where
  coe x := x.value.get

/-! ## Zero -------------------------------------------------------------------/

class LawfulZeroCoe (α β : Type) [Zero α] [Zero β] [Coe α β] where
  cast_zero : ((0 : α) : β) = (0 : β)

@[simps] instance [Zero α] [Coe α ℝ] [LawfulZeroCoe α ℝ]: Zero (FilteredReal α) where
  zero := {
    value := (0 : α)
    range := ⟨0, by simp [Thunk.get, LawfulZeroCoe.cast_zero]⟩
  }

instance [Zero α] [Coe α ℝ] [LawfulZeroCoe α ℝ]: LawfulZeroCoe (FilteredReal α) ℝ where
  cast_zero := by simp [LawfulZeroCoe.cast_zero, Thunk.get]


/-! ## One --------------------------------------------------------------------/

class LawfulOneCoe (α β : Type) [One α] [One β] [Coe α β] where
  cast_one : ((1 : α) : β) = (1 : β)

@[simps] instance [One α] [Coe α ℝ] [LawfulOneCoe α ℝ] : One (FilteredReal α) where
  one := {
    value := Thunk.mk 1
    range := ⟨1, by simp [Thunk.get, LawfulOneCoe.cast_one]⟩
  }

instance [One α] [Coe α ℝ] [LawfulOneCoe α ℝ]: LawfulOneCoe (FilteredReal α) ℝ where
  cast_one := by simp [LawfulOneCoe.cast_one, Thunk.get]


/-! ## Add --------------------------------------------------------------------/

class LawfulAddCoe (α β : Type) [Add α] [Add β] [Coe α β] where
  cast_add : ∀ (x y : α), ((x : β) + (y : β)) = ((x + y : α) : β)

@[simps] instance [Add α] [Coe α ℝ] [LawfulAddCoe α ℝ] : Add (FilteredReal α) where
  add x y := {
    value := Thunk.mk (fun () => x.value.get + y.value.get)
    range := {
      i := x.range.i + y.range.i
      mem := by
        suffices (x.value.get : ℝ) + (y.value.get : ℝ) ∈ approx (x.range.i + y.range.i) by
          simpa [LawfulAddCoe.cast_add]
        mono
    }
  }

instance [Add α] [Coe α ℝ] [LawfulAddCoe α ℝ] : LawfulAddCoe (FilteredReal α) ℝ where
  cast_add := by simp [LawfulAddCoe.cast_add, Thunk.get]


/-! ## Sub --------------------------------------------------------------------/

class LawfulSubCoe (α β : Type) [Sub α] [Sub β] [Coe α β] where
  cast_sub : ∀ (x y : α), ((x : β) - (y : β)) = ((x - y : α) : β)

@[simps] instance [Sub α] [Coe α ℝ] [LawfulSubCoe α ℝ] : Sub (FilteredReal α) where
  sub x y := {
    value := Thunk.mk (fun () => x.value.get - y.value.get)
    range := {
      i := x.range.i - y.range.i
      mem := by
        suffices (x.value.get : ℝ) - (y.value.get : ℝ) ∈ approx (x.range.i - y.range.i) by
          simpa [LawfulSubCoe.cast_sub]
        mono
    }
  }

instance [Sub α] [Coe α ℝ] [LawfulSubCoe α ℝ] : LawfulSubCoe (FilteredReal α) ℝ where
  cast_sub := by simp [LawfulSubCoe.cast_sub, Thunk.get]


/-! ## Mul --------------------------------------------------------------------/

class LawfulMulCoe (α β : Type) [Mul α] [Mul β] [Coe α β] where
  cast_mul : ∀ (x y : α), ((x : β) * (y : β)) = ((x * y : α) : β)

@[simps] instance [Mul α] [Coe α ℝ] [LawfulMulCoe α ℝ] : Mul (FilteredReal α) where
  mul x y := {
    value := Thunk.mk (fun () => x.value.get * y.value.get)
    range := {
      i := x.range.i * y.range.i
      mem := by
        suffices (x.value.get : ℝ) * (y.value.get : ℝ) ∈ approx (x.range.i * y.range.i) by
          simpa [LawfulMulCoe.cast_mul]
        mono
    }
  }

instance [Mul α] [Coe α ℝ] [LawfulMulCoe α ℝ] : LawfulMulCoe (FilteredReal α) ℝ where
  cast_mul := by simp [LawfulMulCoe.cast_mul, Thunk.get]


/-! ## Equality ---------------------------------------------------------------/

instance same_value [Coe α ℝ] : Setoid (FilteredReal α) where
  r     := InvImage (· = ·) (λ x ↦ x.value.get)
  iseqv := InvImage.equivalence _ _ eq_equivalence

-- TODO: equality and comparisons

