import Mathlib.Data.Real.Basic
import Ray.Approx.Interval.Around
import Ray.Approx.Interval.Mul

open Pointwise

structure FilteredReal (α : Type) [Coe α ℝ] where
  value  : Thunk α
  range  : Around (value.get)

instance same_value [Coe α ℝ] : Setoid (FilteredReal α) where
  r := InvImage (· = ·) (λ x ↦ x.value.get)
  iseqv := InvImage.equivalence _ _ eq_equivalence

@[simps] instance [Coe α ℝ] : Coe (FilteredReal α) ℝ where
  coe x := x.value.get

section Zero
  class LawfulZeroCoe (α β : Type) [Zero α] [Zero β] [Coe α β] where
    cast_zero : ((0 : α) : β) = (0 : β)

  @[simps] instance [Zero α] [Coe α ℝ] [LawfulZeroCoe α ℝ]: Zero (FilteredReal α) where
    zero := {
      value := (0 : α)
      range := {
        i := 0
        mem := by simp [Thunk.get, LawfulZeroCoe.cast_zero]
      }
    }

  instance [Zero α] [Coe α ℝ] [LawfulZeroCoe α ℝ]: LawfulZeroCoe (FilteredReal α) ℝ where
    cast_zero := by simp [LawfulZeroCoe.cast_zero, Thunk.get]

end Zero


section One
  class LawfulOneCoe (α β : Type) [One α] [One β] [Coe α β] where
    cast_one : ((1 : α) : β) = (1 : β)

  @[simps] instance [One α] [Coe α ℝ] [LawfulOneCoe α ℝ] : One (FilteredReal α) where
    one := {
      value := (1 : α)
      range := {
        i := 1
        mem := by simp [Thunk.get, LawfulOneCoe.cast_one]
      }
    }

  instance [One α] [Coe α ℝ] [LawfulOneCoe α ℝ]: LawfulOneCoe (FilteredReal α) ℝ where
    cast_one := by
      simp [LawfulOneCoe.cast_one, Thunk.get]
end One


section Add
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
end Add


section Sub
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

end Sub


section Mul
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

end Mul


