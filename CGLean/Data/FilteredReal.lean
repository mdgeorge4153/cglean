import Mathlib.Data.Real.Basic

structure ExampleAround (x : ℝ) where
  val : Nat
  ltx : x < val

instance (x₁ x₂ : ℝ) : HAdd (ExampleAround x₁) (ExampleAround x₂) (ExampleAround (x₁ + x₂)) where
  hAdd a₁ a₂ := {
    val := a₁.val + a₂.val
    ltx := by sorry
  }

def f (x : Nat) : ℝ := x

theorem f_additive : ∀ (x₁ x₂ : ℕ), f (x₁ + x₂) = f x₁ + f x₂
  := by sorry

structure WrappedExample (α : Type) where
  z  : Thunk Nat
  ex : ExampleAround (f z.get)

instance [Add α] : Add (WrappedExample α) where
  add a₁ a₂ := {
    z  := Thunk.mk fun () => a₁.z.get + a₂.z.get
    ex := a₁.ex + a₂.ex
  }

