import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith.Frontend
open Mathlib.Tactic.Ring

inductive Sign : Type
  | neg | zer | pos
deriving BEq, DecidableEq, Ord

open Sign

example : compare neg zer = Ordering.lt := by rfl
example : compare zer pos = Ordering.lt := by rfl
example : compare zer zer = Ordering.eq := by rfl
  
instance : LT Sign := ltOfOrd
instance : LE Sign := leOfOrd

example : neg < zer := by rfl
example : zer ≤ zer := by rfl

@[simps] instance : Neg Sign where
  neg s := match s with
    | .neg => .pos
    | .pos => .neg
    | .zer => .zer

instance : InvolutiveNeg Sign where
  neg_neg := by intro x; cases x <;> rfl

@[simps] instance : Mul Sign where
  mul s₁ s₂ := match s₁ with
    | .zer => .zer
    | .pos => s₂
    | .neg => -s₂

@[simps] instance : Zero Sign := ⟨zer⟩
@[simps] instance : One  Sign := ⟨pos⟩

instance : CommMonoidWithZero Sign where
  mul_assoc := by intros a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul   := by intros; rfl
  mul_one   := by intros a; cases a <;> rfl
  zero_mul  := by intros; rfl
  mul_zero  := by intros a; cases a <;> rfl
  mul_comm  := by intros a b; cases a <;> cases b <;> rfl

instance : CancelMonoidWithZero Sign where
  mul_left_cancel_of_ne_zero := by
    intros a b c ne0; cases a <;> cases b <;> cases c <;> simp <;> contradiction
  mul_right_cancel_of_ne_zero := by
    intros a b c ne0; cases a <;> cases b <;> cases c <;> simp <;> contradiction

class Signed (α : Type) where
  sign : α → Sign

open Signed

class SignCone (R : Type) [Ring R] extends Signed R where
  sign_zero : sign 0 = zer
  sign_one  : sign 1 = pos
  zero_sign : ∀ (a : R), sign a = 0 → a = 0
  sign_neg  : ∀ (a : R), sign (-a) = -sign a
  sign_plus : ∀ (a b : R), sign a ≠ neg → sign b ≠ neg → sign (a + b) ≠ neg
  sign_mult : ∀ (a b : R), sign (a * b) = sign a * sign b

@[simps] instance [Zero R] [Ord R] : Signed R where
  sign x := match compare x 0 with | .lt => .neg | .eq => .zer | .gt => .pos

@[simp] lemma sign_neg [LinearOrderedCommRing R] (x : R) : sign x = .neg ↔ x < 0 := by
  cases h: compare x 0 <;> simp [h] <;> simp [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at h <;> linarith

@[simp] lemma sign_zer [LinearOrderedCommRing R] (x : R) : sign x = .zer ↔ x = 0 := by
  cases h: compare x 0 <;> simp [h] <;> simp [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at h <;> linarith

@[simp] lemma sign_pos [LinearOrderedCommRing R] (x : R) : sign x = .pos ↔ x > 0 := by
  cases h: compare x 0 <;> simp [h] <;> simp [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at h <;> linarith

@[simp] lemma sign_nneg [LinearOrderedCommRing R] (x : R) : sign x ≠ neg ↔ x ≥ 0 := by
  cases h: compare x 0 <;> simp [h] <;> simp [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at h <;> linarith

instance [LinearOrderedCommRing R] : SignCone R where
  sign_zero := by rw [sign_zer]
  sign_one  := by rw [sign_pos]; linarith
  zero_sign := by
    intro a
    exact (sign_zer a).1

  sign_neg := by
    intro a
    cases h: sign a <;> (conv => right; simp) <;> simp only [sign_neg, sign_pos, sign_zer] at * <;> linarith

  sign_plus := by
    intro a b anneg bnneg
    cases h: sign a <;> (try contradiction) <;> rw [sign_nneg] at * <;> linarith

  sign_mult := by sorry

theorem AddCommGroup.TotalPositiveCone.mkOfSign [Ring R] [SignCone R] : AddCommGroup.TotalPositiveCone R := {
  nonneg := fun x => sign x ≠ neg
  zero_nonneg := by simp; rw [SignCone.sign_zero]; trivial
  add_nonneg  := by apply SignCone.sign_plus
  nonneg_antisymm := by
    intro a
    intros anneg anpos
    apply SignCone.zero_sign
    cases h: (sign a) <;> rw [SignCone.sign_neg, h] at anpos <;> trivial

  nonnegDecidable := by infer_instance
  nonneg_total := by
    simp [SignCone.sign_neg]; intro a; cases (sign a) <;> trivial
}

