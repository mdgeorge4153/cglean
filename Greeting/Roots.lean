import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Mathport.Syntax
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Order.Ring.Defs

open Mathlib.Tactic.Ring

/-- Definitions ---------------------------------------------------------------/

-- Numbers of the form a₁ + aₙ√n
@[ext] structure AdjoinRoot (R : Type u) (n : R) where
  a₁ : R
  aₙ : R

namespace AdjoinRoot

instance [Zero R] : Zero (AdjoinRoot R n) where
  zero := ⟨0,0⟩
@[simp] theorem zero_1 [Zero R] : (0 : AdjoinRoot R n).a₁ = (0 : R) := by rfl
@[simp] theorem zero_n [Zero R] : (0 : AdjoinRoot R n).aₙ = (0 : R) := by rfl

instance [One R] [Zero R] : One (AdjoinRoot R n) where
  one := ⟨1,0⟩
@[simp] theorem one_1 [One R] [Zero R] : (1 : AdjoinRoot R n).a₁ = (1 : R) := by rfl
@[simp] theorem one_n [One R] [Zero R] : (1 : AdjoinRoot R n).aₙ = (0 : R) := by rfl

instance [Add R] : Add (AdjoinRoot R n) where
  add x y := ⟨ x.a₁ + y.a₁, x.aₙ + y.aₙ ⟩
@[simp] theorem add_1 [Add R] (x y : AdjoinRoot R n) : (x + y).a₁ = x.a₁ + y.a₁ := by rfl
@[simp] theorem add_n [Add R] (x y : AdjoinRoot R n) : (x + y).aₙ = x.aₙ + y.aₙ := by rfl

instance [Neg R] : Neg (AdjoinRoot R n) where
  neg x := ⟨ -x.a₁, -x.aₙ ⟩ 
@[simp] theorem neg_1   [Neg R] (x : AdjoinRoot R n) : (-x).a₁ = -x.a₁ := by rfl
@[simp] theorem neg_n   [Neg R] (x : AdjoinRoot R n) : (-x).aₙ = -x.aₙ := by rfl

instance [Mul R] [Add R] : Mul (AdjoinRoot R n) where
  mul x y := ⟨x.a₁*y.a₁ + n*x.aₙ*y.aₙ, x.a₁*y.aₙ + x.aₙ*y.a₁⟩
@[simp] theorem mul_1 [Mul R] [Add R] (x y : AdjoinRoot R n) : (x * y).a₁ = x.a₁*y.a₁ + n*x.aₙ*y.aₙ := by rfl
@[simp] theorem mul_n [Mul R] [Add R] (x y : AdjoinRoot R n) : (x * y).aₙ = x.a₁*y.aₙ + x.aₙ*y.a₁   := by rfl

instance [Mul R] : SMul R (AdjoinRoot R n) where
  smul x y := ⟨x*y.a₁, x*y.aₙ⟩
@[simp] theorem smul_1 [Mul R] (x : R) (y : AdjoinRoot R n) : (x • y).a₁ = x*y.a₁ := by rfl
@[simp] theorem smul_n [Mul R] (x : R) (y : AdjoinRoot R n) : (x • y).aₙ = x*y.aₙ := by rfl

instance coe [Zero R] : Coe R (AdjoinRoot R n) where
  coe x := ⟨x, 0⟩
@[simp] theorem coe_1 [Zero R] (x : R): (x : AdjoinRoot R n).a₁ = x := by rfl
@[simp] theorem coe_n [Zero R] (x : R): (x : AdjoinRoot R n).aₙ = 0 := by rfl

abbrev conj [Neg R] (x : AdjoinRoot R n) : AdjoinRoot R n := ⟨x.a₁, -x.aₙ⟩

instance [Mul R] [Add R] [Neg R] : CoeDep (AdjoinRoot R n) (x * conj x) R where
  coe := (x * conj x).a₁ 

instance [Zero R] [Neg R] [Mul R] [Add R] [Inv R]: Inv (AdjoinRoot R n) where
  inv x := x.conj * (x * x.conj : R)⁻¹
@[simp] theorem inv_1 [Zero R] [Neg R] [Mul R] [Add R] [Inv R] (x : AdjoinRoot R n) : x⁻¹.a₁ = (x.conj * (x * x.conj : R)⁻¹).a₁ := by rfl
@[simp] theorem inv_n [Zero R] [Neg R] [Mul R] [Add R] [Inv R] (x : AdjoinRoot R n) : x⁻¹.aₙ = (x.conj * (x * x.conj : R)⁻¹).aₙ := by rfl


-- inductive Sign : Type
--   | neg | pos | zer
-- 
-- instance : Neg Sign where
--   neg s := match s with
--     | Sign.neg => Sign.pos
--     | Sign.pos => Sign.neg
--     | Sign.zer => Sign.zer
-- 
-- class Signed (α : Type) where
--   sign : α → Sign
-- 
-- open Signed
-- 
-- instance [Signed R] [Mul R] [Add R] [Neg R]: Signed (AdjoinRoot R n) where
--   sign x :=
--     match (sign x.a₁, sign x.aₙ) with
--       | (.zer, .zer) => .zer
--       | (.pos, .pos) | (.pos,.zer) | (.zer, .pos) => .pos
--       | (.neg, .neg) | (.neg,.zer) | (.zer, .neg) => .neg
--       | (.pos, .neg) =>  sign (x * x.conj : R) -- a + b√n > 0 ↔ a > -b√n ↔ a² > b²n (since both sides of inequality are pos)
--       | (.neg, .pos) => -sign (x * x.conj : R) -- a + b√n > 0 ↔ a > -b√n ↔ a² < b²n (since both sides of inequality are neg)


/-- Theorems ------------------------------------------------------------------/

instance [AddSemigroup R]: AddSemigroup (AdjoinRoot R n) where
  add_assoc := by intros; ext <;> simp <;> apply add_assoc

instance [AddMonoid R]: AddMonoid (AdjoinRoot R n) where
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp

instance [AddCommMonoid R]: AddCommMonoid (AdjoinRoot R n) := by
  constructor; intros; ext <;> apply add_comm

instance [NonUnitalNonAssocSemiring R]: NonUnitalNonAssocSemiring (AdjoinRoot R n) := by
  constructor <;> intros <;> ext <;> simp [left_distrib, right_distrib, add_assoc] <;> conv =>
    -- this proof just involves finding the right places to commute things. We
    -- should just hand this off to something like `ring`, but I don't think
    -- there are nice tactics like that for things higher in the hierarchy
    --
    -- we use all_goals so that the two goals are focused on the same part of
    -- the expression as you navigate through the proof
    congr
    all_goals rhs
    rw [add_comm, add_assoc]
    all_goals rhs
    rw [add_comm]
    all_goals rfl


instance [CommSemiring R]: NonUnitalSemiring (AdjoinRoot R n) := by
  constructor; intros; ext <;> simp <;> ring

instance [CommSemiring R]: Semiring (AdjoinRoot R n) where
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp

instance [CommSemiring R]: Algebra R (AdjoinRoot R n) where
  toFun (x : R) := x
  map_one'  := by rfl
  map_mul'  := by intros; ext <;> simp
  map_zero' := by rfl
  map_add'  := by intros; ext <;> simp
  commutes' := by intros; ext <;> simp <;> apply mul_comm
  smul_def' := by intros; ext <;> simp

instance [CommRing R]: Ring (AdjoinRoot R n) where
  add_left_neg := by intros; ext <;> simp

instance [CommRing R]: CommRing (AdjoinRoot R n) where
  mul_comm := by intros; ext <;> simp <;> ring

class Nonsquare (R : Type) [Mul R] (n : R) where
  not_square : ∀ x : R, x * x ≠ n

lemma cancel_neg [CommRing R] (a b : R) : a + -b = 0 -> a = b := by
  intro H
  have H' : a + -b + b = b
  . rw [H]; exact zero_add b
  rw [← H']
  ring

lemma conj_0 [Field R] [Nonsquare R n] : ∀ x : AdjoinRoot R n, (x * x.conj : R) = 0 → x = 0 := by
  intros x H
  simp at H
  by_cases an0 : x.aₙ = 0
  case pos =>
    rw [an0] at H
    field_simp at H
    apply eq_zero_or_eq_zero_of_mul_eq_zero at H
    cases H <;> ext <;> simp <;> assumption
  case neg =>
    have H'' : (x.a₁ * x.aₙ⁻¹) * (x.a₁  * x.aₙ⁻¹) = n := by
      field_simp
      apply cancel_neg
      rw [←mul_assoc]
      assumption
    apply Nonsquare.not_square at H''
    exfalso; assumption

instance [Field R] [Nonsquare R n]: Field (AdjoinRoot R n) where
  mul_inv_cancel := by
    -- TODO: this proof is a bit nasty I think
    intros x xne0; ext
    field_simp
    rw [div_eq_mul_inv]
    apply mul_inv_cancel
    intro H
    apply xne0
    apply conj_0
    rw [←H]
    simp

    -- an
    field_simp
    left
    ring

  inv_zero := by
    ext <;> simp

  exists_pair_ne := by
    obtain ⟨ x, y, pf ⟩ := exists_pair_ne R
    exists x, y
    simp;
    assumption



example [CommRing R] (x y : AdjoinRoot R n) : AdjoinRoot R n := x - y

