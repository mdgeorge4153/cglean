import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Mathport.Syntax
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith.Frontend
import Greeting.SignMathlib

open Mathlib.Tactic.Ring

/-- Definitions ---------------------------------------------------------------/

-- Numbers of the form a₁ + aₙ√n
@[ext] structure AdjoinSqrt (R : Type u) (n : R) where
  a₁ : R
  aₙ : R

namespace AdjoinSqrt

@[simps] instance [Zero R] : Zero (AdjoinSqrt R n) where
  zero := ⟨0,0⟩

@[simps] instance [One R] [Zero R] : One (AdjoinSqrt R n) where
  one := ⟨1,0⟩

@[simps] instance [Add R] : Add (AdjoinSqrt R n) where
  add x y := ⟨ x.a₁ + y.a₁, x.aₙ + y.aₙ ⟩

@[simps] instance [Neg R] : Neg (AdjoinSqrt R n) where
  neg x := ⟨ -x.a₁, -x.aₙ ⟩

@[simps] instance [Mul R] [Add R] : Mul (AdjoinSqrt R n) where
  mul x y := ⟨x.a₁*y.a₁ + n*x.aₙ*y.aₙ, x.a₁*y.aₙ + x.aₙ*y.a₁⟩

@[simps] instance [Mul R] : SMul R (AdjoinSqrt R n) where
  smul x y := ⟨x*y.a₁, x*y.aₙ⟩

@[simps] instance [Zero R] : Coe R (AdjoinSqrt R n) where
  coe x := ⟨x, 0⟩

abbrev conj [Neg R] (x : AdjoinSqrt R n) : AdjoinSqrt R n := ⟨x.a₁, -x.aₙ⟩

@[simps] instance [Mul R] [Add R] [Neg R] : CoeDep (AdjoinSqrt R n) (x * conj x) R where
  coe := (x * conj x).a₁

@[simps] instance [Zero R] [Neg R] [Mul R] [Add R] [Inv R]: Inv (AdjoinSqrt R n) where
  inv x := x.conj * (x * x.conj : R)⁻¹

open Signed

@[simps] instance [Signed R] [Mul R] [Add R] [Neg R]: Signed (AdjoinSqrt R n) where
  sign x :=
    match (sign x.a₁, sign x.aₙ) with
      | (.zero, .zero) => .zero
      | (.pos, .pos) | (.pos,.zero) | (.zero, .pos) => .pos
      | (.neg, .neg) | (.neg,.zero) | (.zero, .neg) => .neg
      | (.pos, .neg) =>  sign (x * x.conj : R) -- a + b√n > 0 ↔ a > -b√n ↔ a² > b²n (since both sides of inequality are pos)
      | (.neg, .pos) => -sign (x * x.conj : R) -- a + b√n > 0 ↔ a > -b√n ↔ a² < b²n (since both sides of inequality are neg)


/-- Theorems ------------------------------------------------------------------/

instance [AddSemigroup R]: AddSemigroup (AdjoinSqrt R n) where
  add_assoc := by intros; ext <;> apply add_assoc

instance [AddMonoid R]: AddMonoid (AdjoinSqrt R n) where
  zero_add := by intros a; ext <;> simp
  add_zero := by intros; ext <;> simp
  nsmul := nsmulRec

instance [AddCommMonoid R]: AddCommMonoid (AdjoinSqrt R n) := by
  constructor; intros; ext <;> apply add_comm

instance [NonUnitalNonAssocSemiring R]: NonUnitalNonAssocSemiring (AdjoinSqrt R n) := by
  constructor <;> intros <;> ext <;> simp [left_distrib, right_distrib, add_assoc] <;> try conv =>
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
  all_goals rw [add_zero]

instance [CommSemiring R]: NonUnitalSemiring (AdjoinSqrt R n) := by
  constructor; intros; ext <;> simp <;> ring

instance [CommSemiring R]: Semiring (AdjoinSqrt R n) where
  one_mul := by intros; ext <;> simp <;> ring
  mul_one := by intros; ext <;> simp <;> ring

instance [CommSemiring R]: Algebra R (AdjoinSqrt R n) where
  toFun (x : R) := x
  map_one'  := by rfl
  map_mul'  := by intros; ext <;> simp <;> ring
  map_zero' := by rfl
  map_add'  := by intros; ext <;> simp; ring
  commutes' := by intros; ext <;> simp <;> ring
  smul_def' := by intros; ext <;> simp <;> ring

instance [CommRing R]: Ring (AdjoinSqrt R n) where
  add_left_neg := by intros; ext <;> simp <;> ring
  zsmul := zsmulRec

instance [CommRing R]: CommRing (AdjoinSqrt R n) where
  mul_comm := by intros; ext <;> simp <;> ring

class Nonsquare (R : Type) [Mul R] (n : R) where
  not_square : ∀ x : R, x * x ≠ n

lemma cancel_neg [CommRing R] (a b : R) : a + -b = 0 -> a = b := by
  intro H
  have H' : a + -b + b = b
  . rw [H]; exact zero_add b
  rw [← H']
  ring

-- TODO: need this for a CommRing, not just a field
-- should be possible just using cancellation maybe? Might need a UFD or something
lemma conj_0 [Field R] [Nonsquare R n] : ∀ x : AdjoinSqrt R n, (x * x.conj : R) = 0 → x = 0 := by
  intros x H
  simp at H
  by_cases an0 : x.aₙ = 0
  case pos =>
    rw [an0] at H
    field_simp at H
    apply eq_zero_or_eq_zero_of_mul_eq_zero at H
    cases H <;> ext <;> simp <;> assumption
  case neg =>
    -- here's where we need division in this proof
    have H'' : (x.a₁ * x.aₙ⁻¹) * (x.a₁  * x.aₙ⁻¹) = n := by
      field_simp
      apply cancel_neg
      rw [←mul_assoc]
      assumption
    apply Nonsquare.not_square at H''
    exfalso; assumption

instance [Field R] [Nonsquare R n]: Field (AdjoinSqrt R n) where
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

  qsmul := _


example [CommRing R] (x y : AdjoinSqrt R n) : AdjoinSqrt R n := x - y

-- instance [Field R] [i: SignedRing R] [Nonsquare R n]: SignedRing (AdjoinSqrt R n) where
--   sign_zero := by
--     simp
--     cases h: sign (0:R) <;> simp
--     rw [SignedRing.sign_zero] at h
--   sign_one  := by simp; rw[SignCone.sign_zero, SignCone.sign_one]
--   zero_sign := by
--     intro a
--     simp
--     cases h1: sign a.a₁ <;> cases hn: sign a.aₙ <;> simp
--     case zero.zero =>
--       have a1zero : a.a₁ = 0 := by apply SignCone.zero_sign; trivial
--       have anzero : a.aₙ = 0 := by apply SignCone.zero_sign; trivial
--       intro; ext <;> trivial
--     case pos.neg =>
--       intro h
--       apply SignCone.zero_sign at h
--       apply conj_0 a
--       simp; trivial
--     case neg.pos =>
--       intro h
--       rw [←SignCone.sign_neg] at h
--       apply SignCone.zero_sign at h
--       rw [neg_eq_zero] at h
--       apply conj_0
--       simp; trivial
-- 
--   sign_neg := by
--     intros a
--     cases h1: sign a.a₁ <;> cases hn: sign a.aₙ <;> simp [SignCone.sign_neg, h1, hn] <;> try rfl
--     case neg.pos =>
--       rw [add_comm]
--       rw [neg_involutive]
-- 
-- 
