import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import CGLean.Algebra.Signed
import CGLean.Classes.RingOps

/-- Definitions ---------------------------------------------------------------/

-- Numbers of the form a₁ + aₙ√n
@[ext] structure AdjoinSqrt (R : Type) (n : R) where
  a₁ : R
  aₙ : R

namespace AdjoinSqrt

variable {R : Type} {n : R}

@[simps] instance instZero [Zero R] : Zero (AdjoinSqrt R n) where
  zero := ⟨0,0⟩

@[simps] instance instOne [One R] [Zero R] : One (AdjoinSqrt R n) where
  one := ⟨1,0⟩

@[simps] instance instAdd [Add R] : Add (AdjoinSqrt R n) where
  add x y := ⟨ x.a₁ + y.a₁, x.aₙ + y.aₙ ⟩

@[simps] instance instNeg [Neg R] : Neg (AdjoinSqrt R n) where
  neg x := ⟨ -x.a₁, -x.aₙ ⟩

@[simps] instance instMul [Mul R] [Add R] : Mul (AdjoinSqrt R n) where
  mul x y := ⟨x.a₁*y.a₁ + n*x.aₙ*y.aₙ, x.a₁*y.aₙ + x.aₙ*y.a₁⟩

/-- marker instance to encapsulate the above -/
instance ringOps [RingOps R]: RingOps (AdjoinSqrt R n) where

@[simps] instance instSMul [Mul R] : SMul R (AdjoinSqrt R n) where
  smul x y := ⟨x*y.a₁, x*y.aₙ⟩

@[simps] instance instCoe [Zero R] : Coe R (AdjoinSqrt R n) where
  coe x := ⟨x, 0⟩

abbrev conj [Neg R] (x : AdjoinSqrt R n) : AdjoinSqrt R n := ⟨x.a₁, -x.aₙ⟩

/-- The norm `x * conj x`, which lies in `R` rather than `R[√n]`. -/
@[simps] instance instCoeDepNorm [Mul R] [Add R] [Neg R] {x : AdjoinSqrt R n} :
    CoeDep (AdjoinSqrt R n) (x * conj x) R where
  coe := (x * conj x).a₁

@[simps] instance instInv [Zero R] [Neg R] [Mul R] [Add R] [Inv R]: Inv (AdjoinSqrt R n) where
  inv x := x.conj * (x * x.conj : R)⁻¹

open Signed

@[simps] instance instSigned [Signed R] [Mul R] [Add R] [Neg R]: Signed (AdjoinSqrt R n) where
  sign x :=
    match (sign x.a₁, sign x.aₙ) with
      | (.zero, .zero) => .zero
      | (.pos, .pos) | (.pos,.zero) | (.zero, .pos) => .pos
      | (.neg, .neg) | (.neg,.zero) | (.zero, .neg) => .neg
      | (.pos, .neg) =>  sign (x * x.conj : R) -- a + b√n > 0 ↔ a > -b√n ↔ a² > b²n (since both sides of inequality are pos)
      | (.neg, .pos) => -sign (x * x.conj : R) -- a + b√n > 0 ↔ a > -b√n ↔ a² < b²n (since both sides of inequality are neg)


/-- Theorems ------------------------------------------------------------------/

instance instAddSemigroup [AddSemigroup R]: AddSemigroup (AdjoinSqrt R n) where
  add_assoc := by intros; ext <;> apply add_assoc

instance instAddMonoid [AddMonoid R]: AddMonoid (AdjoinSqrt R n) where
  zero_add := by intros a; ext <;> simp
  add_zero := by intros; ext <;> simp
  nsmul := nsmulRec

instance instAddCommMonoid [AddCommMonoid R]: AddCommMonoid (AdjoinSqrt R n) := by
  constructor; intros; ext <;> apply add_comm

instance instNonUnitalAssocSemiring [NonUnitalNonAssocSemiring R]: NonUnitalNonAssocSemiring (AdjoinSqrt R n) := by
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

instance instNonUnitalSemiring [CommSemiring R]: NonUnitalSemiring (AdjoinSqrt R n) := by
  constructor; intros; ext <;> simp <;> ring

instance instSemiring [CommSemiring R]: Semiring (AdjoinSqrt R n) where
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp

instance instAlgebra [CommSemiring R]: Algebra R (AdjoinSqrt R n) where
  algebraMap := {
    toFun (x : R) := (x : AdjoinSqrt R n)
    map_one'  := rfl
    map_mul'  := by intros; ext <;> simp
    map_zero' := rfl
    map_add'  := by intros; ext <;> simp
  }
  commutes' := by intros; ext <;> simp <;> ring
  smul_def' := by intros; ext <;> simp

instance instRing [CommRing R]: Ring (AdjoinSqrt R n) where
  neg_add_cancel := by intros; ext <;> simp
  zsmul := zsmulRec

instance instCommRing [CommRing R]: CommRing (AdjoinSqrt R n) where
  mul_comm := by intros; ext <;> simp <;> ring

class Nonsquare (R : Type) [Mul R] (n : R) where
  not_square : ∀ x : R, x * x ≠ n

lemma cancel_neg [CommRing R] (a b : R) : a + -b = 0 -> a = b := by
  intro H
  have H' : a + -b + b = b := by rw [H]; exact zero_add b
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
    simp at H
    ext <;> simp_all
  case neg =>
    -- here's where we need division in this proof
    have H'' : (x.a₁ * x.aₙ⁻¹) * (x.a₁  * x.aₙ⁻¹) = n := by
      field_simp
      apply cancel_neg
      linear_combination H
    apply Nonsquare.not_square at H''
    exfalso; assumption

instance instField [Field R] [Nonsquare R n]: Field (AdjoinSqrt R n) where
  mul_inv_cancel := by
    intro x xne0
    -- the norm `x * conj x` is non-zero, which is `conj_0` contrapositive
    have hd : x.a₁ ^ 2 + -(n * x.aₙ ^ 2) ≠ 0 := fun h =>
      xne0 (conj_0 x (by simp [AdjoinSqrt.conj]; linear_combination h))
    ext <;> simp [AdjoinSqrt.conj]
    · field_simp
    · ring

  inv_zero := by
    ext <;> simp

  exists_pair_ne := by
    obtain ⟨ x, y, pf ⟩ := exists_pair_ne R
    exists x, y
    simp;
    assumption

  qsmul := _
  nnqsmul := _


example [CommRing R] (x y : AdjoinSqrt R n) : AdjoinSqrt R n := x - y

class Pos (R : Type) [Signed R] (n : R) where
  n_pos : sign n = .pos

open SignedRing

instance instSignedRing [SignedRing R] [Nonsquare R n] [Pos R n] :
    SignedRing (AdjoinSqrt R n) where
  __ := instCommRing
  sign_zero := by sorry
  sign_one  := by sorry
  sign_mul  := by sorry
  zero_sign := by sorry
  sign_neg  := by sorry
  sign_plus := by sorry

-- TODO
--   sign_zero := by simp [SignedRing.sign_zero]
--   sign_one := by simp [SignedRing.sign_zero, SignedRing.sign_one]
--   sign_neg := by
--     intros a
--     cases h1: sign a.a₁ <;> cases hn: sign a.aₙ <;> simp [SignedRing.sign_neg, h1, hn]
-- 
--   zero_sign := by
--     intro a
--     cases asign : sign (a.a₁) <;> cases bsign : sign (a.aₙ) <;> simp [asign, bsign]
--     case zero.zero => apply SignedRing.zero_sign at asign; apply SignedRing.zero_sign at bsign; ext <;> trivial
-- 
--     case neg.pos =>
--       intro h
--       rw [← SignedRing.sign_neg] at h
--       apply SignedRing.zero_sign at h
--       rw [neg_eq_zero] at h
--       apply conj_0
--       simp; trivial
-- 
--     case pos.neg =>
--       intro h
--       apply SignedRing.zero_sign at h
--       apply @conj_0 _ _ f.toField _ a
--       simp; trivial
-- 
--   sign_mul := sorry
--   sign_plus := sorry

/-- The order on `A[√n]`, obtained from its `SignedRing` structure via
`CGLean.Algebra.Signed`. -/
def linearOrderOfNonsquareOfPos [SignedRing R] [Nonsquare R n] [Pos R n] :
    LinearOrder (AdjoinSqrt R n) := inferInstance

/-- That order is compatible with the ring operations, so `A[√n]` is a linearly
ordered ring whenever `A` is one and `n` is a positive non-square. -/
def isStrictOrderedRingOfNonsquareOfPos [SignedRing R] [Nonsquare R n] [Pos R n] :
    IsStrictOrderedRing (AdjoinSqrt R n) := inferInstance

def toReal (f : R → ℝ) (x : AdjoinSqrt R n) : ℝ := sorry -- TODO: (f x.a₁) + (f x.aₙ) * (Real.sqrt (f n))

@[simp] def root (n : R) [Zero R] [One R] : AdjoinSqrt R n := ⟨0, 1⟩

theorem root_n_squared [CommRing R]: root n * root n = (n : AdjoinSqrt R n) := by
  sorry

