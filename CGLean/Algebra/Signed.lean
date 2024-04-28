import Mathlib.Data.Sign
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Tactic.Linarith.Frontend

-- goals:
--   given a ordered structure, produce a signed structure
--   given a signed structure, produce an ordered structure

class Signed (R : Type) where
  sign : R → SignType

open Signed

-- TODO: start higher in the hierarchy - e.g. SignedGroup etc
class SignedRing (R : Type) extends Ring R, Signed R where
 sign_zero : sign 0 = 0
 sign_one  : sign 1 = 1
 sign_mul  : ∀ (a b : R), sign (a * b) = sign a * sign b
 zero_sign : ∀ (a : R), sign a = 0 → a = 0
 sign_neg  : ∀ (a : R), sign (-a) = -sign a
 sign_plus : ∀ (a b : R), sign a ≠ .neg → sign b ≠ .neg → sign (a + b) ≠ .neg

open SignedRing

def SignedRing.signHom [SignedRing R] : R →*₀ SignType := {
  toFun := sign
  map_zero' := SignedRing.sign_zero
  map_one'  := SignedRing.sign_one
  map_mul'  := SignedRing.sign_mul
}

instance [SignedRing R] : Nontrivial R where
  exists_pair_ne := by
    exists 0, 1
    intro eq
    have h : sign (0:R) = sign (1:R) := by rw [eq]
    rw [SignedRing.sign_zero, SignedRing.sign_one] at h
    contradiction

instance [SignedRing R] : LinearOrderedRing R := .mkOfPositiveCone {
  nonneg := fun (x:R) => sign x ≠ .neg
  zero_nonneg := by simp [SignedRing.sign_zero]
  add_nonneg  := by apply sign_plus
  nonneg_antisymm := by
    intros a anneg anpos
    apply zero_sign
    cases h: (sign a)
    case a.zero => rfl
    case a.neg => contradiction
    case a.pos => simp [SignedRing.sign_neg] at anpos; contradiction

  one_nonneg := by simp [SignedRing.sign_one]
  mul_pos := by
    simp [SignedRing.sign_neg]
    intros a b _ apos _ bpos
    rw [SignedRing.sign_mul, apos, bpos]; decide
  nonnegDecidable := by infer_instance
  nonneg_total := by
    simp [SignedRing.sign_neg]; intro a; cases (sign a) <;> trivial
}

-- TODO: I think we don't need Comm, except it allows for linarith
instance [LinearOrderedCommRing R] : SignedRing R where
  sign := SignType.sign
  sign_zero := sign_zero
  sign_one  := sign_one
  sign_mul  := sign_mul
  zero_sign := by simp
  sign_neg  := by exact Left.sign_neg
  sign_plus := by
    simp
    intros a b anneg bnneg
    rw [sign_eq_neg_one_iff, lt_iff_not_le] at *
    simp at *
    linarith

