import Mathlib.Data.Sign
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Tactic.Linarith.Frontend

-- goals:
--   given a ordered structure, produce a signed structure
--   given a signed structure, produce an ordered structure

-- TODO: would like to unbundle [sign] from this structure, but I'm not sure how
-- to clearly add a requirement that [sign] is a MonoidWithZeroHom.
class Signcone (R : Type) [Ring R] where
  sign : R →*₀ SignType
  zero_sign : ∀ (a : R), sign a = 0 → a = 0
  sign_neg  : ∀ (a : R), sign (-a) = -sign a
  sign_plus : ∀ (a b : R), sign a ≠ .neg → sign b ≠ .neg → sign (a + b) ≠ .neg

open Signcone

instance [Ring R] [Signcone R] : Nontrivial R where
  exists_pair_ne := by
    exists 0, 1
    intro eq
    have h : sign (0:R) = sign (1:R) := by rw [eq]
    rw [map_zero, map_one] at h
    contradiction


instance [Ring R] [Signcone R]: LinearOrderedRing R := .mkOfPositiveCone {
  nonneg := fun (x:R) => sign x ≠ .neg
  zero_nonneg := by simp
  one_nonneg  := by simp
  add_nonneg  := by apply sign_plus
  nonneg_antisymm := by
    intros a anneg anpos
    apply zero_sign
    cases h: (sign a)
    rfl
    contradiction
    simp [Signcone.sign_neg] at anpos
    contradiction
  nonnegDecidable := by infer_instance
  nonneg_total := by
    simp [Signcone.sign_neg]; intro a; cases (sign a) <;> trivial

  mul_pos := by
    simp [Signcone.sign_neg]
    intros a b _ apos _ bpos
    rw [apos, bpos]; decide
}

-- TODO: don't need Comm, except it allows for linarith
instance [LinearOrderedCommRing R] : Signcone R where
  sign := signHom
  zero_sign := by unfold signHom; simp
  sign_neg  := by unfold signHom; simp [Left.sign_neg]
  sign_plus := by
    unfold signHom; simp
    intros a b anneg bnneg
    rw [sign_eq_neg_one_iff, lt_iff_not_le] at *
    simp at *
    linarith

