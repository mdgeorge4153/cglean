import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.Order.Ring.Cone

-- goals:
--   given a ordered structure, produce a signed structure
--   given a signed structure, produce an ordered structure

variable {R : Type}

class Signed (R : Type) where
  sign : R → SignType

open Signed

-- TODO: start higher in the hierarchy - e.g. SignedGroup etc
class SignedRing (R : Type) extends CommRing R, Signed R where
 sign_zero : sign 0 = 0
 sign_one  : sign 1 = 1
 sign_mul  : ∀ (a b : R), sign (a * b) = sign a * sign b
 zero_sign : ∀ (a : R), sign a = 0 → a = 0
 sign_neg  : ∀ (a : R), sign (-a) = -sign a
 sign_plus : ∀ (a b : R), sign a ≠ .neg → sign b ≠ .neg → sign (a + b) ≠ .neg

/-- A field whose sign function is well behaved. Mathlib's own `Field` extends
both `CommRing` and `DivisionRing`, so the shared ring structure is flattened
rather than duplicated. -/
class SignedField (R : Type) extends SignedRing R, Field R

open SignedRing

def SignedRing.signHom [SignedRing R] : R →*₀ SignType := {
  toFun := sign
  map_zero' := SignedRing.sign_zero
  map_one'  := SignedRing.sign_one
  map_mul'  := SignedRing.sign_mul
}

instance instNontrivialOfSignedRing [SignedRing R] : Nontrivial R where
  exists_pair_ne := by
    exists 0, 1
    intro eq
    have h : sign (0:R) = sign (1:R) := by rw [eq]
    rw [SignedRing.sign_zero, SignedRing.sign_one] at h
    contradiction

/-- The non-negative elements of a signed ring, as a cone. This is the bridge
to Mathlib's order machinery: an order on `R` is built by designating this set
as its cone of non-negative elements. -/
def SignedRing.nonnegCone (R : Type) [SignedRing R] : RingCone R where
  carrier   := {x | sign x ≠ .neg}
  zero_mem' := by simp [Set.mem_setOf_eq, SignedRing.sign_zero]
  one_mem'  := by simp [Set.mem_setOf_eq, SignedRing.sign_one]
  add_mem'  := SignedRing.sign_plus _ _
  mul_mem'  := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, SignedRing.sign_mul] at *
    cases hsa : sign a <;> cases hsb : sign b <;> simp_all
  eq_zero_of_mem_of_neg_mem' := by
    intro a anneg anpos
    simp only [Set.mem_setOf_eq] at anneg anpos
    apply zero_sign
    cases h : sign a
    case zero => rfl
    case neg => exact absurd h anneg
    case pos => rw [SignedRing.sign_neg, h] at anpos; exact absurd rfl anpos

/-- The cone is maximal: every element is non-negative or its negation is. -/
instance SignedRing.nonnegCone.hasMemOrNegMem [SignedRing R] :
    HasMemOrNegMem (SignedRing.nonnegCone R) where
  mem_or_neg_mem a := by
    show sign a ≠ .neg ∨ sign (-a) ≠ .neg
    rw [SignedRing.sign_neg a]
    cases sign a <;> simp

/-- Decidable because `SignType` has decidable equality. This is what keeps the
derived order computable, and hence what an extracted binary can run on. -/
instance instDecidablePredMemNonnegCone [SignedRing R] :
    DecidablePred (· ∈ SignedRing.nonnegCone R) :=
  fun x => inferInstanceAs (Decidable (sign x ≠ .neg))

instance instLinearOrderOfSignedRing [SignedRing R] : LinearOrder R :=
  LinearOrder.mkOfAddGroupCone (SignedRing.nonnegCone R)

/-- `≤` on a signed ring is membership of the difference in the cone. True by
definition, but worth naming: every order fact below goes through it. -/
theorem SignedRing.le_iff [SignedRing R] {a b : R} :
    a ≤ b ↔ sign (b - a) ≠ .neg := Iff.rfl

/-- A positive element has positive sign. -/
theorem SignedRing.sign_of_pos [SignedRing R] {a : R} (h : 0 < a) : sign a = .pos := by
  obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp h
  rw [SignedRing.le_iff, sub_zero] at hle
  cases hs : sign a
  case neg => exact absurd hs hle
  case zero => exact absurd (SignedRing.zero_sign a hs).symm hne
  case pos => rfl

/-- `sign` and the order determine each other. These four turn sign reasoning
into inequality reasoning, where the ordered-field lemmas apply. -/
theorem SignedRing.nonneg_iff [SignedRing R] {a : R} : 0 ≤ a ↔ sign a ≠ .neg := by
  rw [SignedRing.le_iff, sub_zero]


theorem SignedRing.sign_eq_zero_iff [SignedRing R] {a : R} : sign a = .zero ↔ a = 0 :=
  ⟨SignedRing.zero_sign a, fun h => by rw [h]; exact SignedRing.sign_zero⟩

theorem SignedRing.sign_eq_pos_iff [SignedRing R] {a : R} : sign a = .pos ↔ 0 < a := by
  refine ⟨fun h => lt_of_le_of_ne (nonneg_iff.mpr (by rw [h]; decide)) ?_, sign_of_pos⟩
  intro h0
  rw [← h0, SignedRing.sign_zero] at h
  exact absurd h (by decide)

instance instIsOrderedRingOfSignedRing [SignedRing R] : IsOrderedRing R :=
  IsOrderedRing.mkOfCone (SignedRing.nonnegCone R)

instance instIsStrictOrderedRingOfSignedRing [SignedRing R] :
    IsStrictOrderedRing R := by
  refine IsStrictOrderedRing.of_mul_pos fun a b apos bpos => ?_
  have hprod : sign (a * b) = .pos := by
    rw [SignedRing.sign_mul, SignedRing.sign_of_pos apos, SignedRing.sign_of_pos bpos]
    rfl
  refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
  · rw [SignedRing.le_iff, sub_zero, hprod]; decide
  · intro h; rw [← h, SignedRing.sign_zero] at hprod; exact absurd hprod (by decide)

theorem SignedRing.sign_eq_neg_iff [SignedRing R] {a : R} : sign a = .neg ↔ a < 0 := by
  constructor
  · intro h
    have : sign (-a) = .pos := by rw [SignedRing.sign_neg, h]; rfl
    exact neg_pos.mp (sign_eq_pos_iff.mp this)
  · intro h
    have : sign (-a) = .pos := sign_eq_pos_iff.mpr (neg_pos.mpr h)
    rw [SignedRing.sign_neg] at this
    cases hs : sign a <;> rw [hs] at this <;> simp_all


/-- Conversely, a linearly ordered commutative ring has a well-behaved sign
function. -/
instance instSignedRingOfLinearOrderedCommRing
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] : SignedRing R where
  sign := SignType.sign
  sign_zero := sign_zero
  sign_one  := sign_one
  sign_mul  := sign_mul
  zero_sign := by simp
  sign_neg  := by exact Left.sign_neg
  sign_plus := by
    intro a b anneg bnneg
    simp only [SignType.neg_eq_neg_one, ne_eq, sign_eq_neg_one_iff, not_lt]
      at anneg bnneg ⊢
    exact add_nonneg anneg bnneg
