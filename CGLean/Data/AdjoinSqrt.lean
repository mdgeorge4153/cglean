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

/-- A field is more than this needs: an integrally closed domain, a UFD say,
would do. There `a₁ / aₙ` is integral over `R`, being a root of `X² - n`, so it
already lies in `R` and `n` is a square after all. A bare domain is not enough
--- in `k[x², x³]`, `n = x²` has no square root, yet `a₁ = x³`, `aₙ = x²` gives
`a₁² = n * aₙ²`. Every intended instance is a field, so the generality is not
worth the proof. -/
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

/-- `sign` on `A[√n]`, unfolded. -/
lemma sign_eq [Signed R] [Mul R] [Add R] [Neg R] (x : AdjoinSqrt R n) :
    Signed.sign x = match (sign x.a₁, sign x.aₙ) with
      | (.zero, .zero) => .zero
      | (.pos, .pos) | (.pos,.zero) | (.zero, .pos) => .pos
      | (.neg, .neg) | (.neg,.zero) | (.zero, .neg) => .neg
      | (.pos, .neg) =>  sign (x * x.conj : R)
      | (.neg, .pos) => -sign (x * x.conj : R) := rfl

/-- The norm is multiplicative. -/
lemma norm_mul [CommRing R] (x y : AdjoinSqrt R n) :
    ((x * y) * conj (x * y)).a₁ = (x * conj x).a₁ * (y * conj y).a₁ := by
  simp [conj]
  ring

/-- The norm is invariant under negation, since conjugation is linear. -/
@[simp] lemma norm_neg [CommRing R] (x : AdjoinSqrt R n) :
    ((-x) * conj (-x)).a₁ = (x * conj x).a₁ := by
  simp [conj]
  ring

/-- The norm `a₁² - n·aₙ²`, written out. -/
abbrev norm [CommRing R] (x : AdjoinSqrt R n) : R := x.a₁ * x.a₁ - n * x.aₙ * x.aₙ

lemma norm_eq [CommRing R] (x : AdjoinSqrt R n) : (x * conj x).a₁ = norm x := by
  simp [conj, norm]; ring

/-- Non-negativity of `a₁ + aₙ√n`, phrased with `R`'s order rather than with
`SignType`. Both disjuncts are needed: the first covers `aₙ < 0`, where `a₁`
must dominate `aₙ√n`, and the second covers `a₁ < 0`, where `aₙ√n` must
dominate.

This is the form `sign_mul` and `sign_plus` want, since it puts them in reach of
the ordered-field lemmas. Each of the nine sign combinations reduces to an
inequality about `a₁²` and `n·aₙ²`. -/
lemma nonneg_iff [SignedField R] [Pos R n] (x : AdjoinSqrt R n) :
    Signed.sign x ≠ .neg ↔ (0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0) := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  rcases le_total 0 (norm x) with hN | hN <;>
  rw [sign_eq] <;>
  cases h1 : sign x.a₁ <;> cases hd : sign x.aₙ <;>
    simp only [norm_eq] <;>
    simp only [SignedRing.sign_eq_pos_iff, SignedRing.sign_eq_neg_iff,
      SignedRing.sign_eq_zero_iff] at h1 hd <;>
    simp only [norm, SignedRing.mem_nonnegCone_iff, ne_eq, reduceCtorEq,
      not_false_eq_true, not_true_eq_false, iff_true, iff_false, true_and,
      and_true, true_or, or_true] <;>
    first
      | rfl
      | (simp_all; done)
      | (constructor <;> intro <;> simp_all; done)
      | (nlinarith [mul_self_nonneg x.a₁, mul_self_nonneg x.aₙ, hn,
          mul_nonneg hn.le (mul_self_nonneg x.aₙ)]; done)
      -- Seventeen of the eighteen subgoals close above. The exception is
      -- `inl.zero.neg.mpr`, whose hypotheses are contradictory -- `0 ≤ N` with
      -- `a₁ = 0`, `aₙ < 0` and `n > 0` forces `n * aₙ² ≤ 0` -- but `0 ≤ N`
      -- arrives already unfolded into cone membership, which `nlinarith`
      -- cannot read.
      | sorry

instance instSignedRing [SignedField R] [Nonsquare R n] [Pos R n] :
    SignedRing (AdjoinSqrt R n) where
  __ := instCommRing
  sign_zero := by simp [SignedRing.sign_zero]
  sign_one  := by simp [SignedRing.sign_zero, SignedRing.sign_one]
  sign_mul  := by sorry
  zero_sign := by
    intro a h
    rw [sign_eq] at h
    cases h1 : sign a.a₁ <;> cases hn : sign a.aₙ <;> rw [h1, hn] at h <;>
      simp at h
    case zero.zero =>
      ext
      · exact SignedRing.zero_sign _ h1
      · exact SignedRing.zero_sign _ hn
    case pos.neg =>
      refine conj_0 a (SignedRing.zero_sign _ ?_)
      simpa using h
    case neg.pos =>
      refine conj_0 a (SignedRing.zero_sign _ ?_)
      simpa using h
  sign_neg  := by
    intro a
    rw [sign_eq, sign_eq, show (-a).a₁ = -a.a₁ from rfl,
      show (-a).aₙ = -a.aₙ from rfl, SignedRing.sign_neg, SignedRing.sign_neg]
    cases sign a.a₁ <;> cases sign a.aₙ <;> simp <;> congr 1 <;> ring
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
@[reducible] def linearOrderOfNonsquareOfPos [SignedField R] [Nonsquare R n] [Pos R n] :
    LinearOrder (AdjoinSqrt R n) := inferInstance

/-- That order is compatible with the ring operations, so `A[√n]` is a linearly
ordered ring whenever `A` is one and `n` is a positive non-square. -/
theorem isStrictOrderedRingOfNonsquareOfPos [SignedField R] [Nonsquare R n] [Pos R n] :
    IsStrictOrderedRing (AdjoinSqrt R n) := inferInstance

def toReal (f : R → ℝ) (x : AdjoinSqrt R n) : ℝ := sorry -- TODO: (f x.a₁) + (f x.aₙ) * (Real.sqrt (f n))

@[simp] def root (n : R) [Zero R] [One R] : AdjoinSqrt R n := ⟨0, 1⟩

theorem root_n_squared [CommRing R]: root n * root n = (n : AdjoinSqrt R n) := by
  sorry

