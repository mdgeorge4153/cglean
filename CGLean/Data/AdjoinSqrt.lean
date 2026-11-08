import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Cone
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

/-- `R` acting on `A[√n]` componentwise. Not an instance: for `R = ℕ`, `ℤ` or
`ℚ` it would compete with the action every semiring, ring or field already has,
which agrees with this one only up to a proof. -/
@[reducible, simps] def componentSMul [Mul R] : SMul R (AdjoinSqrt R n) where
  smul x y := ⟨x*y.a₁, x*y.aₙ⟩

@[simps] instance instCoe [Zero R] : Coe R (AdjoinSqrt R n) where
  coe x := ⟨x, 0⟩

section Ops
variable [Add R] [Mul R] [Sub R] [Neg R]

@[simps] def conj (x : AdjoinSqrt R n) : AdjoinSqrt R n := ⟨x.a₁, -x.aₙ⟩
def norm (x : AdjoinSqrt R n) : R := x.a₁ * x.a₁ - n * x.aₙ * x.aₙ

@[simps] instance instInv [Inv R] [Zero R]: Inv (AdjoinSqrt R n) where
  inv x := x.conj * x.norm⁻¹
end Ops

/-- The element `√n` itself. -/
@[simp] def root [Zero R] [One R] (n : R): AdjoinSqrt R n := ⟨0, 1⟩

/-- `a₁ + aₙ√n ≥ 0` if either `a₁ ≥ 0` and `a₁` dominates, or `aₙ ≥ 0` and `aₙ` dominates -/
def IsNonneg [LE R] [Mul R] [Zero R] [Add R] [Sub R] (x : AdjoinSqrt R n) : Prop :=
  (0 ≤ x.a₁ ∧ 0 ≤ (norm x : R)) ∨ (0 ≤ x.aₙ ∧ (norm x : R) ≤ 0)

-- TODO: efficient comparison. Reinstate `cmpZero`, prove
-- `cmpZero x = .lt ↔ ¬ IsNonneg x` and `cmpZero x = .eq ↔ x = 0`, and override
-- `compare` (and decidability) in `instLinearOrder` with it. The earlier
-- proofs (`cmpZero_spec`, `lt_iff_cmpZero`, the hand-built instance) are in ee3b01f.
/-
/-- We compare with zero using a faster technique that avoids computing the norm sometimes -/
def cmpZero [Ord R] [Zero R] [Mul R] (x : AdjoinSqrt R n) : Ordering :=
  match compare x.a₁ 0, compare x.aₙ 0 with
  | .eq, o => o
  | o, .eq => o
  | .gt, .gt => .gt
  | .lt, .lt => .lt
  | .gt, .lt => compare (x.a₁ * x.a₁) (n * x.aₙ * x.aₙ)
  | .lt, .gt => compare (n * x.aₙ * x.aₙ) (x.a₁ * x.a₁)
-/

/-  Theorems ------------------------------------------------------------------/

instance instAddSemigroup [AddSemigroup R]: AddSemigroup (AdjoinSqrt R n) where
  add_assoc := by intros; ext <;> apply add_assoc

instance instAddMonoid [AddMonoid R]: AddMonoid (AdjoinSqrt R n) where
  zero_add := by intros a; ext <;> simp
  add_zero := by intros; ext <;> simp
  nsmul := nsmulRec

instance instAddCommMonoid [AddCommMonoid R]: AddCommMonoid (AdjoinSqrt R n) := by
  constructor; intros; ext <;> apply add_comm

instance instNonUnitalAssocSemiring [NonUnitalNonAssocSemiring R]: NonUnitalNonAssocSemiring (AdjoinSqrt R n) := by
  constructor <;> intros <;> ext <;> simp [left_distrib, right_distrib] <;> ac_rfl

instance instNonUnitalSemiring [CommSemiring R]: NonUnitalSemiring (AdjoinSqrt R n) := by
  constructor; intros; ext <;> simp <;> ring

instance instSemiring [CommSemiring R]: Semiring (AdjoinSqrt R n) where
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp

/-- `A[√n]` is an `A`-algebra. Not an instance, for the same reason as
`componentSMul`; bring it into scope with `letI := AdjoinSqrt.algebra`. -/
abbrev algebra [CommSemiring R] : Algebra R (AdjoinSqrt R n) where
  toSMul := componentSMul
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

/-- A field is more than this needs: an integrally closed domain, a UFD say,
would do. There `a₁ / aₙ` is integral over `R`, being a root of `X² - n`, so it
already lies in `R` and `n` is a square after all. A bare domain is not enough
--- in `k[x², x³]`, `n = x²` has no square root, yet `a₁ = x³`, `aₙ = x²` gives
`a₁² = n * aₙ²`. Every intended instance is a field, so the generality is not
worth the proof. -/
lemma norm_0 [Field R] [nonsquare: Fact (¬ IsSquare n)] {x : AdjoinSqrt R n} (H: x.norm = 0): x = 0 := by
  simp [norm] at H
  if x.aₙ = 0 then
    ext <;> simp_all
  else
    -- here's where we need division in this proof
    exact absurd ⟨x.a₁ / x.aₙ, by field_simp; linear_combination -H⟩ nonsquare.out

instance instField [Field R] [Fact (¬ IsSquare n)]: Field (AdjoinSqrt R n) where
  mul_inv_cancel := by
    intro x xne0
    have hd : norm x ≠ 0 := fun h => xne0 (norm_0 h)
    ext <;> simp <;> field_simp <;> simp [norm]; ring

  inv_zero := by
    ext <;> simp

  exists_pair_ne := by
    obtain ⟨ x, y, pf ⟩ := exists_pair_ne R
    exists x, y
    simp;
    assumption

  qsmul := _
  nnqsmul := _


/- ## Conj and norm -/

section Conj

variable [CommRing R]

lemma norm_mul (x y : AdjoinSqrt R n) :
    norm (x * y) = norm x * norm y := by
  simp [norm]; ring

/-- Negation doesn't change the norm. -/
lemma norm_neg (x : AdjoinSqrt R n) : norm (-x) = norm x := by simp [norm]

end Conj

/-! ## Order

`A[√n]` is ordered by designating its non-negative elements, the *positive
cone*, as Mathlib does for any ordered ring. Membership is decided in `A`:
`a₁ + aₙ√n ≥ 0` when a non-negative part dominates the other, which, since
`n > 0`, is a comparison of squares, i.e. the sign of the norm. -/

section Order

/-- The non-negative elements are closed under multiplication. Each case turns
on comparing `(a₁*b₁)²` with `(n*aₙ*bₙ)²`, whose difference factors
through the two norms. -/
lemma nonneg_mul [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [pos: Fact (n > 0)] {x y : AdjoinSqrt R n}
    (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x*y) := by
  have ha : (x*y).a₁ = x.a₁*y.a₁ + n*x.aₙ*y.aₙ := rfl
  have hb : (x*y).aₙ = x.a₁*y.aₙ + x.aₙ*y.a₁ := rfl
  have hn : 0 < n := pos.elim
  rcases hx with ⟨hx1, hxN⟩ | ⟨hx1, hxN⟩ <;> rcases hy with ⟨hy1, hyN⟩ | ⟨hy1, hyN⟩
  · left
    refine ⟨?_, by rw [norm_mul x y]; exact mul_nonneg hxN hyN⟩
    simp only [norm] at *
    nlinarith [
      mul_nonneg hx1 hy1,
      mul_nonneg hn.le (mul_self_nonneg x.aₙ)
    ]
  · right
    refine ⟨?_, by rw [norm_mul x y]; exact mul_nonpos_of_nonneg_of_nonpos hxN hyN⟩
    simp only [norm] at *
    nlinarith [
      mul_nonneg hx1 hy1,
      mul_nonneg hxN (mul_self_nonneg y.aₙ),
      mul_nonneg (mul_self_nonneg x.aₙ) (neg_nonneg.mpr hyN)
    ]
  · right
    refine ⟨?_, by rw [norm_mul x y]; exact mul_nonpos_of_nonpos_of_nonneg hxN hyN⟩
    simp only [norm] at *
    nlinarith [
      mul_nonneg hx1 hy1,
      mul_nonneg hyN (mul_self_nonneg x.aₙ),
      mul_nonneg (mul_self_nonneg y.aₙ) (neg_nonneg.mpr hxN)
    ]
  · left
    refine ⟨?_, by rw [norm_mul x y]; exact mul_nonneg_of_nonpos_of_nonpos hxN hyN⟩
    simp only [norm] at *
    nlinarith [
      mul_nonneg (mul_nonneg hn.le hx1) hy1
    ]

variable [Field R] [LinearOrder R]

/-- utility for the proof of nonneg_add; we prove (x + y)(multiplier x y) is
  nonnegative, and conclude that (x+y) is nonnegative -/
def multiplier (x y : AdjoinSqrt R n) : AdjoinSqrt R n := ⟨|x.a₁| + |y.a₁|, |x.aₙ| + |y.aₙ|⟩

/-- values in the NE quadrant are obviously positive -/
lemma nonneg_of_coeffs_nonneg { x : AdjoinSqrt R n } ( h₁ : 0 ≤ x.a₁) (hₙ : 0 ≤ x.aₙ) : IsNonneg x := by
  rcases le_total 0 x.norm <;> unfold IsNonneg <;> aesop

/-- The nonnegative elements fall into the four quadrants ENE, ESE, NNW, NNE -/
lemma IsNonneg.wedges {x : AdjoinSqrt R n} (hx : IsNonneg x) :
    (0 ≤ x.a₁ ∧ 0 ≤ x.aₙ ∧ 0 ≤ norm x) ∨ (0 ≤ x.a₁ ∧ x.aₙ ≤ 0 ∧ 0 ≤ norm x) ∨
    (0 ≤ x.a₁ ∧ 0 ≤ x.aₙ ∧ norm x ≤ 0) ∨ (x.a₁ ≤ 0 ∧ 0 ≤ x.aₙ ∧ norm x ≤ 0) := by
  rcases hx with ⟨h1, hN⟩ | ⟨hn, hN⟩
  · rcases le_total 0 x.aₙ with hn | hn <;> tauto
  · rcases le_total 0 x.a₁ with h1 | h1 <;> tauto

variable [IsStrictOrderedRing R]

/-- Every element is non-negative or non-positive. -/
lemma nonneg_or_neg_nonneg (x : AdjoinSqrt R n) : IsNonneg x ∨ IsNonneg (-x) := by
  unfold IsNonneg; rw [norm_neg]
  rcases le_total 0 (norm x) with h | h
    <;> rcases le_total 0 x.a₁ with ha | ha
    <;> rcases le_total 0 x.aₙ with hb | hb
    <;> aesop

/-- If the multiplier is 0, the two factors are 0 --/
lemma eq_zero_of_multiplier_eq_zero {x y : AdjoinSqrt R n} (h : multiplier x y = 0) : (x = 0) ∧ (y = 0) := by
  injection h with h1 hn
  obtain ⟨_,_⟩ : |x.a₁| = 0 ∧ |y.a₁| = 0 := (add_eq_zero_iff_of_nonneg (abs_nonneg x.a₁) (abs_nonneg y.a₁)).mp h1
  obtain ⟨_,_⟩ : |x.aₙ| = 0 ∧ |y.aₙ| = 0 := (add_eq_zero_iff_of_nonneg (abs_nonneg x.aₙ) (abs_nonneg y.aₙ)).mp hn
  constructor <;> ext <;> simp <;> rw [<-abs_eq_zero] <;> assumption

lemma multiplier_nonneg {x y : AdjoinSqrt R n} : IsNonneg (multiplier x y) := by
  apply nonneg_of_coeffs_nonneg <;> simp [multiplier] <;> positivity

variable [Fact (¬ IsSquare n)] [pos: Fact (n > 0)]

/-- Only `0` is both non-negative and non-positive. -/
lemma nonneg_antisymm {x : AdjoinSqrt R n}
    (hx : IsNonneg x) (hnx : IsNonneg (-x)) : x = 0 := by
  rw [<- norm_0]
  have h1 : (-x).a₁ = -x.a₁ := rfl
  have h2 : (-x).aₙ = -x.aₙ := rfl
  rcases hx with ⟨p,q⟩ | ⟨p,q⟩ <;> rcases hnx with ⟨r,s⟩ | ⟨r, s⟩
    <;> rw [norm_neg, h1, h2, norm] at *
    <;> nlinarith [mul_self_nonneg x.aₙ, pos.elim,mul_nonneg pos.elim.le (mul_nonneg p r)]

/-- if xy ≥ 0 and y > 0 then x ≥ 0 -/
lemma nonneg_mul_of_pos {x y : AdjoinSqrt R n}
  (hmul : IsNonneg (x * y)) (hy : IsNonneg y) (hne : y ≠ 0) : IsNonneg x := by
  rcases (nonneg_or_neg_nonneg x) with h | h
  . exact h
  . have hNegMul : (-(x*y)).IsNonneg := by rw [<- neg_mul]; apply nonneg_mul <;> assumption
    have hMulZero : x*y = 0 := nonneg_antisymm hmul hNegMul
    have hZero : x = 0 := Or.resolve_right (mul_eq_zero.mp hMulZero) hne
    rw [hZero]; simp [IsNonneg, norm]

/-- The non-negative elements are closed under addition. -/
lemma nonneg_add {x y : AdjoinSqrt R n}
    (hx : IsNonneg x) (hy : IsNonneg y) : IsNonneg (x + y) := by
  -- if the multiplier is 0, x and y are 0 so we're done
  rcases eq_or_ne (x.multiplier y) 0 with h | hMultiplier
  . obtain ⟨hx,hy⟩ := eq_zero_of_multiplier_eq_zero h
    simp [hx,hy,IsNonneg,norm]

  -- now we proceed by proving (x + y)(multiplier) ≥ 0 by showing the coefficients are nonneg
  apply nonneg_mul_of_pos _ multiplier_nonneg hMultiplier
  have hn : 0 < n := Fact.out
  rcases hx.wedges with ⟨hx1, hxn, hxN⟩ | ⟨hx1, hxn, hxN⟩ | ⟨hx1, hxn, hxN⟩ | ⟨hx1, hxn, hxN⟩
    <;> rcases hy.wedges with ⟨hy1, hyn, hyN⟩ | ⟨hy1, hyn, hyN⟩ | ⟨hy1, hyn, hyN⟩ | ⟨hy1, hyn, hyN⟩
    <;> apply nonneg_of_coeffs_nonneg
    <;> simp only [multiplier, mul_a₁, mul_aₙ, add_a₁, add_aₙ, norm, sub_nonneg, sub_nonpos] at hxN hyN ⊢
    <;> simp only [abs_of_nonneg, abs_of_nonpos, *]

  -- now we've split into 32 cases; we add a bunch of simple facts and then crush them with linarith / nlinarith
  all_goals
    have := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hxn)
    have := mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hyn)
    have := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)
    have := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hyn)
    have := mul_nonneg (sub_nonneg.mpr hxn) (sub_nonneg.mpr hy1)
    have := mul_nonneg (sub_nonneg.mpr hxn) (sub_nonneg.mpr hyn)
    have := mul_nonneg hn.le (mul_nonneg (sub_nonneg.mpr hxn) (sub_nonneg.mpr hyn))
    have := mul_nonneg hn.le (mul_self_nonneg x.aₙ)
    have := mul_nonneg hn.le (mul_self_nonneg y.aₙ)
    have := mul_self_nonneg x.a₁
    have := mul_self_nonneg y.a₁

  -- linarith closes most goals; the remaining ones need to compare n * |x.aₙ| * |y.aₙ| to |x.a₁| * |y.a₁|
  -- we could add lemmas about these cases, but nlinarith is able to figure it out.
  all_goals first | linarith | nlinarith

/-- The non-negative elements of `A[√n]`. -/
def nonnegCone : RingCone (AdjoinSqrt R n) where
  carrier := {x | IsNonneg x}
  zero_mem' := Or.inl ⟨le_refl _, by simp [norm]⟩
  one_mem' := Or.inl ⟨zero_le_one, by simp [norm]⟩
  add_mem' := nonneg_add
  mul_mem' := nonneg_mul
  eq_zero_of_mem_of_neg_mem' := nonneg_antisymm

/-! ### The order from the cone -/

instance : HasMemOrNegMem (nonnegCone (R := R) (n := n)) where
  mem_or_neg_mem := nonneg_or_neg_nonneg

instance : DecidablePred (· ∈ nonnegCone (R := R) (n := n)) := fun x =>
  decidable_of_iff ((0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0)) Iff.rfl

/-- The order on `A[√n]`: `a ≤ b` when `b - a` is in the non-negative cone. -/
instance instLinearOrder : LinearOrder (AdjoinSqrt R n) :=
  LinearOrder.mkOfAddGroupCone nonnegCone

instance instIsStrictOrderedRing : IsStrictOrderedRing (AdjoinSqrt R n) :=
  haveI : IsOrderedRing (AdjoinSqrt R n) := IsOrderedRing.mkOfCone (nonnegCone (R := R) (n := n))
  IsOrderedRing.toIsStrictOrderedRing _

theorem nonneg_iff (x : AdjoinSqrt R n) : 0 ≤ x ↔ IsNonneg x := by
  show IsNonneg (x - 0) ↔ _; rw [sub_zero]


end Order


theorem root_n_squared [CommRing R]: root n * root n = (n : AdjoinSqrt R n) := by
  ext <;> simp
