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

lemma norm_mul' [CommRing R] (x y : AdjoinSqrt R n) :
    norm (x * y) = norm x * norm y := by
  simp [norm]; ring

/-- With no rational part, `a₁ + aₙ√n` is a nonzero multiple of `√n`, so its
norm is strictly negative. -/
lemma norm_neg_of_a₁_eq_zero [SignedField R] [Pos R n] (x : AdjoinSqrt R n)
    (h1 : x.a₁ = 0) (hd : x.aₙ ≠ 0) : norm x < 0 := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hsq : 0 < x.aₙ * x.aₙ := mul_self_pos.mpr hd
  simp only [norm, h1]
  nlinarith

/-- With no `√n` part, the norm is the square of the rational part. -/
lemma norm_pos_of_aₙ_eq_zero [SignedField R] (x : AdjoinSqrt R n)
    (hd : x.aₙ = 0) (h1 : x.a₁ ≠ 0) : 0 < norm x := by
  have hsq : 0 < x.a₁ * x.a₁ := mul_self_pos.mpr h1
  simp only [norm, hd]
  nlinarith

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
  rw [sign_eq]
  cases h1 : sign x.a₁ <;> cases hd : sign x.aₙ <;>
    simp only [norm_eq] <;>
    simp only [SignedRing.sign_eq_pos_iff, SignedRing.sign_eq_neg_iff,
      SignedRing.sign_eq_zero_iff] at h1 hd
  case zero.zero => simp [norm, h1, hd]
  case zero.neg =>
    have hN := norm_neg_of_a₁_eq_zero x h1 (ne_of_lt hd)
    simp only [ne_eq, not_true_eq_false, false_iff, not_or, not_and]
    exact ⟨fun _ => not_le.mpr hN, fun h => absurd h (not_le.mpr hd)⟩
  case zero.pos =>
    have hN := norm_neg_of_a₁_eq_zero x h1 (ne_of_gt hd)
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    exact Or.inr ⟨le_of_lt hd, le_of_lt hN⟩
  case neg.zero =>
    have hN := norm_pos_of_aₙ_eq_zero x hd (ne_of_lt h1)
    simp only [ne_eq, not_true_eq_false, false_iff, not_or, not_and]
    exact ⟨fun h => absurd h (not_le.mpr h1), fun _ => not_le.mpr hN⟩
  case neg.neg =>
    simp only [ne_eq, not_true_eq_false, false_iff, not_or, not_and]
    exact ⟨fun h => absurd h (not_le.mpr h1), fun h => absurd h (not_le.mpr hd)⟩
  case neg.pos =>
    simp only [ne_eq, neg_eq_iff_eq_neg]
    rw [show -SignType.neg = SignType.pos from rfl, SignedRing.sign_eq_pos_iff]
    constructor
    · intro h
      exact Or.inr ⟨le_of_lt hd, not_lt.mp h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h (not_le.mpr h1)
      · exact not_lt.mpr h
  case pos.zero =>
    have hN := norm_pos_of_aₙ_eq_zero x hd (ne_of_gt h1)
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    exact Or.inl ⟨le_of_lt h1, le_of_lt hN⟩
  case pos.neg =>
    rw [SignedRing.nonneg_iff.symm]
    constructor
    · intro h; exact Or.inl ⟨le_of_lt h1, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h (not_le.mpr hd)
  case pos.pos =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
    rcases le_total 0 (norm x) with hN | hN
    · exact Or.inl ⟨le_of_lt h1, hN⟩
    · exact Or.inr ⟨le_of_lt hd, hN⟩

/-- The non-negative elements are closed under multiplication. Each case turns
on comparing `(x.a₁*y.a₁)²` with `(n*x.aₙ*y.aₙ)²`, whose difference factors
through the two norms. -/
lemma nonneg_mul [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx : (0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0))
    (hy : (0 ≤ y.a₁ ∧ 0 ≤ norm y) ∨ (0 ≤ y.aₙ ∧ norm y ≤ 0)) :
    (0 ≤ (x*y).a₁ ∧ 0 ≤ norm (x*y)) ∨ (0 ≤ (x*y).aₙ ∧ norm (x*y) ≤ 0) := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hprod : norm (x*y) = norm x * norm y := norm_mul' x y
  have ha : (x*y).a₁ = x.a₁*y.a₁ + n*x.aₙ*y.aₙ := rfl
  have hb : (x*y).aₙ = x.a₁*y.aₙ + x.aₙ*y.a₁ := rfl
  rcases hx with ⟨hx1, hxN⟩ | ⟨hx1, hxN⟩ <;> rcases hy with ⟨hy1, hyN⟩ | ⟨hy1, hyN⟩
  · left
    refine ⟨?_, by rw [hprod]; exact mul_nonneg hxN hyN⟩
    rw [ha]
    nlinarith [mul_nonneg hx1 hy1, mul_nonneg hxN (mul_self_nonneg y.a₁),
      mul_nonneg (mul_nonneg hn.le (mul_self_nonneg x.aₙ)) hyN,
      sq_nonneg (x.a₁*y.a₁ - n*x.aₙ*y.aₙ), sq_nonneg (x.a₁*y.a₁ + n*x.aₙ*y.aₙ)]
  · right
    refine ⟨?_, by rw [hprod]; exact mul_nonpos_of_nonneg_of_nonpos hxN hyN⟩
    rw [hb]
    nlinarith [mul_nonneg hx1 hy1, mul_nonneg hxN (mul_self_nonneg y.aₙ),
      mul_nonneg (mul_self_nonneg x.aₙ) (neg_nonneg.mpr hyN),
      sq_nonneg (x.a₁*y.aₙ - x.aₙ*y.a₁), sq_nonneg (x.a₁*y.aₙ + x.aₙ*y.a₁)]
  · right
    refine ⟨?_, by rw [hprod]; exact mul_nonpos_of_nonpos_of_nonneg hxN hyN⟩
    rw [hb]
    nlinarith [mul_nonneg hx1 hy1, mul_nonneg hyN (mul_self_nonneg x.aₙ),
      mul_nonneg (mul_self_nonneg y.aₙ) (neg_nonneg.mpr hxN),
      sq_nonneg (x.a₁*y.aₙ - x.aₙ*y.a₁), sq_nonneg (x.a₁*y.aₙ + x.aₙ*y.a₁)]
  · left
    refine ⟨?_, by
      rw [hprod]; nlinarith [mul_nonneg (neg_nonneg.mpr hxN) (neg_nonneg.mpr hyN)]⟩
    rw [ha]
    nlinarith [mul_nonneg (mul_nonneg hn.le hx1) hy1,
      mul_nonneg (neg_nonneg.mpr hxN) (mul_self_nonneg y.a₁),
      mul_nonneg (mul_nonneg hn.le (mul_self_nonneg x.aₙ)) (neg_nonneg.mpr hyN),
      sq_nonneg (x.a₁*y.a₁ - n*x.aₙ*y.aₙ), sq_nonneg (x.a₁*y.a₁ + n*x.aₙ*y.aₙ),
      mul_nonneg hn.le (mul_nonneg hx1 hy1)]

/-- Only zero has zero sign. -/
lemma eq_zero_of_sign_eq_zero [SignedField R] [Nonsquare R n] (a : AdjoinSqrt R n)
    (h : Signed.sign a = 0) : a = 0 := by
  rw [sign_eq] at h
  cases h1 : sign a.a₁ <;> cases hd : sign a.aₙ <;> rw [h1, hd] at h <;> simp at h
  case zero.zero =>
    ext
    · exact SignedRing.zero_sign _ h1
    · exact SignedRing.zero_sign _ hd
  case pos.neg =>
    refine conj_0 a (SignedRing.zero_sign _ ?_)
    simpa using h
  case neg.pos =>
    refine conj_0 a (SignedRing.zero_sign _ ?_)
    simpa using h

/-- Negation flips the sign. -/
lemma sign_neg_eq [SignedField R] (a : AdjoinSqrt R n) :
    Signed.sign (-a) = -Signed.sign a := by
  rw [sign_eq, sign_eq, show (-a).a₁ = -a.a₁ from rfl,
    show (-a).aₙ = -a.aₙ from rfl, SignedRing.sign_neg, SignedRing.sign_neg]
  cases sign a.a₁ <;> cases sign a.aₙ <;> simp <;> congr 1 <;> ring

/-- Comparison of squares reflects, given the larger side is non-negative.
Mathlib states this for `^2`; this is the `mul_self` form the norms use. -/
lemma le_of_mul_self_le [SignedField R] {a b : R} (hb : 0 ≤ b)
    (h : a * a ≤ b * b) : a ≤ b :=
  le_of_sq_le_sq (by rw [sq, sq]; exact h) hb

/-- Equality of squares reflects, given both sides are non-negative. -/
lemma eq_of_mul_self_eq [SignedField R] {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a * a = b * b) : a = b :=
  le_antisymm (le_of_mul_self_le hb h.le) (le_of_mul_self_le ha h.ge)

/-- The norm vanishes only at zero. -/
lemma norm_eq_zero_iff [SignedField R] [Nonsquare R n] (z : AdjoinSqrt R n) :
    norm z = 0 ↔ z = 0 := by
  refine ⟨fun h => conj_0 z ?_, fun h => by rw [h]; simp [norm]⟩
  rw [norm_eq]; exact h

/-- When both norms are non-negative and both rational parts are, the rational
part dominates the cross term. -/
lemma cross_le [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx : 0 ≤ x.a₁) (hy : 0 ≤ y.a₁) (hxN : 0 ≤ norm x) (hyN : 0 ≤ norm y) :
    n * x.aₙ * y.aₙ ≤ x.a₁ * y.a₁ := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  simp only [norm] at hxN hyN
  nlinarith [mul_nonneg hx hy, mul_nonneg hxN (mul_self_nonneg y.a₁),
    mul_nonneg (mul_nonneg hn.le (mul_self_nonneg x.aₙ)) hyN,
    sq_nonneg (x.a₁*y.a₁ - n*x.aₙ*y.aₙ), sq_nonneg (x.a₁*y.a₁ + n*x.aₙ*y.aₙ)]

/-- Dual of `cross_le`. -/
lemma cross_ge [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx : 0 ≤ x.aₙ) (hy : 0 ≤ y.aₙ) (hxN : norm x ≤ 0) (hyN : norm y ≤ 0) :
    x.a₁ * y.a₁ ≤ n * x.aₙ * y.aₙ := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  simp only [norm] at hxN hyN
  nlinarith [mul_nonneg (mul_nonneg hn.le hx) hy,
    mul_nonneg (neg_nonneg.mpr hxN) (mul_self_nonneg y.aₙ),
    mul_nonneg (mul_self_nonneg x.aₙ) (neg_nonneg.mpr hyN),
    sq_nonneg (x.a₁*y.a₁ - n*x.aₙ*y.aₙ), sq_nonneg (x.a₁*y.a₁ + n*x.aₙ*y.aₙ)]

/-- In a mixed pair, if the rational parts sum to something non-positive then the
`√n` parts sum to something non-negative. -/
lemma aₙ_add_nonneg [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ) (hxN : 0 ≤ norm x) (hyN : norm y ≤ 0)
    (h : x.a₁ + y.a₁ ≤ 0) : 0 ≤ x.aₙ + y.aₙ := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  simp only [norm] at hxN hyN
  have h1 : x.a₁ * x.a₁ ≤ (-y.a₁) * (-y.a₁) :=
    mul_self_le_mul_self hx1 (by linarith)
  have h2 : n * (x.aₙ * x.aₙ) ≤ n * (y.aₙ * y.aₙ) := by nlinarith [h1]
  have h3 : x.aₙ * x.aₙ ≤ y.aₙ * y.aₙ := le_of_mul_le_mul_left h2 hn
  have h4 : -x.aₙ ≤ y.aₙ := le_of_mul_self_le hy1 (by nlinarith [h3])
  linarith

/-- The governing identity for the mixed cases: the product of the two norms is
the norm of `x * conj y`. It is what makes the remaining inequality tight, since
both sides vanish together. -/
lemma norm_mul_norm_eq [CommRing R] (x y : AdjoinSqrt R n) :
    norm x * norm y
      = (x.a₁*y.a₁ - n*x.aₙ*y.aₙ) * (x.a₁*y.a₁ - n*x.aₙ*y.aₙ)
        - n * (x.a₁*y.aₙ - x.aₙ*y.a₁) * (x.a₁*y.aₙ - x.aₙ*y.a₁) := by
  simp only [norm]; ring

/-- The easy half of the mixed case: when `x`'s `√n` part is also non-negative,
the sum lands on the `√n`-dominated side by a chain of square comparisons, with
no `√n` reasoning needed.

The remaining half, `x.aₙ < 0`, is the outstanding gap in `sign_plus`. Writing
`u = -x.aₙ > 0` and `v = -y.a₁ ≥ 0` it asks for `(v - a)² ≤ n·(d - u)²` given
`a² ≥ n·u²`, `v² ≤ n·d²`, `v ≥ a ≥ 0` and `d ≥ u ≥ 0`. That follows in one step
from `v ≤ √n·d` and `a ≥ √n·u` by subtraction, but the resulting certificate
lives in `R[√n]` rather than `R`, which is why `nlinarith` does not find it. -/
lemma norm_add_nonpos_of_aₙ_nonneg [SignedField R] [Pos R n]
    {x y : AdjoinSqrt R n} (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ)
    (hyN : norm y ≤ 0) (hb : 0 ≤ x.aₙ) (h : x.a₁ + y.a₁ ≤ 0) :
    norm (x+y) ≤ 0 := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hsum : norm (x+y)
      = (x.a₁+y.a₁)*(x.a₁+y.a₁) - n*(x.aₙ+y.aₙ)*(x.aₙ+y.aₙ) := by simp [norm]
  rw [hsum]
  simp only [norm] at hyN
  have k1 : (-(x.a₁+y.a₁)) * (-(x.a₁+y.a₁)) ≤ (-y.a₁) * (-y.a₁) :=
    mul_self_le_mul_self (by linarith) (by linarith)
  have k2 : y.aₙ * y.aₙ ≤ (x.aₙ+y.aₙ) * (x.aₙ+y.aₙ) :=
    mul_self_le_mul_self hy1 (by linarith)
  nlinarith [k1, k2, hyN, hn, mul_le_mul_of_nonneg_left k2 hn.le]

/-- Sign is multiplicative. The zero cases follow from `A[√n]` being a field,
hence a domain; the rest reduce to closure of the non-negative elements under
multiplication, with `sign_neg_eq` covering the negative combinations. -/
lemma sign_mul_eq [SignedField R] [Nonsquare R n] [Pos R n] (x y : AdjoinSqrt R n) :
    Signed.sign (x * y) = Signed.sign x * Signed.sign y := by
  have hz : ∀ u : AdjoinSqrt R n, Signed.sign u = 0 ↔ u = 0 := fun u =>
    ⟨eq_zero_of_sign_eq_zero u, fun h => by rw [h]; simp [SignedRing.sign_zero]⟩
  have hclosed : ∀ u v : AdjoinSqrt R n,
      Signed.sign u ≠ .neg → Signed.sign v ≠ .neg → Signed.sign (u * v) ≠ .neg :=
    fun u v hu hv =>
      (nonneg_iff _).mpr (nonneg_mul ((nonneg_iff u).mp hu) ((nonneg_iff v).mp hv))
  have hpos : ∀ u : AdjoinSqrt R n, Signed.sign u ≠ .neg → u ≠ 0 →
      Signed.sign u = .pos := by
    intro u h1 h2
    cases hs : Signed.sign u
    · exact absurd ((hz u).mp hs) h2
    · exact absurd hs h1
    · rfl
  have hflip : ∀ u : AdjoinSqrt R n, Signed.sign u = .neg → Signed.sign (-u) = .pos := by
    intro u h; rw [sign_neg_eq, h]; rfl
  have hdicho : ∀ u : AdjoinSqrt R n, u ≠ 0 →
      Signed.sign u = .pos ∨ Signed.sign u = .neg := by
    intro u hu
    cases hs : Signed.sign u
    · exact absurd ((hz u).mp hs) hu
    · exact Or.inr rfl
    · exact Or.inl rfl
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_mul, (hz 0).mpr rfl, zero_mul]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [mul_zero, (hz 0).mpr rfl, mul_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  rcases hdicho x hx with hsx | hsx <;> rcases hdicho y hy with hsy | hsy
  · rw [hsx, hsy,
      hpos _ (hclosed _ _ (by rw [hsx]; decide) (by rw [hsy]; decide)) hxy]
    rfl
  · have h := hpos (x * -y)
      (hclosed _ _ (by rw [hsx]; decide) (by rw [hflip y hsy]; decide))
      (by simpa using hxy)
    rw [mul_neg, sign_neg_eq] at h
    rw [hsx, hsy]
    cases hm : Signed.sign (x*y) <;> rw [hm] at h <;>
      first | rfl | exact absurd h (by decide)
  · have h := hpos (-x * y)
      (hclosed _ _ (by rw [hflip x hsx]; decide) (by rw [hsy]; decide))
      (by simpa using hxy)
    rw [neg_mul, sign_neg_eq] at h
    rw [hsx, hsy]
    cases hm : Signed.sign (x*y) <;> rw [hm] at h <;>
      first | rfl | exact absurd h (by decide)
  · have h := hpos (-x * -y)
      (hclosed _ _ (by rw [hflip x hsx]; decide) (by rw [hflip y hsy]; decide))
      (by simpa using hxy)
    rw [neg_mul_neg] at h
    rw [hsx, hsy, h]
    rfl

/-- The remaining half of the mixed case, `x.aₙ ≤ 0`.

Writing `a = x.a₁`, `u = -x.aₙ`, `v = -y.a₁`, `d = y.aₙ`, the goal is
`(v-a)² ≤ n(d-u)²`. Multiplying by `d+u` makes it provable in `R`:

    (v-a)²(d+u) ≤ (v-a)(v+a)(d-u) ≤ n(d-u)(d+u)(d-u)

The first step is `(v-a)(d+u) ≤ (v+a)(d-u)`, which reduces to `u·v ≤ a·d`; the
second is `v² - a² ≤ n(d² - u²)`, which is just the two norm hypotheses added.
Dividing by `d+u` finishes, with `d+u = 0` forcing everything to zero. -/
lemma norm_add_nonpos_of_aₙ_nonpos [SignedField R] [Pos R n]
    {x y : AdjoinSqrt R n} (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ)
    (hxN : 0 ≤ norm x) (hyN : norm y ≤ 0) (hb : x.aₙ ≤ 0)
    (h : x.a₁ + y.a₁ ≤ 0) : norm (x+y) ≤ 0 := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hbd : 0 ≤ x.aₙ + y.aₙ := aₙ_add_nonneg hx1 hy1 hxN hyN h
  have hsum : norm (x+y)
      = (x.a₁+y.a₁)*(x.a₁+y.a₁) - n*(x.aₙ+y.aₙ)*(x.aₙ+y.aₙ) := by simp [norm]
  rw [hsum]
  simp only [norm] at hxN hyN
  have hc : y.a₁ ≤ 0 := by linarith
  have hdpu : 0 ≤ y.aₙ - x.aₙ := by linarith
  -- `u·v ≤ a·d`, by comparing squares
  have step1 : x.aₙ * y.a₁ ≤ x.a₁ * y.aₙ := by
    refine le_of_mul_self_le (mul_nonneg hx1 hy1) ?_
    nlinarith [mul_self_nonneg x.aₙ, mul_self_nonneg y.aₙ, hxN, hyN, hn,
      mul_le_mul_of_nonneg_left hyN (mul_self_nonneg x.aₙ),
      mul_le_mul_of_nonneg_right hxN (mul_self_nonneg y.aₙ)]
  rcases eq_or_lt_of_le hdpu with heq | hlt
  · -- `d + u = 0` collapses everything
    have hb0 : x.aₙ = 0 := le_antisymm hb (by linarith)
    have hd0 : y.aₙ = 0 := by linarith
    have hc0 : y.a₁ = 0 := by
      have hsq : y.a₁ * y.a₁ ≤ 0 := by
        have h' := hyN; rw [hd0] at h'; simpa using h'
      exact mul_self_eq_zero.mp (le_antisymm hsq (mul_self_nonneg _))
    have ha0 : x.a₁ = 0 := le_antisymm (by linarith) hx1
    simp [hb0, hd0, hc0, ha0]
  · -- multiply the target by `d + u` and chain
    have key : (y.aₙ - x.aₙ) *
        ((x.a₁+y.a₁)*(x.a₁+y.a₁) - n*(x.aₙ+y.aₙ)*(x.aₙ+y.aₙ)) ≤ 0 := by
      nlinarith [step1, hxN, hyN, h, hbd, hx1, hy1, hc, hdpu, hn,
        mul_nonneg (neg_nonneg.mpr h) hbd,
        mul_nonneg (neg_nonneg.mpr h) hdpu,
        mul_nonneg hbd hdpu]
    nlinarith [key, hlt]

/-- Dual of `norm_add_nonpos`: if the `√n` parts sum to something non-positive,
the sum sits on the rational-dominated side. -/
lemma norm_add_nonneg [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ) (hxN : 0 ≤ norm x) (hyN : norm y ≤ 0)
    (h : x.aₙ + y.aₙ ≤ 0) : 0 ≤ norm (x+y) := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hsum : norm (x+y)
      = (x.a₁+y.a₁)*(x.a₁+y.a₁) - n*(x.aₙ+y.aₙ)*(x.aₙ+y.aₙ) := by simp [norm]
  rw [hsum]
  simp only [norm] at hxN hyN
  have hb : x.aₙ ≤ 0 := by linarith
  rcases le_total 0 y.a₁ with hc | hc
  · -- `c ≥ 0`: the rational part only grows, the `√n` part only shrinks
    nlinarith [hxN, hn, hx1, hc, hy1, hb, h,
      mul_self_nonneg (x.aₙ + y.aₙ), mul_nonneg hx1 hc,
      mul_le_mul_of_nonneg_left
        (show (x.aₙ+y.aₙ)*(x.aₙ+y.aₙ) ≤ x.aₙ*x.aₙ by nlinarith [hy1, hb, h]) hn.le]
  · -- `c ≤ 0`: the mirrored certificate, multiplier `a - c`
    have hac : 0 ≤ x.a₁ - y.a₁ := by linarith
    have step1 : x.aₙ * y.a₁ ≤ x.a₁ * y.aₙ := by
      refine le_of_mul_self_le (mul_nonneg hx1 hy1) ?_
      nlinarith [mul_self_nonneg x.aₙ, mul_self_nonneg y.aₙ, hxN, hyN, hn,
        mul_le_mul_of_nonneg_left hyN (mul_self_nonneg x.aₙ),
        mul_le_mul_of_nonneg_right hxN (mul_self_nonneg y.aₙ)]
    -- `a + c ≥ 0`, again by comparing squares
    have hdb : y.aₙ ≤ -x.aₙ := by linarith
    have hpr : 0 ≤ x.a₁ + y.a₁ := by
      have hsq : (-y.a₁) * (-y.a₁) ≤ x.a₁ * x.a₁ := by
        nlinarith [hxN, hyN, hn, hy1, mul_self_le_mul_self hy1 hdb]
      linarith [le_of_mul_self_le hx1 hsq]
    rcases eq_or_lt_of_le hac with heq | hlt
    · have hz : x.a₁ = 0 := le_antisymm (by linarith) hx1
      have hy0 : y.a₁ = 0 := by linarith
      have hb0 : x.aₙ = 0 := by
        have hsq : x.aₙ * x.aₙ ≤ 0 := by
          have h' := hxN; rw [hz] at h'; nlinarith [h', hn]
        exact mul_self_eq_zero.mp (le_antisymm hsq (mul_self_nonneg _))
      have hd0 : y.aₙ = 0 := le_antisymm (by linarith) hy1
      simp [hz, hy0, hb0, hd0]
    · have key : 0 ≤ (x.a₁ - y.a₁) *
          ((x.a₁+y.a₁)*(x.a₁+y.a₁) - n*(x.aₙ+y.aₙ)*(x.aₙ+y.aₙ)) := by
        nlinarith [step1, hxN, hyN, hx1, hy1, hb, hc, h, hac, hpr, hn,
          mul_nonneg (mul_nonneg hn.le (neg_nonneg.mpr h)) hac,
          mul_nonneg hpr hac, mul_nonneg (neg_nonneg.mpr h) hpr,
          mul_nonneg hx1 hy1]
      nlinarith [key, hlt]

/-- The two halves combined: in a mixed pair whose rational parts sum to
something non-positive, the sum sits on the `√n`-dominated side. -/
lemma norm_add_nonpos [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ) (hxN : 0 ≤ norm x) (hyN : norm y ≤ 0)
    (h : x.a₁ + y.a₁ ≤ 0) : norm (x+y) ≤ 0 := by
  rcases le_total 0 x.aₙ with hb | hb
  · exact norm_add_nonpos_of_aₙ_nonneg hx1 hy1 hyN hb h
  · exact norm_add_nonpos_of_aₙ_nonpos hx1 hy1 hxN hyN hb h

/-- The non-negative elements are closed under addition. -/
lemma nonneg_add [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx : (0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0))
    (hy : (0 ≤ y.a₁ ∧ 0 ≤ norm y) ∨ (0 ≤ y.aₙ ∧ norm y ≤ 0)) :
    (0 ≤ (x+y).a₁ ∧ 0 ≤ norm (x+y)) ∨ (0 ≤ (x+y).aₙ ∧ norm (x+y) ≤ 0) := by
  have ha : (x+y).a₁ = x.a₁ + y.a₁ := rfl
  have hb : (x+y).aₙ = x.aₙ + y.aₙ := rfl
  have hsum : norm (x+y) = norm x + norm y + 2*(x.a₁*y.a₁ - n*x.aₙ*y.aₙ) := by
    simp [norm]; ring
  rcases hx with ⟨hx1, hxN⟩ | ⟨hx1, hxN⟩ <;> rcases hy with ⟨hy1, hyN⟩ | ⟨hy1, hyN⟩
  · exact Or.inl ⟨by rw [ha]; linarith,
      by rw [hsum]; linarith [cross_le hx1 hy1 hxN hyN]⟩
  · rcases le_total 0 (x.a₁ + y.a₁) with hle | hle
    · rcases le_total 0 (x.aₙ + y.aₙ) with hbd | hbd
      · rcases le_total 0 (norm (x+y)) with hN | hN
        · exact Or.inl ⟨by rw [ha]; exact hle, hN⟩
        · exact Or.inr ⟨by rw [hb]; exact hbd, hN⟩
      · exact Or.inl ⟨by rw [ha]; exact hle, norm_add_nonneg hx1 hy1 hxN hyN hbd⟩
    · exact Or.inr ⟨by rw [hb]; exact aₙ_add_nonneg hx1 hy1 hxN hyN hle,
        norm_add_nonpos hx1 hy1 hxN hyN hle⟩
  · rcases le_total 0 (x.a₁ + y.a₁) with hle | hle
    · rcases le_total 0 (x.aₙ + y.aₙ) with hbd | hbd
      · rcases le_total 0 (norm (x+y)) with hN | hN
        · exact Or.inl ⟨by rw [ha]; exact hle, hN⟩
        · exact Or.inr ⟨by rw [hb]; exact hbd, hN⟩
      · refine Or.inl ⟨by rw [ha]; exact hle, ?_⟩
        rw [show x + y = y + x from add_comm x y]
        exact norm_add_nonneg hy1 hx1 hyN hxN (by linarith)
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hb, add_comm]; exact aₙ_add_nonneg hy1 hx1 hyN hxN (by linarith)
      · rw [show x + y = y + x from add_comm x y]
        exact norm_add_nonpos hy1 hx1 hyN hxN (by linarith)
  · exact Or.inr ⟨by rw [hb]; linarith,
      by rw [hsum]; linarith [cross_ge hx1 hy1 hxN hyN]⟩

/-- `sign_plus`, the last axiom of `instSignedRing`. -/
lemma sign_plus_eq [SignedField R] [Nonsquare R n] [Pos R n]
    (a b : AdjoinSqrt R n) (ha : Signed.sign a ≠ .neg)
    (hb : Signed.sign b ≠ .neg) : Signed.sign (a + b) ≠ .neg :=
  (nonneg_iff _).mpr (nonneg_add ((nonneg_iff a).mp ha) ((nonneg_iff b).mp hb))



instance instSignedRing [SignedField R] [Nonsquare R n] [Pos R n] :
    SignedRing (AdjoinSqrt R n) where
  __ := instCommRing
  sign_zero := by simp [SignedRing.sign_zero]
  sign_one  := by simp [SignedRing.sign_zero, SignedRing.sign_one]
  sign_mul  := sign_mul_eq
  zero_sign := eq_zero_of_sign_eq_zero
  sign_neg  := sign_neg_eq
  sign_plus := sign_plus_eq

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

