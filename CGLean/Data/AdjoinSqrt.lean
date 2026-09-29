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
import Mathlib.Data.Sign.Basic
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

abbrev conj [Neg R] (x : AdjoinSqrt R n) : AdjoinSqrt R n := ⟨x.a₁, -x.aₙ⟩

/-- The norm `x * conj x`, which lies in `R` rather than `R[√n]`. -/
@[simps] instance instCoeDepNorm [Mul R] [Add R] [Neg R] {x : AdjoinSqrt R n} :
    CoeDep (AdjoinSqrt R n) (x * conj x) R where
  coe := (x * conj x).a₁

@[simps] instance instInv [Zero R] [Neg R] [Mul R] [Add R] [Inv R]: Inv (AdjoinSqrt R n) where
  inv x := x.conj * (x * x.conj : R)⁻¹

/-- The element `√n` itself. -/
@[simp] def root (n : R) [Zero R] [One R] : AdjoinSqrt R n := ⟨0, 1⟩

/-- Multiplying by `√n` moves `a₁` into the `√n`-coefficient slot, and `aₙ`
(scaled by `n`) into the rational slot. -/
lemma mul_root_a₁ [CommRing R] (x : AdjoinSqrt R n) :
    (x * root n).a₁ = n * x.aₙ := by simp [root]

lemma mul_root_aₙ [CommRing R] (x : AdjoinSqrt R n) :
    (x * root n).aₙ = x.a₁ := by simp [root]

/-- The norm `a₁² - n·aₙ²`, written out. Only needs enough structure to state
the formula, so that the order (below) can use it directly. -/
abbrev norm [Mul R] [Add R] [Neg R] (x : AdjoinSqrt R n) : R :=
  x.a₁ * x.a₁ + -(n * x.aₙ * x.aₙ)


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


/-! ## Order

`A[√n]` is ordered by designating its non-negative elements, the *positive
cone*, as Mathlib does for any ordered ring. Membership is decided in `A`:
`a₁ + aₙ√n ≥ 0` when a non-negative part dominates the other, which, since
`n > 0`, is a comparison of squares, i.e. the sign of the norm. -/

/-- `n` is positive, so that `√n` exists in the ordered sense. -/
class Pos (R : Type) [Zero R] [LT R] (n : R) : Prop where
  n_pos : 0 < n

lemma norm_eq [CommRing R] (x : AdjoinSqrt R n) : (x * conj x).a₁ = norm x := by
  simp [conj, norm]

lemma norm_mul [CommRing R] (x y : AdjoinSqrt R n) :
    norm (x * y) = norm x * norm y := by
  simp [norm]; ring

/-- Negation doesn't change the norm. -/
lemma norm_neg [CommRing R] (x : AdjoinSqrt R n) : norm (-x) = norm x := by
  simp [norm]

/-- Neither does conjugation: `norm` only sees `x.aₙ²`. -/
lemma norm_conj [CommRing R] (x : AdjoinSqrt R n) : norm (conj x) = norm x := by
  simp [norm]

/-- Multiplying by `√n` swaps the roles of `a₁` and `aₙ` (up to a factor of
`n`), so it negates the norm. This is the algebraic engine behind the
`A`-dominated/`√n`-dominated symmetry: rotating an element by `√n` trades one
regime for the other while flipping the norm's sign. -/
lemma norm_mul_rootN [CommRing R] (x : AdjoinSqrt R n) :
    norm (x * root n) = -n * norm x := by
  simp [norm, root]; ring

section Order

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `a₁ + aₙ√n ≥ 0`, phrased in `A`. Both disjuncts are needed: the first covers
`aₙ < 0`, where `a₁` must dominate `aₙ√n`, and the second covers `a₁ < 0`,
where `aₙ√n` must dominate. -/
def IsNonneg (x : AdjoinSqrt R n) : Prop :=
  (0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0)

/-- Comparison of squares reflects, given the larger side is non-negative.
Mathlib states this for `^2`; this is the `mul_self` form the norms use. -/
lemma le_of_mul_self_le {a b : R} (hb : 0 ≤ b)
    (h : a * a ≤ b * b) : a ≤ b :=
  le_of_sq_le_sq (by rw [sq, sq]; exact h) hb


/-- When both norms are non-negative and both rational parts are, the rational
part dominates the cross term. -/
lemma cross_le [Pos R n] {x y : AdjoinSqrt R n}
    (hx : 0 ≤ x.a₁) (hy : 0 ≤ y.a₁) (hxN : 0 ≤ norm x) (hyN : 0 ≤ norm y) :
    n * x.aₙ * y.aₙ ≤ x.a₁ * y.a₁ := by
  have hn : 0 < n := Pos.n_pos
  simp only [norm] at hxN hyN
  nlinarith [mul_nonneg hx hy, mul_nonneg hxN (mul_self_nonneg y.a₁),
    mul_nonneg (mul_nonneg hn.le (mul_self_nonneg x.aₙ)) hyN,
    sq_nonneg (x.a₁*y.a₁ - n*x.aₙ*y.aₙ), sq_nonneg (x.a₁*y.a₁ + n*x.aₙ*y.aₙ)]

/-- Dual of `cross_le`. -/
lemma cross_ge [Pos R n] {x y : AdjoinSqrt R n}
    (hx : 0 ≤ x.aₙ) (hy : 0 ≤ y.aₙ) (hxN : norm x ≤ 0) (hyN : norm y ≤ 0) :
    x.a₁ * y.a₁ ≤ n * x.aₙ * y.aₙ := by
  -- Obtained for free by rotating both x, y by √n (which swaps a₁ ↔ n·aₙ and
  -- negates the norm) and dividing the resulting cross_le instance by n.
  have hn : 0 < n := Pos.n_pos
  have hx' : 0 ≤ (x * root n).a₁ := by rw [mul_root_a₁]; exact mul_nonneg hn.le hx
  have hy' : 0 ≤ (y * root n).a₁ := by rw [mul_root_a₁]; exact mul_nonneg hn.le hy
  have hxN' : 0 ≤ norm (x * root n) := by rw [norm_mul_rootN]; nlinarith
  have hyN' : 0 ≤ norm (y * root n) := by rw [norm_mul_rootN]; nlinarith
  have h := cross_le hx' hy' hxN' hyN'
  rw [mul_root_a₁, mul_root_a₁, mul_root_aₙ, mul_root_aₙ] at h
  nlinarith [h]

/-- `x` and `conj y` share `.a₁` and `norm`, so `cross_le`/`cross_ge` apply to
either pairing of `x` with `y` or `conj y`; the two conclusions bound
`n * x.aₙ * y.aₙ` from opposite sides. This is the tool `nonneg_mul`'s
same-regime cases use to avoid re-deriving the cross-term certificate. -/
lemma cross_le_conj [Pos R n] {x y : AdjoinSqrt R n}
    (hx : 0 ≤ x.a₁) (hy : 0 ≤ y.a₁) (hxN : 0 ≤ norm x) (hyN : 0 ≤ norm y) :
    -(n * x.aₙ * y.aₙ) ≤ x.a₁ * y.a₁ := by
  have h := cross_le hx (show 0 ≤ (conj y).a₁ from hy) hxN
    (show 0 ≤ norm (conj y) from norm_conj y ▸ hyN)
  rw [show (conj y).a₁ = y.a₁ from rfl, show (conj y).aₙ = -y.aₙ from rfl] at h
  linarith

/-- The non-negative elements are closed under multiplication. Each case turns
on comparing `(a₁*b₁)²` with `(n*aₙ*bₙ)²`, whose difference factors
through the two norms. -/
lemma nonneg_mul [Pos R n] {x y : AdjoinSqrt R n}
    (hx : (0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0))
    (hy : (0 ≤ y.a₁ ∧ 0 ≤ norm y) ∨ (0 ≤ y.aₙ ∧ norm y ≤ 0)) :
    (0 ≤ (x*y).a₁ ∧ 0 ≤ norm (x*y)) ∨ (0 ≤ (x*y).aₙ ∧ norm (x*y) ≤ 0) := by
  have hn : 0 < n := Pos.n_pos
  have hprod : norm (x*y) = norm x * norm y := norm_mul x y
  have ha : (x*y).a₁ = x.a₁*y.a₁ + n*x.aₙ*y.aₙ := rfl
  have hb : (x*y).aₙ = x.a₁*y.aₙ + x.aₙ*y.a₁ := rfl
  rcases hx with ⟨hx1, hxN⟩ | ⟨hx1, hxN⟩ <;> rcases hy with ⟨hy1, hyN⟩ | ⟨hy1, hyN⟩
  · left
    refine ⟨?_, by rw [hprod]; exact mul_nonneg hxN hyN⟩
    rw [ha]; linarith [cross_le_conj hx1 hy1 hxN hyN]
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
    -- Rotate both by √n (swapping into the L-regime `cross_le_conj` covers)
    -- and divide the resulting bound by `n`.
    have hx' : 0 ≤ (x * root n).a₁ := by rw [mul_root_a₁]; exact mul_nonneg hn.le hx1
    have hy' : 0 ≤ (y * root n).a₁ := by rw [mul_root_a₁]; exact mul_nonneg hn.le hy1
    have hxN' : 0 ≤ norm (x * root n) := by rw [norm_mul_rootN]; nlinarith
    have hyN' : 0 ≤ norm (y * root n) := by rw [norm_mul_rootN]; nlinarith
    have h := cross_le_conj hx' hy' hxN' hyN'
    rw [mul_root_a₁, mul_root_a₁, mul_root_aₙ, mul_root_aₙ] at h
    nlinarith [h]

/-- In a mixed pair, if the rational parts sum to something non-positive then the
`√n` parts sum to something non-negative. -/
lemma aₙ_add_nonneg [Pos R n] {x y : AdjoinSqrt R n}
    (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ) (hxN : 0 ≤ norm x) (hyN : norm y ≤ 0)
    (h : x.a₁ + y.a₁ ≤ 0) : 0 ≤ x.aₙ + y.aₙ := by
  have hn : 0 < n := Pos.n_pos
  simp only [norm] at hxN hyN
  have h1 : x.a₁ * x.a₁ ≤ (-y.a₁) * (-y.a₁) :=
    mul_self_le_mul_self hx1 (by linarith)
  have h2 : n * (x.aₙ * x.aₙ) ≤ n * (y.aₙ * y.aₙ) := by nlinarith [h1]
  have h3 : x.aₙ * x.aₙ ≤ y.aₙ * y.aₙ := le_of_mul_le_mul_left h2 hn
  have h4 : -x.aₙ ≤ y.aₙ := le_of_mul_self_le hy1 (by nlinarith [h3])
  linarith

/-- Dual of `norm_add_nonpos`: if the `√n` parts sum to something non-positive,
the sum sits on the rational-dominated side. -/
lemma norm_add_nonneg [Pos R n] {x y : AdjoinSqrt R n}
    (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ) (hxN : 0 ≤ norm x) (hyN : norm y ≤ 0)
    (h : x.aₙ + y.aₙ ≤ 0) : 0 ≤ norm (x+y) := by
  have hn : 0 < n := Pos.n_pos
  have hsum : norm (x+y)
      = (x.a₁+y.a₁)*(x.a₁+y.a₁) - n*(x.aₙ+y.aₙ)*(x.aₙ+y.aₙ) := by simp [norm]; ring
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

/-- The `√n`-dominated twin of `norm_add_nonneg`. -/
lemma norm_add_nonpos [Pos R n] {x y : AdjoinSqrt R n}
    (hx1 : 0 ≤ x.a₁) (hy1 : 0 ≤ y.aₙ) (hxN : 0 ≤ norm x) (hyN : norm y ≤ 0)
    (h : x.a₁ + y.a₁ ≤ 0) : norm (x+y) ≤ 0 := by
  -- Obtained for free by rotating both summands by √n: x' := y*√n and
  -- y' := x*√n swap regimes (L↔R) and negate their norms, and
  -- x'.aₙ + y'.aₙ = y.a₁ + x.a₁ is exactly the given hypothesis (relabelled).
  -- So norm_add_nonneg applies directly to (x', y'), giving
  -- 0 ≤ norm (x'+y') = norm ((x+y)*√n) = -n * norm (x+y), i.e. norm (x+y) ≤ 0.
  have hn : 0 < n := Pos.n_pos
  have hx' : 0 ≤ (y * root n).a₁ := by rw [mul_root_a₁]; exact mul_nonneg hn.le hy1
  have hy' : 0 ≤ (x * root n).aₙ := by rw [mul_root_aₙ]; exact hx1
  have hxN' : 0 ≤ norm (y * root n) := by rw [norm_mul_rootN]; nlinarith
  have hyN' : norm (x * root n) ≤ 0 := by rw [norm_mul_rootN]; nlinarith
  have hsum : 0 ≤ norm (y * root n + x * root n) := by
    refine norm_add_nonneg hx' hy' hxN' hyN' ?_
    rw [mul_root_aₙ, mul_root_aₙ]; linarith
  have hrot : y * root n + x * root n = (x + y) * root n := by
    rw [← right_distrib, add_comm y x]
  rw [hrot, norm_mul_rootN] at hsum
  nlinarith

/-- The non-negative elements are closed under addition. -/
lemma nonneg_add [Pos R n] {x y : AdjoinSqrt R n}
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
/-- Only `0` is both non-negative and non-positive. -/
lemma nonneg_antisymm [Nonsquare R n] [Pos R n] {x : AdjoinSqrt R n}
    (hx : IsNonneg x) (hnx : IsNonneg (-x)) : x = 0 := by
  have hn : 0 < n := Pos.n_pos
  have hN : norm (-x) = norm x := norm_neg x
  have h1 : (-x).a₁ = -x.a₁ := rfl
  have h2 : (-x).aₙ = -x.aₙ := rfl
  unfold IsNonneg at hx hnx
  rw [hN, h1, h2] at hnx
  have hzero : norm x = 0 → x = 0 := fun h => conj_0 x (by rw [norm_eq]; exact h)
  -- every case forces `norm x = 0`
  apply hzero
  rcases hx with ⟨p, _⟩ | ⟨p, _⟩ <;> rcases hnx with ⟨q, _⟩ | ⟨q, _⟩ <;> simp only [norm] at * <;>
    nlinarith [mul_nonneg p q, mul_nonneg (mul_nonneg hn.le p) q,
      mul_nonneg hn.le (mul_self_nonneg x.aₙ), mul_self_nonneg x.a₁]

/-- Every element is non-negative or non-positive. -/
lemma nonneg_or_neg_nonneg (x : AdjoinSqrt R n) : IsNonneg x ∨ IsNonneg (-x) := by
  have hN : norm (-x) = norm x := norm_neg x
  unfold IsNonneg; rw [hN]
  show _ ∨ (0 ≤ -x.a₁ ∧ _) ∨ (0 ≤ -x.aₙ ∧ _)
  rcases le_total 0 (norm x) with h | h
  · rcases le_total 0 x.a₁ with ha | ha
    · exact Or.inl (Or.inl ⟨ha, h⟩)
    · exact Or.inr (Or.inl ⟨by linarith, h⟩)
  · rcases le_total 0 x.aₙ with hb | hb
    · exact Or.inl (Or.inr ⟨hb, h⟩)
    · exact Or.inr (Or.inr ⟨by linarith, h⟩)

/-- The non-negative elements of `A[√n]`. -/
def nonnegCone [Nonsquare R n] [Pos R n] : RingCone (AdjoinSqrt R n) where
  carrier := {x | IsNonneg x}
  zero_mem' := Or.inl ⟨le_refl _, by simp [norm]⟩
  one_mem' := Or.inl ⟨zero_le_one, by simp [norm]⟩
  add_mem' := nonneg_add
  mul_mem' := nonneg_mul
  eq_zero_of_mem_of_neg_mem' := nonneg_antisymm

/-! ### Deciding the order

`cmpZero x` compares `x` with `0`. It looks at the signs of the parts first;
only when they differ does it need the squares, so the norm is computed for
at most one comparison in `A`. -/

/-- Compare `a₁ + aₙ√n` with `0`. -/
def cmpZero (x : AdjoinSqrt R n) : Ordering :=
  match compare x.a₁ 0, compare x.aₙ 0 with
  | .eq, o => o
  | o, .eq => o
  | .gt, .gt => .gt
  | .lt, .lt => .lt
  | .gt, .lt => compare (x.a₁ * x.a₁) (n * x.aₙ * x.aₙ)
  | .lt, .gt => compare (n * x.aₙ * x.aₙ) (x.a₁ * x.a₁)

theorem cmpZero_spec [Nonsquare R n] [Pos R n] (x : AdjoinSqrt R n) :
    (cmpZero x = .lt ↔ ¬ IsNonneg x) ∧ (cmpZero x = .eq ↔ x = 0) := by
  have hn : 0 < n := Pos.n_pos
  have hzero : norm x = 0 → x = 0 := fun h => conj_0 x (by rw [norm_eq]; exact h)
  have hx0 : x = 0 ↔ x.a₁ = 0 ∧ x.aₙ = 0 := AdjoinSqrt.ext_iff
  have sq := mul_self_nonneg x.a₁
  have sqn : 0 ≤ n * x.aₙ * x.aₙ := by rw [mul_assoc]; exact mul_nonneg hn.le (mul_self_nonneg _)
  have sqpos : x.aₙ ≠ 0 → 0 < n * x.aₙ * x.aₙ := fun h => by
    rw [mul_assoc]; exact mul_pos hn (mul_self_pos.mpr h)
  unfold cmpZero IsNonneg
  simp only [norm, hx0] at hzero ⊢
  rcases lt_trichotomy x.a₁ 0 with h1 | h1 | h1 <;>
    rcases lt_trichotomy x.aₙ 0 with h2 | h2 | h2 <;>
    simp only [compare_lt_iff_lt.mpr, compare_eq_iff_eq.mpr, compare_gt_iff_gt.mpr, h1, h2,
      hx0]
  all_goals simp only [compare_lt_iff_lt, compare_eq_iff_eq, reduceCtorEq, true_iff, false_iff,
    not_or, not_and, not_le, and_true, true_and, le_refl, neg_zero, add_zero, zero_add,
    mul_zero, not_true_eq_false, and_false]
  -- Nine cases on the signs of `a₁` and `aₙ`. When they agree, or one is zero,
  -- the answer is immediate; when they differ, `norm x` decides. Each case is
  -- propositional structure over linear facts, except `0 < n·aₙ²`, which is
  -- `sqpos`.
  all_goals aesop (add unsafe 50% (by linarith), unsafe 30% (by nlinarith), unsafe apply sqpos)

section Instances

variable [Nonsquare R n] [Pos R n]

theorem cmpZero_eq_lt_iff (x : AdjoinSqrt R n) : cmpZero x = .lt ↔ ¬ IsNonneg x :=
  (cmpZero_spec x).1

theorem cmpZero_eq_eq_iff (x : AdjoinSqrt R n) : cmpZero x = .eq ↔ x = 0 :=
  (cmpZero_spec x).2

/-- The partial order of the cone: `a ≤ b` when `b - a` is non-negative. -/
abbrev partialOrder : PartialOrder (AdjoinSqrt R n) :=
  PartialOrder.mkOfAddGroupCone (nonnegCone (R := R) (n := n))

section
attribute [local instance] partialOrder

theorem le_iff_isNonneg {a b : AdjoinSqrt R n} : a ≤ b ↔ IsNonneg (b - a) := Iff.rfl

theorem lt_iff_cmpZero {a b : AdjoinSqrt R n} : a < b ↔ cmpZero (a - b) = .lt := by
  rw [lt_iff_le_not_ge, le_iff_isNonneg, le_iff_isNonneg, cmpZero_eq_lt_iff]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have := (nonneg_or_neg_nonneg (a - b)).resolve_left h
  rwa [neg_sub] at this

/-- The order on `A[√n]`. Comparisons go through `cmpZero`, so each costs one
call to it, rather than the two that deriving `<` and `compare` from `≤` would. -/
instance instLinearOrder : LinearOrder (AdjoinSqrt R n) where
  __ := partialOrder
  le_total a b := by
    rcases nonneg_or_neg_nonneg (b - a) with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [le_iff_isNonneg, ← neg_sub]; exact h)
  toDecidableLE a b :=
    decidable_of_iff (cmpZero (b - a) ≠ .lt) (by rw [ne_eq, cmpZero_eq_lt_iff, not_not]; rfl)
  toDecidableLT a b := decidable_of_iff (cmpZero (a - b) = .lt) lt_iff_cmpZero.symm
  toDecidableEq a b := decidable_of_iff (a.a₁ = b.a₁ ∧ a.aₙ = b.aₙ) AdjoinSqrt.ext_iff.symm
  compare a b := cmpZero (a - b)
  compare_eq_compareOfLessAndEq a b := by
    unfold compareOfLessAndEq
    split_ifs with h1 h2
    · exact lt_iff_cmpZero.mp h1
    · rw [h2, sub_self]; exact (cmpZero_eq_eq_iff 0).mpr rfl
    · cases h : cmpZero (a - b)
      · exact absurd (lt_iff_cmpZero.mpr h) h1
      · exact absurd (sub_eq_zero.mp ((cmpZero_eq_eq_iff _).mp h)) h2
      · rfl

end

instance instIsStrictOrderedRing : IsStrictOrderedRing (AdjoinSqrt R n) :=
  haveI : IsOrderedRing (AdjoinSqrt R n) := IsOrderedRing.mkOfCone (nonnegCone (R := R) (n := n))
  IsOrderedRing.toIsStrictOrderedRing _

theorem nonneg_iff (x : AdjoinSqrt R n) : 0 ≤ x ↔ IsNonneg x := by
  show IsNonneg (x - 0) ↔ _; rw [sub_zero]

/-- `compare` is `cmpZero` of the difference, by definition. -/
theorem compare_eq (a b : AdjoinSqrt R n) : compare a b = cmpZero (a - b) := rfl

/-- The sign of `a₁ + aₙ√n`: that of `a₁` when the rational part dominates
(`norm ≥ 0`), otherwise that of `aₙ`. This was the definition of `sign` in the
sign-based formulation; here it is a theorem about Mathlib's `SignType.sign`. -/
theorem sign_eq (x : AdjoinSqrt R n) :
    SignType.sign x = match SignType.sign (norm x) with
      | .neg => SignType.sign x.aₙ
      | _ => SignType.sign x.a₁ := by
  have hn : 0 < n := Pos.n_pos
  have hzero : norm x = 0 → x = 0 := fun h => conj_0 x (by rw [norm_eq]; exact h)
  have key : ∀ {s : R}, (0 < s ↔ 0 < x) → (s = 0 ↔ x = 0) → SignType.sign x = SignType.sign s := by
    intro s hpos hz
    rcases lt_trichotomy s 0 with h | h | h
    · have hx : x < 0 := lt_of_le_of_ne (not_lt.mp (hpos.not.mp (not_lt.mpr h.le)))
        (fun e => h.ne (hz.mpr e))
      rw [sign_neg h, sign_neg hx]
    · rw [h, hz.mp h, sign_zero, sign_zero]
    · rw [sign_pos h, sign_pos (hpos.mp h)]
  rcases lt_trichotomy (norm x) 0 with hN | hN | hN
  · rw [show SignType.sign (norm x) = .neg from (sign_neg hN).trans SignType.neg_eq_neg_one.symm]
    have haₙ : x.aₙ ≠ 0 := fun h => by simp only [norm, h, mul_zero, neg_zero, add_zero] at hN; nlinarith [mul_self_nonneg x.a₁]
    have hx : x ≠ 0 := fun h => by rw [h] at hN; simp [norm] at hN
    refine key ⟨fun h => lt_of_le_of_ne ((nonneg_iff x).mpr (Or.inr ⟨h.le, hN.le⟩)) (Ne.symm hx), fun h => ?_⟩
      ⟨fun h => absurd h haₙ, fun h => absurd h hx⟩
    rcases (nonneg_iff x).mp h.le with ⟨_, h'⟩ | ⟨h', _⟩
    · exact absurd h' (not_le.mpr hN)
    · exact lt_of_le_of_ne h' (Ne.symm haₙ)
  · rw [hzero hN]; simp [norm]
  · rw [show SignType.sign (norm x) = .pos from (sign_pos hN).trans rfl]
    have ha₁ : x.a₁ ≠ 0 := fun h => by
      simp only [norm, h, mul_zero, zero_add] at hN; nlinarith [mul_nonneg hn.le (mul_self_nonneg x.aₙ)]
    have hx : x ≠ 0 := fun h => by rw [h] at hN; simp [norm] at hN
    refine key ⟨fun h => lt_of_le_of_ne ((nonneg_iff x).mpr (Or.inl ⟨h.le, hN.le⟩)) (Ne.symm hx), fun h => ?_⟩
      ⟨fun h => absurd h ha₁, fun h => absurd h hx⟩
    rcases (nonneg_iff x).mp h.le with ⟨h', _⟩ | ⟨_, h'⟩
    · exact lt_of_le_of_ne h' (Ne.symm ha₁)
    · exact absurd h' (not_le.mpr hN)

end Instances

end Order


theorem root_n_squared [CommRing R]: root n * root n = (n : AdjoinSqrt R n) := by
  ext <;> simp

