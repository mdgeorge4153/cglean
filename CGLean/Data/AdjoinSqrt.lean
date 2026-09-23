import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
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

/-- The element `√n` itself. -/
@[simp] def root (n : R) [Zero R] [One R] : AdjoinSqrt R n := ⟨0, 1⟩

/-- Multiplying by `√n` moves `a₁` into the `√n`-coefficient slot, and `aₙ`
(scaled by `n`) into the rational slot. -/
lemma mul_root_a₁ [CommRing R] (x : AdjoinSqrt R n) :
    (x * root n).a₁ = n * x.aₙ := by simp [root]

lemma mul_root_aₙ [CommRing R] (x : AdjoinSqrt R n) :
    (x * root n).aₙ = x.a₁ := by simp [root]

/-- The norm `a₁² - n·aₙ²`, written out. Only needs enough structure to state
the formula, so that `sign` (below) can use it directly. -/
abbrev norm [Mul R] [Add R] [Neg R] (x : AdjoinSqrt R n) : R :=
  x.a₁ * x.a₁ + -(n * x.aₙ * x.aₙ)

open Signed

/-- `a + aₙ√n` compares to `0` the same way `a₁` does when `a₁² ≥ n·aₙ²`
(the rational part dominates), and the same way `aₙ` does otherwise (the
`√n` part dominates). See `nonneg_iff` for why this is the right criterion,
and `sign_mul_rootN`/`norm_mul_rootN` for why multiplying by `√n` swaps the
two regimes. -/
@[simps] instance instSigned [Signed R] [Mul R] [Add R] [Neg R]: Signed (AdjoinSqrt R n) where
  sign x :=
    match sign (norm x) with
      | .neg => sign x.aₙ
      | _    => sign x.a₁


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
    Signed.sign x = match sign (norm x) with
      | .neg => sign x.aₙ
      | _    => sign x.a₁ := rfl

lemma norm_eq [CommRing R] (x : AdjoinSqrt R n) : (x * conj x).a₁ = norm x := by
  simp [conj, norm]

lemma norm_mul [CommRing R] (x y : AdjoinSqrt R n) :
    norm (x * y) = norm x * norm y := by
  simp [norm]; ring

/-- Negation doesn't change the norm. -/
lemma norm_neg [CommRing R] (x : AdjoinSqrt R n) : norm (-x) = norm x := by
  simp [norm]

lemma sign_zero_eq [SignedField R] : Signed.sign (0 : AdjoinSqrt R n) = 0 := by
  simp [norm, SignedRing.sign_zero]

lemma sign_one_eq [SignedField R] : Signed.sign (1 : AdjoinSqrt R n) = 1 := by
  simp [norm, SignedRing.sign_one]

/-- Multiplying by `√n` swaps the roles of `a₁` and `aₙ` (up to a factor of
`n`), so it negates the norm. This is the algebraic engine behind the
`A`-dominated/`√n`-dominated symmetry: rotating an element by `√n` trades one
regime for the other while flipping the norm's sign. -/
lemma norm_mul_rootN [CommRing R] (x : AdjoinSqrt R n) :
    norm (x * root n) = -n * norm x := by
  simp [norm, root]; ring

/-- `√n` has positive sign, given `n > 0`. -/
lemma sign_rootN [SignedField R] [Pos R n] : Signed.sign (root n : AdjoinSqrt R n) = .pos := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hneg : norm (root n : AdjoinSqrt R n) = -n := by simp [norm, root]
  -- norm (√n) = -n < 0, so `sign` falls through to the √n-coefficient, which is 1
  rw [sign_eq, hneg, show sign (-n) = .neg from SignedRing.sign_eq_neg_iff.mpr (by linarith)]
  show sign (1:R) = .pos
  rw [SignedRing.sign_one]; rfl

/-- Multiplying by `√n` doesn't change the sign. -/
lemma sign_mul_rootN [SignedField R] [Nonsquare R n] [Pos R n] (x : AdjoinSqrt R n) :
    Signed.sign (x * root n) = Signed.sign x := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  rw [sign_eq, sign_eq, norm_mul_rootN, mul_root_a₁, mul_root_aₙ]
  rcases lt_trichotomy (norm x) 0 with hlt | heq | hgt
  · rw [show sign (-n * norm x) = SignType.pos from
        SignedRing.sign_eq_pos_iff.mpr (by nlinarith),
      show sign (norm x) = SignType.neg from SignedRing.sign_eq_neg_iff.mpr hlt,
      show sign (n * x.aₙ) = sign x.aₙ from by
        rw [SignedRing.sign_mul, Pos.n_pos]; cases sign x.aₙ <;> rfl]
  · have hx0 : x = 0 := conj_0 x (by rw [norm_eq]; exact heq)
    subst hx0; simp [norm]
  · rw [show sign (-n * norm x) = SignType.neg from
        SignedRing.sign_eq_neg_iff.mpr (by nlinarith),
      show sign (norm x) = SignType.pos from SignedRing.sign_eq_pos_iff.mpr hgt]

/-- Non-negativity of `a₁ + aₙ√n`, phrased with `R`'s order rather than with
`SignType`. Both disjuncts are needed: the first covers `aₙ < 0`, where `a₁`
must dominate `aₙ√n`, and the second covers `a₁ < 0`, where `aₙ√n` must
dominate.

This is the form `sign_mul` and `sign_plus` want, since it puts them in reach of
the ordered-field lemmas. It splits on the trichotomy of `norm x`: away from
`0` the sign of `norm x` alone picks out which disjunct is live and reduces
directly to `SignedRing.nonneg_iff`; at `norm x = 0`, `Nonsquare` (via
`conj_0`) forces `x = 0`, where both disjuncts hold trivially. -/
lemma nonneg_iff [SignedField R] [Nonsquare R n] [Pos R n] (x : AdjoinSqrt R n) :
    Signed.sign x ≠ .neg ↔ (0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0) := by
  rw [sign_eq]
  rcases lt_trichotomy (norm x) 0 with hlt | heq | hgt
  · have hsn : sign (norm x) = .neg := SignedRing.sign_eq_neg_iff.mpr hlt
    simp only [hsn]
    rw [← SignedRing.nonneg_iff]
    constructor
    · intro h; exact Or.inr ⟨h, hlt.le⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h (not_le.mpr hlt)
      · exact h
  · have hx0 : x = 0 := conj_0 x (by rw [norm_eq]; exact heq)
    subst hx0
    simp [norm, SignedRing.sign_zero]
  · have hsn : sign (norm x) = .pos := SignedRing.sign_eq_pos_iff.mpr hgt
    simp only [hsn]
    rw [← SignedRing.nonneg_iff]
    constructor
    · intro h; exact Or.inl ⟨h, hgt.le⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact h
      · exact absurd h (not_le.mpr hgt)

/-- The non-negative elements are closed under multiplication. Each case turns
on comparing `(a₁*b₁)²` with `(n*aₙ*bₙ)²`, whose difference factors
through the two norms. -/
lemma nonneg_mul [SignedField R] [Pos R n] {x y : AdjoinSqrt R n}
    (hx : (0 ≤ x.a₁ ∧ 0 ≤ norm x) ∨ (0 ≤ x.aₙ ∧ norm x ≤ 0))
    (hy : (0 ≤ y.a₁ ∧ 0 ≤ norm y) ∨ (0 ≤ y.aₙ ∧ norm y ≤ 0)) :
    (0 ≤ (x*y).a₁ ∧ 0 ≤ norm (x*y)) ∨ (0 ≤ (x*y).aₙ ∧ norm (x*y) ≤ 0) := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  have hprod : norm (x*y) = norm x * norm y := norm_mul x y
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

/-- `eq_zero_of_sign_eq_zero`'s positive-norm case, factored out so the
negative-norm case can reduce to it by rotating through `√n`. -/
lemma eq_zero_of_sign_eq_zero_of_norm_pos [SignedField R] [Pos R n] (a : AdjoinSqrt R n)
    (hgt : 0 < norm a) (h : Signed.sign a = 0) : a = 0 := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  rw [sign_eq, show sign (norm a) = SignType.pos from SignedRing.sign_eq_pos_iff.mpr hgt] at h
  have ha₁ : a.a₁ = 0 := SignedRing.zero_sign _ h
  have hnorm : norm a = -(n * a.aₙ * a.aₙ) := by simp [norm, ha₁]
  have haₙ0 : a.aₙ = 0 := by
    by_contra haₙne
    have : 0 < n * a.aₙ * a.aₙ := by
      nlinarith [mul_pos hn (mul_self_pos.mpr haₙne)]
    nlinarith
  ext <;> simp_all

/-- Only zero has zero sign. Needs both `Pos` and `Nonsquare` to rule out
other representations of `0`. -/
lemma eq_zero_of_sign_eq_zero [SignedField R] [Nonsquare R n] [Pos R n] (a : AdjoinSqrt R n)
    (h : Signed.sign a = 0) : a = 0 := by
  have hn : 0 < n := SignedRing.sign_eq_pos_iff.mp Pos.n_pos
  rcases lt_trichotomy (norm a) 0 with hlt | heq | hgt
  · have hb : a * root n = 0 :=
      eq_zero_of_sign_eq_zero_of_norm_pos (a * root n)
        (by rw [norm_mul_rootN]; nlinarith) (by rw [sign_mul_rootN]; exact h)
    have ha₁ : a.a₁ = 0 := by simpa [mul_root_aₙ] using congrArg AdjoinSqrt.aₙ hb
    have haₙ : n * a.aₙ = 0 := by simpa [mul_root_a₁] using congrArg AdjoinSqrt.a₁ hb
    have haₙ0 : a.aₙ = 0 := (mul_eq_zero.mp haₙ).resolve_left hn.ne'
    ext <;> assumption
  · exact conj_0 a (by rw [norm_eq]; exact heq)
  · exact eq_zero_of_sign_eq_zero_of_norm_pos a hgt h

/-- Negation flips the sign. -/
lemma sign_neg_eq [SignedField R] (a : AdjoinSqrt R n) :
    Signed.sign (-a) = -Signed.sign a := by
  rw [sign_eq, sign_eq, norm_neg, show (-a).a₁ = -a.a₁ from rfl,
    show (-a).aₙ = -a.aₙ from rfl]
  cases sign (norm a) <;> simp [SignedRing.sign_neg]

/-- Sign is multiplicative. The zero cases follow from `A[√n]` being a field,
hence a domain; the rest reduce to closure of the non-negative elements under
multiplication, with `sign_neg_eq` covering the negative combinations. -/
lemma sign_mul_eq [SignedField R] [Nonsquare R n] [Pos R n] (x y : AdjoinSqrt R n) :
    Signed.sign (x * y) = Signed.sign x * Signed.sign y := by
  have hz : ∀ u : AdjoinSqrt R n, Signed.sign u = 0 ↔ u = 0 := fun u =>
    ⟨eq_zero_of_sign_eq_zero u, fun h => by rw [h]; exact sign_zero_eq⟩
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

