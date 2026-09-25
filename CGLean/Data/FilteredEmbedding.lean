/-
Copyright (c) 2024 Michael D. George. All rights reserved.
TODO: choose a license
Author: Michael D. George.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Erased
import Mathlib.Data.Real.Basic
import CGLean.Data.Interval
import CGLean.Classes.RingOps

/-!
# Filtered real numbers

`FilteredReal e` is intended to be a drop-in replacement for a type `α` of exact
numbers, given a ring homomorphism `α →+* ℝ` and a way to bracket its values
(bundled together as `e : RealApprox α`). Each value carries a dyadic interval
containing its image in `ℝ`.

Arithmetic on `FilteredReal e` is evaluated lazily on `α` and eagerly on the
intervals. Comparisons consult the intervals first, and evaluate the `α` values
only when the intervals overlap.

Two values are equal when their `α` values are, whatever their intervals: the
interval of `(x + y) + z` need not be that of `x + (y + z)`. So `FilteredReal e`
is a quotient of `FilteredEmbedding e`, and its algebraic and order structure is
pulled back along the injection `FilteredReal.get` into `α`.

The intervals are LeanCert's `IntervalDyadic`, which uses software arithmetic on
dyadic rationals rather than hardware floating point. This is cheaper than exact
arithmetic in nested `A[√n]` but slower than floats would be.

TODO: The hope is that we are only comparing numbers that are far away from each
other, but comparing equal points for equality is also likely to be a common
operation, and it will always fall back on the slow implementation (unless the
FP approximations are exact). It is worth looking into the paper on reference
equality optimizations (or even some kind of union-find structure) to see if
this can be improved.
-/

namespace CGLean

open LeanCert.Core

/-! ## Bracketing elements of `α` -/

/-- A ring homomorphism into `ℝ`, together with an interval containing the image
of each element.

The homomorphism is what lets an interval for `x + y` be built from intervals for
`x` and `y`. `approx` supplies an interval for a value that was not built that
way: a constant, or a reciprocal whose argument's interval contains zero.

The homomorphism is `Erased`: it lands in `ℝ`, so it cannot be computed, and it
is needed only in proofs. Held directly, it would make every `RealApprox`, and
so every computation with `FilteredReal`, noncomputable. -/
structure RealApprox (α : Type) [Ring α] where
  hom : Erased (α →+* ℝ)
  approx : α → IntervalDyadic
  mem_approx : ∀ a, hom.out a ∈ approx a

variable {α : Type}

/-- The embedding into `ℝ`. -/
noncomputable def RealApprox.toRingHom [Ring α] (e : RealApprox α) : α →+* ℝ := e.hom.out

theorem RealApprox.mem_approx' [Ring α] (e : RealApprox α) (a : α) :
    e.toRingHom a ∈ e.approx a :=
  e.mem_approx a

/-- The rationals, bracketed exactly when dyadic and to `ratPrec` otherwise. -/
def RealApprox.rat : RealApprox ℚ where
  hom := Erased.mk (Rat.castHom ℝ)
  approx := ofRat
  mem_approx q := by rw [Erased.out_mk]; exact mem_ofRat q

instance : Fact (StrictMono RealApprox.rat.toRingHom) :=
  ⟨by rw [RealApprox.toRingHom, RealApprox.rat, Erased.out_mk]; exact Rat.cast_strictMono⟩

/-- A value of `α`, not yet computed, with an interval containing its image. -/
structure FilteredEmbedding [Ring α] (e : RealApprox α) where
  value : Thunk α
  range : IntervalDyadic
  mem : e.toRingHom value.get ∈ range

namespace FilteredEmbedding

/-! ### Ring operations -/

section Ring

variable [CommRing α] {e : RealApprox α}

/-- An already computed value, bracketed by `e.approx`. -/
def pure (a : α) : FilteredEmbedding e :=
  ⟨Thunk.pure a, e.approx a, e.mem_approx a⟩

instance : IntCast (FilteredEmbedding e) where
  intCast i := ⟨Thunk.pure i, ofInt i, by
    show e.toRingHom (i : α) ∈ _
    rw [map_intCast]; exact mem_ofInt i⟩

instance : NatCast (FilteredEmbedding e) where
  natCast n := ⟨Thunk.pure n, ofInt n, by
    show e.toRingHom (n : α) ∈ _
    rw [map_natCast]; exact_mod_cast mem_ofInt n⟩

instance : Zero (FilteredEmbedding e) := ⟨((0 : ℤ) : FilteredEmbedding e)⟩
instance : One (FilteredEmbedding e) := ⟨((1 : ℤ) : FilteredEmbedding e)⟩

instance : Add (FilteredEmbedding e) where
  add x y := ⟨Thunk.mk fun _ => x.value.get + y.value.get, trim (x.range.add y.range), by
    show e.toRingHom (x.value.get + y.value.get) ∈ _
    rw [map_add]; exact mem_trim (IntervalDyadic.mem_add x.mem y.mem)⟩

instance : Neg (FilteredEmbedding e) where
  neg x := ⟨Thunk.mk fun _ => -x.value.get, x.range.neg, by
    show e.toRingHom (-x.value.get) ∈ _
    rw [map_neg]; exact IntervalDyadic.mem_neg x.mem⟩

instance : Sub (FilteredEmbedding e) where
  sub x y := ⟨Thunk.mk fun _ => x.value.get - y.value.get, trim (x.range.sub y.range), by
    show e.toRingHom (x.value.get - y.value.get) ∈ _
    rw [map_sub]; exact mem_trim (IntervalDyadic.mem_sub x.mem y.mem)⟩

instance : Mul (FilteredEmbedding e) where
  mul x y := ⟨Thunk.mk fun _ => x.value.get * y.value.get, trim (x.range.mul y.range), by
    show e.toRingHom (x.value.get * y.value.get) ∈ _
    rw [map_mul]; exact mem_trim (IntervalDyadic.mem_mul x.mem y.mem)⟩

instance : SMul ℕ (FilteredEmbedding e) := ⟨fun n x => (n : FilteredEmbedding e) * x⟩
instance : SMul ℤ (FilteredEmbedding e) := ⟨fun n x => (n : FilteredEmbedding e) * x⟩

/-- `x ^ n` by repeated multiplication. -/
def npow : ℕ → FilteredEmbedding e → FilteredEmbedding e
  | 0, _ => 1
  | n + 1, x => npow n x * x

instance : Pow (FilteredEmbedding e) ℕ := ⟨fun x n => npow n x⟩

theorem value_pow (x : FilteredEmbedding e) (n : ℕ) : (x ^ n).value.get = x.value.get ^ n := by
  induction n with
  | zero => show ((1 : ℤ) : α) = _; simp
  | succ n ih =>
    show (npow n x).value.get * x.value.get = _
    rw [show (npow n x).value.get = (x ^ n).value.get from rfl, ih, pow_succ]

end Ring

/-! ### Values are equivalent when their `α` values are equal -/

instance setoid [Ring α] (e : RealApprox α) : Setoid (FilteredEmbedding e) where
  r x y := x.value.get = y.value.get
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-! ### Comparison -/

section Order

variable [Ring α] [LinearOrder α] {e : RealApprox α}

/-- Compare two values by their intervals, falling back on `α` only when the
intervals overlap. -/
def cmp (x y : FilteredEmbedding e) : Ordering :=
  match compare? x.range y.range with
  | some o => o
  | none => compare x.value.get y.value.get

/-- The filtered comparison agrees with the exact one. -/
theorem cmp_eq [Fact (StrictMono e.toRingHom)] (x y : FilteredEmbedding e) :
    x.cmp y = compare x.value.get y.value.get := by
  unfold cmp
  split
  · next o h =>
    rw [← compare_of_compare? h _ x.mem _ y.mem, ← cmp_eq_compare, ← cmp_eq_compare,
      (Fact.out : StrictMono e.toRingHom).cmp_map_eq]
  · rfl

end Order

/-! ### Reciprocals -/

section Field

variable [Field α] {e : RealApprox α}

/-- The reciprocal. When the interval contains zero it has no interval
reciprocal, so the value is computed here and bracketed afresh by `e.approx`. -/
def inv (x : FilteredEmbedding e) : FilteredEmbedding e :=
  let v : Thunk α := Thunk.mk fun _ => x.value.get⁻¹
  match h : inv? x.range with
  | some J => ⟨v, J, by
      show e.toRingHom (x.value.get⁻¹) ∈ J
      rw [map_inv₀]; exact mem_inv? x.mem h⟩
  | none => ⟨v, e.approx v.get, e.mem_approx _⟩

theorem value_inv (x : FilteredEmbedding e) : (inv x).value.get = x.value.get⁻¹ := by
  unfold inv; split <;> rfl

instance : RatCast (FilteredEmbedding e) where
  ratCast q := ⟨Thunk.pure q, ofRat q, by
    show e.toRingHom (q : α) ∈ _
    rw [map_ratCast]; exact mem_ofRat q⟩

end Field

end FilteredEmbedding

/-! ## The quotient -/

/-- Values of `α` with intervals, identified when their `α` values are equal. -/
def FilteredReal [Ring α] (e : RealApprox α) : Type := Quotient (FilteredEmbedding.setoid e)

namespace FilteredReal

section Ring

variable [CommRing α] {e : RealApprox α}

/-- The exact value. -/
def get : FilteredReal e → α := Quotient.lift (fun x => x.value.get) (fun _ _ h => h)

theorem get_injective : Function.Injective (get (e := e)) := by
  intro x y h
  induction x using Quotient.ind
  induction y using Quotient.ind
  exact Quotient.sound h

/-- An already computed value. -/
def ofValue (a : α) : FilteredReal e := ⟦FilteredEmbedding.pure a⟧

@[simp] theorem get_ofValue (a : α) : get (ofValue a : FilteredReal e) = a := rfl

instance : IntCast (FilteredReal e) := ⟨fun i => ⟦i⟧⟩
instance : NatCast (FilteredReal e) := ⟨fun n => ⟦n⟧⟩
instance : Zero (FilteredReal e) := ⟨⟦0⟧⟩
instance : One (FilteredReal e) := ⟨⟦1⟧⟩

instance : Add (FilteredReal e) where
  add := Quotient.map₂ (· + ·) fun _ _ h₁ _ _ h₂ => by
    show _ + _ = _ + _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Neg (FilteredReal e) where
  neg := Quotient.map (- ·) fun _ _ h => by
    show -_ = -_; rw [show _ = _ from h]

instance : Sub (FilteredReal e) where
  sub := Quotient.map₂ (· - ·) fun _ _ h₁ _ _ h₂ => by
    show _ - _ = _ - _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Mul (FilteredReal e) where
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => by
    show _ * _ = _ * _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : SMul ℕ (FilteredReal e) := ⟨fun n x => (n : FilteredReal e) * x⟩
instance : SMul ℤ (FilteredReal e) := ⟨fun n x => (n : FilteredReal e) * x⟩

instance : Pow (FilteredReal e) ℕ where
  pow x n := Quotient.map (· ^ n) (fun a b h => by
    show (a ^ n).value.get = (b ^ n).value.get
    rw [FilteredEmbedding.value_pow, FilteredEmbedding.value_pow, show _ = _ from h]) x

@[simp] theorem get_intCast (i : ℤ) : get (i : FilteredReal e) = i := rfl
@[simp] theorem get_natCast (n : ℕ) : get (n : FilteredReal e) = n := rfl
@[simp] theorem get_zero : get (0 : FilteredReal e) = 0 := Int.cast_zero
@[simp] theorem get_one : get (1 : FilteredReal e) = 1 := Int.cast_one

@[simp] theorem get_add (x y : FilteredReal e) : get (x + y) = get x + get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_neg (x : FilteredReal e) : get (-x) = -get x := by
  induction x using Quotient.ind; rfl

@[simp] theorem get_sub (x y : FilteredReal e) : get (x - y) = get x - get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_mul (x y : FilteredReal e) : get (x * y) = get x * get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_nsmul (n : ℕ) (x : FilteredReal e) : get (n • x) = n • get x := by
  rw [nsmul_eq_mul, ← get_natCast]; exact get_mul _ _

@[simp] theorem get_zsmul (n : ℤ) (x : FilteredReal e) : get (n • x) = n • get x := by
  rw [zsmul_eq_mul, ← get_intCast]; exact get_mul _ _

@[simp] theorem get_pow (x : FilteredReal e) (n : ℕ) : get (x ^ n) = get x ^ n := by
  induction x using Quotient.ind; exact FilteredEmbedding.value_pow _ n

instance instRingOps : RingOps (FilteredReal e) where

instance instCommRing : CommRing (FilteredReal e) :=
  get_injective.commRing get get_zero get_one get_add get_mul get_neg get_sub get_nsmul
    get_zsmul get_pow get_natCast get_intCast

end Ring

/-! ### Order -/

section Order

variable [CommRing α] [LinearOrder α] {e : RealApprox α} [Fact (StrictMono e.toRingHom)]

instance : Ord (FilteredReal e) where
  compare := Quotient.lift₂ FilteredEmbedding.cmp fun _ _ _ _ h₁ h₂ => by
    rw [FilteredEmbedding.cmp_eq, FilteredEmbedding.cmp_eq, show _ = _ from h₁,
      show _ = _ from h₂]

theorem compare_get (x y : FilteredReal e) : compare (get x) (get y) = compare x y := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact (FilteredEmbedding.cmp_eq _ _).symm

instance : LE (FilteredReal e) := ⟨fun x y => get x ≤ get y⟩
instance : LT (FilteredReal e) := ⟨fun x y => get x < get y⟩

/-! These decide by `compare`, so by the intervals when they suffice. -/

instance : DecidableLE (FilteredReal e) := fun x y =>
  decidable_of_iff (compare x y ≠ .gt) (by
    rw [← compare_get, Ne, compare_gt_iff_gt, not_lt]; rfl)

instance : DecidableLT (FilteredReal e) := fun x y =>
  decidable_of_iff (compare x y = .lt) (by rw [← compare_get, compare_lt_iff_lt]; rfl)

instance : DecidableEq (FilteredReal e) := fun x y =>
  decidable_of_iff (compare x y = .eq) (by
    rw [← compare_get, compare_eq_iff_eq, get_injective.eq_iff])

instance : Max (FilteredReal e) := ⟨fun x y => if x ≤ y then y else x⟩
instance : Min (FilteredReal e) := ⟨fun x y => if x ≤ y then x else y⟩

theorem get_max (x y : FilteredReal e) : get (x ⊔ y) = get x ⊔ get y := by
  show get (if x ≤ y then y else x) = _
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

theorem get_min (x y : FilteredReal e) : get (x ⊓ y) = get x ⊓ get y := by
  show get (if x ≤ y then x else y) = _
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

instance instLinearOrder : LinearOrder (FilteredReal e) :=
  get_injective.linearOrder get Iff.rfl Iff.rfl get_min get_max compare_get

instance instIsStrictOrderedRing [IsStrictOrderedRing α] : IsStrictOrderedRing (FilteredReal e) :=
  Function.Injective.isStrictOrderedRing get get_zero get_one get_add get_mul Iff.rfl Iff.rfl

end Order

/-! ### Field -/

section Field

variable [Field α] {e : RealApprox α}

instance instInv : Inv (FilteredReal e) where
  inv := Quotient.map FilteredEmbedding.inv fun a b h => by
    show (FilteredEmbedding.inv a).value.get = (FilteredEmbedding.inv b).value.get
    rw [FilteredEmbedding.value_inv, FilteredEmbedding.value_inv, show _ = _ from h]

instance : Div (FilteredReal e) := ⟨fun x y => x * y⁻¹⟩
instance : RatCast (FilteredReal e) := ⟨fun q => ⟦q⟧⟩
instance : NNRatCast (FilteredReal e) := ⟨fun q => ((q : ℚ) : FilteredReal e)⟩
instance : SMul ℚ (FilteredReal e) := ⟨fun q x => (q : FilteredReal e) * x⟩
instance : SMul ℚ≥0 (FilteredReal e) := ⟨fun q x => (q : FilteredReal e) * x⟩

instance : Pow (FilteredReal e) ℤ where
  pow x
    | .ofNat n => x ^ n
    | .negSucc n => (x ^ (n + 1))⁻¹

@[simp] theorem get_inv (x : FilteredReal e) : get x⁻¹ = (get x)⁻¹ := by
  induction x using Quotient.ind; exact FilteredEmbedding.value_inv _

@[simp] theorem get_div (x y : FilteredReal e) : get (x / y) = get x / get y := by
  show get (x * y⁻¹) = _; rw [get_mul, get_inv, div_eq_mul_inv]

@[simp] theorem get_ratCast (q : ℚ) : get (q : FilteredReal e) = q := rfl

@[simp] theorem get_nnratCast (q : ℚ≥0) : get (q : FilteredReal e) = q := by
  show ((q : ℚ) : α) = _; exact Rat.cast_nnratCast q

@[simp] theorem get_qsmul (q : ℚ) (x : FilteredReal e) : get (q • x) = q • get x := by
  show get ((q : FilteredReal e) * x) = _; rw [get_mul, get_ratCast, Rat.smul_def]

@[simp] theorem get_nnqsmul (q : ℚ≥0) (x : FilteredReal e) : get (q • x) = q • get x := by
  show get ((q : FilteredReal e) * x) = _; rw [get_mul, get_nnratCast, NNRat.smul_def]

@[simp] theorem get_zpow (x : FilteredReal e) (n : ℤ) : get (x ^ n) = get x ^ n := by
  cases n with
  | ofNat n => show get (x ^ n) = _; rw [get_pow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n => show get ((x ^ (n + 1))⁻¹) = _; rw [get_inv, get_pow, zpow_negSucc]

instance instField : Field (FilteredReal e) :=
  get_injective.field get get_zero get_one get_add get_mul get_neg get_sub get_inv get_div
    get_nsmul get_zsmul get_nnqsmul get_qsmul get_pow get_zpow get_natCast get_intCast
    get_nnratCast get_ratCast

end Field

end FilteredReal

end CGLean
