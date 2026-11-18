/-
Copyright (c) 2024 Michael D. George. All rights reserved.
TODO: choose a license
Author: Michael D. George.
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Data.Rat.Cast.Lemmas
public import CGLean.Classes.ApproxStrategy
public import CGLean.Classes.RingOps

/-!
# Filtered real numbers

`FilteredReal α` is intended to be a drop-in replacement for a type `α` of exact
numbers, given an approximation strategy `ApproxStrategy α A`: an order-preserving ring
homomorphism `α →+* ℝ`, and a way to approximate its values by elements of a type
`A` of approximations (`RealApprox A`). Each value carries an approximation of its
image in `ℝ`.

Arithmetic on `FilteredReal α` is evaluated lazily on `α` and eagerly on the
approximations. Comparisons consult the approximations first, and evaluate the
`α` values only when the approximations don't decide.

Two values are equal when their `α` values are, whatever their approximations:
the approximation of `(x + y) + z` need not be that of `x + (y + z)`. So `FilteredReal α`
is a quotient of `FilteredEmbedding α`, and its algebraic and order structure is
pulled back along the injection `FilteredReal.get` into `α`.

TODO: The hope is that we are only comparing numbers that are far away from each
other, but comparing equal points for equality is also likely to be a common
operation, and it will always fall back on the slow implementation (unless the
FP approximations are exact). It is worth looking into the paper on reference
equality optimizations (or even some kind of union-find structure) to see if
this can be improved.
-/

@[expose] public section

namespace CGLean

open RealApprox

variable {α A : Type} [RealApprox A]

/-- A value of `α`, not yet computed, with an approximation of its image. -/
structure FilteredEmbedding (α : Type) [Ring α] [Preorder α] {A : Type} [RealApprox A]
    [e : ApproxStrategy α A] where
  value : Thunk α
  range : A
  mem : e.toRingHom value.get ∈ range

namespace FilteredEmbedding

/-! ### Ring operations -/

section Ring

variable [CommRing α] [Preorder α] [e : ApproxStrategy α A]

/-- An already computed value, approximated by `e.approx`. -/
def pure (a : α) : FilteredEmbedding α :=
  ⟨Thunk.pure a, e.approx a, e.mem_approx a⟩

instance : IntCast (FilteredEmbedding α) where
  intCast i := ⟨Thunk.pure i, RealApprox.ofInt i, by
    show e.toRingHom (i : α) ∈ _
    rw [map_intCast]; exact mem_ofInt i⟩

instance : NatCast (FilteredEmbedding α) where
  natCast n := ⟨Thunk.pure n, RealApprox.ofInt n, by
    show e.toRingHom (n : α) ∈ _
    rw [map_natCast]; exact_mod_cast mem_ofInt (A := A) n⟩

instance : Zero (FilteredEmbedding α) := ⟨((0 : ℤ) : FilteredEmbedding α)⟩
instance : One (FilteredEmbedding α) := ⟨((1 : ℤ) : FilteredEmbedding α)⟩

instance : Add (FilteredEmbedding α) where
  add x y := ⟨Thunk.mk fun _ => x.value.get + y.value.get, x.range + y.range, by
    show e.toRingHom (x.value.get + y.value.get) ∈ _
    rw [map_add]; exact mem_add x.mem y.mem⟩

instance : Neg (FilteredEmbedding α) where
  neg x := ⟨Thunk.mk fun _ => -x.value.get, -x.range, by
    show e.toRingHom (-x.value.get) ∈ _
    rw [map_neg]; exact mem_neg x.mem⟩

instance : Sub (FilteredEmbedding α) where
  sub x y := ⟨Thunk.mk fun _ => x.value.get - y.value.get, x.range - y.range, by
    show e.toRingHom (x.value.get - y.value.get) ∈ _
    rw [map_sub]; exact mem_sub x.mem y.mem⟩

instance : Mul (FilteredEmbedding α) where
  mul x y := ⟨Thunk.mk fun _ => x.value.get * y.value.get, x.range * y.range, by
    show e.toRingHom (x.value.get * y.value.get) ∈ _
    rw [map_mul]; exact mem_mul x.mem y.mem⟩

instance : SMul ℕ (FilteredEmbedding α) := ⟨fun n x => (n : FilteredEmbedding α) * x⟩
instance : SMul ℤ (FilteredEmbedding α) := ⟨fun n x => (n : FilteredEmbedding α) * x⟩

/-- `x ^ n`: the value by `α`'s own power, the approximation by `A`'s. -/
instance : Pow (FilteredEmbedding α) ℕ where
  pow x n := ⟨Thunk.mk fun _ => x.value.get ^ n, x.range ^ n, by
    show e.toRingHom (x.value.get ^ n) ∈ _
    rw [map_pow]; exact mem_pow x.mem n⟩

theorem value_pow (x : FilteredEmbedding α) (n : ℕ) : (x ^ n).value.get = x.value.get ^ n := rfl

end Ring

/-! ### Values are equivalent when their `α` values are equal -/

instance setoid [Ring α] [Preorder α] [ApproxStrategy α A] : Setoid (FilteredEmbedding α) where
  r x y := x.value.get = y.value.get
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-! ### Comparison -/

section Order

variable [Ring α] [LinearOrder α] [e : ApproxStrategy α A]

/-- Compare two values by their approximations, falling back on `α` only when
the approximations don't decide. -/
def cmp (x y : FilteredEmbedding α) : Ordering :=
  match compare? x.range y.range with
  | some o => o
  | none => compare x.value.get y.value.get

/-- The filtered comparison agrees with the exact one. -/
theorem cmp_eq (x y : FilteredEmbedding α) :
    x.cmp y = compare x.value.get y.value.get := by
  unfold cmp
  split
  · next o h =>
    rw [← compare_of_compare? h _ x.mem _ y.mem, ← cmp_eq_compare, ← cmp_eq_compare,
      e.strictMono'.cmp_map_eq]
  · rfl

end Order

/-! ### Reciprocals -/

section Field

variable [Field α] [Preorder α] [e : ApproxStrategy α A]

/-- The reciprocal. When the approximation has no reciprocal (it may contain
zero), the value is computed here and approximated afresh by `e.approx`. -/
def inv (x : FilteredEmbedding α) : FilteredEmbedding α :=
  let v : Thunk α := Thunk.mk fun _ => x.value.get⁻¹
  match h : inv? x.range with
  | some J => ⟨v, J, by
      show e.toRingHom (x.value.get⁻¹) ∈ J
      rw [map_inv₀]; exact mem_inv? x.mem h⟩
  | none => ⟨v, e.approx v.get, e.mem_approx _⟩

theorem value_inv (x : FilteredEmbedding α) : (inv x).value.get = x.value.get⁻¹ := by
  unfold inv; split <;> rfl

instance : RatCast (FilteredEmbedding α) where
  ratCast q := ⟨Thunk.pure q, RealApprox.ofRat q, by
    show e.toRingHom (q : α) ∈ _
    rw [map_ratCast]; exact mem_ofRat q⟩

end Field

end FilteredEmbedding

/-! ## The quotient -/

/-- Values of `α` with approximations, identified when their `α` values are
equal. -/
def FilteredReal (α : Type) [Ring α] [Preorder α] {A : Type} [RealApprox A]
    [e : ApproxStrategy α A] : Type :=
  Quotient (FilteredEmbedding.setoid (α := α))

namespace FilteredReal

section Ring

variable [CommRing α] [Preorder α] [e : ApproxStrategy α A]

/-- The exact value. -/
def get : FilteredReal α → α := Quotient.lift (fun x => x.value.get) (fun _ _ h => h)

theorem get_injective : Function.Injective (get (α := α)) := by
  intro x y h
  induction x using Quotient.ind
  induction y using Quotient.ind
  exact Quotient.sound h

/-- An already computed value. -/
def ofValue (a : α) : FilteredReal α := ⟦FilteredEmbedding.pure a⟧

@[simp] theorem get_ofValue (a : α) : get (ofValue a : FilteredReal α) = a := rfl

instance : IntCast (FilteredReal α) := ⟨fun i => ⟦i⟧⟩
instance : NatCast (FilteredReal α) := ⟨fun n => ⟦n⟧⟩
instance : Zero (FilteredReal α) := ⟨⟦0⟧⟩
instance : One (FilteredReal α) := ⟨⟦1⟧⟩

instance : Add (FilteredReal α) where
  add := Quotient.map₂ (· + ·) fun _ _ h₁ _ _ h₂ => by
    show _ + _ = _ + _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Neg (FilteredReal α) where
  neg := Quotient.map (- ·) fun _ _ h => by
    show -_ = -_; rw [show _ = _ from h]

instance : Sub (FilteredReal α) where
  sub := Quotient.map₂ (· - ·) fun _ _ h₁ _ _ h₂ => by
    show _ - _ = _ - _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Mul (FilteredReal α) where
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => by
    show _ * _ = _ * _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : SMul ℕ (FilteredReal α) := ⟨fun n x => (n : FilteredReal α) * x⟩
instance : SMul ℤ (FilteredReal α) := ⟨fun n x => (n : FilteredReal α) * x⟩

instance : Pow (FilteredReal α) ℕ where
  pow x n := Quotient.map (· ^ n) (fun a b h => by
    show (a ^ n).value.get = (b ^ n).value.get
    rw [FilteredEmbedding.value_pow, FilteredEmbedding.value_pow, show _ = _ from h]) x

@[simp] theorem get_intCast (i : ℤ) : get (i : FilteredReal α) = i := rfl
@[simp] theorem get_natCast (n : ℕ) : get (n : FilteredReal α) = n := rfl
@[simp] theorem get_zero : get (0 : FilteredReal α) = 0 := Int.cast_zero
@[simp] theorem get_one : get (1 : FilteredReal α) = 1 := Int.cast_one

@[simp] theorem get_add (x y : FilteredReal α) : get (x + y) = get x + get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_neg (x : FilteredReal α) : get (-x) = -get x := by
  induction x using Quotient.ind; rfl

@[simp] theorem get_sub (x y : FilteredReal α) : get (x - y) = get x - get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_mul (x y : FilteredReal α) : get (x * y) = get x * get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_nsmul (n : ℕ) (x : FilteredReal α) : get (n • x) = n • get x := by
  rw [nsmul_eq_mul, ← get_natCast]; exact get_mul _ _

@[simp] theorem get_zsmul (n : ℤ) (x : FilteredReal α) : get (n • x) = n • get x := by
  rw [zsmul_eq_mul, ← get_intCast]; exact get_mul _ _

@[simp] theorem get_pow (x : FilteredReal α) (n : ℕ) : get (x ^ n) = get x ^ n := by
  induction x using Quotient.ind; exact FilteredEmbedding.value_pow _ n

instance instRingOps : RingOps (FilteredReal α) where

instance instCommRing : CommRing (FilteredReal α) :=
  get_injective.commRing get get_zero get_one get_add get_mul get_neg get_sub get_nsmul
    get_zsmul get_pow get_natCast get_intCast

end Ring

/-! ### Order -/

section Order

variable [CommRing α] [LinearOrder α] [e : ApproxStrategy α A]

instance : Ord (FilteredReal α) where
  compare := Quotient.lift₂ FilteredEmbedding.cmp fun _ _ _ _ h₁ h₂ => by
    rw [FilteredEmbedding.cmp_eq, FilteredEmbedding.cmp_eq, show _ = _ from h₁,
      show _ = _ from h₂]

theorem compare_get (x y : FilteredReal α) : compare (get x) (get y) = compare x y := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact (FilteredEmbedding.cmp_eq _ _).symm

instance : LE (FilteredReal α) := ⟨fun x y => get x ≤ get y⟩
instance : LT (FilteredReal α) := ⟨fun x y => get x < get y⟩

/-! These decide by `compare`, so by the intervals when they suffice. -/

instance : DecidableLE (FilteredReal α) := fun x y =>
  decidable_of_iff (compare x y ≠ .gt) (by
    rw [← compare_get, Ne, compare_gt_iff_gt, not_lt]; rfl)

instance : DecidableLT (FilteredReal α) := fun x y =>
  decidable_of_iff (compare x y = .lt) (by rw [← compare_get, compare_lt_iff_lt]; rfl)

instance : DecidableEq (FilteredReal α) := fun x y =>
  decidable_of_iff (compare x y = .eq) (by
    rw [← compare_get, compare_eq_iff_eq, get_injective.eq_iff])

instance : Max (FilteredReal α) := ⟨fun x y => if x ≤ y then y else x⟩
instance : Min (FilteredReal α) := ⟨fun x y => if x ≤ y then x else y⟩

theorem get_max (x y : FilteredReal α) : get (x ⊔ y) = get x ⊔ get y := by
  show get (if x ≤ y then y else x) = _
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

theorem get_min (x y : FilteredReal α) : get (x ⊓ y) = get x ⊓ get y := by
  show get (if x ≤ y then x else y) = _
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

instance instLinearOrder : LinearOrder (FilteredReal α) :=
  get_injective.linearOrder get Iff.rfl Iff.rfl get_min get_max compare_get

instance instIsStrictOrderedRing [IsStrictOrderedRing α] : IsStrictOrderedRing (FilteredReal α) :=
  Function.Injective.isStrictOrderedRing get get_zero get_one get_add get_mul Iff.rfl Iff.rfl

end Order

/-! ### Field -/

section Field

variable [Field α] [Preorder α] [e : ApproxStrategy α A]

instance instInv : Inv (FilteredReal α) where
  inv := Quotient.map FilteredEmbedding.inv fun a b h => by
    show (FilteredEmbedding.inv a).value.get = (FilteredEmbedding.inv b).value.get
    rw [FilteredEmbedding.value_inv, FilteredEmbedding.value_inv, show _ = _ from h]

instance : Div (FilteredReal α) := ⟨fun x y => x * y⁻¹⟩
instance : RatCast (FilteredReal α) := ⟨fun q => ⟦q⟧⟩
instance : NNRatCast (FilteredReal α) := ⟨fun q => ((q : ℚ) : FilteredReal α)⟩
instance : SMul ℚ (FilteredReal α) := ⟨fun q x => (q : FilteredReal α) * x⟩
instance : SMul ℚ≥0 (FilteredReal α) := ⟨fun q x => (q : FilteredReal α) * x⟩

instance : Pow (FilteredReal α) ℤ where
  pow x
    | .ofNat n => x ^ n
    | .negSucc n => (x ^ (n + 1))⁻¹

@[simp] theorem get_inv (x : FilteredReal α) : get x⁻¹ = (get x)⁻¹ := by
  induction x using Quotient.ind; exact FilteredEmbedding.value_inv _

@[simp] theorem get_div (x y : FilteredReal α) : get (x / y) = get x / get y := by
  show get (x * y⁻¹) = _; rw [get_mul, get_inv, div_eq_mul_inv]

@[simp] theorem get_ratCast (q : ℚ) : get (q : FilteredReal α) = q := rfl

@[simp] theorem get_nnratCast (q : ℚ≥0) : get (q : FilteredReal α) = q := by
  show ((q : ℚ) : α) = _; exact Rat.cast_nnratCast q

@[simp] theorem get_qsmul (q : ℚ) (x : FilteredReal α) : get (q • x) = q • get x := by
  show get ((q : FilteredReal α) * x) = _; rw [get_mul, get_ratCast, Rat.smul_def]

@[simp] theorem get_nnqsmul (q : ℚ≥0) (x : FilteredReal α) : get (q • x) = q • get x := by
  show get ((q : FilteredReal α) * x) = _; rw [get_mul, get_nnratCast, NNRat.smul_def]

@[simp] theorem get_zpow (x : FilteredReal α) (n : ℤ) : get (x ^ n) = get x ^ n := by
  cases n with
  | ofNat n => show get (x ^ n) = _; rw [get_pow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n => show get ((x ^ (n + 1))⁻¹) = _; rw [get_inv, get_pow, zpow_negSucc]

instance instField : Field (FilteredReal α) :=
  get_injective.field get get_zero get_one get_add get_mul get_neg get_sub get_inv get_div
    get_nsmul get_zsmul get_nnqsmul get_qsmul get_pow get_zpow get_natCast get_intCast
    get_nnratCast get_ratCast

end Field

end FilteredReal

end CGLean
