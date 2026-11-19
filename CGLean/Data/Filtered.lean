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
# Filtered numbers

`Filtered A` is intended to be a drop-in replacement for a type `A` of exact
numbers, given an approximation strategy `ApproxStrategy A α`: an order embedding
`A →+* ℝ`, and a way to approximate its values by elements of a type `α` of
approximations (`RealApprox α`). Each value carries an approximation of its
image in `ℝ`.

Arithmetic on `Filtered A` is evaluated lazily on `A` and eagerly on the
approximations. Comparisons consult the approximations first, and evaluate the
`A` values only when the approximations don't decide.

Two values are equal when their `A` values are, whatever their approximations:
the approximation of `(x + y) + z` need not be that of `x + (y + z)`. So
`Filtered A` is a quotient of `Filtered.Pre A`, and its algebraic and order structure is
pulled back along the injection `Filtered.get` into `A`.

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

variable {A α : Type} [RealApprox α]

/-- A value of `A`, not yet computed, with an approximation of its image. -/
structure Filtered.Pre (A : Type) [Ring A] [Preorder A] {α : Type} [RealApprox α]
    [strategy : ApproxStrategy A α] where
  value : Thunk A
  range : α
  mem : strategy.toRingHom value.get ∈ range

namespace Filtered.Pre

/-! ### Ring operations -/

section Ring

variable [CommRing A] [Preorder A] [strategy : ApproxStrategy A α]

/-- An already computed value, approximated by `strategy.approx`. -/
def pure (a : A) : Filtered.Pre A :=
  ⟨Thunk.pure a, strategy.approx a, strategy.mem_approx a⟩

/-! Constants are computed in `A` and approximated by the strategy. -/

instance : IntCast (Filtered.Pre A) := ⟨fun i => pure i⟩
instance : NatCast (Filtered.Pre A) := ⟨fun n => pure n⟩

instance : Zero (Filtered.Pre A) := ⟨((0 : ℤ) : Filtered.Pre A)⟩
instance : One (Filtered.Pre A) := ⟨((1 : ℤ) : Filtered.Pre A)⟩

instance : Add (Filtered.Pre A) where
  add x y := ⟨Thunk.mk fun _ => x.value.get + y.value.get, x.range + y.range, by
    show strategy.toRingHom (x.value.get + y.value.get) ∈ _
    rw [map_add]; exact mem_add x.mem y.mem⟩

instance : Neg (Filtered.Pre A) where
  neg x := ⟨Thunk.mk fun _ => -x.value.get, -x.range, by
    show strategy.toRingHom (-x.value.get) ∈ _
    rw [map_neg]; exact mem_neg x.mem⟩

instance : Sub (Filtered.Pre A) where
  sub x y := ⟨Thunk.mk fun _ => x.value.get - y.value.get, x.range - y.range, by
    show strategy.toRingHom (x.value.get - y.value.get) ∈ _
    rw [map_sub]; exact mem_sub x.mem y.mem⟩

instance : Mul (Filtered.Pre A) where
  mul x y := ⟨Thunk.mk fun _ => x.value.get * y.value.get, x.range * y.range, by
    show strategy.toRingHom (x.value.get * y.value.get) ∈ _
    rw [map_mul]; exact mem_mul x.mem y.mem⟩

instance : SMul ℕ (Filtered.Pre A) := ⟨fun n x => (n : Filtered.Pre A) * x⟩
instance : SMul ℤ (Filtered.Pre A) := ⟨fun n x => (n : Filtered.Pre A) * x⟩

/-- `x ^ n`: the value by `A`'s own power, the approximation by `α`'s. -/
instance : Pow (Filtered.Pre A) ℕ where
  pow x n := ⟨Thunk.mk fun _ => x.value.get ^ n, x.range ^ n, by
    show strategy.toRingHom (x.value.get ^ n) ∈ _
    rw [map_pow]; exact mem_pow x.mem n⟩

theorem value_pow (x : Filtered.Pre A) (n : ℕ) : (x ^ n).value.get = x.value.get ^ n := rfl

end Ring

/-! ### Values are equivalent when their `A` values are equal -/

instance setoid [Ring A] [Preorder A] [ApproxStrategy A α] : Setoid (Filtered.Pre A) where
  r x y := x.value.get = y.value.get
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-! ### Comparison -/

section Order

variable [Ring A] [LinearOrder A] [strategy : ApproxStrategy A α]

/-- Compare two values by their approximations, falling back on `A` only when
the approximations don't decide. -/
def cmp (x y : Filtered.Pre A) : Ordering :=
  match compare? x.range y.range with
  | some o => o
  | none => compare x.value.get y.value.get

/-- The filtered comparison agrees with the exact one. -/
theorem cmp_eq (x y : Filtered.Pre A) :
    x.cmp y = compare x.value.get y.value.get := by
  unfold cmp
  split
  · next o h =>
    rw [← compare_of_compare? h _ x.mem _ y.mem, ← cmp_eq_compare, ← cmp_eq_compare,
      strategy.strictMono'.cmp_map_eq]
  · rfl

end Order

/-! ### Reciprocals -/

section Field

variable [Field A] [Preorder A] [strategy : ApproxStrategy A α]

/-- The reciprocal. When the approximation has no reciprocal (it may contain
zero), the value is computed here and approximated afresh by `strategy.approx`. -/
def inv (x : Filtered.Pre A) : Filtered.Pre A :=
  let v : Thunk A := Thunk.mk fun _ => x.value.get⁻¹
  match h : inv? x.range with
  | some J => ⟨v, J, by
      show strategy.toRingHom (x.value.get⁻¹) ∈ J
      rw [map_inv₀]; exact mem_inv? x.mem h⟩
  | none => ⟨v, strategy.approx v.get, strategy.mem_approx _⟩

theorem value_inv (x : Filtered.Pre A) : (inv x).value.get = x.value.get⁻¹ := by
  unfold inv; split <;> rfl

instance : RatCast (Filtered.Pre A) := ⟨fun q => pure q⟩

end Field

end Filtered.Pre

/-! ## The quotient -/

/-- Values of `A` with approximations, identified when their `A` values are
equal. -/
def Filtered (A : Type) [Ring A] [Preorder A] {α : Type} [RealApprox α]
    [strategy : ApproxStrategy A α] : Type :=
  Quotient (Filtered.Pre.setoid (A := A))

namespace Filtered

section Ring

variable [CommRing A] [Preorder A] [strategy : ApproxStrategy A α]

/-- The exact value. -/
def get : Filtered A → A := Quotient.lift (fun x => x.value.get) (fun _ _ h => h)

theorem get_injective : Function.Injective (get (A := A)) := by
  intro x y h
  induction x using Quotient.ind
  induction y using Quotient.ind
  exact Quotient.sound h

/-- An already computed value. -/
def ofValue (a : A) : Filtered A := ⟦Filtered.Pre.pure a⟧

@[simp] theorem get_ofValue (a : A) : (ofValue a : Filtered A).get = a := rfl

instance : IntCast (Filtered A) := ⟨fun i => ⟦i⟧⟩
instance : NatCast (Filtered A) := ⟨fun n => ⟦n⟧⟩
instance : Zero (Filtered A) := ⟨⟦0⟧⟩
instance : One (Filtered A) := ⟨⟦1⟧⟩

instance : Add (Filtered A) where
  add := Quotient.map₂ (· + ·) fun _ _ h₁ _ _ h₂ => by
    show _ + _ = _ + _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Neg (Filtered A) where
  neg := Quotient.map (- ·) fun _ _ h => by
    show -_ = -_; rw [show _ = _ from h]

instance : Sub (Filtered A) where
  sub := Quotient.map₂ (· - ·) fun _ _ h₁ _ _ h₂ => by
    show _ - _ = _ - _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Mul (Filtered A) where
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => by
    show _ * _ = _ * _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : SMul ℕ (Filtered A) := ⟨fun n x => (n : Filtered A) * x⟩
instance : SMul ℤ (Filtered A) := ⟨fun n x => (n : Filtered A) * x⟩

instance : Pow (Filtered A) ℕ where
  pow x n := Quotient.map (· ^ n) (fun a b h => by
    show (a ^ n).value.get = (b ^ n).value.get
    rw [Filtered.Pre.value_pow, Filtered.Pre.value_pow, show _ = _ from h]) x

@[simp] theorem get_intCast (i : ℤ) : (i : Filtered A).get = i := rfl
@[simp] theorem get_natCast (n : ℕ) : (n : Filtered A).get = n := rfl
@[simp] theorem get_zero : (0 : Filtered A).get = 0 := Int.cast_zero
@[simp] theorem get_one : (1 : Filtered A).get = 1 := Int.cast_one

@[simp] theorem get_add (x y : Filtered A) : (x + y).get = x.get + y.get := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_neg (x : Filtered A) : (-x).get = -x.get := by
  induction x using Quotient.ind; rfl

@[simp] theorem get_sub (x y : Filtered A) : (x - y).get = x.get - y.get := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_mul (x y : Filtered A) : (x * y).get = x.get * y.get := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_nsmul (n : ℕ) (x : Filtered A) : (n • x).get = n • x.get := by
  rw [nsmul_eq_mul, ← get_natCast]; exact get_mul _ _

@[simp] theorem get_zsmul (n : ℤ) (x : Filtered A) : (n • x).get = n • x.get := by
  rw [zsmul_eq_mul, ← get_intCast]; exact get_mul _ _

@[simp] theorem get_pow (x : Filtered A) (n : ℕ) : (x ^ n).get = x.get ^ n := by
  induction x using Quotient.ind; exact Filtered.Pre.value_pow _ n

instance instRingOps : RingOps (Filtered A) where

instance instCommRing : CommRing (Filtered A) :=
  get_injective.commRing get get_zero get_one get_add get_mul get_neg get_sub get_nsmul
    get_zsmul get_pow get_natCast get_intCast

end Ring

/-! ### Order -/

section Order

variable [CommRing A] [LinearOrder A] [strategy : ApproxStrategy A α]

instance : Ord (Filtered A) where
  compare := Quotient.lift₂ Filtered.Pre.cmp fun _ _ _ _ h₁ h₂ => by
    rw [Filtered.Pre.cmp_eq, Filtered.Pre.cmp_eq, show _ = _ from h₁,
      show _ = _ from h₂]

theorem compare_get (x y : Filtered A) : compare x.get y.get = compare x y := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact (Filtered.Pre.cmp_eq _ _).symm

/-! The order instances split specification from implementation:

* `LE` and `LT` are propositions, defined through `get`, so that the order is
  `A`'s, transferred along `get_injective`.
* `Ord` computes with `Filtered.Pre.cmp`, which tries `compare?` on the
  approximations and falls back on `A`; `compare_get` says it agrees with `A`.
* `DecidableLE`, `DecidableLT` and `DecidableEq` decide those propositions by
  `compare`, so by the approximations when they suffice.
* `instLinearOrder` bundles these, with `compare_get` as the proof that its
  `compare` field agrees with `≤`.
-/

instance : LE (Filtered A) := ⟨fun x y => x.get ≤ y.get⟩
instance : LT (Filtered A) := ⟨fun x y => x.get < y.get⟩

instance : DecidableLE (Filtered A) := fun x y =>
  decidable_of_iff (compare x y ≠ .gt) (by
    rw [← compare_get, Ne, compare_gt_iff_gt, not_lt]; rfl)

instance : DecidableLT (Filtered A) := fun x y =>
  decidable_of_iff (compare x y = .lt) (by rw [← compare_get, compare_lt_iff_lt]; rfl)

instance : DecidableEq (Filtered A) := fun x y =>
  decidable_of_iff (compare x y = .eq) (by
    rw [← compare_get, compare_eq_iff_eq, get_injective.eq_iff])

instance : Max (Filtered A) := ⟨fun x y => if x ≤ y then y else x⟩
instance : Min (Filtered A) := ⟨fun x y => if x ≤ y then x else y⟩

theorem get_max (x y : Filtered A) : (x ⊔ y).get = x.get ⊔ y.get := by
  show (if x ≤ y then y else x).get = _
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

theorem get_min (x y : Filtered A) : (x ⊓ y).get = x.get ⊓ y.get := by
  show (if x ≤ y then x else y).get = _
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

instance instLinearOrder : LinearOrder (Filtered A) :=
  get_injective.linearOrder get Iff.rfl Iff.rfl get_min get_max compare_get

instance instIsStrictOrderedRing [IsStrictOrderedRing A] : IsStrictOrderedRing (Filtered A) :=
  Function.Injective.isStrictOrderedRing get get_zero get_one get_add get_mul Iff.rfl Iff.rfl

end Order

/-! ### Field -/

section Field

variable [Field A] [Preorder A] [strategy : ApproxStrategy A α]

instance instInv : Inv (Filtered A) where
  inv := Quotient.map Filtered.Pre.inv fun a b h => by
    show (Filtered.Pre.inv a).value.get = (Filtered.Pre.inv b).value.get
    rw [Filtered.Pre.value_inv, Filtered.Pre.value_inv, show _ = _ from h]

instance : Div (Filtered A) := ⟨fun x y => x * y⁻¹⟩
instance : RatCast (Filtered A) := ⟨fun q => ⟦q⟧⟩
instance : NNRatCast (Filtered A) := ⟨fun q => ((q : ℚ) : Filtered A)⟩
instance : SMul ℚ (Filtered A) := ⟨fun q x => (q : Filtered A) * x⟩
instance : SMul ℚ≥0 (Filtered A) := ⟨fun q x => (q : Filtered A) * x⟩

instance : Pow (Filtered A) ℤ where
  pow x
    | .ofNat n => x ^ n
    | .negSucc n => (x ^ (n + 1))⁻¹

@[simp] theorem get_inv (x : Filtered A) : (x⁻¹).get = x.get⁻¹ := by
  induction x using Quotient.ind; exact Filtered.Pre.value_inv _

@[simp] theorem get_div (x y : Filtered A) : (x / y).get = x.get / y.get := by
  show (x * y⁻¹).get = _; rw [get_mul, get_inv, div_eq_mul_inv]

@[simp] theorem get_ratCast (q : ℚ) : (q : Filtered A).get = q := rfl

@[simp] theorem get_nnratCast (q : ℚ≥0) : (q : Filtered A).get = q := by
  show ((q : ℚ) : A) = _; exact Rat.cast_nnratCast q

@[simp] theorem get_qsmul (q : ℚ) (x : Filtered A) : (q • x).get = q • x.get := by
  show ((q : Filtered A) * x).get = _; rw [get_mul, get_ratCast, Rat.smul_def]

@[simp] theorem get_nnqsmul (q : ℚ≥0) (x : Filtered A) : (q • x).get = q • x.get := by
  show ((q : Filtered A) * x).get = _; rw [get_mul, get_nnratCast, NNRat.smul_def]

@[simp] theorem get_zpow (x : Filtered A) (n : ℤ) : (x ^ n).get = x.get ^ n := by
  cases n with
  | ofNat n => show (x ^ n).get = _; rw [get_pow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n => show ((x ^ (n + 1))⁻¹).get = _; rw [get_inv, get_pow, zpow_negSucc]

instance instField : Field (Filtered A) :=
  get_injective.field get get_zero get_one get_add get_mul get_neg get_sub get_inv get_div
    get_nsmul get_zsmul get_nnqsmul get_qsmul get_pow get_zpow get_natCast get_intCast
    get_nnratCast get_ratCast

end Field

end Filtered

end CGLean
