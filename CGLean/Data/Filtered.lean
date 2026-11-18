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

`Filtered α` is intended to be a drop-in replacement for a type `α` of exact
numbers, given an approximation strategy `ApproxStrategy α A`: an order embedding
`α →+* ℝ`, and a way to approximate its values by elements of a type `A` of
approximations (`RealApprox A`). Each value carries an approximation of its
image in `ℝ`.

Arithmetic on `Filtered α` is evaluated lazily on `α` and eagerly on the
approximations. Comparisons consult the approximations first, and evaluate the
`α` values only when the approximations don't decide.

Two values are equal when their `α` values are, whatever their approximations:
the approximation of `(x + y) + z` need not be that of `x + (y + z)`. So
`Filtered α` is a quotient of `Filtered.Pre α`, and its algebraic and order structure is
pulled back along the injection `Filtered.get` into `α`.

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
structure Filtered.Pre (α : Type) [Ring α] [Preorder α] {A : Type} [RealApprox A]
    [strategy : ApproxStrategy α A] where
  value : Thunk α
  range : A
  mem : strategy.toRingHom value.get ∈ range

namespace Filtered.Pre

/-! ### Ring operations -/

section Ring

variable [CommRing α] [Preorder α] [strategy : ApproxStrategy α A]

/-- An already computed value, approximated by `strategy.approx`. -/
def pure (a : α) : Filtered.Pre α :=
  ⟨Thunk.pure a, strategy.approx a, strategy.mem_approx a⟩

/-! Constants are computed in `α` and approximated by the strategy. -/

instance : IntCast (Filtered.Pre α) := ⟨fun i => pure i⟩
instance : NatCast (Filtered.Pre α) := ⟨fun n => pure n⟩

instance : Zero (Filtered.Pre α) := ⟨((0 : ℤ) : Filtered.Pre α)⟩
instance : One (Filtered.Pre α) := ⟨((1 : ℤ) : Filtered.Pre α)⟩

instance : Add (Filtered.Pre α) where
  add x y := ⟨Thunk.mk fun _ => x.value.get + y.value.get, x.range + y.range, by
    show strategy.toRingHom (x.value.get + y.value.get) ∈ _
    rw [map_add]; exact mem_add x.mem y.mem⟩

instance : Neg (Filtered.Pre α) where
  neg x := ⟨Thunk.mk fun _ => -x.value.get, -x.range, by
    show strategy.toRingHom (-x.value.get) ∈ _
    rw [map_neg]; exact mem_neg x.mem⟩

instance : Sub (Filtered.Pre α) where
  sub x y := ⟨Thunk.mk fun _ => x.value.get - y.value.get, x.range - y.range, by
    show strategy.toRingHom (x.value.get - y.value.get) ∈ _
    rw [map_sub]; exact mem_sub x.mem y.mem⟩

instance : Mul (Filtered.Pre α) where
  mul x y := ⟨Thunk.mk fun _ => x.value.get * y.value.get, x.range * y.range, by
    show strategy.toRingHom (x.value.get * y.value.get) ∈ _
    rw [map_mul]; exact mem_mul x.mem y.mem⟩

instance : SMul ℕ (Filtered.Pre α) := ⟨fun n x => (n : Filtered.Pre α) * x⟩
instance : SMul ℤ (Filtered.Pre α) := ⟨fun n x => (n : Filtered.Pre α) * x⟩

/-- `x ^ n`: the value by `α`'s own power, the approximation by `A`'s. -/
instance : Pow (Filtered.Pre α) ℕ where
  pow x n := ⟨Thunk.mk fun _ => x.value.get ^ n, x.range ^ n, by
    show strategy.toRingHom (x.value.get ^ n) ∈ _
    rw [map_pow]; exact mem_pow x.mem n⟩

theorem value_pow (x : Filtered.Pre α) (n : ℕ) : (x ^ n).value.get = x.value.get ^ n := rfl

end Ring

/-! ### Values are equivalent when their `α` values are equal -/

instance setoid [Ring α] [Preorder α] [ApproxStrategy α A] : Setoid (Filtered.Pre α) where
  r x y := x.value.get = y.value.get
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-! ### Comparison -/

section Order

variable [Ring α] [LinearOrder α] [strategy : ApproxStrategy α A]

/-- Compare two values by their approximations, falling back on `α` only when
the approximations don't decide. -/
def cmp (x y : Filtered.Pre α) : Ordering :=
  match compare? x.range y.range with
  | some o => o
  | none => compare x.value.get y.value.get

/-- The filtered comparison agrees with the exact one. -/
theorem cmp_eq (x y : Filtered.Pre α) :
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

variable [Field α] [Preorder α] [strategy : ApproxStrategy α A]

/-- The reciprocal. When the approximation has no reciprocal (it may contain
zero), the value is computed here and approximated afresh by `strategy.approx`. -/
def inv (x : Filtered.Pre α) : Filtered.Pre α :=
  let v : Thunk α := Thunk.mk fun _ => x.value.get⁻¹
  match h : inv? x.range with
  | some J => ⟨v, J, by
      show strategy.toRingHom (x.value.get⁻¹) ∈ J
      rw [map_inv₀]; exact mem_inv? x.mem h⟩
  | none => ⟨v, strategy.approx v.get, strategy.mem_approx _⟩

theorem value_inv (x : Filtered.Pre α) : (inv x).value.get = x.value.get⁻¹ := by
  unfold inv; split <;> rfl

instance : RatCast (Filtered.Pre α) := ⟨fun q => pure q⟩

end Field

end Filtered.Pre

/-! ## The quotient -/

/-- Values of `α` with approximations, identified when their `α` values are
equal. -/
def Filtered (α : Type) [Ring α] [Preorder α] {A : Type} [RealApprox A]
    [strategy : ApproxStrategy α A] : Type :=
  Quotient (Filtered.Pre.setoid (α := α))

namespace Filtered

section Ring

variable [CommRing α] [Preorder α] [strategy : ApproxStrategy α A]

/-- The exact value. -/
def get : Filtered α → α := Quotient.lift (fun x => x.value.get) (fun _ _ h => h)

theorem get_injective : Function.Injective (get (α := α)) := by
  intro x y h
  induction x using Quotient.ind
  induction y using Quotient.ind
  exact Quotient.sound h

/-- An already computed value. -/
def ofValue (a : α) : Filtered α := ⟦Filtered.Pre.pure a⟧

@[simp] theorem get_ofValue (a : α) : get (ofValue a : Filtered α) = a := rfl

instance : IntCast (Filtered α) := ⟨fun i => ⟦i⟧⟩
instance : NatCast (Filtered α) := ⟨fun n => ⟦n⟧⟩
instance : Zero (Filtered α) := ⟨⟦0⟧⟩
instance : One (Filtered α) := ⟨⟦1⟧⟩

instance : Add (Filtered α) where
  add := Quotient.map₂ (· + ·) fun _ _ h₁ _ _ h₂ => by
    show _ + _ = _ + _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Neg (Filtered α) where
  neg := Quotient.map (- ·) fun _ _ h => by
    show -_ = -_; rw [show _ = _ from h]

instance : Sub (Filtered α) where
  sub := Quotient.map₂ (· - ·) fun _ _ h₁ _ _ h₂ => by
    show _ - _ = _ - _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : Mul (Filtered α) where
  mul := Quotient.map₂ (· * ·) fun _ _ h₁ _ _ h₂ => by
    show _ * _ = _ * _; rw [show _ = _ from h₁, show _ = _ from h₂]

instance : SMul ℕ (Filtered α) := ⟨fun n x => (n : Filtered α) * x⟩
instance : SMul ℤ (Filtered α) := ⟨fun n x => (n : Filtered α) * x⟩

instance : Pow (Filtered α) ℕ where
  pow x n := Quotient.map (· ^ n) (fun a b h => by
    show (a ^ n).value.get = (b ^ n).value.get
    rw [Filtered.Pre.value_pow, Filtered.Pre.value_pow, show _ = _ from h]) x

@[simp] theorem get_intCast (i : ℤ) : get (i : Filtered α) = i := rfl
@[simp] theorem get_natCast (n : ℕ) : get (n : Filtered α) = n := rfl
@[simp] theorem get_zero : get (0 : Filtered α) = 0 := Int.cast_zero
@[simp] theorem get_one : get (1 : Filtered α) = 1 := Int.cast_one

@[simp] theorem get_add (x y : Filtered α) : get (x + y) = get x + get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_neg (x : Filtered α) : get (-x) = -get x := by
  induction x using Quotient.ind; rfl

@[simp] theorem get_sub (x y : Filtered α) : get (x - y) = get x - get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_mul (x y : Filtered α) : get (x * y) = get x * get y := by
  induction x using Quotient.ind; induction y using Quotient.ind; rfl

@[simp] theorem get_nsmul (n : ℕ) (x : Filtered α) : get (n • x) = n • get x := by
  rw [nsmul_eq_mul, ← get_natCast]; exact get_mul _ _

@[simp] theorem get_zsmul (n : ℤ) (x : Filtered α) : get (n • x) = n • get x := by
  rw [zsmul_eq_mul, ← get_intCast]; exact get_mul _ _

@[simp] theorem get_pow (x : Filtered α) (n : ℕ) : get (x ^ n) = get x ^ n := by
  induction x using Quotient.ind; exact Filtered.Pre.value_pow _ n

instance instRingOps : RingOps (Filtered α) where

instance instCommRing : CommRing (Filtered α) :=
  get_injective.commRing get get_zero get_one get_add get_mul get_neg get_sub get_nsmul
    get_zsmul get_pow get_natCast get_intCast

end Ring

/-! ### Order -/

section Order

variable [CommRing α] [LinearOrder α] [strategy : ApproxStrategy α A]

instance : Ord (Filtered α) where
  compare := Quotient.lift₂ Filtered.Pre.cmp fun _ _ _ _ h₁ h₂ => by
    rw [Filtered.Pre.cmp_eq, Filtered.Pre.cmp_eq, show _ = _ from h₁,
      show _ = _ from h₂]

theorem compare_get (x y : Filtered α) : compare (get x) (get y) = compare x y := by
  induction x using Quotient.ind; induction y using Quotient.ind
  exact (Filtered.Pre.cmp_eq _ _).symm

instance : LE (Filtered α) := ⟨fun x y => get x ≤ get y⟩
instance : LT (Filtered α) := ⟨fun x y => get x < get y⟩

/-! These decide by `compare`, so by the intervals when they suffice. -/

instance : DecidableLE (Filtered α) := fun x y =>
  decidable_of_iff (compare x y ≠ .gt) (by
    rw [← compare_get, Ne, compare_gt_iff_gt, not_lt]; rfl)

instance : DecidableLT (Filtered α) := fun x y =>
  decidable_of_iff (compare x y = .lt) (by rw [← compare_get, compare_lt_iff_lt]; rfl)

instance : DecidableEq (Filtered α) := fun x y =>
  decidable_of_iff (compare x y = .eq) (by
    rw [← compare_get, compare_eq_iff_eq, get_injective.eq_iff])

instance : Max (Filtered α) := ⟨fun x y => if x ≤ y then y else x⟩
instance : Min (Filtered α) := ⟨fun x y => if x ≤ y then x else y⟩

theorem get_max (x y : Filtered α) : get (x ⊔ y) = get x ⊔ get y := by
  show get (if x ≤ y then y else x) = _
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

theorem get_min (x y : Filtered α) : get (x ⊓ y) = get x ⊓ get y := by
  show get (if x ≤ y then x else y) = _
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

instance instLinearOrder : LinearOrder (Filtered α) :=
  get_injective.linearOrder get Iff.rfl Iff.rfl get_min get_max compare_get

instance instIsStrictOrderedRing [IsStrictOrderedRing α] : IsStrictOrderedRing (Filtered α) :=
  Function.Injective.isStrictOrderedRing get get_zero get_one get_add get_mul Iff.rfl Iff.rfl

end Order

/-! ### Field -/

section Field

variable [Field α] [Preorder α] [strategy : ApproxStrategy α A]

instance instInv : Inv (Filtered α) where
  inv := Quotient.map Filtered.Pre.inv fun a b h => by
    show (Filtered.Pre.inv a).value.get = (Filtered.Pre.inv b).value.get
    rw [Filtered.Pre.value_inv, Filtered.Pre.value_inv, show _ = _ from h]

instance : Div (Filtered α) := ⟨fun x y => x * y⁻¹⟩
instance : RatCast (Filtered α) := ⟨fun q => ⟦q⟧⟩
instance : NNRatCast (Filtered α) := ⟨fun q => ((q : ℚ) : Filtered α)⟩
instance : SMul ℚ (Filtered α) := ⟨fun q x => (q : Filtered α) * x⟩
instance : SMul ℚ≥0 (Filtered α) := ⟨fun q x => (q : Filtered α) * x⟩

instance : Pow (Filtered α) ℤ where
  pow x
    | .ofNat n => x ^ n
    | .negSucc n => (x ^ (n + 1))⁻¹

@[simp] theorem get_inv (x : Filtered α) : get x⁻¹ = (get x)⁻¹ := by
  induction x using Quotient.ind; exact Filtered.Pre.value_inv _

@[simp] theorem get_div (x y : Filtered α) : get (x / y) = get x / get y := by
  show get (x * y⁻¹) = _; rw [get_mul, get_inv, div_eq_mul_inv]

@[simp] theorem get_ratCast (q : ℚ) : get (q : Filtered α) = q := rfl

@[simp] theorem get_nnratCast (q : ℚ≥0) : get (q : Filtered α) = q := by
  show ((q : ℚ) : α) = _; exact Rat.cast_nnratCast q

@[simp] theorem get_qsmul (q : ℚ) (x : Filtered α) : get (q • x) = q • get x := by
  show get ((q : Filtered α) * x) = _; rw [get_mul, get_ratCast, Rat.smul_def]

@[simp] theorem get_nnqsmul (q : ℚ≥0) (x : Filtered α) : get (q • x) = q • get x := by
  show get ((q : Filtered α) * x) = _; rw [get_mul, get_nnratCast, NNRat.smul_def]

@[simp] theorem get_zpow (x : Filtered α) (n : ℤ) : get (x ^ n) = get x ^ n := by
  cases n with
  | ofNat n => show get (x ^ n) = _; rw [get_pow, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n => show get ((x ^ (n + 1))⁻¹) = _; rw [get_inv, get_pow, zpow_negSucc]

instance instField : Field (Filtered α) :=
  get_injective.field get get_zero get_one get_add get_mul get_neg get_sub get_inv get_div
    get_nsmul get_zsmul get_nnqsmul get_qsmul get_pow get_zpow get_natCast get_intCast
    get_nnratCast get_ratCast

end Field

end Filtered

end CGLean
