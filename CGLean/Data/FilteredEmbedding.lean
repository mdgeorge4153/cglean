/-
Copyright (c) 2024 Michael D. George. All rights reserved.
TODO: choose a license
Author: Michael D. George.
-/
import Mathlib.Data.Real.Basic
import Ray.Approx.Interval.Around
import Ray.Approx.Interval.Mul

/-!
# Filtered Real Numbers

The `FilteredEmbedding f` type is intended to be a drop-in replacement for a
type `α` that encapsulates a subset of the real numbers (which is provided by
`f : α → ℝ`). It attempts to improve computational performance by maintaining
floating point intervals that bound the real values of the encapsulated `α`
values.

Operations that produce `FilteredEmbedding f` values (like `+` and `*`) are
evaluated lazily on the underlying `α` type; the underlying operations on the
`α` type are only evaluated if and when the floating-point approximations are
insufficiently precise to evaluate comparisons (like `=` and `≤`).

NOTE: The current implementation is just a proof of concept based on the
`Ray.Approx` floating-point approximation library, which uses software floating
point instead of hardware floating point. It is therefore unlikely to provide
an actual performance improvement.

TODO: The hope is that we are only comparing numbers that are far away from each
other, but comparing equal points for equality is also likely to be a common
operation, and it will always fall back on the slow implementation (unless the
FP approximations are exact). It is worth looking into the paper on reference
equality optimizations (or even some kind of union-find structure) to see if
this can be improved.

TODO: Update documentation to reflect FilteredReal (quotient of
FilteredEmbedding)

## Implementation note

Since a `FilteredEmbedding f` value must contain a proof that the
floating-point interval contains the real value, we can only implement
operations if we know that `f` is well-behaved. For example, to implement `Zero
(FilteredEmbedding f)`, we not only need a `Zero α`, but we need to know that
`f 0 = 0` (i.e. that `f` is a 0-homomorphism).

This means that when constructing your `FilteredEmbedding f`, `f` should be a
homomorphism for the operations that you want to be able to perform. For
example, if you need an instance of `Zero`, you need `f` to be a `ZeroHom`:

```
def exampleWithZero : ZeroHom example ℝ where
  toFun x   := ...
  map_zero' := ...

abbrev ExampleFiltered : Type := FilteredEmbedding exampleWithZero

example : ExampleFiltered := 0
```

-/

open Pointwise

attribute [simp] Thunk.get

structure FilteredEmbedding (f : α → ℝ) where
  value  : Thunk α
  range  : Around (f value.get)

@[simp] def FilteredEmbedding.toReal (x : FilteredEmbedding f) : ℝ := f x.value.get

/-! ## FilteredReals are equivalence classes of FilteredEmbedding -------------/

@[simp] def eqv (f : α → ℝ) (x y : FilteredEmbedding f) : Prop := x.value.get = y.value.get

@[simps] instance same_value (f : α → ℝ): Setoid (FilteredEmbedding f) where
  r     := eqv f
  iseqv := InvImage.equivalence _ _ eq_equivalence

def FilteredReal (f : α → ℝ) : Type := Quotient (same_value f)

namespace FilteredReal

def mk (f : α → ℝ) (value : α) (range : Around (f value)) : FilteredReal f :=
  Quotient.mk' ⟨value, range⟩

theorem mk_eq_mk : x = y → mk f x p₁ = mk f y p₂ := by
  intro; apply Quot.sound; simpa [InvImage]

end FilteredReal

/-! ## Zero -------------------------------------------------------------------/

section Zero

variable [Zero α] [FunLike F α ℝ] [ZeroHomClass F α ℝ] (f : F)

@[simps] instance: Zero (FilteredEmbedding f) where
  zero := {
    value := (0 : α)
    range := ⟨0, by simp [map_zero]⟩
  }

def toZeroHom: ZeroHom (FilteredEmbedding f) ℝ where
  toFun     := FilteredEmbedding.toReal
  map_zero' := by simp

instance: Zero (FilteredReal f) where
  zero := Quotient.mk' 0

end Zero

/-! ## One --------------------------------------------------------------------/

section One

variable [One α] [FunLike F α ℝ] [OneHomClass F α ℝ] (f : F)

@[simps] instance: One (FilteredEmbedding f) where
  one := {
    value := (1 : α)
    range := ⟨1, by simp [map_one]⟩
  }

def toOneHom: OneHom (FilteredEmbedding f) ℝ where
  toFun    := FilteredEmbedding.toReal
  map_one' := by simp

instance: One (FilteredReal f) where
  one := Quotient.mk' 1

end One

/-! ## Add --------------------------------------------------------------------/

section Add

variable [Add α] [FunLike F α ℝ] [AddHomClass F α ℝ] (f : F)

@[simps] instance: Add (FilteredEmbedding f) where
  add x y := {
    value := x.value.get + y.value.get
    range := ⟨x.range.i + y.range.i, by simp [map_add]; mono⟩
  }

def toAddHom: AddHom (FilteredEmbedding f) ℝ where
  toFun := FilteredEmbedding.toReal
  map_add' := by simp

instance: Add (FilteredReal f) where
  add := Quot.map₂ (· + ·) (by simp_all) (by simp_all)

end Add

/-! ## Mul --------------------------------------------------------------------/

section Mul

variable [Mul α] [FunLike F α ℝ] [MulHomClass F α ℝ] (f : F)

@[simps] instance: Mul (FilteredEmbedding f) where
  mul x y := {
    value := x.value.get * y.value.get
    range := ⟨x.range.i * y.range.i, by simp [map_mul]; mono⟩
  }

def toMulHom: MulHom (FilteredEmbedding f) ℝ where
  toFun := FilteredEmbedding.toReal
  map_mul' := by simp

instance: Mul (FilteredReal f) where
  mul := Quot.map₂ (· * ·) (by simp_all) (by simp_all)

end Mul

/- TODO: this section only depends on intervals, migrate it somewhere -/

namespace Interval

/--
Returns `some o` if `x` is entirely to the left or entirely to the right of `y`
-/
def compare? (x y : Interval) : Option Ordering :=
  if x = nan ∨ y = nan then none
  else if x.lo > y.hi then some .gt
  else if x.hi < y.lo then some .lt
  else if x.lo = y.hi ∧ x.hi = y.lo then some .eq
  else none

/--
If `compare?` returns `some o`, then comparing any element of the intervals
must return `o`
-/

theorem compare_of_compare?_approx:
  ∀ (i₁ i₂ : Interval), compare? i₁ i₂ = some o →
    ∀ x₁ ∈ approx i₁, ∀ x₂ ∈ approx i₂, compare x₁ x₂ = o := by
      -- TODO: this proof can probably be automated a lot better
      intros i₁ i₂ cmp x₁ in₁ x₂ in₂
      unfold compare? at cmp
      split_ifs at cmp with hnan hgt hlt heq
        <;> simp at hnan
        <;> cases hnan
        <;> rw [Option.some.injEq] at cmp
        <;> rw [←cmp]
      . have lt: x₂ < x₁ := by calc
          x₂ ≤ i₂.hi.val := by apply le_hi <;> assumption
           _ < i₁.lo.val := by simpa using hgt
           _ ≤ x₁        := by apply lo_le <;> assumption
        simpa [compare_gt_iff_gt] using lt
      . have lt: x₁ < x₂ := by calc
          x₁ ≤ i₁.hi.val := by apply le_hi <;> assumption
           _ < i₂.lo.val := by simpa using hlt
           _ ≤ x₂        := by apply lo_le <;> assumption
        simpa [compare_lt_iff_lt] using lt
      . have le₁₂: x₁ ≤ x₂ := by calc
          x₁ ≤ i₁.hi.val := by apply le_hi <;> assumption
           _ = i₂.lo.val := by rw [heq.2]
           _ ≤ x₂        := by apply lo_le <;> assumption
        have le₂₁: x₂ ≤ x₁ := by calc
          x₂ ≤ i₂.hi.val := by apply le_hi <;> assumption
           _ = i₁.lo.val := by rw [heq.1]
           _ ≤ x₁        := by apply lo_le <;> assumption
        have eq: x₁ = x₂ := by exact eq_of_le_of_le le₁₂ le₂₁
        simpa [compare_eq_iff_eq]

lemma mem_approx_nan : ∀ (x : ℝ) (i : Interval), i = nan → x ∈ approx i := by simp

lemma exists_in [Membership α β] {p : α → Prop} {y : β} (x : α) (h: x ∈ y) (h': p x) : ∃ x ∈ y, p x := by exists x

/--
`compare?` only returns `none` if the intervals are incomparable. This is not
necessary for correctness of FilteredReal, but ensures that we don't evaluate
thunks unnecessarily.
-/
theorem compare?_complete:
  ∀ (x y : Interval), compare? x y = none →
    ∃ x₁ ∈ approx x, ∃ x₂ ∈ approx x, ∃ y₁ ∈ approx y, ∃ y₂ ∈ approx y,
      compare x₁ y₁ ≠ compare x₂ y₂ := by
        unfold compare?
        intros x y cmp
        split_ifs at cmp with nan
        . cases nan
          . -- x = nan
            let x₁ := y.lo.val - 1
            let x₂ := y.hi.val + 1
            let y₁ := y.lo.val
            let y₂ := y.hi.val

            apply exists_in x₁ (by apply mem_approx_nan; assumption)
            apply exists_in x₂ (by apply mem_approx_nan; assumption)
            apply exists_in y₁ (by exact lo_mem)
            apply exists_in y₂ (by exact hi_mem)

            have hlt: compare x₁ y₁ = .lt := by rw [compare_lt_iff_lt]; simp [x₁, y₁]
            have hgt: compare x₂ y₂ = .gt := by rw [compare_gt_iff_gt]; simp [x₂, y₂]

            simp [hlt, hgt]
          . -- y = nan (TODO: this repeats the x = nan case; abstract it out)
            let x₁ := x.lo.val
            let x₂ := x.hi.val
            let y₁ := x.lo.val - 1
            let y₂ := x.hi.val + 1

            apply exists_in x₁ (by exact lo_mem)
            apply exists_in x₂ (by exact hi_mem)
            apply exists_in y₁ (by apply mem_approx_nan; assumption)
            apply exists_in y₂ (by apply mem_approx_nan; assumption)

            have hlt: compare x₁ y₁ = .gt := by rw [compare_gt_iff_gt]; simp [x₁, y₁]
            have hgt: compare x₂ y₂ = .lt := by rw [compare_lt_iff_lt]; simp [x₂, y₂]

            simp [hlt, hgt]

        . sorry

end Interval


/-! ## Equality ---------------------------------------------------------------/

section BEq

variable [BEq α] (f : α → ℝ)

instance: BEq (FilteredEmbedding f) where
  beq x y := match Interval.compare? x.range.i y.range.i with
    | some .eq => true
    | some .lt | some .gt => false
    | none => x.value.get == y.value.get

variable [LawfulBEq α]

theorem eqv_of_beq: ∀ (x y : FilteredEmbedding f), x == y → x.toReal = y.toReal := by
  intros x y h
  simp only [BEq.beq] at h
  split at h
  . simp [←compare_eq_iff_eq, Interval.compare_of_compare?_approx _ _ (by assumption), Around.mem]
  . contradiction
  . contradiction
  . simp at h; simp [h]

theorem beq_of_eqv: ∀ (x y : FilteredEmbedding f), eqv f x y → x == y := by
  simp only [BEq.beq]
  intros x y h
  split
  . rfl
  . have lt: x.toReal < y.toReal := by
      simp [←compare_lt_iff_lt, Interval.compare_of_compare?_approx _ _ (by assumption), Around.mem]
    simp at h
    simp [h] at lt
  . have gt: x.toReal > y.toReal := by
      simp [←compare_gt_iff_gt, Interval.compare_of_compare?_approx _ _ (by assumption), Around.mem]
    simp at h
    simp [h] at gt
  . simpa using h


-- TODO: implement BEq and/or DecidableEq
-- TODO: comparisons
-- TODO: CGLean.Algebra.Signed

