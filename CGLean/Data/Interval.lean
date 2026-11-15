import LeanCert.Core.IntervalDyadic

/-!
# Comparing intervals

`compare? x y` reports the order of two intervals when they are separated, and
`none` when they overlap. Overlap is exactly the case in which the intervals
carry no information about the order of the values inside them, which is what
`compare?_complete` records.

This is the decision a filtered representation makes before falling back on
exact arithmetic.
-/

namespace CGLean

open LeanCert.Core

/-! # Comparing intervals -/

/-- The common order of every member of `x` with every member of `y`, or `none`
when the intervals overlap. -/
def compare? (x y : IntervalDyadic) : Option Ordering :=
  if x.hi < y.lo then some .lt
  else if y.hi < x.lo then some .gt
  else if compare x.lo x.hi == .eq && compare x.hi y.lo == .eq && compare y.lo y.hi == .eq then some .eq
  else none

/-! # LeanCert helpers -/

@[simp] lemma dyadic_compare_eq_iff (d e : LeanCert.Core.Dyadic) :
    compare d e = .eq ↔ d.toRat = e.toRat := LeanCert.Core.Dyadic.compare_eq_iff d e

@[simp] lemma dyadic_lt_iff_toRat_lt (d e : LeanCert.Core.Dyadic) :
    d < e ↔ d.toRat < e.toRat := by
  simp [LT.lt, LeanCert.Core.Dyadic.lt, LeanCert.Core.Dyadic.compare_lt_iff]

/-! # Main results -/

@[simp] lemma compare?_eq_iff_coords_eq (x y : IntervalDyadic) : compare? x y = some .eq ↔
    x.lo.toRat = x.hi.toRat ∧ x.hi.toRat = y.lo.toRat ∧ y.lo.toRat = y.hi.toRat := by
  unfold compare?
  constructor <;> split_ifs with h1 h2 h3 <;> simp at * <;> aesop

@[simp] lemma compare?_lt_iff_lt (x y : IntervalDyadic) :
    compare? x y = some .lt ↔ x.hi.toRat < y.lo.toRat := by
  unfold compare?
  constructor <;> split_ifs with h1 h2 h3 <;> simp at * <;> linarith [x.le, y.le]

@[simp] lemma compare?_gt_iff_gt (x y : IntervalDyadic) :
    compare? x y = some .gt ↔ y.hi.toRat < x.lo.toRat := by
  unfold compare?
  constructor <;> split_ifs with h1 h2 h3 <;> simp at * <;> linarith [x.le, y.le]


/-- When `compare?` commits to an order, every pair of members realises it. -/
theorem compare_of_compare? {x y : IntervalDyadic} {o : Ordering}
    (h : compare? x y = some o) :
    ∀ a ∈ x, ∀ b ∈ y, compare a b = o := by
  intro a ⟨halo, hahi⟩ b ⟨hblo, hbhi⟩
  unfold compare? at h
  split_ifs at h with h1 h2 h3 <;> rw [Option.some.injEq] at h <;> subst h
  · apply compare_lt_iff_lt.mpr
    have : (x.hi.toRat < (y.lo.toRat : ℝ)) := by
      exact_mod_cast (dyadic_lt_iff_toRat_lt x.hi y.lo).mp h1
    linarith
  . apply compare_gt_iff_gt.mpr
    have : (y.hi.toRat < (x.lo.toRat : ℝ)) := by
      exact_mod_cast (dyadic_lt_iff_toRat_lt y.hi x.lo).mp h2
    linarith
  . apply compare_eq_iff_eq.mpr
    simp at h3
    obtain ⟨⟨he1, he2⟩, he3⟩ := h3
    rw [he1] at halo
    rw [←he3] at hbhi
    rw [←he2] at hblo hbhi
    linarith

/-- `compare?` returns `none` only when the intervals genuinely determine
nothing: there are members realising two different orders. This is not needed
for soundness, but it is what makes the filter worth having --- it says the
exact fallback is taken only when unavoidable. -/
theorem compare?_complete {x y : IntervalDyadic} (h : compare? x y = none) :
    ∃ x₁ ∈ x, ∃ y₁ ∈ y, ∃ x₂ ∈ x, ∃ y₂ ∈ y, compare x₁ y₁ ≠ compare x₂ y₂ := by
  refine ⟨x.lo.toRat, ⟨by simp [x.le], ?_⟩⟩
  refine ⟨y.hi.toRat, ⟨by simp [y.le], ?_⟩⟩
  refine ⟨x.hi.toRat, ⟨by simp [x.le], ?_⟩⟩
  refine ⟨y.lo.toRat, ⟨by simp [y.le], ?_⟩⟩

  have hxle : (x.lo.toRat : ℝ) ≤ (x.hi.toRat : ℝ) := by exact_mod_cast x.le
  have hyle : (y.lo.toRat : ℝ) ≤ (y.hi.toRat : ℝ) := by exact_mod_cast y.le

  unfold compare? at h; split_ifs at h with h1 h2 h3; simp at h3

  intro e; cases hab : compare (x.lo.toRat : ℝ) y.hi.toRat <;> rw [hab, eq_comm] at e
  . simp [compare_lt_iff_lt] at *; linarith
  . simp at *; apply h3 <;> linarith
  . simp [compare_gt_iff_gt] at *; linarith

end CGLean
