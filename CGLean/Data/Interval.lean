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

/-- The common order of every member of `x` with every member of `y`, or `none`
when the intervals overlap. -/
def compare? (x y : IntervalDyadic) : Option Ordering :=
  if Dyadic.lt x.hi y.lo then some .lt
  else if Dyadic.lt y.hi x.lo then some .gt
  else if Dyadic.le y.hi x.lo && Dyadic.le x.hi y.lo then some .eq
  else none

/-- When `compare?` commits to an order, every pair of members realises it. -/
theorem compare_of_compare? {x y : IntervalDyadic} {o : Ordering}
    (h : compare? x y = some o) :
    ∀ a ∈ x, ∀ b ∈ y, compare a b = o := by
  intro a ha b hb
  rw [IntervalDyadic.mem_def] at ha hb
  obtain ⟨halo, hahi⟩ := ha
  obtain ⟨hblo, hbhi⟩ := hb
  unfold compare? at h
  split_ifs at h with h1 h2 h3 <;> rw [Option.some.injEq] at h <;> subst h
  · have hd : (x.hi.toRat : ℝ) < (y.lo.toRat : ℝ) := by
      have := (LeanCert.Core.Dyadic.compare_lt_iff x.hi y.lo).mp
        (by simpa [LeanCert.Core.Dyadic.lt] using h1)
      exact_mod_cast this
    exact compare_lt_iff_lt.mpr (by linarith)
  · have hd : (y.hi.toRat : ℝ) < (x.lo.toRat : ℝ) := by
      have := (LeanCert.Core.Dyadic.compare_lt_iff y.hi x.lo).mp
        (by simpa [LeanCert.Core.Dyadic.lt] using h2)
      exact_mod_cast this
    exact compare_gt_iff_gt.mpr (by linarith)
  · obtain ⟨e1, e2⟩ := by simpa using h3
    have hyx : (y.hi.toRat : ℝ) ≤ (x.lo.toRat : ℝ) := by
      exact_mod_cast (LeanCert.Core.Dyadic.le_iff_toRat_le y.hi x.lo).mp e1
    have hxy : (x.hi.toRat : ℝ) ≤ (y.lo.toRat : ℝ) := by
      exact_mod_cast (LeanCert.Core.Dyadic.le_iff_toRat_le x.hi y.lo).mp e2
    exact compare_eq_iff_eq.mpr (by linarith)

/-- `compare?` returns `none` only when the intervals genuinely determine
nothing: there are members realising two different orders. This is not needed
for soundness, but it is what makes the filter worth having --- it says the
exact fallback is taken only when unavoidable. -/
theorem compare?_complete {x y : IntervalDyadic} (h : compare? x y = none) :
    ∃ a₁ ∈ x, ∃ b₁ ∈ y, ∃ a₂ ∈ x, ∃ b₂ ∈ y, compare a₁ b₁ ≠ compare a₂ b₂ := by
  unfold compare? at h
  split_ifs at h with h1 h2 h3
  -- the overlap is non-empty
  have hxle : (x.lo.toRat : ℝ) ≤ (x.hi.toRat : ℝ) := by exact_mod_cast x.le
  have hyle : (y.lo.toRat : ℝ) ≤ (y.hi.toRat : ℝ) := by exact_mod_cast y.le
  have hxy : (x.lo.toRat : ℝ) ≤ (y.hi.toRat : ℝ) := by
    by_contra hc
    exact h2 (by
      have : (y.hi.toRat : ℝ) < (x.lo.toRat : ℝ) := by linarith [not_le.mp hc]
      simpa [LeanCert.Core.Dyadic.lt] using
        (LeanCert.Core.Dyadic.compare_lt_iff y.hi x.lo).mpr (by exact_mod_cast this))
  have hyx : (y.lo.toRat : ℝ) ≤ (x.hi.toRat : ℝ) := by
    by_contra hc
    exact h1 (by
      have : (x.hi.toRat : ℝ) < (y.lo.toRat : ℝ) := by linarith [not_le.mp hc]
      simpa [LeanCert.Core.Dyadic.lt] using
        (LeanCert.Core.Dyadic.compare_lt_iff x.hi y.lo).mpr (by exact_mod_cast this))
  set p : ℝ := max (x.lo.toRat : ℝ) (y.lo.toRat : ℝ) with hp
  have hpx : p ∈ x := by
    rw [IntervalDyadic.mem_def]
    exact ⟨le_max_left _ _, max_le hxle hyx⟩
  have hpy : p ∈ y := by
    rw [IntervalDyadic.mem_def]
    exact ⟨le_max_right _ _, max_le hxy hyle⟩
  -- not both degenerate, so one side has strict slack
  have hslack : (y.lo.toRat : ℝ) < (x.hi.toRat : ℝ) ∨ (x.lo.toRat : ℝ) < (y.hi.toRat : ℝ) := by
    by_contra hc
    push_neg at hc
    exact h3 (by
      simp only [Bool.and_eq_true]
      constructor
      · exact (LeanCert.Core.Dyadic.le_iff_toRat_le y.hi x.lo).mpr (by exact_mod_cast hc.2)
      · exact (LeanCert.Core.Dyadic.le_iff_toRat_le x.hi y.lo).mpr (by exact_mod_cast hc.1))
  rcases hslack with hs | hs
  · refine ⟨p, hpx, p, hpy, (x.hi.toRat : ℝ), ?_, (y.lo.toRat : ℝ), ?_, ?_⟩
    · rw [IntervalDyadic.mem_def]; exact ⟨hxle, le_refl _⟩
    · rw [IntervalDyadic.mem_def]; exact ⟨le_refl _, hyle⟩
    · rw [compare_eq_iff_eq.mpr rfl, compare_gt_iff_gt.mpr hs]; decide
  · refine ⟨p, hpx, p, hpy, (x.lo.toRat : ℝ), ?_, (y.hi.toRat : ℝ), ?_, ?_⟩
    · rw [IntervalDyadic.mem_def]; exact ⟨le_refl _, hxle⟩
    · rw [IntervalDyadic.mem_def]; exact ⟨hyle, le_refl _⟩
    · rw [compare_eq_iff_eq.mpr rfl, compare_lt_iff_lt.mpr hs]; decide

end CGLean
