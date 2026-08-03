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

end CGLean
