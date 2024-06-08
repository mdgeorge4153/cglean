import Ray.Approx.Floating.Order
import Ray.Approx.Interval.Basic

namespace Interval

/--
# Facts about intervals

This stuff can maybe be upstreamed
-/

instance: BoundedOrder Floating where
  top := sorry
  bot := nan
  le_top := sorry
  bot_le := sorry

def glb (i : Interval) : Floating :=
  if i.lo = nan then ⊥ else i.lo

lemma glb_mem (i : Interval) : i.glb.val ∈ approx i := by sorry
lemma ge_glb (i : Interval)  : ∀ f : Floating, f.val ∈ approx i → f ≥ i.glb := by sorry

def lub (i : Interval) : Floating :=
  if i.hi = nan then ⊤ else i.hi

lemma lub_mem (i : Interval) : i.lub.val ∈ approx i := by sorry
lemma le_lub  (i : Interval) : ∀ f : Floating, f.val ∈ approx i → f ≤ i.lub := by sorry

/-
i₁ < i₂ : everything in i₁ is < everything in i₂
 is transitive
 is irreflexive
 is asymmetric

as a partial order:
 everything in i₁ is < everything in i₂ or i₁ = i₂

i₁ ≤ i₂ : everything in i₁ is ≤ everything in i₂
  is transitive
  not reflexive
  is antisymmetric

-/

@[simps] instance: LT Interval where
  lt x y := x.hi < y.lo

instance: IsIrrefl Interval (· < ·) where
  irrefl := by simp [Floating.blt_eq_lt, Bool.decide_coe]
  
instance: IsTrans Interval (· < ·) where
  trans := by
    simp
    intros a b c altb bltc
    calc a.hi.val
      _ < b.lo.val := by assumption
      _ ≤ b.hi.val := by apply le
      _ < c.lo.val := by assumption

instance: IsStrictOrder Interval (· < ·) where

/-! ## Comparing intervals ----------------------------------------------------/

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
If `compare?` returns `some o`, then comparing any elements of the intervals
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

-- theorem compare?_complete:
--   ∀ (x y : Interval), compare? x y = none →
--     ∃ x₁ ∈ approx x, ∃ x₂ ∈ approx x, ∃ y₁ ∈ approx y, ∃ y₂ ∈ approx y,
--       compare x₁ y₁ ≠ compare x₂ y₂ := by
--         intros x y cmp

        
        

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
        split_ifs at cmp with nan gt lt eq
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

        . apply exists_in x.glb.val (by apply glb_mem)
          apply exists_in x.lub.val (by apply lub_mem)
          apply exists_in y.lub.val (by apply lub_mem)
          apply exists_in y.glb.val (by apply glb_mem)

          have cmp1: x.glb.val ≤ y.lub.val := by sorry
          have cmp2: x.lub.val ≥ y.glb.val := by sorry

          cases h1: (compare x.glb.val y.lub.val)
            <;> cases h2: (compare x.lub.val y.glb.val)
              <;> simp
          case neg.lt.lt => rw [←compare_ge_iff_ge] at *; contradiction
          case neg.gt.gt => rw [←compare_le_iff_le] at *; contradiction
          case neg.eq.eq =>
            rw [compare_eq_iff_eq] at *
            simp [nan, glb] at *
            sorry

end Interval

