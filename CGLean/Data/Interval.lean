import Ray.Approx.Floating.Order
import Ray.Approx.Interval.Basic

/--
# Facts about intervals

This stuff can maybe be upstreamed
-/

instance: BoundedOrder Floating where
  top := sorry
  bot := nan
  le_top := sorry
  bot_le := sorry

def Interval.glb (i : Interval) : Floating :=
  if i.lo = nan then ⊥ else i.lo

lemma glb_mem (i : Interval) : i.glb.val ∈ approx i := by sorry
lemma ge_glb (i : Interval)  : ∀ f : Floating, f.val ∈ approx i → f ≥ i.glb := by sorry

def Interval.lub (i : Interval) : Floating :=
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
      _ ≤ b.hi.val := by apply Interval.le
      _ < c.lo.val := by assumption

instance: IsStrictOrder Interval (· < ·) where

