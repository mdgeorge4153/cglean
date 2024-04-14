import Mathlib.Data.Real.Basic
import Ray.Approx.Interval.Around

import Mathlib.Data.Set.Basic

class ToReal (α : Type) [Add α] where
  toReal : α → ℝ
  additive : ∀ (x y : α), toReal (x + y) = toReal x + toReal y

notation " ⟦ " x " ⟧ " => ToReal.toReal x

variable (α : Type) [Add α] [ToReal α]

structure ApproxData where
  exact : Thunk α
  range : Around ⟦exact.get⟧

namespace ApproxData

instance : LE Interval where
  le x y := x.hi ≤ y.lo

instance : LT Interval where
  lt x y := x.hi < y.lo

def compare (x y : ApproxData α) : Ordering :=
  if x.range.i.hi < y.range.i.lo then .lt
  else if x.range.i.lo > y.range.i.hi then .gt
  else if x.range.i.lo == y.range.i.hi && y.range.i.lo == x.range.i.hi then .eq
  else .lt

instance [BEq α] : BEq (ApproxData α) where
  beq x y :=
    if x.range.hi < y.


abbrev eq (x y : ApproxData α) : Prop :=
  x.exact.get = y.exact.get

instance eqEquiv : Equivalence (eq α) where
  refl := by simp
  -- TODO: seems like these oughta be one-liners
  symm := by
    simp [eq, Thunk.get]
    intros x y h
    rw [h]
  -- TODO: seems like these oughta be one-liners
  trans := by
    simp [eq, Thunk.get]
    intros x y z h1 h2
    rw [h1,h2]

instance setoid : Setoid (ApproxData α) where
  r := ApproxData.eq α 
  iseqv := eqEquiv α

def FastApprox := Quotient (ApproxData.setoid α)

def compare (x y : ApproxData) : Bool :=
  if 

instance : DecidableEq (FastApprox α) where
  x := 0

end ApproxData

instance [Add α] [ToReal α]: Add (ApproxData α) where
  add x y := {
    exact := Thunk.mk fun () => x.exact.get + y.exact.get
    range := {
      i   := x.range.i + y.range.i
      mem := by simp [Thunk.get, ToReal.additive]; mono
    }
  }

def ApproxData.eq (x y : ApproxData α) : bool :=
  ℚ 


