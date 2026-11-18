module

public import Mathlib.Data.Rat.Cast.Order
public import CGLean.Classes.ApproxStrategy

/-!
# Filtering `ℚ`

An approximation strategy for the rationals, the base of every tower of square
roots. It isn't an instance, since it works for any type of approximations: the
application picks one.
-/

@[expose] public section

namespace CGLean

/-- The rationals, approximated by `RealApprox.ofRat`. -/
@[instance_reducible]
def ApproxStrategy.rat (A : Type) [RealApprox A] : ApproxStrategy ℚ A where
  hom := Erased.mk (Rat.castHom ℝ)
  strictMono := by rw [Erased.out_mk]; exact Rat.cast_strictMono
  approx := RealApprox.ofRat
  mem_approx q := by rw [Erased.out_mk]; exact RealApprox.mem_ofRat q

end CGLean
