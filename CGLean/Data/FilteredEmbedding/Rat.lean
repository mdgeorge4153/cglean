import CGLean.Data.FilteredEmbedding

/-!
# Filtering `ℚ`

The `RealApprox` for the rationals, the base of every tower of square roots.
-/

namespace CGLean

/-- The rationals, bracketed exactly when dyadic and to `ratPrec` otherwise. -/
def RealApprox.rat : RealApprox ℚ where
  hom := Erased.mk (Rat.castHom ℝ)
  approx := ofRat
  mem_approx q := by rw [Erased.out_mk]; exact mem_ofRat q

instance : Fact (StrictMono RealApprox.rat.toRingHom) :=
  ⟨by rw [RealApprox.toRingHom, RealApprox.rat, Erased.out_mk]; exact Rat.cast_strictMono⟩

end CGLean
