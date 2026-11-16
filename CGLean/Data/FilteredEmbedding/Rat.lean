import CGLean.Data.FilteredEmbedding

/-!
# Filtering `ℚ`

The `RealApprox` for the rationals, the base of every tower of square roots.
-/

namespace CGLean

/-- The rationals, bracketed exactly when dyadic and to `ratPrec` otherwise. -/
instance RealApprox.rat : RealApprox ℚ where
  hom := Erased.mk (Rat.castHom ℝ)
  strictMono := by rw [Erased.out_mk]; exact Rat.cast_strictMono
  approx := ofRat
  mem_approx q := by rw [Erased.out_mk]; exact mem_ofRat q

end CGLean
