// Functions that our code calls but that live in modules web/prune.py cuts
// from the link, copied here from those modules' generated C.
//
// These arise because Lean's compiler reuses specializations across modules:
// if a module happens to have already compiled, say, `Nat.cast : ℕ → ℚ`, code
// in later modules calls that copy rather than making its own, even when the
// module holding it is a tactic. Before adding one, check that it uses nothing
// its module's initializer would have set up (it can't, if, like these, it
// only calls other functions).

#include <lean/lean.h>

lean_object * l_Rat_ofInt(lean_object *);

// From Mathlib/Tactic/Linarith/Oracle/SimplexAlgorithm.c: Nat.cast : ℕ → ℚ
LEAN_EXPORT lean_object * lp_mathlib_Nat_cast___at___00Mathlib_Tactic_Linarith_SimplexAlgorithm_postprocess_spec__0(lean_object * a) {
  return l_Rat_ofInt(lean_nat_to_int(a));
}
