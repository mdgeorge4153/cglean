// Functions that our code calls but that live in modules web/prune.py cuts
// from the link, copied here from those modules' generated C.
//
// These arise because Lean's compiler reuses specializations across modules:
// if a module happens to have already compiled, say, `Nat.cast : ℕ → ℚ`, code
// in later modules calls that copy rather than making its own, even when the
// module holding it is a tactic. Before adding one, check that it uses nothing
// its module's initializer would have set up (it can't, if, like these, it
// only calls other functions).

// None are needed at the moment. The last, Nat.cast : ℕ → ℚ from
// Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm, went with Lean v4.35.0.

#include <lean/lean.h>
