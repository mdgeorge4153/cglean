/-!
# Counterclockwise systems

Knuth's axiomatisation of orientation, from *Axioms and Hulls*. A ternary
relation `ccw p q r`, read as "the three points are traversed
counterclockwise", is asked to satisfy five laws. Algorithms proved from the
laws alone hold of every model, and there are models not arising from any
placement of points in the plane, so such proofs cover strictly more than the
concrete case.

Only four are laws here. Cyclic symmetry, antisymmetry, interiority and
transitivity are theorems about points with coordinates in a linearly ordered
ring. Non-degeneracy is not: it asserts that no three points are collinear,
which is an assumption about a configuration rather than a law of the plane,
and assuming it would rule out exactly the degenerate arrangements this
development means to support. It is therefore absent, and every result is
expected to hold with collinear points present.

Nothing has to be weakened to leave it out. All four remaining laws are
conditional on turns that are already counterclockwise, so a collinear triple
satisfies their hypotheses vacuously and they stay true verbatim. Collinearity
is detected instead by the three-valued `CGLean.orientation`, which reports
`.zero`; see `CGLean/Geometry/Orientation.lean`.

The four laws say something about a fixed pivot and something between pivots.
Antisymmetry and transitivity are laws of `ccw p` as a relation on the
remaining two arguments; cyclic symmetry and interiority relate the relations
at different pivots. See `notes/angular-order.md` for what `ccw p` is as an
order — a strict total order on a half-plane through `p`, and no more than
that.
-/

namespace CGLean

/-- A ternary orientation relation satisfying those of Knuth's axioms that hold
of points in the plane: cyclic symmetry, antisymmetry, interiority and
transitivity.

Non-degeneracy is deliberately absent, so collinear points are permitted and a
triple may satisfy neither `ccw p q r` nor `ccw p r q`. -/
class CCWSystem (P : Type) where
  /-- The orientation relation. `ccw p q r` reads as a counterclockwise turn
  from `p` through `q` to `r`, with `p` as the pivot. -/
  ccw : P → P → P → Prop
  /-- Knuth's axiom 1: the relation depends on the cyclic order of its
  arguments, not on which is written first. -/
  cyclic {p q r : P} : ccw p q r → ccw q r p
  /-- Knuth's axiom 2: exchanging the two points seen from the pivot reverses
  the turn, so at most one of the two orders is counterclockwise. -/
  antisymm {p q r : P} : ccw p q r → ¬ ccw p r q
  /-- Knuth's axiom 4: a point `t` seeing all three edges of `p q r` from the
  same side lies inside it, and then `p q r` turns counterclockwise. -/
  interiority {p q r t : P} : ccw t q r → ccw p t r → ccw p q t → ccw p q r
  /-- Knuth's axiom 5: seen from `t`, the order is transitive on points lying
  to one side of the line `t s`. The three hypotheses naming `s` are what
  confine `p`, `q` and `r` to that side; without them the order is cyclic and
  the conclusion fails. -/
  transitivity {p q r s t : P} :
    ccw t s p → ccw t s q → ccw t s r → ccw t p q → ccw t q r → ccw t p r

export CCWSystem (ccw)

end CGLean
