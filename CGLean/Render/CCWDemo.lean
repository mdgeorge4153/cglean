import CGLean.Render.CCW

/-!
# The counterclockwise axioms, drawn

One picture per axiom, in the arrangement of the hand sketch: hypotheses in
blue, the conclusion in orange. Coordinates are given explicitly here; laying
them out from the constraints alone is the next step.

Hypotheses are stated with the pivot first throughout, which is the cyclic
rotation that makes the shape of each axiom visible: interiority says the inner
point sees all three edges the same way, and transitivity says the same of a
point off to one side.
-/

namespace CGLean.Render

open ProofWidgets Svg

def frame : Frame where
  xmin := -2.6; ymin := -2.2; xSize := 5.2; width := 420; height := 340

/-- Cyclic symmetry: `ccw p q r → ccw q r p`. Same three points, same turn,
read from a different starting vertex. -/
def cyclic : Svg frame :=
  let p : Float × Float := (1.4, -1.4)
  let q : Float × Float := (1.4, 1.4)
  let r : Float × Float := (-1.8, 0.0)
  turnsSvg frame
    #[ {p := p, q := q, r := r},
       {p := q, q := r, r := p, isGoal := true} ]
    #[("p", p), ("q", q), ("r", r)]

/-- Antisymmetry, in the reversed form `ccw p q r → ¬ ccw r q p`: the same walk
taken backwards, which is easier to see than transposing two of the three. -/
def reversal : Svg frame :=
  let p : Float × Float := (1.4, -1.4)
  let q : Float × Float := (1.4, 1.4)
  let r : Float × Float := (-1.8, 0.0)
  turnsSvg frame
    #[ {p := p, q := q, r := r},
       {p := r, q := q, r := p, isGoal := true, ρ := 0.5} ]
    #[("p", p), ("q", q), ("r", r)]

/-- Interiority: `ccw t q r → ccw t r p → ccw t p q → ccw p q r`. The three
hypotheses share the pivot `t`, which sits inside the triangle. -/
def interiority : Svg frame :=
  let p : Float × Float := (0.4, -1.7)
  let q : Float × Float := (1.9, 1.2)
  let r : Float × Float := (-2.0, 0.6)
  let t : Float × Float := (0.0, 0.0)
  turnsSvg frame
    #[ {p := t, q := q, r := r, ρ := 0.42},
       {p := t, q := r, r := p, ρ := 0.42},
       {p := t, q := p, r := q, ρ := 0.42},
       {p := p, q := q, r := r, isGoal := true} ]
    #[("p", p), ("q", q), ("r", r), ("t", t)]

/-- Transitivity: `ccw s t p → ccw s t q → ccw s t r → ccw s p q → ccw s q r →
ccw s p r`. The first three premises confine `p`, `q` and `r` to one side of
`s t`, and are drawn in a lighter blue since they are what makes the angular
order around `s` linear rather than cyclic; the last two are the order itself.

Without them the conclusion is false, so they are not decoration: three points
spread over more than half a revolution around `s` step forwards twice and
still arrive behind where they started. -/
def transitivity : Svg frame :=
  let s : Float × Float := (-2.2, -0.2)
  let t : Float × Float := (0.2, -1.9)
  let p : Float × Float := (1.9, -0.9)
  let q : Float × Float := (2.0, 0.4)
  let r : Float × Float := (1.1, 1.7)
  let side : Color := (0.55, 0.71, 0.87)
  turnsSvg frame
    #[ {p := s, q := t, r := p, ρ := 0.50, colour := some side},
       {p := s, q := t, r := q, ρ := 0.75, colour := some side},
       {p := s, q := t, r := r, ρ := 1.00, colour := some side},
       {p := s, q := p, r := q, ρ := 1.35},
       {p := s, q := q, r := r, ρ := 1.35},
       {p := s, q := p, r := r, isGoal := true, ρ := 1.75} ]
    #[("s", s), ("t", t), ("p", p), ("q", q), ("r", r)]

end CGLean.Render

open CGLean.Render ProofWidgets in
#html cyclic.toHtml

open CGLean.Render ProofWidgets in
#html reversal.toHtml

open CGLean.Render ProofWidgets in
#html interiority.toHtml

open CGLean.Render ProofWidgets in
#html transitivity.toHtml
