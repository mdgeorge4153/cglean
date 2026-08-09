import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Drawing counterclockwise claims

A `Turn p q r` is drawn as the two rays leaving the pivot `p` towards `q` and
`r`, together with an arc at `p` sweeping from the first to the second. The arc
carries an arrowhead, so the direction of the turn is shown rather than
inferred from the order of the labels; and since a counterclockwise turn is by
definition one of less than half a revolution, the arc drawn is always the
minor one and always sweeps anticlockwise.

Drawing at the pivot is what makes several claims about a common pivot
comparable. Their arcs share a centre and nest, so a picture of `ccw t p q`,
`ccw t q r` and `ccw t p r` can be read as an angular order around `t` rather
than as three unrelated wedges.

Colour distinguishes goals from hypotheses, in mid-tone hues that hold up
against either a light or a dark background since the diagram supplies none of
its own. Only the arcs are coloured. The rays are drawn in a neutral grey
because they belong to the points rather than to any one claim — two claims
about a common pivot draw the same ray, and colouring it would mean whichever
was drawn last won. Claims sharing a pivot are separated by giving their arcs
different radii, which also lets a chain of them be read as an angular order.
-/

namespace CGLean.Render

open ProofWidgets Svg

/-- A claim that `p`, `q`, `r` make a counterclockwise turn, positioned for
drawing, with `p` as the pivot. `isGoal` selects the conclusion colour. -/
structure Turn where
  p : Float × Float
  q : Float × Float
  r : Float × Float
  isGoal : Bool := false
  /-- Radius of the arc at the pivot `p`. -/
  ρ : Float := 0.35
  /-- Colour of this claim's connectors. Defaults by `isGoal`; set it to tell
  several hypotheses in one picture apart. -/
  colour : Option Color := none
  /-- How far to slide this claim's connectors along the bisector of the angle
  at the pivot, positive being into the wedge. The points themselves do not move:
  they are the data, while the lines joining them are annotation.

  The bisector is the right axis because it is the one direction determined by
  the claim itself. Two claims sharing a vertex and a pair of rays share a
  bisector, so opposite offsets separate them symmetrically; claims sharing
  only a pivot have bisectors that already point apart, and fan without being
  told to. -/
  offset : Float := 0.0
  deriving Inhabited

namespace Turn

private def sub (a b : Float × Float) : Float × Float := (a.1 - b.1, a.2 - b.2)
private def add (a b : Float × Float) : Float × Float := (a.1 + b.1, a.2 + b.2)
private def smul (s : Float) (a : Float × Float) : Float × Float := (s * a.1, s * a.2)
private def angle (v : Float × Float) : Float := Float.atan2 v.2 v.1
private def polar (c : Float × Float) (ρ θ : Float) : Float × Float :=
  add c (ρ * Float.cos θ, ρ * Float.sin θ)

private def norm (v : Float × Float) : Float := Float.sqrt (v.1 * v.1 + v.2 * v.2)
private def unit (v : Float × Float) : Float × Float :=
  let n := norm v
  if n ≤ 1e-9 then (0.0, 0.0) else smul (1.0 / n) v

/-- Unit vector along the bisector of the angle `p q r`, pointing into the
wedge. Degenerates when the rays are opposed, where the wedge has no interior;
the perpendicular is used instead so that an offset still does something. -/
private def bisector (p q r : Float × Float) : Float × Float :=
  let b := add (unit (sub p q)) (unit (sub r q))
  if norm b ≤ 1e-6 then
    let u := unit (sub p q)
    (-u.2, u.1)
  else unit b

/-- The counterclockwise angle from `a` to `b`, in `[0, 2π)`.

Always counterclockwise, never the minor arc: a `Turn` asserts that its three
points make a counterclockwise turn, so the sweep is under half a revolution
whenever the claim holds of the coordinates given. Points that in fact turn
clockwise draw a reflex arc, which is the diagram reporting that it has been
asked to picture something false. -/
private def sweep (a b : Float) : Float :=
  let τ := 6.28318530717959
  let d := b - a
  if d < 0 then d + τ else d

/-- Two short strokes closing back on the arc, marking its far end. -/
private def arrowHead (frame : Frame) (tip : Float × Float) (dir : Float) (s : Float) :
    Array (Element frame) :=
  let back := dir + 3.14159265358979
  #[ line tip (polar tip s (back + 0.4)), line tip (polar tip s (back - 0.4)) ]

/-- The elements of one turn: the two rays from the pivot, and the arc between
them with its arrowhead. -/
def elements (frame : Frame) (t : Turn) : Array (Element frame) := Id.run do
  let ρ := t.ρ
  let off := smul t.offset (bisector t.q t.p t.r)
  let p := add t.p off
  let q := add t.q off
  let r := add t.r off
  -- blue and orange: mid-luminance, so legible on either background, and the
  -- usual pair that survives the common colour blindnesses
  let c : Color := t.colour.getD (if t.isGoal then (0.93, 0.53, 0.11) else (0.16, 0.48, 0.84))
  let arcStroke : Element frame → Element frame := fun e => e.setStroke c (.px 3)
  -- the rays are shared scaffolding: two claims about the same pivot draw the
  -- same ray, so colouring them would let whichever is drawn last win
  let stroke : Element frame → Element frame := fun e => e.setStroke (0.55, 0.57, 0.62) (.px 2)
  let mut out : Array (Element frame) := #[stroke (line p q), stroke (line p r)]
  -- the arc at the pivot, from the ray towards q to the ray towards r
  let a0 := angle (sub q p)
  let a1 := angle (sub r p)
  let Δ  := sweep a0 a1
  let steps := 24
  let raw : Array (Float × Float) := (Array.range (steps + 1)).map fun i =>
    polar p ρ (a0 + Δ * i.toFloat / steps.toFloat)
  let pts : Array (Point frame) := raw.map fun (x, y) => .abs x y
  out := out.push (arcStroke (polyline pts))
  -- arrowhead at the far end, tangent to the arc
  let tangent := a1 + 1.5707963
  out := out ++ (arrowHead frame (polar p ρ a1) tangent 0.12).map arcStroke
  return out

/-- Dots and labels for the points, drawn last so that they sit above the
connectors. -/
def marks (frame : Frame) (named : Array (String × (Float × Float))) :
    Array (Element frame) :=
  let ink : Color := (0.45, 0.47, 0.53)
  named.flatMap fun (nm, pt) =>
    #[ (circle pt (.abs 0.06)).setFill ink,
       text (add pt (0.11, 0.09)) nm (.abs 0.28) |>.setFill ink ]

end Turn

/-- Several claims in one picture: the connectors, then the points and their
labels on top. -/
def turnsSvg (frame : Frame) (ts : Array Turn)
    (named : Array (String × (Float × Float))) : Svg frame :=
  { elements := ts.flatMap (Turn.elements frame) ++ Turn.marks frame named }

end CGLean.Render
