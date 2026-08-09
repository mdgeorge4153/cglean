import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Drawing counterclockwise claims

A `Turn p q r` is drawn as the two segments meeting at `q` together with an arc
sweeping from `qp` to `qr`, which is where the orientation is legible: the arc
carries an arrowhead, so the direction of the turn is shown rather than
inferred from the order of the labels.

Goals and hypotheses are told apart by colour, in mid-tone hues that hold up
against either a light or a dark background since the diagram supplies none of
its own. Where two claims would coincide, each carries a small offset applied
to its segments and arc but not to the points: the points are the data and stay
where they are, while the lines joining them are annotation and may slide.
-/

namespace CGLean.Render

open ProofWidgets Svg

/-- A claim that `p`, `q`, `r` make a counterclockwise turn, positioned for
drawing. `isGoal` selects the dashed rendering. -/
structure Turn where
  p : Float × Float
  q : Float × Float
  r : Float × Float
  isGoal : Bool := false
  /-- Radius of the arc at `q`. -/
  ρ : Float := 0.35
  /-- Colour of this claim's connectors. Defaults by `isGoal`; set it to tell
  several hypotheses in one picture apart. -/
  colour : Option Color := none
  /-- How far to slide this claim's connectors along the bisector of the angle
  at `q`, positive being into the wedge. The points themselves do not move:
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

/-- The signed angle from `a` to `b`, in `(-π, π]`, so that the arc drawn is
always the minor one. -/
private def sweep (a b : Float) : Float :=
  let π := 3.14159265358979
  let d := b - a
  if d > π then d - 2*π else if d ≤ -π then d + 2*π else d

/-- Two short strokes closing back on the arc, marking its far end. -/
private def arrowHead (frame : Frame) (tip : Float × Float) (dir : Float) (s : Float) :
    Array (Element frame) :=
  let back := dir + 3.14159265358979
  #[ line tip (polar tip s (back + 0.4)), line tip (polar tip s (back - 0.4)) ]

/-- The elements of one turn: two segments, the arc at `q` with its arrowhead,
and a dot and label at each point. -/
def elements (frame : Frame) (t : Turn) : Array (Element frame) := Id.run do
  let ρ := t.ρ
  let off := smul t.offset (bisector t.p t.q t.r)
  let p := add t.p off
  let q := add t.q off
  let r := add t.r off
  -- blue and orange: mid-luminance, so legible on either background, and the
  -- usual pair that survives the common colour blindnesses
  let c : Color := t.colour.getD (if t.isGoal then (0.93, 0.53, 0.11) else (0.16, 0.48, 0.84))
  let stroke : Element frame → Element frame := fun e => e.setStroke c (.px 2)
  let arcStroke := stroke
  -- the two segments
  let mut out : Array (Element frame) := #[stroke (line p q), stroke (line q r)]
  -- the arc at q, from the ray towards p to the ray towards r, the short way
  let a0 := angle (sub p q)
  let a1 := angle (sub r q)
  let Δ  := sweep a0 a1
  let steps := 24
  let raw : Array (Float × Float) := (Array.range (steps + 1)).map fun i =>
    polar q ρ (a0 + Δ * i.toFloat / steps.toFloat)
  let pts : Array (Point frame) := raw.map fun (x, y) => .abs x y
  out := out.push (arcStroke (polyline pts))
  -- arrowhead at the far end, tangent to the arc
  let tangent := a1 + (if Δ ≥ 0 then 1.5707963 else -1.5707963)
  out := out ++ (arrowHead frame (polar q ρ a1) tangent 0.12).map arcStroke
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
