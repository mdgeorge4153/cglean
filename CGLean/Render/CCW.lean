import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Drawing counterclockwise claims

A `Turn p q r` is drawn as the two segments meeting at `q` together with an arc
sweeping from `qp` to `qr`, which is where the orientation is legible: the arc
carries an arrowhead, so the direction of the turn is shown rather than
inferred from the order of the labels.

Goals are drawn dashed and hypotheses solid, so that several claims about the
same points can share a diagram. Where they would still coincide, each claim
carries a small offset applied to its segments and arc but not to the points:
the points are the data and stay where they are, while the lines joining them
are annotation and may slide.
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
  /-- Translation applied to this claim's segments and arc, but not to the
  points themselves. Several claims about the same points would otherwise draw
  on top of one another; the points stay where they are, and only the
  annotation connecting them moves. -/
  offset : Float × Float := (0.0, 0.0)
  deriving Inhabited

namespace Turn

private def sub (a b : Float × Float) : Float × Float := (a.1 - b.1, a.2 - b.2)
private def add (a b : Float × Float) : Float × Float := (a.1 + b.1, a.2 + b.2)
private def smul (s : Float) (a : Float × Float) : Float × Float := (s * a.1, s * a.2)
private def angle (v : Float × Float) : Float := Float.atan2 v.2 v.1
private def polar (c : Float × Float) (ρ θ : Float) : Float × Float :=
  add c (ρ * Float.cos θ, ρ * Float.sin θ)

/-- The signed angle from `a` to `b`, in `(-π, π]`, so that the arc drawn is
always the minor one. -/
private def sweep (a b : Float) : Float :=
  let π := 3.14159265358979
  let d := b - a
  if d > π then d - 2*π else if d ≤ -π then d + 2*π else d

private def dist (a b : Float × Float) : Float :=
  let d := sub b a
  Float.sqrt (d.1 * d.1 + d.2 * d.2)

/-- Round dots evenly spaced along a path, `Element` carrying no dash pattern.
Dots rather than short dashes: on an arc, and at these lengths, a dash is only
distinguishable from a solid line by looking closely, whereas a dot is not. -/
private def dotted (frame : Frame) (path : Array (Float × Float))
    (gap : Float := 0.16) (ρ : Float := 0.035) : Array (Element frame) := Id.run do
  let total := (Array.range (path.size - 1)).foldl
    (fun acc i => acc + dist path[i]! path[i+1]!) 0.0
  if total ≤ 0.0 then return #[]
  let n := max 2 (total / gap).toUInt32.toNat
  let mut out := #[]
  let mut seg := 0
  let mut used := 0.0
  for k in [:n+1] do
    let want := total * k.toFloat / n.toFloat
    while seg + 1 < path.size - 1 && used + dist path[seg]! path[seg+1]! < want do
      used := used + dist path[seg]! path[seg+1]!
      seg := seg + 1
    let a := path[seg]!
    let b := path[seg+1]!
    let len := dist a b
    let t := if len ≤ 0.0 then 0.0 else min 1.0 ((want - used) / len)
    out := out.push ((circle (add a (smul t (sub b a))) (.abs ρ)))
  return out

/-- Two short strokes closing back on the arc, marking its far end. -/
private def arrowHead (frame : Frame) (tip : Float × Float) (dir : Float) (s : Float) :
    Array (Element frame) :=
  let back := dir + 3.14159265358979
  #[ line tip (polar tip s (back + 0.4)), line tip (polar tip s (back - 0.4)) ]

/-- The elements of one turn: two segments, the arc at `q` with its arrowhead,
and a dot and label at each point. -/
def elements (frame : Frame) (t : Turn) : Array (Element frame) := Id.run do
  let ρ := t.ρ
  let p := add t.p t.offset
  let q := add t.q t.offset
  let r := add t.r t.offset
  let stroke : Element frame → Element frame := fun e =>
    e.setStroke (if t.isGoal then (0.35, 0.35, 0.45) else (0.1, 0.1, 0.2)) (.px 2)
  let arcStroke : Element frame → Element frame := fun e =>
    e.setStroke (if t.isGoal then (0.55, 0.3, 0.75) else (0.85, 0.2, 0.15)) (.px 2)
  -- the two segments
  let mut out : Array (Element frame) :=
    if t.isGoal then
      (dotted frame #[p, q] ++ dotted frame #[q, r]).map (fun e =>
        e.setFill (0.35, 0.35, 0.45))
    else #[stroke (line p q), stroke (line q r)]
  -- the arc at q, from the ray towards p to the ray towards r, the short way
  let a0 := angle (sub p q)
  let a1 := angle (sub r q)
  let Δ  := sweep a0 a1
  let steps := 24
  let raw : Array (Float × Float) := (Array.range (steps + 1)).map fun i =>
    polar q ρ (a0 + Δ * i.toFloat / steps.toFloat)
  let pts : Array (Point frame) := raw.map fun (x, y) => .abs x y
  out := out ++
    (if t.isGoal then
      (dotted frame raw 0.12 0.03).map (fun e => e.setFill (0.55, 0.3, 0.75))
     else #[arcStroke (polyline pts)])
  -- arrowhead at the far end, tangent to the arc
  let tangent := a1 + (if Δ ≥ 0 then 1.5707963 else -1.5707963)
  out := out ++ (arrowHead frame (polar q ρ a1) tangent 0.12).map arcStroke
  return out

/-- Dots and labels for the points, drawn last so that they sit above the
connectors. Each label is backed by a patch of the diagram's own background,
so that a line passing behind it is interrupted rather than crossing the
glyph. -/
def marks (frame : Frame) (named : Array (String × (Float × Float)))
    (bg : Color := (1.0, 1.0, 1.0)) : Array (Element frame) :=
  let ink : Color := (0.1, 0.1, 0.2)
  let size := 0.28
  named.flatMap fun (nm, pt) =>
    let anchor := add pt (0.11, 0.09)
    let w := 0.62 * size * nm.length.toFloat + 0.1
    #[ (rect (add anchor (-0.05, -0.06)) (.abs w) (.abs (size + 0.12))).setFill bg,
       text anchor nm (.abs size) |>.setFill ink,
       (circle pt (.abs 0.06)).setFill ink ]

end Turn

/-- Several claims in one picture: a solid ground, then the connectors, then
the points and their labels on top. -/
def turnsSvg (frame : Frame) (ts : Array Turn)
    (named : Array (String × (Float × Float)))
    (bg : Color := (1.0, 1.0, 1.0)) : Svg frame :=
  let ground : Element frame :=
    (rect (.abs frame.xmin frame.ymin) (.abs frame.xSize) (.abs frame.ySize)).setFill bg
  { elements := #[ground] ++ ts.flatMap (Turn.elements frame) ++ Turn.marks frame named bg }

end CGLean.Render
