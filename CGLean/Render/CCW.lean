import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

/-!
# Drawing counterclockwise claims

A `Turn p q r` is drawn as the two segments meeting at `q` together with an arc
sweeping from `qp` to `qr`, which is where the orientation is legible: the arc
carries an arrowhead, so the direction of the turn is shown rather than
inferred from the order of the labels.

Goals are drawn dashed and hypotheses solid, so that several claims about the
same points can share a diagram.
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

/-- A segment broken into dashes, since `Element` carries no dash pattern. -/
private def dashes (frame : Frame) (a b : Float × Float) (n : Nat) :
    Array (Element frame) := Id.run do
  let mut out := #[]
  for i in [:n] do
    let t0 := i.toFloat / n.toFloat
    let t1 := (i.toFloat + 0.55) / n.toFloat
    out := out.push (line (add a (smul t0 (sub b a))) (add a (smul t1 (sub b a))))
  return out

/-- Two short strokes closing back on the arc, marking its far end. -/
private def arrowHead (frame : Frame) (tip : Float × Float) (dir : Float) (s : Float) :
    Array (Element frame) :=
  let back := dir + 3.14159265358979
  #[ line tip (polar tip s (back + 0.4)), line tip (polar tip s (back - 0.4)) ]

/-- The elements of one turn: two segments, the arc at `q` with its arrowhead,
and a dot and label at each point. -/
def elements (frame : Frame) (t : Turn) (ρ : Float := 0.35) : Array (Element frame) := Id.run do
  let stroke : Element frame → Element frame := fun e =>
    e.setStroke (if t.isGoal then (0.35, 0.35, 0.45) else (0.1, 0.1, 0.2)) (.px 2)
  let arcStroke : Element frame → Element frame := fun e =>
    e.setStroke (if t.isGoal then (0.55, 0.3, 0.75) else (0.85, 0.2, 0.15)) (.px 2)
  -- the two segments
  let mut out : Array (Element frame) :=
    if t.isGoal then (dashes frame t.p t.q 7 ++ dashes frame t.q t.r 7).map stroke
    else #[stroke (line t.p t.q), stroke (line t.q t.r)]
  -- the arc at q, from the ray towards p to the ray towards r, the short way
  let a0 := angle (sub t.p t.q)
  let a1 := angle (sub t.r t.q)
  let Δ  := sweep a0 a1
  let steps := 24
  let pts : Array (Point frame) := (Array.range (steps + 1)).map fun i =>
    let (x, y) := polar t.q ρ (a0 + Δ * i.toFloat / steps.toFloat)
    .abs x y
  out := out.push (arcStroke (polyline pts))
  -- arrowhead at the far end, tangent to the arc
  let tangent := a1 + (if Δ ≥ 0 then 1.5707963 else -1.5707963)
  out := out ++ (arrowHead frame (polar t.q ρ a1) tangent 0.12).map arcStroke
  return out

/-- Dots and labels for the three points. Kept separate so that several turns
sharing points do not stack labels on top of one another. -/
def marks (frame : Frame) (named : Array (String × (Float × Float))) :
    Array (Element frame) :=
  named.flatMap fun (nm, pt) =>
    #[ (circle pt (.abs 0.06)).setFill (0.1, 0.1, 0.2),
       text (add pt (0.12, 0.12)) nm (.abs 0.28) |>.setFill (0.1, 0.1, 0.2) ]

end Turn

/-- Several claims in one picture. -/
def turnsSvg (frame : Frame) (ts : Array Turn)
    (named : Array (String × (Float × Float))) : Svg frame :=
  { elements := ts.flatMap (Turn.elements frame) ++ Turn.marks frame named }

end CGLean.Render
