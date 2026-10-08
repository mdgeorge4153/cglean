/-
Drag-and-drop test for the WebAssembly build: a point that can be dragged with
the mouse, but is held inside an axis-aligned box. Coordinates are exact, in
ℚ[√2]: the box's corners are irrational, and clamping uses the order on
`AdjoinSqrt`.

The state lives here, and the page's JavaScript only forwards pointer events
and displays the SVG that `render` returns (see `web/`).
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum
import CGLean.Data.AdjoinSqrt
import CGLean.Classes.Floatable

namespace CGLeanWeb.Drag

open AdjoinSqrt

abbrev K := AdjoinSqrt ℚ 2

instance : Inhabited K := ⟨0⟩

-- TODO: √2 is irrational. Proofs are erased from compiled code, so this sorry
-- doesn't affect what runs.
instance : Nonsquare ℚ 2 := ⟨sorry⟩
instance : Pos ℚ 2 := ⟨by norm_num⟩

def toFloat (a : K) : Float := Floatable.toFloat a.a₁ + Floatable.toFloat a.aₙ * Float.sqrt 2

-- Mouse positions, rounded to hundredths of a unit.
def ofFloat (f : Float) : K := ⟨mkRat (f * 100).round.toInt64.toInt 100, 0⟩

def K.toString (a : K) : String :=
  if a.aₙ = 0 then s!"{a.a₁}"
  else if a.a₁ = 0 then s!"{a.aₙ}√2"
  else s!"{a.a₁} + {a.aₙ}√2"

structure Point where
  x : K
  y : K
  deriving Inhabited

-- An axis-aligned bounding box, given by its corners with the smallest and
-- largest coordinates.
structure Box where
  lo : Point
  hi : Point
  deriving Inhabited

-- The point of the box closest to `p`.
def Box.clamp (b : Box) (p : Point) : Point :=
  ⟨max b.lo.x (min p.x b.hi.x), max b.lo.y (min p.y b.hi.y)⟩

structure State where
  box      : Box
  point    : Point
  dragging : Bool
  deriving Inhabited

def sqrt2 : K := ⟨0, 1⟩

-- Coordinates are SVG user units; the page's viewBox is 0 0 400 400.
def initial : State where
  box      := ⟨⟨50 * sqrt2, 50 * sqrt2⟩, ⟨200 * sqrt2, 150 * sqrt2⟩⟩
  point    := ⟨100 * sqrt2, 100 * sqrt2⟩
  dragging := false

-- Radius of the dot, in SVG units; also how close a press must be to grab it.
def radius : Float := 10

initialize state : IO.Ref State ← IO.mkRef initial

@[export cglean_pointer_down]
def pointerDown (x y : Float) : IO Unit :=
  state.modify fun s =>
    let dx := toFloat s.point.x - x
    let dy := toFloat s.point.y - y
    { s with dragging := Float.sqrt (dx * dx + dy * dy) ≤ radius }

@[export cglean_pointer_move]
def pointerMove (x y : Float) : IO Unit :=
  state.modify fun s =>
    if s.dragging then { s with point := s.box.clamp ⟨ofFloat x, ofFloat y⟩ } else s

@[export cglean_pointer_up]
def pointerUp : IO Unit :=
  state.modify fun s => { s with dragging := false }

@[export cglean_render]
def render : IO String := do
  let s ← state.get
  let b := s.box
  let p := s.point
  let fill := if s.dragging then "#c33" else "#33c"
  return s!"<rect x='{toFloat b.lo.x}' y='{toFloat b.lo.y}' \
    width='{toFloat (b.hi.x - b.lo.x)}' height='{toFloat (b.hi.y - b.lo.y)}' \
    fill='none' stroke='#888' stroke-width='2'/>\
    <circle cx='{toFloat p.x}' cy='{toFloat p.y}' r='{radius}' fill='{fill}'/>\
    <text x='10' y='390' font-size='14'>({K.toString p.x}, {K.toString p.y})</text>"

end CGLeanWeb.Drag
