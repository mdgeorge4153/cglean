/-
Drag-and-drop test for the WebAssembly build: a point that can be dragged with
the mouse, but is held inside an axis-aligned box. Coordinates are exact, in
CGLean's number type `Filtered ℚ[√2][√3]`: the box's corners are irrational,
and clamping uses its order.

The state lives here, and the page's JavaScript only forwards pointer events
and displays the SVG that `render` returns (see `web/`).
-/
import CGLean.App.NumberType
import CGLean.Classes.Floatable

namespace CGLeanWeb.Drag

open CGLean.NumberType

instance {R : Type} [Floatable R] {n : R} : Floatable (AdjoinSqrt R n) where
  toFloat a := Floatable.toFloat a.a₁ + Floatable.toFloat a.aₙ * (Floatable.toFloat n).sqrt

instance : Inhabited Num := ⟨0⟩

def toFloat (a : Num) : Float := Floatable.toFloat a.get

-- Mouse positions, rounded to hundredths of a unit.
def ofFloat (f : Float) : Num := (mkRat (f * 100).round.toInt64.toInt 100 : ℚ)

-- `a₁ + aₙ√n`, leaving out the parts that are zero. The components are shown
-- with `str`, in parentheses when they have more than one part themselves.
def showSqrt {R : Type} {n : R} [Zero R] [DecidableEq R] (str : R → String) (r : String)
    (a : AdjoinSqrt R n) : String :=
  let paren (x : R) := let t := str x; if t.contains ' ' then s!"({t})" else t
  if a.aₙ = 0 then str a.a₁
  else if a.a₁ = 0 then s!"{paren a.aₙ}√{r}"
  else s!"{paren a.a₁} + {paren a.aₙ}√{r}"

def Num.toString (a : Num) : String :=
  showSqrt (showSqrt (fun q : ℚ => s!"{q}") "2") "3" a.get

structure Point where
  x : Num
  y : Num
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

def sqrt2 : Num := .ofValue ⟨⟨0, 1⟩, 0⟩
def sqrt3 : Num := .ofValue ⟨0, 1⟩

-- Coordinates are SVG user units; the page's viewBox is 0 0 400 400.
def initial : State where
  box      := ⟨⟨50 * sqrt2, 50 * sqrt3⟩, ⟨200 * sqrt2, 150 * sqrt3⟩⟩
  point    := ⟨100 * sqrt2, 100 * sqrt3⟩
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
    <text x='10' y='390' font-size='14'>({Num.toString p.x}, {Num.toString p.y})</text>"

end CGLeanWeb.Drag
