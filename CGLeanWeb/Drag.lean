/-
Drag-and-drop test for the WebAssembly build: a point that can be dragged with
the mouse, but is held inside an axis-aligned box. Coordinates are exact, in
`ℚ[√2][√3]`: the box's corners are irrational, and clamping uses its order.

The page runs it in filtered arithmetic (`Num = Filtered L`). Each drag is
recorded, and on release replayed through both filtered and exact arithmetic
(`L`), so that the two can be timed against each other.

The state lives here, and the page's JavaScript only forwards pointer events
and displays the SVG that `render` returns (see `web/`).
-/
import CGLean.App.NumberType
import CGLean.Classes.Floatable

namespace CGLeanWeb.Drag

open CGLean.NumberType

/-! ## The number types -/

instance {R : Type} [Floatable R] {n : R} : Floatable (AdjoinSqrt R n) where
  toFloat a := Floatable.toFloat a.a₁ + Floatable.toFloat a.aₙ * (Floatable.toFloat n).sqrt

instance : Floatable Num := ⟨fun a => Floatable.toFloat a.get⟩

-- `a₁ + aₙ√n`, leaving out the parts that are zero. The components are shown
-- with `str`, in parentheses when they have more than one part themselves.
def showSqrt {R : Type} {n : R} [Zero R] [DecidableEq R] (str : R → String) (r : String)
    (a : AdjoinSqrt R n) : String :=
  let paren (x : R) := let t := str x; if t.contains ' ' then s!"({t})" else t
  if a.aₙ = 0 then str a.a₁
  else if a.a₁ = 0 then s!"{paren a.aₙ}√{r}"
  else s!"{paren a.a₁} + {paren a.aₙ}√{r}"

instance : ToString K := ⟨showSqrt (fun q : ℚ => s!"{q}") "2"⟩
instance : ToString L := ⟨showSqrt toString "3"⟩
instance : ToString Num := ⟨fun a => toString a.get⟩

instance : Inhabited L := ⟨0⟩
instance : Inhabited Num := ⟨0⟩

/-! ## The demo, for any ordered field `R` -/

section
variable {R : Type} [Field R] [LinearOrder R] [Floatable R] [ToString R]

-- Mouse positions, rounded to hundredths of a unit.
def ofFloat (f : Float) : R := (mkRat (f * 100).round.toInt64.toInt 100 : ℚ)

variable (R) in
structure Point where
  x : R
  y : R

-- An axis-aligned bounding box, given by its corners with the smallest and
-- largest coordinates.
variable (R) in
structure Box where
  lo : Point R
  hi : Point R

-- The point of the box closest to `p`.
def Box.clamp (b : Box R) (p : Point R) : Point R :=
  ⟨max b.lo.x (min p.x b.hi.x), max b.lo.y (min p.y b.hi.y)⟩

variable (R) in
structure State where
  box      : Box R
  point    : Point R
  dragging : Bool

-- Coordinates are SVG user units; the page's viewBox is 0 0 400 400.
def initial (sqrt2 sqrt3 : R) : State R where
  box      := ⟨⟨50 * sqrt2, 50 * sqrt3⟩, ⟨200 * sqrt2, 150 * sqrt3⟩⟩
  point    := ⟨100 * sqrt2, 100 * sqrt3⟩
  dragging := false

-- Radius of the dot, in SVG units; also how close a press must be to grab it.
def radius : Float := 10

def toFloat (a : R) : Float := Floatable.toFloat a

inductive Event where
  | down (x y : Float)
  | move (x y : Float)
  | up

def State.step (s : State R) : Event → State R
  | .down x y =>
    let dx := toFloat s.point.x - x
    let dy := toFloat s.point.y - y
    { s with dragging := Float.sqrt (dx * dx + dy * dy) ≤ radius }
  | .move x y =>
    if s.dragging then { s with point := s.box.clamp ⟨ofFloat x, ofFloat y⟩ } else s
  | .up => { s with dragging := false }

def State.render (s : State R) : String :=
  let b := s.box
  let p := s.point
  let fill := if s.dragging then "#c33" else "#33c"
  s!"<rect x='{toFloat b.lo.x}' y='{toFloat b.lo.y}' \
    width='{toFloat (b.hi.x - b.lo.x)}' height='{toFloat (b.hi.y - b.lo.y)}' \
    fill='none' stroke='#888' stroke-width='2'/>\
    <circle cx='{toFloat p.x}' cy='{toFloat p.y}' r='{radius}' fill='{fill}'/>\
    <text x='10' y='390' font-size='14'>({p.x}, {p.y})</text>"

def Point.map {S : Type} (f : R → S) (p : Point R) : Point S := ⟨f p.x, f p.y⟩

def State.map {S : Type} (f : R → S) (s : State R) : State S :=
  ⟨⟨s.box.lo.map f, s.box.hi.map f⟩, s.point.map f, s.dragging⟩

-- Runs `trace` from `s`, and shows where the point ends up.
def replay (s : State R) (trace : Array Event) : String :=
  let p := (trace.foldl State.step s).point
  s!"({p.x}, {p.y})"

end

/-! ## The live demo, and replays -/

def initialFiltered : State Num := initial (.ofValue ⟨⟨0, 1⟩, 0⟩) (.ofValue ⟨0, 1⟩)

-- A drag for the native benchmark (Bench.lean): press on the dot, then circle
-- around the box's centre, in and out of it.
def syntheticTrace : Array Event := Id.run do
  let mut t := #[.down 141.42 173.2]
  for i in [0:2000] do
    let a := i.toFloat / 50
    let r := 40 + 140 * (Float.sin (a / 7)).abs
    t := t.push (.move (190 + r * Float.cos a) (150 + r * Float.sin a))
  return t.push .up

structure Live where
  state : State Num
  -- The state when the last drag started, and its events since.
  start : State Num
  trace : Array Event

instance : Nonempty Live := ⟨⟨initialFiltered, initialFiltered, #[]⟩⟩

initialize live : IO.Ref Live ← IO.mkRef ⟨initialFiltered, initialFiltered, #[]⟩

-- A press that grabs the dot starts a new trace; one that misses clears it.
def handle (e : Event) : IO Unit :=
  live.modify fun l =>
    let state := l.state.step e
    match e with
    | .down .. => { state, start := l.state, trace := if state.dragging then #[e] else #[] }
    | _ => { l with state, trace := if l.trace.isEmpty then #[] else l.trace.push e }

@[export cglean_pointer_down]
def pointerDown (x y : Float) : IO Unit := handle (.down x y)

@[export cglean_pointer_move]
def pointerMove (x y : Float) : IO Unit := handle (.move x y)

@[export cglean_pointer_up]
def pointerUp : IO Unit := handle .up

@[export cglean_render]
def render : IO String := return (← live.get).state.render

-- The number of events in the last drag, or 0 if the last press missed the dot.
@[export cglean_trace_size]
def traceSize : IO UInt32 := return (← live.get).trace.size.toUInt32

-- Replays the last drag once, from where it started, in exact arithmetic or
-- filtered; returns where the point ends up.
@[export cglean_replay]
def replayTrace (exact : UInt8) : IO String := do
  let l ← live.get
  return if exact != 0 then replay (l.start.map CGLean.Filtered.get) l.trace else replay l.start l.trace

-- For the native benchmark: the built-in drag, from the initial state.
def useSyntheticTrace : IO Unit :=
  live.set ⟨initialFiltered, initialFiltered, syntheticTrace⟩

end CGLeanWeb.Drag
