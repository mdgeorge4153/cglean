/-
Drag-and-drop test for the WebAssembly build: a point that can be dragged with
the mouse, but is held inside an axis-aligned box. Coordinates are exact, in
`ℚ[√2][√3]`: the box's corners are irrational, and clamping uses its order.

The demo runs twice side by side, once in exact arithmetic (`L`) and once
filtered (`Num = Filtered L`), so that the two can be timed against each other:
the page can record a drag (or use a built-in one) and replay it through either.

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

-- Runs `trace` from `s`, and shows where the point ends up.
def replay (s : State R) (trace : Array Event) : String :=
  let p := (trace.foldl State.step s).point
  s!"({p.x}, {p.y})"

end

/-! ## Both versions, live -/

def initialExact : State L := initial ⟨⟨0, 1⟩, 0⟩ ⟨0, 1⟩
def initialFiltered : State Num := initial (.ofValue ⟨⟨0, 1⟩, 0⟩) (.ofValue ⟨0, 1⟩)

-- A drag for benchmarks: press on the dot, then circle around the box's
-- centre (√ not needed: these are only mouse positions) in and out of it.
def syntheticTrace : Array Event := Id.run do
  let mut t := #[.down 141.42 173.2]
  for i in [0:2000] do
    let a := i.toFloat / 50
    let r := 40 + 140 * (Float.sin (a / 7)).abs
    t := t.push (.move (190 + r * Float.cos a) (150 + r * Float.sin a))
  return t.push .up

structure Live where
  exact     : State L
  filtered  : State Num
  -- Which of the two the page shows.
  showExact : Bool
  recording : Bool
  trace     : Array Event

instance : Nonempty Live := ⟨⟨initialExact, initialFiltered, false, false, #[]⟩⟩

initialize live : IO.Ref Live ←
  IO.mkRef ⟨initialExact, initialFiltered, false, false, syntheticTrace⟩

def handle (e : Event) : IO Unit :=
  live.modify fun l =>
    { l with exact := l.exact.step e, filtered := l.filtered.step e,
             trace := if l.recording then l.trace.push e else l.trace }

@[export cglean_pointer_down]
def pointerDown (x y : Float) : IO Unit := handle (.down x y)

@[export cglean_pointer_move]
def pointerMove (x y : Float) : IO Unit := handle (.move x y)

@[export cglean_pointer_up]
def pointerUp : IO Unit := handle .up

@[export cglean_render]
def render : IO String := do
  let l ← live.get
  return if l.showExact then l.exact.render else l.filtered.render

@[export cglean_show_exact]
def showExact (b : UInt8) : IO Unit := live.modify ({ · with showExact := b != 0 })

-- Recording replaces the trace with the events from now until it stops.
@[export cglean_set_recording]
def setRecording (b : UInt8) : IO Unit :=
  live.modify fun l =>
    if b != 0 then { l with recording := true, trace := #[] } else { l with recording := false }

@[export cglean_use_synthetic_trace]
def useSyntheticTrace : IO Unit := live.modify ({ · with recording := false, trace := syntheticTrace })

@[export cglean_trace_size]
def traceSize : IO UInt32 := return (← live.get).trace.size.toUInt32

-- Replays the trace once, from the initial state, in exact arithmetic or
-- filtered; returns where the point ends up.
@[export cglean_replay]
def replayTrace (exact : UInt8) : IO String := do
  let t := (← live.get).trace
  return if exact != 0 then replay initialExact t else replay initialFiltered t

end CGLeanWeb.Drag
