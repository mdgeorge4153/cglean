import CGLean.Data.NumberType
import CGLean.Classes.Floatable

/-!
# Exact vs filtered arithmetic in `ℚ[√2][√3]`

Orientation tests, `(q - p) × (r - p) > 0`, on random points and on points built
from them by intersecting lines, run once in exact arithmetic and once filtered.

    lake build bench && .lake/build/bin/bench [tests] [seed]

Building compiles every imported Mathlib module to native code, so the first
build takes several minutes.
-/

open CGLean CGLean.NumberType

abbrev F := Filtered
instance : Inhabited L := ⟨0⟩
instance : Inhabited F := ⟨0⟩

/-- Deterministic pseudo-random rationals. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

def randQ (s : Nat) : ℚ × Nat :=
  let s1 := lcg s; let s2 := lcg s1
  (((s1 / 65536 % 101 : Nat) : ℚ) - 50) / (((s2 / 65536 % 20 : Nat) : ℚ) + 1) |> (·, s2)

def randL (s : Nat) : L × Nat :=
  let (a, s) := randQ s; let (b, s) := randQ s; let (c, s) := randQ s; let (d, s) := randQ s
  (⟨⟨a, b⟩, ⟨c, d⟩⟩, s)

def randPts (n s : Nat) : Array (L × L) := Id.run do
  let mut s := s; let mut out := #[]
  for _ in [0:n] do
    let (x, s') := randL s; let (y, s'') := randL s'; s := s''
    out := out.push (x, y)
  return out

section
variable {R : Type} [CommRing R] [LinearOrder R] [Inhabited R]
def orient (p q r : R × R) : R := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)
def randTriples (n m s : Nat) : Array (Nat × Nat × Nat) := Id.run do
  let mut s := s; let mut out := #[]
  for _ in [0:n] do
    s := lcg s; let i := s / 65536 % m
    s := lcg s; let j := s / 65536 % m
    s := lcg s; let k := s / 65536 % m
    out := out.push (i, j, k)
  return out
def countPos (pts : Array (R × R)) (triples : Array (Nat × Nat × Nat)) : Nat :=
  triples.foldl (fun acc (i, j, k) => if 0 < orient pts[i]! pts[j]! pts[k]! then acc + 1 else acc) 0
end

def countZero {R : Type} [CommRing R] [LinearOrder R] [Inhabited R] (pts : Array (R × R)) (triples : Array (Nat × Nat × Nat)) : Nat :=
  triples.foldl (fun acc (i, j, k) => if orient pts[i]! pts[j]! pts[k]! = 0 then acc + 1 else acc) 0

def timeIt (label : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  IO.println s!"{label}: result {r}"
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0) / 1000000} ms"

section
variable {R : Type} [Field R] [Inhabited R]

/-- Intersection of line ab with line cd. -/
def inter (a b c d : R × R) : R × R :=
  let den := (a.1 - b.1) * (c.2 - d.2) - (a.2 - b.2) * (c.1 - d.1)
  let t := ((a.1 - c.1) * (c.2 - d.2) - (a.2 - c.2) * (c.1 - d.1)) / den
  (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

/-- `m` intersections of random lines through points of `src`. -/
def level (src : Array (R × R)) (m s : Nat) : Array (R × R) := Id.run do
  let mut s := s; let mut out := #[]
  let k := src.size
  for _ in [0:m] do
    s := lcg s; let a := s / 65536 % k
    s := lcg s; let b := s / 65536 % k
    s := lcg s; let c := s / 65536 % k
    s := lcg s; let d := s / 65536 % k
    out := out.push (inter src[a]! src[b]! src[c]! src[d]!)
  return out

/-- `m` intersections of the fixed line src[0]src[1] with random lines: all collinear. -/
def onLine (src : Array (R × R)) (m s : Nat) : Array (R × R) := Id.run do
  let mut s := s; let mut out := #[]
  let k := src.size
  for _ in [0:m] do
    s := lcg s; let c := 2 + s / 65536 % (k - 2)
    s := lcg s; let d := 2 + s / 65536 % (k - 2)
    out := out.push (inter src[0]! src[1]! src[c]! src[d]!)
  return out
end

unsafe def rangeOfImpl (x : F) : LeanCert.Core.IntervalDyadic := (Quot.unquot x).range

/-- The interval of the representative. Not a function of the value, since equal
values can carry different intervals, hence `implemented_by`; used only to
report how the filter did. -/
@[implemented_by rangeOfImpl]
opaque rangeOf : F → LeanCert.Core.IntervalDyadic

/-- Fallbacks, and mean log₂ width of the orientation intervals. -/
def diag (pts : Array (F × F)) (triples : Array (Nat × Nat × Nat)) : Nat × Float :=
  let (fb, w) := triples.foldl (fun (fb, w) (i, j, k) =>
    let r := rangeOf (orient pts[i]! pts[j]! pts[k]!)
    let fb := if compare? r (ofInt 0) == none then fb + 1 else fb
    let width := Floatable.toFloat (r.hi.toRat - r.lo.toRat)
    (fb, w + (if width == 0 then -200 else Float.log2 width))) (0, 0)
  (fb, w / triples.size.toFloat)

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 2000
  let seed := (args.tail.head? >>= String.toNat?).getD 42
  let pts := randPts 300 seed
  let toF (p : L × L) : F × F := (FilteredReal.ofValue p.1, FilteredReal.ofValue p.2)
  let fpts := pts.map toF
  let chk := fpts.foldl (fun acc (x, _) => acc + (rangeOf x).lo.mantissa.natAbs % 2) 0
  IO.println s!"(forced {chk})"
  let t0 := randTriples n 300 7
  let t1 := randTriples n 300 8
  let t2 := randTriples n 100 9
  let tc := randTriples 100 100 10
  let report (label : String) (fp : Array (F × F)) (tr : Array (Nat × Nat × Nat)) : IO Unit := do
    let (fb, w) := diag fp tr
    IO.println s!"  {label}: {fb}/{tr.size} fall back, mean log2 width {w}"
  IO.println s!"== depth 0: {n} tests on input points"
  timeIt "exact   " fun _ => countPos pts t0
  timeIt "filtered" fun _ => countPos fpts t0
  report "filtered" fpts t0
  IO.println s!"== depth 1: 300 intersection points, {n} tests"
  timeIt "exact   " fun _ => countPos (level pts 300 seed) t1
  timeIt "filtered" fun _ => countPos (level fpts 300 seed) t1
  report "filtered" (level fpts 300 seed) t1
  IO.println s!"== depth 2: 100 intersections of lines through depth-1 points, {n} tests"
  timeIt "exact   " fun _ => countPos (level (level pts 300 seed) 100 (seed+1)) t2
  timeIt "filtered" fun _ => countPos (level (level fpts 300 seed) 100 (seed+1)) t2
  report "filtered" (level (level fpts 300 seed) 100 (seed+1)) t2
  IO.println s!"exact zeros: depth0 {countZero pts t0}, depth1 {countZero (level pts 300 seed) t1}, depth2 {countZero (level (level pts 300 seed) 100 (seed+1)) t2}"
  IO.println "== degenerate: 100 intersections with one fixed line, 100 tests (all collinear)"
  timeIt "exact   " fun _ => countPos (onLine pts 100 seed) tc
  timeIt "filtered" fun _ => countPos (onLine fpts 100 seed) tc
  report "filtered" (onLine fpts 100 seed) tc
