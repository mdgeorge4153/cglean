import Mathlib.Data.Rat.Field
import Mathlib.Algebra.Ring.Prod
import LeanColls.Data.RBMap
import CGLean.Geometry.Basic
import CGLean.Classes.Basic
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

open LeanColls

variable (k : Type)
variable [LinearOrderedRing k]

-- Points are pairs of numbers. We use lexicographic ordering for <, so that
-- we first sort by x coordinate and then y coordinate. You can think of this
-- as sorting from left to right, except we need a way to handle the special
-- case where p₁ and p₂ have the same x coordinate. The trick is that we
-- imagine applying a tiny shear transformation, so that the pair (x,y) really
-- represents the point (x+εy, y). Then if y₁ < y₂, the point represented by
-- (x,y₁) is actually a little to the left of the point represented by (x,y₂).
-- This is exactly what we get by using the lexicographic ordering
abbrev Point := k ×ₗ k

abbrev Segment := Point k × Point k

abbrev Point.x (p : Point k) := p.fst
abbrev Point.y (p : Point k) := p.snd

def p : Point Rat := (1,2)
def q : Point Rat := (3,4)

def f (p₁ p₂ : Point k) : Point k := p₁ + p₂

#eval p < q
#eval 3*p
#eval p - q
#eval p / 3

def dotProduct (p q : Point k) : k := p.x * q.x + p.y * q.y

infixl:72 " ⬝ " => dotProduct _

#eval p ⬝ q
#eval compare p q

def h (p₁ p₂ : Point k) : k := p₁ ⬝ p₂

structure Edge : Type where
  target   : Point k
  left_in  : Bool -- is the right side of the line "inside" the region?
  right_in : Bool -- is the left side of the edge "inside" the region?

/--
A region is stored as a map; each vertex in the boundary of the region has a
corresponding key.  The values are lists of edges.  We refer to the source
of an edge as the key under which the edge is stored.

a region r is valid if
 1. the target of every edge is less than the source (in the < order)
 2. the target of every edge has a corresponding vertex in the map
 3. the edges at each source are sorted (by the compare_edges_around order)
 4. the edges and vertices are all interior-disjoint
-/
structure RegionImpl : Type where
  edges : List (Point k × List (Edge k))
  -- TODO: invariants

def RegionImpl.segments (r : RegionImpl k) : List (Point k × Point k) :=
  do let (source, edges) ← r.edges
     let edge ← edges
     pure (source, edge.target)

def RegionImpl.vertices (r : RegionImpl k) : List (Point k) :=
  List.map Prod.fst r.edges

instance: HAdd (RegionImpl k) (Point k) (RegionImpl k) where
  hAdd r offset := {
    edges := do
      let (source, edges) ← r.edges
      pure (source + offset, List.map (fun e => {target := e.target + offset, left_in := e.left_in, right_in := e.right_in}) edges)
  }

def bigTri : RegionImpl ℚ := {
  edges := [
    ((0, 0), []),
    ((0,2), [⟨(0,0), true, false⟩]),
    ((2,0), [⟨(0,2), true, false⟩, ⟨(0,0), false, true⟩])
  ]
}

open ProofWidgets Svg

private def frame : Frame where
  xmin   := -1
  ymin   := -1
  xSize  := 4
  width  := 400
  height := 400

def floatPoint [Floatable α] (p : Point α) : Float × Float := (Floatable.toFloat p.x, Floatable.toFloat p.y)

def toSvg [Floatable α] (r : RegionImpl α) : Svg frame :=
  let nodes : Array (Element frame) := r.vertices |> List.map (fun p => circle (floatPoint p) (.abs 0.05) |>.setFill (0.5,0.5,1.)) |> List.toArray
  let edges : Array (Element frame) := r.segments |> List.map (fun (p,q) => line (floatPoint p) (floatPoint q) |>.setStroke (0.8, 0.0, 0.0) (.px 2)) |> List.toArray
  { elements := edges ++ nodes }

#html bigTri |> toSvg |>.toHtml

instance : Region (RegionImpl k) (Point k) := sorry
