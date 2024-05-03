import Mathlib.Data.Rat.Field
import Mathlib.Algebra.Ring.Prod
import LeanColls.Data.RBMap
import CGLean.Classes.Region
import CGLean.Geometry.Point2D

open LeanColls

variable (k : Type) [LinearOrderedRing k]

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
structure Arrangement : Type where
  edges : List (Point k × List (Edge k))
  -- TODO: invariants

def Arrangement.segments (r : Arrangement k) : List (Point k × Point k) :=
  do let (source, edges) ← r.edges
     let edge ← edges
     pure (source, edge.target)

def Arrangement.vertices (r : Arrangement k) : List (Point k) :=
  List.map Prod.fst r.edges

instance: HAdd (Arrangement k) (Point k) (Arrangement k) where
  hAdd r offset := {
    edges := do
      let (source, edges) ← r.edges
      pure (source + offset, List.map (fun e => {target := e.target + offset, left_in := e.left_in, right_in := e.right_in}) edges)
  }

instance : Region (Arrangement k) (Point k) where
  union := sorry
  inter := sorry
  simplify := sorry
  location := sorry

  vertices := Arrangement.vertices k
  segments := Arrangement.segments k
