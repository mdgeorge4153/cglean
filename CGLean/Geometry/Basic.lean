import LeanColls

inductive Location :=
  | inside
  | boundary
  | outside
deriving Repr

/--
A region (r : ρ) represents a region of a plane (with π-typed points) that is
bounded by line segments.  Regions generalize polygons: they may have multiple
disconnected components, they may have holes, and they may have 0- or
1-dimensional features (isolated points or line segments)
-/
class Region (ρ : Type) (π : outParam Type)
  extends Union ρ, Inter ρ
  where

  -- drop all low-dimensional features. For example:
  --
  -- ```
  --    ┌┐            ┌┐
  --   ┌┴┘            └┘
  -- ┌─┴─┬─┐  ━━>  ┌─────┐
  -- │ ⬝ │ │       │     │
  -- └─────┘       └─────┘
  --
  -- ```
  --
  simplify : ρ → ρ

  -- is the point inside the region?
  location : ρ → π → Location

  -- the vertices on the boundary of the region.
  vertices : ρ → List π

  -- the edges on the boundary of the region
  edges : ρ → List (π × π)


def Region.interior [Region ρ π] (r : ρ) : Set π := {x | Region.location r x = .inside}
def Region.exterior [Region ρ π] (r : ρ) : Set π := {x | Region.location r x = .outside}
def Region.boundary [Region ρ π] (r : ρ) : Set π := {x | Region.location r x = .boundary}

def union_spec (loc₁ loc₂ : Location) : Location := match (loc₁, loc₂) with
  | (.inside, _)   | (_, .inside)   => .inside
  | (.boundary, _) | (_, .boundary) => .boundary
  | _ => .outside

example : union_spec .outside .boundary = .boundary := by rfl
example : union_spec .outside .outside  = .outside  := by rfl
example : union_spec .inside  .boundary = .inside   := by rfl

def inter_spec (loc₁ loc₂ : Location) : Location := match (loc₁, loc₂) with
  | (.outside, _) | (_, .outside) => .outside
  | (.boundary, _) | (_, .boundary) => .boundary
  | _ => .inside

example : inter_spec .inside .boundary = .boundary := by rfl
example : inter_spec .inside .inside   = .inside   := by rfl

class LawfulRegion (ρ : Type) (π : outParam Type) extends Region ρ π where

  union_lawful : ∀ (p : π) (r₁ r₂ : ρ),
    location (r₁ ∪ r₂) p = union_spec (location r₁ p) (location r₂ p)

  inter_lawful : ∀ (p : π) (r₁ r₂ : ρ),
    location (r₁ ∩ r₂) p = inter_spec (location r₁ p) (location r₂ p)

  -- TODO: all vertices are on the boundary
  vertices_boundary : sorry
