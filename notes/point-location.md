# Plan: point location and collision-avoiding drag

Plan for the next stretch of geometry. It was agreed on 2026-11-20 and is meant to be
revised as the work goes; delete or fold it into the blueprint once it is
done. The blueprint itself only gets statements as they are implemented, with
`\TODO` bullets for prose. It does not get this plan.

## Goal

Extend the demo so that the dot follows the cursor but never enters a fixed
polygonal obstacle. The dot goes to the closest point to the cursor that is not
inside the obstacle. Later, the dragged object becomes a polygon, as in the
OCaml version.

## Reference: the OCaml implementation

`tangrams/mdg39/` in `portfolio-private`: `region.ml`, `geometry.ml`, `game.ml`.

- `Region` stores an arrangement. Each vertex is a key, ordered
  lexicographically, and each edge is stored at its larger endpoint with
  `left_in`/`right_in` flags. `CGLean/Geometry/Arrangement.lean` is a port of
  this.
- `create` accepts only convex, counterclockwise, non-degenerate polygons.
  Everything else comes from `union`, a sweep line.
- `locate` counts, by parity, the crossings of a downward ray with the edges
  whose `left_in ≠ right_in`. Vertices get a separate pass so that isolated
  points count. Degenerate cases are handled by hand: x-ranges are half-open,
  and vertical edges are a special case.
- `find_closest r p`:
  - returns `p` if it is not `Inside`;
  - otherwise returns the nearest of the closest points on the edges and the
    vertices, compared by squared distance.
- `game.ml`:
  - on click, the "shadow" is the union of the Minkowski differences of each
    convex obstacle with the dragged shape;
  - each difference is the convex hull (Jarvis march) of the pairwise vertex
    differences;
  - each mouse move is `find_closest shadow p`;
  - rotation is in 15° steps over a field with √2 and √3.

## Design

### No sweep-line union at first: a lazy union of convex pieces

In OCaml, `find_closest` is correct only because `union` has produced an
arrangement whose edges are all genuine boundary. The sweep is the hardest code
to verify, so it is deferred. Instead:

- **Convex polygon.** A counterclockwise, non-degenerate list of vertices.
  - `p` is inside if `0 < det vᵢ vᵢ₊₁ p` for every edge.
  - `p` is on the boundary if no `det` is negative and some `det` is zero.
  - This is both the definition and the algorithm. There are no degenerate
    cases to handle, and it uses `det` from #23.
  - Collinear vertex lists are excluded: there every `det` vanishes along the
    whole line, not just the segment.
- **Region.** A list of convex pieces. Its location is `union_spec` folded over
  the pieces, so the union law holds by definition, and `union` is list append.
- **Closest point.**
  - The candidates are `p` itself and the closest point on each edge of each
    piece.
  - Keep the candidates that are not `Inside` any piece, and return the nearest
    by squared distance.
  - The closest point on segment `ab` is `a + t(b − a)`, with
    `t = ((p − a)·(b − a)) / |b − a|²` clamped to `[0, 1]`.
  - There is no square root anywhere, so everything stays exact in
    `ℚ[√2][√3]`.
  - The cost is quadratic in the number of edges, which is fine for the demo.

### Splitting `Region` (option (b))

`Region`/`LawfulRegion` bundle `union`, `inter`, `simplify`, `vertices` and
`segments`. The lazy union has no honest `segments`, because the pieces' edges
include interior ones, and the demo needs none of `inter`, `simplify` or the
exact boundary. Split the class:

1. A class with just `location : ρ → π → Location`.
2. A union operation with `union_lawful` on top of it.
3. A closest-point operation, specified as follows:
   - the result is not `Inside`;
   - no point that is not `Inside` is strictly closer.

   This needs squared distance on `π`, so for now it is stated for `Point k`
   using `Point.dot`.

`inter`, `simplify`, `vertices`/`segments` and `vertices_boundary` return with
arrangements. The names are still open.

### Proof strategy

- **Key lemma, per piece.** Each `det vᵢ vᵢ₊₁ p` is affine in `p`. Along the
  segment from an inside `c` to any `q` that is not inside, some edge function
  goes from positive to non-positive at a computable parameter `t`. That point
  is on the boundary and no farther from `c` than `q`. This is an intermediate
  value argument for affine functions over an ordered field, with no polygon
  Jordan theorem needed.
- **Union.** With `union_spec`, the closest point lies on some piece's boundary
  and is not inside any piece, so it is among the candidates.
- **External meaning.** Relating a convex piece to Mathlib's `convexHull` and
  `interior` is the referee for the internal spec. It comes later, as the
  Arrangements chapter's TODO describes.

### Fast point location: later, proved equal to the lazy union

- Sweep-line union into an `Arrangement`, then point location by "the edge
  directly below `p`", read off its `left_in`/`right_in` flags. The sweep's
  status structure is already ordered by that comparison
  (`compare_edge_to_point`), so a slab or trapezoid structure follows.
- Parity counting on the arrangement, as OCaml's `locate` does it, is another
  implementation of the same meaning.
- On arrangements, degenerate cases should come from the lex/shear convention
  in `Point2D`, not from hand-written cases.
- Every fast version is a theorem: it has the same `location` as the lazy
  union.
- A faster closest-point query is harder. The Voronoi diagram of segments has
  parabolic edges, so the likely route is to exploit drag coherence by checking
  nearby edges only.

### The dragged object

- **Milestone 2:** a point. The circle's radius is only how it is drawn. A true
  disk's configuration space has circular arcs and needs square roots that
  `ℚ[√2][√3]` lacks.
- **Milestone 3:** a convex polygon. The Minkowski difference of convex
  polygons is convex (the hull of pairwise differences), so the shadow is again
  a list of convex pieces and the same closest-point code applies.
  - Every multiple of 15° has its cos and sin in `ℚ(√2, √3)`, e.g.
    `cos 15° = (√6 + √2)/4`. So a regular 24-gon serves as a round-looking
    shape, and 15° rotations are exact.

### Behaviour to keep in mind

The nearest point to the cursor can jump. Dragging through the middle of a thin
obstacle moves the dot to the far side once that side is closer. This is
accepted for now. Sliding along the boundary would need a different spec.

## Milestones

1. **#23: orientation and `det`.** Mike reviews it and writes the blueprint's
   Primitives chapter.
2. **Point and fixed convex obstacles.**
   - Lean:
     - split `Region`;
     - add the convex polygon, the lazy union and closest point, runnable,
       with the correctness theorems `sorry` at first.
   - Blueprint:
     - statements in the Point Location chapter;
     - `\TODO` bullets for prose.
   - Demo:
     - replace `Box` with obstacles;
     - move `Drag.lean` onto the library's `Point k`.
   - Proofs come after, asking Mike first about the ones he wants to write.
3. **Dragged convex polygon.**
   - Convex hull (Jarvis march; the Convex Hull chapter) and Minkowski
     difference.
   - 15° rotations.
   - This reaches parity with OCaml, except that the union is still lazy.
4. **Sweep-line union and fast point location,** each proved equal to the lazy
   union.

## Open questions

- Should the convex-polygon invariants (counterclockwise, strictly convex,
  at least 3 vertices) live in the type, or in a separate predicate?
- What should the split classes be called, and should `Location` move with
  them?
- Should closest point be stated for `Point k` only, or over a class
  providing squared distance?
