# Drawing counterclockwise claims

The conventions the CCW renderer follows, why each was chosen, and what was
tried and rejected. Settled 2026-08-09 by drawing the four Knuth axioms and
looking at the results.

- `notes/ccw-sketch.png` — Mike's original hand-drawn specification, the
  authority for anything this document fails to record.
- `notes/ccw-drawing-key.svg` — the same conventions cleaned up: one claim that
  holds of its points, and one that does not.
- `CGLean/Render/CCW.lean` — the renderer. `CGLean/Render/CCWDemo.lean` — the
  four axioms, viewable as widgets by opening the file.

## The conventions

**The pivot is the first argument, and the arc is drawn there.** `ccw p q r`
is two rays leaving `p`, towards `q` and towards `r`, with an arc at `p`
sweeping from the first to the second.

The alternative was an arc at the middle argument, between the segments `pq`
and `qr`. It was tried first and abandoned: claims about a common pivot then
scatter their arcs across different vertices, and transitivity — whose whole
content is an angular order around one point — became three unrelated wedges.
Drawing at the pivot makes those arcs concentric, so a chain of them reads as
the order it is.

The two encodings are a transposition of the first two arguments apart, and
`ccw q p r ↔ ¬ ccw p q r`, so mixing them makes a diagram readable as its own
negation. The choice has to be global.

**Arcs always sweep counterclockwise, never the minor way.** A claim asserts a
turn of less than half a revolution, so the arc is minor exactly when the claim
holds of the coordinates it is drawn with. Points that in fact turn clockwise
draw a reflex arc.

This is what makes the diagram honest without making it clever. The renderer
never decides whether a claim is true, which it could not do mid-proof anyway;
it draws what the claim says, and a false claim looks like a sweep the long way
round. Contradictory hypotheses in a reductio draw the same way, which is the
intended behaviour and not a failure.

Antisymmetry uses this rather than working around it. `ccw p q r → ¬ ccw p r q`
puts both claims at the same pivot on the same two rays, so the picture is one
wedge holding a short arc and a reflex arc that together make one revolution —
of the two orders on a pair of rays, exactly one is counterclockwise.

**Only the arcs carry colour; the rays are a neutral grey.** A ray belongs to
the points, not to any one claim: two claims about a common pivot draw the same
ray, and colouring it means whichever was drawn last wins. The arc already
identifies its claim, naming the pivot, both rays and the direction.

**A head goes on the ray the turn ends on, and on no other.** Heading both says
nothing, since what has to be distinguished is which of the two the arc sweeps
to. Leaving the other bare also reads well across a figure: in transitivity the
ray to `t` ends up bare, which is exactly what marks it as the reference the
three half-plane premises are measured from.

**Rays stop short of the dots** so the points stay legible under a head.

**Coincident claims are separated twice over.** Each claim slides along the
bisector of its own angle at the pivot by a small offset, applied to its rays
and arc but not to the points — the points are the data and stay where they
are, while the lines joining them are annotation. Claims sharing a pivot also
get arcs of different radii, which doubles as the nesting that lets a chain be
read as an angular order.

The bisector is the right axis because it is the one direction the claim itself
determines. Two claims on the same wedge share it, so opposite offsets separate
them symmetrically; claims sharing only a pivot have bisectors that already
point apart.

**Colour distinguishes goal from hypothesis**, in mid-tone hues that survive
either a light or a dark background, since the diagram supplies none of its
own. A lighter shade of the hypothesis colour marks side conditions — in
transitivity, the three premises that confine the points to a half-plane, as
against the two that are the order itself.

## Rejected

- **Dashed goals.** Illegible at the widths involved, and no help on a
  monochrome device once the lines are thin.
- **A solid background panel behind the diagram and the labels.** Did not
  render, and made the points look worse. Neutral colours chosen to work
  against any background replaced it.
- **Offsetting the points.** The points are the claim's data; moving them draws
  a different configuration. Only the annotation may slide.
- **A third treatment for negated claims.** Unnecessary once arcs always sweep
  counterclockwise, and impossible to apply mid-proof, where whether a
  hypothesis holds is not known.

## Not yet automated

Every coordinate in the demos is chosen by hand. Nothing in a proof state
supplies one: the points are variables. Deriving a placement from the claims
alone is the open problem — see the realization discussion — and it is the only
part of the pipeline that is hard. Which claims to draw, their colours, the
pivot grouping, the radii and the offsets all follow from the claims.

The demos are `#html` commands, so the primary view is the infoview. For
inspecting a render outside the editor, dump `Svg.elements` as JSON with
`ToJson` and rasterize; the coordinate conventions are in `Svg.Frame`.
