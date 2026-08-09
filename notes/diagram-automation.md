# Deriving CCW diagrams from a proof state

Where the design got to on 2026-08-09. Nothing here is built: the four axiom
pictures in `CGLean/Render/CCWDemo.lean` are hand-authored, and every coordinate
in them was chosen by hand. This records what we worked out about replacing
that with something driven by the goal state, so the reasoning survives the
conversation that produced it.

For the drawing conventions themselves, see `notes/diagram-conventions.md`.

## What is and is not in the proof state

| | derivable? |
|---|---|
| which claims to draw | yes — local context, or `selectedLocations` |
| goal against hypothesis, and colour | yes |
| pivot grouping, arc radii, offsets | yes — functions of the claim set |
| **coordinates** | **no** |

That last row is the whole problem. In a proof about `p q r s t : Point k` the
points are variables and there are no numbers anywhere. So automation reduces
to one question: given a set of CCW constraints over symbolic points,
synthesize coordinates realizing them.

Knuth's own result bears on this. Not every CC system is realizable by actual
points, and deciding realizability of an order type is ∃ℝ-complete. An exact
method is therefore out; this has to be numerical, and has to degrade rather
than fail.

One convention already pays off here. Because arcs always sweep
counterclockwise, a constraint the solver fails to satisfy renders as a reflex
arc with no special handling — the failure mode is already meaningful, and a
contradictory hypothesis set mid-proof draws correctly without the renderer
needing to know it is contradictory.

## Penrose: investigated, ruled out

Penrose is three languages over a numerical optimizer. Domain declares types
and predicates; Substance states the facts of one diagram; Style maps
predicates to shapes and constraints, where `?` marks an unknown, `ensure` is a
hard constraint and `encourage` a soft objective. It compiles these to one
objective function and runs a penalty method under autodiff.

It looked promising, and the groundwork is genuinely there. ProofWidgets ships
`DiagramBuilderM` with `addExpr` (registers a Lean expression as a Penrose
object, labelled with live `InteractiveCode`) and `addInstruction`, and
`ProofWidgets/Demos/Euclidean.lean` is nearly a template for our extraction
layer — it walks the local context matching `between` with `e.app4?`. Our
constraint also appears expressible: `widget/penrose/euclidean.sty` uses
coordinate indexing, vector subtraction and direct comparison under `ensure`.

It is ruled out by the interface. `Penrose.DiagramProps` is exactly
`{embeds, dsl, sty, sub, maxOptSteps}`: no field for initial positions, and the
solved coordinates never return to Lean. The optimizer runs in the browser and
renders there. So there is no warm start and no way to cache a previous layout
— and stability across proof steps is a hard requirement, not a preference.

Two lesser reasons, recorded so they are not rediscovered. Going Penrose means
re-expressing the *whole* drawing in Style, not just the point placement, since
we cannot solve there and render here. And Style rules fire per matching tuple
with no good way to sort a group, while our radius nesting is exactly a
per-group sort by angular span.

## Stability across proof steps

The value of this is watching the diagram change as you step, so points must
stay put between steps. Two distinct sources of drift, with different fixes.

**Gauge freedom**, and it is the larger one. `ccw` is invariant under every
orientation-preserving affine map — a six-dimensional group — so a solution is
never a configuration but a whole orbit, and nothing makes a solver pick the
same representative twice. A perfectly stable solve can still rotate, scale or
shear the entire picture between steps.

The fix is independent of the solver: Procrustes-align each new layout to the
previous one before drawing, a closed-form least-squares fit over rotation,
scale and translation.

**Path dependence** is the rest. The fix is to change what is being asked for
— not "a configuration satisfying these constraints" but "the *nearest*
configuration to the current one satisfying them", by adding `λ·Σ‖xᵢ − xᵢ⁻‖²`
to the loss. Points already consistent with the new constraints have zero
gradient and do not move, so what you see when you step is the new hypothesis
biting and nothing else.

The common case is favourable: stepping a proof mostly *grows* the context, so
constraints accumulate rather than churn.

Caveat worth keeping. Sometimes no small motion suffices — a new hypothesis
changes the order type and a point must cross a line. The picture has to jump
then. That is information about the step, not a defect, but it means "the
points never move much" cannot be promised unconditionally.

## What the widget layer can and cannot do

Findings from reading `ProofWidgets/Component/InteractiveSvg.lean` and
`widget/js/interactiveSvg.js`.

`InteractiveSvg State` carries `init`, `update` and `render`. Its state lives
client-side and is round-tripped through the RPC: `SvgState State` is
`RpcEncodable`, arrives in `UpdateParams` and returns in `UpdateResult`. The
server holds nothing.

The client seeds that state with `useRef(props)` — **at mount only**. Every
later prop is ignored, and state is updated solely from RPC results. So
whether state survives a goal change is exactly whether React remounts the
component, and props can never push anything into a live widget.

More restrictive still, `updateSvg` receives `UpdateParams State`, which is
`{elapsed, actions, state, mousePos}`. There is no goal and no local context: a
running `InteractiveSvg` is blind to what is being proved.

The consequence settles a design question. Constraints must live inside
`State`, seeded at mount from a panel widget's props; every goal change must
re-seed to deliver new constraints; so positions have to survive that
re-seeding through something outside the widget. **A server-side layout cache
is required whichever way the remount question falls** — an `IO.Ref` keyed by
declaration and point `FVarId`s, treated strictly as a hint, so that a missing
or stale entry only costs a re-solve from the canonical seed.

Two further notes. There is a heavier escape hatch: the client passes `pos`
into props and RPC methods can reach the document, so a bespoke component could
re-read the goal at the cursor each tick and stay live — at the cost of writing
our own JS rather than reusing `interactiveSvg.js`. And dragging is nearly
free: `mousedown` sets `selected` to the id of the element under the cursor and
`Element` already has an `id` field, so tagging each dot with its point name is
most of the work.

## An idea that unifies the two requirements

`update` receives `Δt_ms` and the client ticks at `callbackTime := 33`. So the
solver could be a continuously running relaxation — a few gradient steps per
frame — rather than a batch solve per render. Stepping the proof then changes
the loss mid-flight and the points visibly slide to accommodate the new
hypothesis; dragging is overriding one point while relaxation continues on the
rest; warm starting is not a feature but a consequence of never restarting.

Under free dragging a point simply goes where it is put and violated claims
draw reflex, which the conventions already handle. That is the cheap mode and
arguably the more useful one: dragging until an arc flips locates the exact
boundary of a constraint. Constrained dragging, where the solver re-satisfies
around a pinned point, is nicer and can wait.

## Prerequisite

There is no orientation predicate in the library. `CGLean/Geometry/Point2D.lean`
has `Point k := k ×ₗ k` and `Point.dot`, and nothing else — no cross product,
no determinant, no `ccw`. The widget has to match on something, so defining
`ccw` over a linearly ordered ring is a hard prerequisite, and it is also step
one of the convex-hull plan. Both lines of work want the same thing next.

## Open

- Continuous relaxation, or a batch solve per goal seeded from the cache? The
  first is more appealing and more coupled to the widget layer.
- Free dragging or constrained dragging first.
- Should a dragged layout be pinnable back into the source via `MakeEditLink`,
  for diagrams meant as documentation rather than as a proof aid?
- What the canonical seed is when there is no cache entry — points on a circle
  in order of first appearance is the obvious candidate, and it needs to be
  deterministic so that equal constraint sets give equal pictures.
- How much of this to do before the convex-hull theory rather than after.
