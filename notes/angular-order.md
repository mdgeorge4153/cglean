# Angular order around a point

What `ccw p` is and is not, as an order-theoretic structure. Written 2026-08-09
while deciding what to state for the convex hull. Both negative claims below
were checked numerically (400k random configurations each) rather than argued
from intuition.

## `ccw p` is not a total order

`ccw p q r` says the counterclockwise angle from `q` to `r`, seen from `p`, lies
in `(0, π)`. Transitivity fails as soon as three points span more than half a
turn. Take `p` at the origin and three points at 0°, 120° and 240°:

    ccw p a b   (0° → 120°)    holds
    ccw p b c   (120° → 240°)  holds
    ccw p a c   (0° → 240°)    fails — that is a right turn

So there is no `IsStrictTotalOrder Point (ccw p)` instance to be had. What is
true is the restricted form: on an open half-plane through `p`, `ccw p` is a
strict total order. That restriction is not a convenience, it is the content of
Knuth's axiom 5, whose side conditions `ccw t s p`, `ccw t s q`, `ccw t s r`
confine `p`, `q`, `r` to one side of the line `ts`. It is also why Graham scan
begins by choosing an extreme point.

The usable statement is therefore conditional: given `h : ∀ x ∈ s, ccw p q x`
confining `s` to a half-plane, `ccw p` restricted to `s` is a strict total
order, and Mathlib's `mergeSort` together with its `Sorted` lemmas gives a
proved angular sort.

## Nor is `ccw` a Mathlib `CircularOrder`

Two of `Mathlib/Order/Circular.lean`'s laws are Knuth's axioms verbatim —
`btw_cyclic_left : btw a b c → btw b c a` is axiom 1, and
`btw_total : btw a b c ∨ btw c b a` is axiom 3. The transitivity laws diverge,
and not subtly: reading `sbtw` as `ccw`, the law
`sbtw a b c → sbtw b d c → sbtw a d c` fails on 19.8% of the configurations
that satisfy its premises.

The reason is dimension. A circular order is one-dimensional — points arranged
around a circle — whereas planar orientation is not. Knuth's CC systems are
their own structure, which is consistent with Mathlib having no notion matching
them, and means stating them here is a real addition rather than a rename.

## The two are related by projection

The same experiment run on points sampled from a circle rather than from the
plane gives zero violations in 66,739 configurations. So the circular order is
there; it just does not live on the plane.

`ccw p q r` depends only on the directions of `q` and `r` from `p`, so
projecting every point onto a circle centred at `p` changes nothing. The
projections carry a genuine circular order, and the pivot form is that order
together with the antipodal map:

    ccw p q r   iff   r′ lies strictly between q′ and the antipode of q′,
                      going counterclockwise

that is, `r` is within half a turn counterclockwise of `q`. A circular order
restricted to any half is linear, which recovers the half-plane statement above
from the other direction.

Whether to route the formalisation through `CircularOrder` on a circle of
directions, or to state the half-plane restriction directly, is open. The
direct route is less machinery; the projection route would need a type of
directions from `p` and a proof that projection preserves `ccw`, in exchange
for whatever Mathlib proves about circular orders.
