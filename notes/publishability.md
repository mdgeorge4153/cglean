# Audience and publishability

Research done 2026-08-07 in response to the question: assuming this project gets
finished, who would benefit, is it publishable and where, and are there
application domains beyond the toy examples.

**Provenance.** Assembled by a subagent doing literature search. One citation
has been checked directly against the publisher — Bertot and Portet, below,
which is the load-bearing one. The rest are reported as found and have **not**
been individually verified; treat them as leads to check rather than
established facts.

## Verdict

Not publishable as it stands, and the gap is not small. The finished half — the
algebra — is where the contribution claim is weakest. The unfinished half — the
geometry — is where a paper would live.

The closest competing result landed in the venue one would target. Yves Bertot
and Thomas Portet, *Formally Verifying a Vertical Cell Decomposition Algorithm*,
ITP 2025, LIPIcs vol. 352, 24:1–24:18, doi:10.4230/LIPIcs.ITP.2025.24, developed
in Rocq with Mathematical Components, code at `math-comp/trajectories`. A sweep
line for decomposing a region containing obstacles into safe cells, with
degenerate cases handled explicitly. That is approximately the paper this
project's arrangements chapter would be, a year earlier, in another prover.

*(Verified: the paper, venue, volume, page range, DOI and repository all check
out.)*

## On the algebra

Adjoining a square root to a discrete ordered field and recovering a discrete
ordered field with decidable order is classical constructive algebra rather than
a new theorem — it is the standard step toward the Euclidean closure of an
ordered field. Reported nearby: Lombardi and Mahboubi, *Geometric theories for
real number algebra without sign test or dependent choice axiom*,
arXiv:2408.10290.

Mathlib already has `Zsqrtd` (ℤ[√d] with a computable linear order), which this
project confirmed independently. Coq's `math-comp/real-closed` (Cohen; Cohen and
Mahboubi, LMCS 2012, arXiv:1201.3731) provides discrete real closed fields with
decidable comparison — strictly more general than a tower of square roots, and
what Bertot and Portet build on.

What is genuinely unoccupied is narrower: a nestable `AdjoinSqrt A n` over an
arbitrary linearly ordered field in Lean 4, with a proved filtered layer above
it. That is a good Mathlib contribution. It is not a paper.

## Who benefits

- **Lean and Mathlib users.** Real but small, and the value is the algebra, not
  the geometry — Lean has essentially no computational-geometry user base to
  serve. One adjacent Lean 4 repository was found,
  `schildep/verified-polygon-intersection`, claiming to be the first formally
  verified polygon intersection; not peer reviewed, but enough that a bare
  "first in Lean" claim would be challenged.

- **Safety-critical geometry.** Genuine and active, and already served — in PVS.
  NASA's PolyCARP verifies polygon containment and collision for UAS
  geofencing; Di Vito and Hocking, *Polygon Merge: A Geometric Algorithm
  Verified Using PVS*, NFM 2021, LNCS 12673, 79–94, verifies a merge against
  point-set criteria. Note the arithmetic they chose: Moscato, Titolo, Feliú and
  Muñoz, *Provably Correct Floating-Point Implementation of a Point-in-Polygon
  Algorithm*, FM 2019, verifies floating point with error bounds rather than
  using exact arithmetic. That constituency has considered this approach and
  gone the other way.

- **ITP researchers.** The actual audience. The reported lineage: Pichardie and
  Bertot (TPHOLs 2001, convex hull); Meikle and Fleuriot (ADG 2004, Graham scan
  in Isabelle); Dufourd and Bertot (ITP 2010, plane Delaunay); Brun, Dufourd and
  Magaud (Computational Geometry, 2012, hypermap convex hull); Bertot (ICTAC
  2018, triangulation); Rau and Nipkow (IJCAR 2020, closest pair, with
  benchmarked extracted code); Bertot and Portet (ITP 2025).

- **CGAL and computational-geometry practitioners.** Effectively none. They will
  not adopt a Lean library.

## Publishability

ITP or CPP, and only with the geometry finished. The claim would have to be a
verified planar arrangement whose correctness is stated against Mathlib's own
set-level definitions, running on a verified exact-arithmetic kernel with a
proved filter. The external-specification framing is the strongest card — it is
what Di Vito and Hocking did with point-set properties, and what most of the Coq
lineage does not do. The exact-arithmetic-plus-verified-filter stack is also
unusual; the nearest prior art reported is Melquiond and Pion, *Formally
certified floating-point filters for homogeneous geometric predicates*,
RAIRO-ITA 41(1):57–69, 2007, which certifies a filter for `orient2d` but not the
exact fallback or the algorithms above it.

The algebra alone is too thin for a full paper. Plausible as a short or
rough-diamond paper, an artifact, or better, a Mathlib contribution.

CADE/IJCAR would take it on the Rau and Nipkow precedent but leans toward
automated reasoning; ITP fits better. JAR suits an extended version later. SoCG
will not take formalisation without a new algorithmic idea. Computational
Geometry: Theory and Applications plausibly would, having published both Kettner
et al. and the hypermap convex hull paper. ADG is a low-barrier early venue.

What reviewers would want that is not there: executable, benchmarked code — Rau
and Nipkow set the bar at competitive with handwritten implementations, and this
project's filtered layer is justified entirely by performance that has never
been measured; explicit treatment of degenerate cases, which every paper in the
lineage foregrounds; a direct comparison with `math-comp/trajectories`; and an
end-to-end theorem resting on no `sorry`.

## Where exact predicates actually matter

- **CAD and solid modelling.** Yes, and it is where the money is — robustness
  failures in the commercial kernels spawned the geometry-healing industry. But
  it needs three dimensions and curved surfaces, which a tower of square roots
  does not reach.

- **Circular-arc arrangements.** The honest sweet spot. Line and circle
  intersections land exactly in degree-2 extensions, which is why CGAL has a
  circular kernel. This is the one place nested square roots are the right tool
  rather than too much or too little.

- **GIS.** Real pain, wrong tool. Coordinates are rational; exact rationals
  suffice and square roots are unnecessary.

- **Chip layout.** No. Integer grids make exactness free; the hard part is
  rounding intersections back onto the grid, which exact arithmetic does not
  address.

- **Robotics motion planning.** Partially. Minkowski sums are standard, but
  arbitrary rotations leave any tower of square roots. The restriction to
  multiples of 15° is, honestly, the tangram and origami niche.

- **Graphics, meshing, topological data analysis.** Tolerate floating point or
  need only rationals; adaptive predicates in the Shewchuk style already won
  there.

## Suggested reading of all this

Finish the sweep line, benchmark it, and target ITP with the Mathlib-level
specification as the differentiator against Bertot and Portet. Offer
`AdjoinSqrt` to Mathlib separately, and now.
