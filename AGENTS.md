# AGENTS.md

Conventions for humans and AI agents working in this repository.

## Notation

### `AdjoinSqrt R n` / `A[√n]`

When writing informal math (prose, LaTeX, or discussion of Lean code) about
elements of `AdjoinSqrt R n`, name each element with a base letter and give
its components the same letter, subscripted: `a = a₁ + aₙ√n`,
`b = b₁ + bₙ√n`, `c = c₁ + cₙ√n`, etc. Avoid generic names like `x`/`y` with
`.a₁`/`.aₙ` field access, and avoid mismatched letters (e.g. don't write
`x = a₁ + aₙ√n`).

This keeps informal notation consistent with the structure's own field names
(`a₁`, `aₙ`) and makes each element's letter self-documenting. (Lean
identifiers quoted verbatim from source, e.g. `x.a₁`, are unaffected — this
is about how to write new prose/proofs, not about renaming existing code.)

### Approximations

When writing informal math about approximate arithmetic (`RealApprox`,
`ApproxStrategy`, `Filtered`), use:

| kind                          | letters         | example                                  |
|-------------------------------|-----------------|------------------------------------------|
| exact values in `A`           | `a`, `b`, `c`   | `a = a₁ + aₙ√n` (as above)               |
| reals                         | `x`, `y`        | `x ∈ X`                                  |
| approximations in `α`         | `X`, `Y`, `Z`   | `X + Y`; `Ŝ` approximates `√n`           |
| embedding and strategy        | `i : A → ℝ`, `f : A → α` | `i(a) ∈ f(a)`                   |
| interval endpoints            | `x_lo`, `x_hi`  | `X = [x_lo, x_hi]`                       |
| dyadic rationals              | `m · 2^k`       |                                          |

This matches the Lean, where `RealApprox`'s fields are stated with
`{x y : ℝ} {X Y : α}`. As above, it governs prose, not Lean identifiers.

## Blueprint prose

Don't write expository prose for the blueprint (proof sketches, explanations,
statement commentary) — instead, leave short bullet points marking what
needs to be written, for the author to fill in by hand later. Put them in a
`\TODO{...}` note (an `itemize` inside it for several), which shows in red in
both the web and print versions, rather than in `%` comments. This doesn't
apply to reference-style material such as the related-work section, which is
fine to write in full.

The blueprint is split into one file per chapter under `blueprint/src/chapters/`,
`\input` from `content.tex`; each chapter gets its own dependency graph
(linked from the chapter's sidebar entry by `toc-graphs.js`). A chapter's graph
shows only that chapter's nodes, so a `\uses` of a node in another chapter
draws no edge; add `\alsoIn{chap:other}` to a node to show it, with its
edges, in that chapter's graph too.
References are a `thebibliography` in `chapters/references.tex`: add a
`\bibitem{key}` there and `\cite{key}` it.

## Mathematical level

Target the level of a bright math undergraduate: someone who has had a first
course in abstract algebra (groups, rings, fields) but no more. Write and
explain as though introducing such a reader to the specific ideas of this
development (ordered fields, adjoining square roots, sign structures, etc.),
in the spirit of using it to teach some abstract-algebra concepts — rather
than assuming the reader is already fluent in this specialized material.
Avoid both research-level terseness and re-explaining basic undergraduate
algebra (groups, subgroups, ring axioms, etc.) that this audience already
knows.

## Lean style

Follow Mathlib's [naming conventions](https://leanprover-community.github.io/contribute/naming.html)
and [style guide](https://leanprover-community.github.io/contribute/style.html).
Prefer Mathlib's classes, bundled homomorphisms and hypotheses (e.g.
`Fact (¬ IsSquare n)`) over project-specific ones.

CI fails on any `lake build` warning other than `declaration uses sorry`, so
fix deprecations and linter warnings rather than leaving them. `sorry` is fine
while sketching; `scripts/check-blueprint.py` reports which blueprint
declarations still depend on it.

## Blueprint conventions

- A blueprint statement states the same hypotheses as its Lean counterpart.
- Write mathematical notation (`$f(a)$`), not Lean names or dot notation;
  Lean names belong in `\lean{}` and `\code{}`.
- Results taken from Mathlib appear as ordinary `definition`/`lemma` blocks
  with `\lean{}` naming the Mathlib declarations and marked `\mathlibok`, so
  they link to Mathlib's docs and the dependency graph colours their
  dependents correctly.
- `\leanok` is the author's sign-off, not a build status: add it only once the
  author has reviewed (or written) the Lean and it matches the blueprint text.
  A green node means the author can move on.
