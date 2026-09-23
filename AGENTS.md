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

## Blueprint prose

Don't write expository prose for the blueprint (proof sketches, explanations,
statement commentary) — instead, leave short bullet points marking what
needs to be written, for the author to fill in by hand later. This doesn't
apply to reference-style material such as the related-work section, which is
fine to write in full.

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
