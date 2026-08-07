CGLean: verified computational geometry in lean
===============================================

Exact-arithmetic computational geometry in Lean 4: number representations that
compute without rounding error, and planar geometry built on top of them.

The blueprint under `blueprint/` is the place to start reading. It states what
the library is meant to prove, and its dependency graph shows how much of that
is done.


Building the library
--------------------

The toolchain is pinned by `lean-toolchain`, so [elan][] installs the right Lean
on first use.

    brew install elan-init      # or see https://github.com/leanprover/elan
    lake exe cache get          # prebuilt Mathlib oleans; slow to build otherwise
    lake build

Note that `lake env lean SomeFile.lean` does *not* apply the `leanOptions` in
`lakefile.toml`, so it will not report `autoImplicit` failures. Use
`lake build CGLean.Some.Module` when iterating on a single file.

[elan]: https://github.com/leanprover/elan


Building the blueprint
----------------------

Needs [leanblueprint][] and Graphviz. `leanblueprint` shells out to `plastex`,
which must run in the same environment as its plugins, so if it is installed as
an isolated tool that directory has to be on `PATH`:

    brew install graphviz
    uv tool install leanblueprint

    PATH="$(uv tool dir)/leanblueprint/bin:$PATH" leanblueprint web

Output lands in `blueprint/web/`, which is gitignored. `dep_graph_document.html`
is the dependency graph; note that its green markings are local rather than
transitive, so a result shown as proved may still rest on a `sorry` beneath it.

To read it from another machine:

    (cd blueprint/web && python3 -m http.server 8800 --bind 0.0.0.0)

A PDF can be produced with `leanblueprint pdf`, which additionally needs a TeX
distribution, but the dependency graph appears only in the web version.

[leanblueprint]: https://github.com/PatrickMassot/leanblueprint


Building the API documentation
------------------------------

[doc-gen4][] lives in its own package under `docbuild/` so that its
dependencies stay out of the library's. It shares the parent's package
directory, so Mathlib is not checked out twice.

    (cd docbuild && lake build CGLean:docs)

Output lands in `docbuild/.lake/build/doc/`, which is gitignored. The first
build also renders Mathlib and the Lean core and takes on the order of an hour;
afterwards the SQLite database next to it lets subsequent builds re-render only
what changed. The blueprint's `\dochome` points at where CI publishes this, so
its statement links resolve only on the deployed site.

[doc-gen4]: https://github.com/leanprover/doc-gen4


Related work
------------

This is one of several implementations of the same ideas, collected in
[mdgeorge4153/algebra][algebra]. The OCaml version, in the `tangrams` directory
of [portfolio-private][], is the most complete: it has a working sweep-line
polygon union, convex hull, and the number tower, and is the reference for what
the Lean version is aiming at. `ocaml/tangrams/writeup/ps4.tex` in
[portfolio][] describes the problem the whole family of implementations solves.

[algebra]: https://github.com/mdgeorge4153/algebra
[portfolio]: https://github.com/mdgeorge4153/portfolio
[portfolio-private]: https://github.com/mdgeorge4153/portfolio-private
