CGLean in the browser
=====================

An experiment in running CGLean's Lean code in a web page, compiled to
WebAssembly. Currently a drag-and-drop test: a point dragged with the mouse,
held inside a box, with exact coordinates in ℚ[√2] (`CGLeanWeb/Drag.lean`).


Building
--------

    brew install emscripten
    lake exe cache get
    web/build.sh
    python3 -m http.server -d web 8000     # then open http://localhost:8000

The first run takes a few minutes and caches its work in `.lake/wasm/`; later
runs take seconds.


How it fits together
--------------------

    CGLeanWeb/Drag.lean   state, event handlers and SVG rendering, in Lean;
                          `@[export]` gives the handlers C names
    web/glue.c            starts Lean's runtime; unwraps IO results for JS
    web/main.js           forwards pointer events, displays the returned SVG
    web/build.sh          the whole pipeline (below)
    web/prune.py          chooses the modules to link
    web/borrowed.c        functions borrowed from modules prune.py cuts

`build.sh`:

1. Builds Lean's C++ runtime and libuv with Emscripten. Lean doesn't
   publish a WebAssembly build; two out-of-date WebAssembly-only stubs in its
   source are patched so that it compiles.
2. Generates C for Lean's core libraries `Init` and `Std` with the installed
   `lean`.
3. Runs Lake, which builds the .olean files and emits C for this package. The
   C for Mathlib and the other dependencies comes with their build cache.
4. Runs `prune.py`, then compiles the chosen C files with `emcc` and links them.

**Pruning.** Each compiled module has an initializer, which calls those of
the modules it imports. Followed naively from `Drag`, that pulls in all of
Lean's elaborator: Mathlib's definition files `public import` tactics (for
attributes like `@[to_dual]`, and for proofs), and a tactic's implementation
is runtime code of its module. Lean's module system splits each initializer
into a runtime and a meta half, but that doesn't help here, since these are
ordinary imports.

`prune.py` follows only the runtime halves, and cuts the chain at tactic and
elaborator modules (`Lean.*`, `Mathlib.Tactic.*`, Aesop, ...), whose
initializers become no-ops and which aren't linked. That takes the build from
about 2,400 modules and a 70 MB `.wasm` (which also needed Lean's C++ kernel,
and still didn't start) to about 1,050 modules and under 1 MB.

If linked code does use something from a cut module, the link fails with an
undefined symbol. So far that has happened only for specializations that
Lean's compiler shares between modules; see `borrowed.c`.

Upstream changes that would make pruning unnecessary: Mathlib using
`meta import` for tactics used only at elaboration time, or Lean running only
the initializers of imports that compiled code actually references.
