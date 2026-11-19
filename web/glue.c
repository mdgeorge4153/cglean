// JavaScript-facing wrappers around the functions exported from
// CGLeanWeb/Drag.lean. These exist to start up the Lean runtime and to unwrap
// the `IO` results, so that JavaScript only sees numbers and strings.
//
// build.sh defines CGLEAN_INIT as the entry module's initializer, whose name
// includes a package prefix chosen by Lake.

#include <lean/lean.h>
#include <emscripten.h>

// Not declared in lean.h; Lean's generated `main` declares it the same way.
void lean_initialize_runtime_module(void);

lean_object * CGLEAN_INIT(uint8_t builtin);
lean_object * cglean_pointer_down(double x, double y);
lean_object * cglean_pointer_move(double x, double y);
lean_object * cglean_pointer_up(void);
lean_object * cglean_render(void);
lean_object * cglean_show_exact(uint8_t b);
lean_object * cglean_set_recording(uint8_t b);
lean_object * cglean_use_synthetic_trace(void);
lean_object * cglean_trace_size(void);
lean_object * cglean_replay(uint8_t exact);

// Every module that imports Lean (as Mathlib's do) calls this from its
// initializer. The real one, in Lean's src/initialize/init.cpp, also
// initializes the `Lean` package, which is exactly what prune.py cuts. The
// rest of what it does is covered by lean_initialize_runtime_module below and
// by the entry module's initializer, which initializes Init itself.
void lean_initialize(void) {}

// Consumes an `IO Unit` result, printing the error if there is one.
static void finish(lean_object * res) {
  if (!lean_io_result_is_ok(res)) lean_io_result_show_error(res);
  lean_dec(res);
}

EMSCRIPTEN_KEEPALIVE void cglean_init(void) {
  lean_initialize_runtime_module();
  finish(CGLEAN_INIT(1));
  lean_io_mark_end_initialization();
}

EMSCRIPTEN_KEEPALIVE void cglean_js_pointer_down(double x, double y) { finish(cglean_pointer_down(x, y)); }
EMSCRIPTEN_KEEPALIVE void cglean_js_pointer_move(double x, double y) { finish(cglean_pointer_move(x, y)); }
EMSCRIPTEN_KEEPALIVE void cglean_js_pointer_up(void)                 { finish(cglean_pointer_up()); }

EMSCRIPTEN_KEEPALIVE void cglean_js_show_exact(int b)    { finish(cglean_show_exact(b != 0)); }
EMSCRIPTEN_KEEPALIVE void cglean_js_set_recording(int b) { finish(cglean_set_recording(b != 0)); }
EMSCRIPTEN_KEEPALIVE void cglean_js_use_synthetic_trace(void) { finish(cglean_use_synthetic_trace()); }

EMSCRIPTEN_KEEPALIVE unsigned cglean_js_trace_size(void) {
  lean_object * res = cglean_trace_size();
  if (!lean_io_result_is_ok(res)) { lean_io_result_show_error(res); lean_dec(res); return 0; }
  unsigned n = lean_unbox_uint32(lean_io_result_get_value(res));
  lean_dec(res);
  return n;
}

// Unwraps an `IO String` result. The returned pointer stays valid until the
// next call with the same `last`.
static const char * string_result(lean_object * res, lean_object ** last) {
  if (*last) lean_dec(*last);
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec(res);
    *last = NULL;
    return "";
  }
  *last = lean_io_result_get_value(res);
  lean_inc(*last);
  lean_dec(res);
  return lean_string_cstr(*last);
}

EMSCRIPTEN_KEEPALIVE const char * cglean_js_render(void) {
  static lean_object * last = NULL;
  return string_result(cglean_render(), &last);
}

EMSCRIPTEN_KEEPALIVE const char * cglean_js_replay(int exact) {
  static lean_object * last = NULL;
  return string_result(cglean_replay(exact != 0), &last);
}
