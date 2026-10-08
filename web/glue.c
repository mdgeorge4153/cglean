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

// The returned pointer stays valid until the next call.
EMSCRIPTEN_KEEPALIVE const char * cglean_js_render(void) {
  static lean_object * last = NULL;
  if (last) lean_dec(last);
  lean_object * res = cglean_render();
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec(res);
    last = NULL;
    return "";
  }
  last = lean_io_result_get_value(res);
  lean_inc(last);
  lean_dec(res);
  return lean_string_cstr(last);
}
