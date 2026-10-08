#!/usr/bin/env bash
# Builds CGLeanWeb to WebAssembly: web/dist/cglean.{mjs,wasm}.
#
# Lean does not ship a WebAssembly build, so the first run also builds Lean's
# runtime and its libuv dependency with Emscripten, and generates and compiles
# the C for Lean's core libraries Init and Std, caching all of it in
# .lake/wasm/. Later runs only redo the steps from Lake onwards.
#
# Needs: emscripten (`brew install emscripten`), elan, curl, python3, and
# Mathlib's build cache (`lake exe cache get`).
#
# See web/README.md for how the pieces fit together.

set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
W=$ROOT/.lake/wasm
OUT=$ROOT/web/dist
JOBS=${JOBS:-$(sysctl -n hw.ncpu 2>/dev/null || nproc)}

# The module whose exported functions the page calls.
ENTRY=CGLeanWeb.Drag

LIBUV_VERSION=1.48.0   # must match the GIT_TAG in Lean's src/CMakeLists.txt

cd "$ROOT"
LEAN=$(elan which lean)
LEAN_VERSION=$(sed 's/.*:v//' lean-toolchain)
SRC=$W/lean4-src

export EM_CACHE=$W/emcache   # the default, inside Homebrew's tree, isn't writable

mkdir -p "$W" "$OUT"

CFLAGS=(-O2 -ffp-contract=off -DNDEBUG -I"$W/include" -I"$SRC/src/include")

# Usage: compile_all COMPILER OBJDIR FLAG... -- SOURCE...
# Compiles each source to OBJDIR/<name>.o in parallel. The flags go through a
# response file, since xargs can only append the source to the command line.
compile_all() {
  local compiler=$1 objdir=$2; shift 2
  local flags=()
  while [ "$1" != -- ]; do flags+=("$1"); shift; done; shift
  mkdir -p "$objdir"
  printf '%s\n' "${flags[@]}" > "$objdir.rsp"
  printf '%s\n' "$@" | xargs -P "$JOBS" -n 1 sh -c \
    'o=$(basename "${0%.*}"); '"$compiler"' @"'"$objdir"'.rsp" -c "$0" -o "'"$objdir"'/$o.o"'
}

## Lean source ################################################################

if [ ! -d "$SRC" ]; then
  echo "== Fetching Lean $LEAN_VERSION source"
  mkdir -p "$SRC"
  # Excluding editor config, which the sandbox Claude Code runs in refuses to
  # write; none of it is needed.
  curl -sfL "https://github.com/leanprover/lean4/archive/refs/tags/v$LEAN_VERSION.tar.gz" \
    | tar xz -C "$SRC" --strip-components 1 --exclude '*/.claude' --exclude '*/.vscode'

  # Two stubs used only when building without libuv support (as we do) have
  # signatures that no longer match their declarations, so they don't compile.
  sed -i '' \
    -e 's|^extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive() {|extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive() {|' \
    -e 's|^    return io_result_mk_error("lean_uv_event_loop_alive is not supported");|    return 0;|' \
    "$SRC/src/runtime/uv/event_loop.cpp"
  sed -i '' \
    -e 's|^extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group() {|extern "C" LEAN_EXPORT lean_obj_res lean_uv_os_get_group(uint64_t gid) {|' \
    "$SRC/src/runtime/uv/system.cpp"
fi

## Generated headers ##########################################################
# Lean's CMake build normally generates these.

mkdir -p "$W/include/lean"
cp "$(dirname "$LEAN")/../include/lean/version.h" "$W/include/lean/version.h"
cat > "$W/include/lean/config.h" <<EOF
#pragma once
#include <lean/version.h>
#define LEAN_SMALL_ALLOCATOR
#define LEAN_IS_STAGE0 0
EOF
echo "#define LEAN_GITHASH \"$("$LEAN" --githash)\"" > "$W/include/githash.h"

## libuv ######################################################################

if [ ! -f "$W/lib/libuv.a" ]; then
  echo "== Building libuv $LIBUV_VERSION"
  UV=$W/libuv
  rm -rf "$UV"; mkdir -p "$UV"
  curl -sfL "https://github.com/libuv/libuv/archive/refs/tags/v$LIBUV_VERSION.tar.gz" \
    | tar xz -C "$UV" --strip-components 1
  UV_SOURCES=(
    fs-poll idna inet random strscpy strtok thread-common threadpool timer
    uv-common uv-data-getter-setters version
    unix/async unix/core unix/dl unix/fs unix/getaddrinfo unix/getnameinfo
    unix/loop-watcher unix/loop unix/pipe unix/poll unix/process
    unix/random-devurandom unix/signal unix/stream unix/tcp unix/thread
    unix/tty unix/udp unix/no-proctitle
  )
  UV_PATHS=()
  for f in "${UV_SOURCES[@]}"; do UV_PATHS+=("$UV/src/$f.c"); done
  compile_all emcc "$W/obj/uv" -O2 -D_FILE_OFFSET_BITS=64 -D_LARGEFILE_SOURCE \
    -I"$UV/include" -I"$UV/src" -I"$UV/src/unix" -- "${UV_PATHS[@]}"
  mkdir -p "$W/lib"
  emar rcs "$W/lib/libuv.a" "$W"/obj/uv/*.o
fi

## Lean runtime ###############################################################

if [ ! -f "$W/lib/libleanrt.a" ]; then
  echo "== Building the Lean runtime"
  RT_SOURCES=(
    debug thread mpz utf8 object apply exception interrupt memory stackinfo
    compact init_module io hash byteslice platform alloc allocprof sharecommon
    stack_overflow process object_ref mpn mutex libuv uv/net_addr
    uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal openssl
  )
  RT_PATHS=()
  for f in "${RT_SOURCES[@]}"; do RT_PATHS+=("$SRC/src/runtime/$f.cpp"); done
  # Object names come from basenames, and runtime/ has no duplicates among these.
  compile_all em++ "$W/obj/rt" "${CFLAGS[@]}" -std=c++20 -fwasm-exceptions \
    -DLEAN_EMSCRIPTEN -DLEAN_EXPORTING -DLEAN_BUILD_TYPE=Release \
    -I"$SRC/src" -I"$W/libuv/include" -- "${RT_PATHS[@]}"
  mkdir -p "$W/lib"
  emar rcs "$W/lib/libleanrt.a" "$W"/obj/rt/*.o
fi

## Init and Std ###############################################################
# Their C is generated with the installed `lean`, rather than taken from
# stage0/, so that it matches the toolchain exactly. Only the modules that
# prune.py selects get compiled, below.

for lib in Init Std; do
  if [ ! -f "$W/core-c/$lib.done" ]; then
    echo "== Generating C for $lib"
    mkdir -p "$W/core-c"
    (cd "$SRC/src" && find "$lib" "$lib.lean" -name '*.lean' | sed 's/\.lean$//') \
      | xargs -P "$JOBS" -n 1 sh -c \
        'cd "'"$SRC/src"'" && "'"$LEAN"'" --root=. -c "'"$W/core-c"'/$(echo "$0" | tr / .).c" "$0.lean"'
    touch "$W/core-c/$lib.done"
  fi
done

## Lake #######################################################################
# Lake builds the .olean files and emits C for this package's modules. The C
# for Mathlib and the other dependencies comes with their build cache.

echo "== Building $ENTRY with Lake"
lake build "$ENTRY"
# This package's modules that ENTRY imports, directly or not.
LOCAL_MODULES=$(python3 - "$ENTRY" <<'EOF'
import re, sys, os
todo, seen = [sys.argv[1]], []
while todo:
    m = todo.pop()
    path = m.replace('.', '/') + '.lean'
    if m in seen or not os.path.exists(path):
        continue
    seen.append(m)
    todo += re.findall(r'^(?:public )?(?:meta )?import\s+(\S+)', open(path).read(), re.M)
print(' '.join('+' + m + ':c' for m in seen))
EOF
)
lake build $LOCAL_MODULES

## Choosing modules ###########################################################

echo "== Choosing modules to link"
APP=$W/app
rm -rf "$APP/prune"
INIT_SYMBOL=$(python3 web/prune.py "$ENTRY" "$APP/prune" \
  .lake/build/ir .lake/packages/*/.lake/build/ir "$W/core-c")

## Compiling ##################################################################

echo "== Compiling"
# Objects are named after their source paths, and only rebuilt when stale.
mkdir -p "$APP/obj"
printf '%s\n' "${CFLAGS[@]}" > "$APP/cflags.rsp"
OBJS=()
while read -r c; do
  o=$APP/obj/$(echo "${c#"$ROOT"/}" | tr / _ | sed 's/\.c$/.o/')
  printf '%s\n%s\n' "$c" "$o"
  OBJS+=("$o")
done < "$APP/prune/sources.txt" > "$APP/pairs.txt"
xargs -P "$JOBS" -n 2 sh -c \
  '[ "$1" -nt "$0" ] || emcc @"'"$APP"'/cflags.rsp" -c "$0" -o "$1"' < "$APP/pairs.txt"
emcc "${CFLAGS[@]}" -c "$APP/prune/stubs.c" -o "$APP/obj/stubs.o"
emcc "${CFLAGS[@]}" -c web/borrowed.c -o "$APP/obj/borrowed.o"
emcc "${CFLAGS[@]}" -DCGLEAN_INIT="$INIT_SYMBOL" -c web/glue.c -o "$APP/obj/glue.o"

## Linking ####################################################################

echo "== Linking ${#OBJS[@]} modules"
printf '%s\n' "${OBJS[@]}" "$APP/obj/stubs.o" "$APP/obj/borrowed.o" "$APP/obj/glue.o" > "$APP/link.rsp"
# em++, not emcc, so that the C++ standard library is linked for the runtime.
# The signature-mismatch warnings for lean_io_create_temp{file,dir} come from
# another out-of-date WebAssembly stub; harmless unless they are called.
if ! em++ -O2 -fwasm-exceptions @"$APP/link.rsp" "$W/lib/libleanrt.a" "$W/lib/libuv.a" \
    -sEXPORTED_RUNTIME_METHODS=ccall,cwrap -sMODULARIZE -sEXPORT_ES6 -sALLOW_MEMORY_GROWTH \
    -o "$OUT/cglean.mjs"; then
  echo >&2
  echo "Undefined symbols above that aren't initializers are code from a module that" >&2
  echo "prune.py cut. If it's safe to, copy the function into web/borrowed.c." >&2
  exit 1
fi

echo "== Done: $(du -h "$OUT/cglean.wasm" | cut -f1) web/dist/cglean.wasm"
echo "Serve with: python3 -m http.server -d web 8000"
