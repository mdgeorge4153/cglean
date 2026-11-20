#!/usr/bin/env bash
# Builds the blueprint and the drag-and-drop demo, puts the demo where the
# blueprint embeds it (demo/, as CI does), and serves the result locally.
#
#     scripts/serve-blueprint.sh [--no-demo]
#
# --no-demo skips rebuilding the demo (web/build.sh), reusing web/dist. The
# blueprint needs leanblueprint and TeX; the demo needs what web/build.sh does.

set -euo pipefail
cd "$(dirname "$0")/.."

# MacTeX's binaries, when they aren't on PATH already.
[ -d /Library/TeX/texbin ] && export PATH=/Library/TeX/texbin:$PATH

[ "${1:-}" = --no-demo ] || web/build.sh

leanblueprint web

rm -rf blueprint/web/demo
mkdir -p blueprint/web/demo
cp -r web/index.html web/main.js web/dist blueprint/web/demo/

leanblueprint serve
