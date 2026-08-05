#!/usr/bin/env bash
# Build EVERY CausalSmith module, not just the root import graph.
#
# `lake -d CausalSmith build` verifies only what `CausalSmith.lean` transitively
# imports. Research-run modules (CausalSmith/<Area>/<RUN>_Research/**) are mostly
# not reachable from it, so a library-wide signature change can break them while
# the default build stays green — on 2026-08-04 fourteen such modules across six
# runs and the substrate were broken at a "green" HEAD. This sweep derives the
# target list from the filesystem so nothing can be silently out of scope.
#
# Usage: full_tree_build.sh  (from anywhere inside the workspace)
# Exit: 0 iff every module builds; failing targets are listed on stderr.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$WS_ROOT"

ALLMODS=$(cd CausalSmith && find CausalSmith -name '*.lean' | sed 's/\.lean$//; s|/|.|g')
N=$(echo "$ALLMODS" | wc -l)
echo "full_tree_build: $N CausalSmith modules (find-derived, root graph + orphans)"

OUT=$(lake -d CausalSmith build $ALLMODS 2>&1)
STATUS=$?
if [ $STATUS -ne 0 ]; then
  echo "$OUT" | sed -n '/Some required targets logged failures/,$p' >&2
  echo "full_tree_build: FAILED (see targets above)" >&2
  exit 1
fi
echo "full_tree_build: OK ($N modules green)"
