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
# EXCLUSION: `**/tmp/**` is skipped. Research runs leave scratch probes under
# `CausalSmith/<Area>/<RUN>_Research/tmp/` (49 such files as of 2026-08-16, all
# untracked). They are throwaway elaboration experiments, not library modules,
# so building them turns a real regression signal into noise. This is the ONLY
# exclusion — everything else stays find-derived on purpose, because the whole
# point of this sweep is that nothing escapes scope by being forgotten.
#
# Usage: full_tree_build.sh  (from anywhere inside the workspace)
# Exit: 0 iff every module builds; failing targets are listed on stderr.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$WS_ROOT"

ALLMODS=$(cd CausalSmith && find CausalSmith -name '*.lean' -not -path '*/tmp/*' \
  | sed 's/\.lean$//; s|/|.|g')
N=$(echo "$ALLMODS" | wc -l)
SKIPPED=$(cd CausalSmith && find CausalSmith -name '*.lean' -path '*/tmp/*' | wc -l)
echo "full_tree_build: $N CausalSmith modules (find-derived, root graph + orphans)"
# Report what was dropped: a silent exclusion would read as "covered everything".
[ "$SKIPPED" -gt 0 ] && echo "full_tree_build: skipped $SKIPPED scratch module(s) under **/tmp/**"

OUT=$(lake -d CausalSmith build $ALLMODS 2>&1)
STATUS=$?
if [ $STATUS -ne 0 ]; then
  echo "$OUT" | sed -n '/Some required targets logged failures/,$p' >&2
  echo "full_tree_build: FAILED (see targets above)" >&2
  exit 1
fi
echo "full_tree_build: OK ($N modules green)"
