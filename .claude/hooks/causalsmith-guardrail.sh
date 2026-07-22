#!/usr/bin/env bash
# PreToolUse guardrail for the CausalSmith research and study modes.
#
# Replaces the legacy global guardrail with a run-scoped heartbeat check so
# CausalSmith research and study runs can coexist.
#
# Active-run signals:
#   - CausalSmith research run: CausalSmith/doc/research/active/<qid>/logs/.run.active
#                    (heartbeat written by tools/src/shared/run_heartbeat.ts;
#                     state-file fallback retained for back-compat)
#   - study-mode run (legacy compatibility): CausalSmith/doc/study/runs/<run_id>/.active
#
# Stale heartbeats (mtime > 5min AND PID dead) are ignored.
#
# Policy:
#   1. Edits to study/nodes/* or study/index.json are ALWAYS denied while
#      ANY .active file is fresh (either pipeline).
#   2. Edits to study/runs/<run_id>/* are denied iff that run's .active
#      file is fresh.
#   3. Edits inside CausalSmith/doc/research/active/<qid>/ are denied iff
#      that qid's .active is fresh (or, if no .active file, the legacy
#      state.json signal indicates a run in flight).
#   4. Anything else is allowed.
#
# Reads tool input JSON on stdin. Emits PreToolUse JSON on stdout. Always
# exits 0; deny decisions are in the JSON.
set -u

# Derive REPO from the hook's own location: <REPO>/.claude/hooks/causalsmith-guardrail.sh.
# Allow $CAUSALSMITH_REPO override for tests / unusual deployments.
HOOK_SELF="${BASH_SOURCE[0]}"
if [ -z "${CAUSALSMITH_REPO:-}" ]; then
  HOOK_DIR=$(cd "$(dirname "$HOOK_SELF")" >/dev/null 2>&1 && pwd)
  REPO=$(cd "$HOOK_DIR/../.." >/dev/null 2>&1 && pwd)
else
  REPO="$CAUSALSMITH_REPO"
fi
STUDY_RUNS="$REPO/CausalSmith/doc/study/runs"
STUDY_NODES_PREFIX="CausalSmith/doc/study/nodes"
STUDY_INDEX="CausalSmith/doc/study/index.json"
FORM_ROOT="$REPO/CausalSmith/doc/research"
RULES_FILE=".claude/skills/causalsmith/SKILL.md"

# Pick a working JSON tool. On Windows, `python3` may resolve to the App
# Store stub that exits silently — probe each candidate before committing.
JSON_TOOL=""
if command -v jq >/dev/null 2>&1; then
  JSON_TOOL=jq
else
  for py in python3 python py; do
    if command -v "$py" >/dev/null 2>&1; then
      if "$py" -c 'import json, sys; sys.exit(0)' >/dev/null 2>&1; then
        JSON_TOOL="$py"
        break
      fi
    fi
  done
fi

if [ -z "$JSON_TOOL" ]; then
  echo "causalsmith guardrail: jq / python missing or non-functional." >&2
  exit 1
fi

emit_deny() {
  case "$JSON_TOOL" in
    jq)
      jq -nc --arg msg "$1" '{
        hookSpecificOutput: {
          hookEventName: "PreToolUse",
          permissionDecision: "deny",
          permissionDecisionReason: $msg
        }
      }'
      ;;
    *)
      "$JSON_TOOL" -c '
import json, sys
print(json.dumps({
  "hookSpecificOutput": {
    "hookEventName": "PreToolUse",
    "permissionDecision": "deny",
    "permissionDecisionReason": sys.argv[1],
  }
}))
' "$1"
      ;;
  esac
}

input=$(cat)
case "$JSON_TOOL" in
  jq)
    file_path=$(printf '%s' "$input" | jq -r '(.tool_input.file_path // .tool_input.path // "")' 2>/dev/null)
    ;;
  *)
    file_path=$(printf '%s' "$input" | "$JSON_TOOL" -c '
import json, sys
try:
  d = json.load(sys.stdin)
  print(d.get("tool_input", {}).get("file_path") or d.get("tool_input", {}).get("path") or "")
except Exception:
  print("")
' 2>/dev/null)
    ;;
esac

if [ -z "$file_path" ]; then
  exit 0
fi

# On Windows (Git Bash / MSYS), tool input may arrive as a Win32 path
# (e.g. "D:\foo\bar"). REPO came from `pwd`, which yields a POSIX-style
# path (e.g. "/d/foo"), so direct prefix-stripping would fail. Normalize
# via cygpath when available; otherwise fall back to a backslash→slash
# rewrite plus drive-letter remap, which covers Git Bash defaults.
normalize_path() {
  local p="$1"
  if command -v cygpath >/dev/null 2>&1; then
    cygpath -u "$p" 2>/dev/null || printf '%s' "$p"
    return
  fi
  if printf '%s' "$p" | grep -qE '^[A-Za-z]:[\\/]'; then
    local drive=$(printf '%s' "$p" | cut -c1 | tr 'A-Z' 'a-z')
    local rest=$(printf '%s' "$p" | cut -c3- | tr '\\' '/')
    printf '/%s%s' "$drive" "$rest"
  else
    printf '%s' "$p" | tr '\\' '/'
  fi
}
file_path=$(normalize_path "$file_path")

rel="${file_path#"$REPO/"}"

# Helper: is a heartbeat file (.run.active / .active) fresh
# (mtime within 5min AND its PID alive)?
#   $1 = heartbeat file path
is_fresh() {
  local active="$1"
  [ -f "$active" ] || return 1
  # mtime check (in seconds, portable across GNU/BSD `stat`)
  local now=$(date +%s)
  local mtime
  mtime=$(stat -c %Y "$active" 2>/dev/null || stat -f %m "$active" 2>/dev/null)
  [ -z "$mtime" ] && return 1
  local age=$((now - mtime))
  [ "$age" -gt 300 ] && return 1
  # PID liveness (first whitespace-separated token).
  local pid
  pid=$(head -n 1 "$active" 2>/dev/null | awk '{print $1}')
  [ -z "$pid" ] && return 1
  if kill -0 "$pid" 2>/dev/null; then
    return 0
  fi
  # Git Bash on Windows can't `kill -0` Win32 PIDs from outside its own
  # process tree; fall back to `tasklist`. MSYS path conversion mangles
  # `/FI` into a path, so prefix flags with `//` (a recognized MSYS escape
  # that leaves them as `/FI` for the Windows binary).
  if command -v tasklist >/dev/null 2>&1; then
    if tasklist //FI "PID eq $pid" //NH 2>/dev/null | grep -qE "[[:space:]]$pid[[:space:]]"; then
      return 0
    fi
  fi
  return 1
}

# Helper: collect all fresh heartbeat files under a roots list.
# CausalSmith research writes `.run.active` at research/<qid>/logs/ (depth 3 below
# the research root); study-mode runs write `.active` at study/runs/<run_id>/
# (depth 2). Banked entries (_bank/, _literature_bank/) are inert — skip them.
collect_fresh() {
  local root
  for root in "$@"; do
    [ -d "$root" ] || continue
    while IFS= read -r f; do
      [ -z "$f" ] && continue
      if is_fresh "$f"; then
        printf '%s\n' "$f"
      fi
    done < <(find "$root" -maxdepth 4 \( -name '.active' -o -name '.run.active' \) -type f \
               ! -path '*/_bank/*' ! -path '*/_literature_bank/*' 2>/dev/null)
  done
}

active_files=$(collect_fresh "$STUDY_RUNS" "$FORM_ROOT")

# 1) Graph files: deny if ANY pipeline is active.
case "$rel" in
  "$STUDY_NODES_PREFIX"/*|"$STUDY_INDEX")
    if [ -n "$active_files" ]; then
      emit_deny "causalsmith guardrail: graph write to '$rel' blocked while a pipeline is active (any of: $(printf '%s ' $active_files)). Wait for the pipeline to finish or remove its heartbeat file after confirming the PID is dead."
      exit 0
    fi
    exit 0
    ;;
esac

# 2) Run-dir edits: deny if THIS run's .active is fresh.
if [ -z "$active_files" ]; then
  # Fall through to the legacy state.json check for paths under
  # CausalSmith/doc/research/active/ — the research pipeline still writes
  # state.json without a .active heartbeat in some code paths.
  :
fi

# Iterate line-by-line: paths can contain spaces (esp. on Windows under
# Git Bash), so a naive `for active in $active_files` would split mid-path.
while IFS= read -r active; do
  [ -z "$active" ] && continue
  active_dir=$(dirname "$active")
  # Research heartbeats live in <run-dir>/logs/.run.active; protect the whole
  # run directory, not only its logs subdirectory. Legacy study-run heartbeats
  # remain directly under their owned run directory.
  if [ "$(basename "$active")" = ".run.active" ] && [ "$(basename "$active_dir")" = "logs" ]; then
    active_dir=$(dirname "$active_dir")
  fi
  case "$file_path" in
    "$active_dir"/*)
      emit_deny "causalsmith guardrail: edit to '$rel' inside an active run directory ($active_dir) blocked. The pipeline owns this directory while its heartbeat (.run.active / .active) is fresh."
      exit 0
      ;;
  esac
done <<EOF
$active_files
EOF

# 3) Legacy state-file check (back-compat).
# Without a .active heartbeat, deny edits to research/active/<qid>/* iff
# there's a *_state.json with stage_completed != "5" for that qid.
case "$rel" in
  CausalSmith/doc/research/*)
    # Research runs live under research/active/<qid>/. Banked entries are inert.
    seg4=$(printf '%s' "$rel" | awk -F/ '{print $4}')
    qid=""
    qid_rel_prefix=""
    case "$seg4" in
      active)
        qid=$(printf '%s' "$rel" | awk -F/ '{print $5}')
        qid_rel_prefix="CausalSmith/doc/research/active/$qid"
        qid_dir="$FORM_ROOT/active/$qid"
        ;;
      _bank)
        ;;
      *) ;;
    esac
    if [ -n "$qid" ]; then
      if [ -d "$qid_dir" ] && command -v jq >/dev/null 2>&1; then
        # If any state.json in this qid dir is unfinished, deny.
        while IFS= read -r sjson; do
          [ -z "$sjson" ] && continue
          stage=$(jq -r '.stage_completed // empty' "$sjson" 2>/dev/null)
          if [ -n "$stage" ] && [ "$stage" != "5" ]; then
            # Allow state.json / PIPELINE_NOTES.md (orchestrator-owned).
            case "$rel" in
              "$qid_rel_prefix"/state.json) exit 0 ;;
              "$qid_rel_prefix"/*_state.json) exit 0 ;;
              "$qid_rel_prefix"/PIPELINE_NOTES.md) exit 0 ;;
              CausalSmith/doc/research/PIPELINE_NOTES.md) exit 0 ;;
            esac
            emit_deny "causalsmith guardrail (legacy state-file path): CausalSmith research appears active for qid=$qid (state.json with stage_completed=$stage). Use causalsmith research --resume rather than editing directly. Re-read $RULES_FILE."
            exit 0
          fi
        done < <(find "$qid_dir" -maxdepth 1 \( -name 'state.json' -o -name '*_state.json' \) -type f 2>/dev/null)
      fi
    fi
    ;;
esac

exit 0
