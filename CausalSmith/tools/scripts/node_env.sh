#!/usr/bin/env bash
# Put a Node satisfying tools/package.json `engines.node` on PATH. SOURCE me:
#
#     source <AUTOID>/CausalSmith/tools/scripts/node_env.sh
#
# Why this exists. Every launcher used to open with
# `source ~/.nvm/nvm.sh && nvm use 20.20.2`, which is wrong twice over:
#
#  1. nvm need not live under $HOME. On a cluster with network home directories
#     $NVM_DIR commonly points outside $HOME, so `~/.nvm/nvm.sh` does not exist.
#     Guarded call sites then silently no-op and the process inherits whatever
#     node happens to be on PATH; UNGUARDED call sites are worse — `source` of a
#     missing file returns nonzero, so the `&& npx ... causalsmith.ts` chained
#     after it never runs at all.
#  2. The pipeline needs *a Node at or above the engines floor*, not the exact
#     patch release 20.20.2. Pinning an exact version breaks every launcher the
#     moment a box's installed set moves on, which is the friction this file
#     removes. The suite is verified green on both 20.20.2 and 22.x.
#
# Policy: keep the Node already on PATH when it satisfies the floor; otherwise
# select the newest satisfying nvm-installed version by prepending its bin/ to
# PATH -- which is all `nvm use` does, without the slow nvm.sh sourcing or the
# $HOME assumption. Sourcing nvm.sh is never required.
#
# Quiet and idempotent on success. On failure prints one actionable line and
# returns 1, so `source node_env.sh && <cmd>` still fails closed.
#
# Escape hatches:
#   CAUSALSMITH_NODE_BIN=/path/to/node/bin   force a specific install
#   CAUSALSMITH_NODE_ENV_VERBOSE=1           echo the resolved interpreter

__cs_node_env() {
  local src tools_root floor cur cand cand_ver best best_ver dir

  src="${BASH_SOURCE[0]:-$0}"
  tools_root="$(cd "$(dirname "$src")/.." 2>/dev/null && pwd)" || return 1

  # Read the floor from package.json so this file never becomes a second,
  # drifting source of truth for the supported Node range.
  floor="$(sed -n 's/.*"node"[[:space:]]*:[[:space:]]*">=[[:space:]]*\([0-9][0-9.]*\)".*/\1/p' \
    "$tools_root/package.json" 2>/dev/null | head -n1)"
  [ -n "$floor" ] || floor="20.20.2"

  # nvm refuses to operate while this is set, and it also redirects
  # `npm --prefix tools` installs to the wrong root.
  unset npm_config_prefix

  # version_ge A B  <=>  min(A,B) == B
  __cs_ge() { [ "$(printf '%s\n%s\n' "$2" "$1" | sort -V | head -n1)" = "$2" ]; }

  if [ -n "${CAUSALSMITH_NODE_BIN:-}" ]; then
    PATH="$CAUSALSMITH_NODE_BIN:$PATH"
    export PATH
  fi

  cur="$(command -v node >/dev/null 2>&1 && node -v 2>/dev/null | sed 's/^v//')"
  if [ -n "$cur" ] && __cs_ge "$cur" "$floor"; then
    [ -n "${CAUSALSMITH_NODE_ENV_VERBOSE:-}" ] &&
      echo "node_env: using $(command -v node) (v$cur, floor >=$floor)" >&2
    unset -f __cs_ge
    return 0
  fi

  # Fall back to the newest satisfying nvm-installed version. Check $NVM_DIR
  # first (authoritative when set), then the conventional $HOME location.
  best=""
  best_ver=""
  for dir in "${NVM_DIR:-}/versions/node" "$HOME/.nvm/versions/node"; do
    [ -d "$dir" ] || continue
    for cand in "$dir"/v*; do
      [ -x "$cand/bin/node" ] || continue
      cand_ver="${cand##*/v}"
      __cs_ge "$cand_ver" "$floor" || continue
      if [ -z "$best_ver" ] || __cs_ge "$cand_ver" "$best_ver"; then
        best="$cand/bin"
        best_ver="$cand_ver"
      fi
    done
  done

  if [ -n "$best" ]; then
    PATH="$best:$PATH"
    export PATH
    [ -n "${CAUSALSMITH_NODE_ENV_VERBOSE:-}" ] &&
      echo "node_env: selected $best/node (v$best_ver, floor >=$floor)" >&2
    unset -f __cs_ge
    return 0
  fi

  echo "node_env: no Node >=$floor found (PATH node: ${cur:-none}; searched \$NVM_DIR=${NVM_DIR:-unset} and \$HOME/.nvm)." >&2
  echo "node_env: install one (\`nvm install $floor\`) or set CAUSALSMITH_NODE_BIN=/path/to/node/bin." >&2
  unset -f __cs_ge
  return 1
}

__cs_node_env
__cs_node_env_rc=$?
unset -f __cs_node_env
# `return` when sourced (the supported use), `exit` when run directly.
return $__cs_node_env_rc 2>/dev/null || exit $__cs_node_env_rc
