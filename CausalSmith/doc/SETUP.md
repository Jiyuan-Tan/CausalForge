# CausalSmith pipeline — environment setup

This document lists everything needed to **run** the CausalSmith (`CausalSmith research`)
pipeline on a fresh machine. For *using* the pipeline once set up, see
[`USER_MANUAL.md`](USER_MANUAL.md).

The pipeline resolves its own repository root at runtime (it walks up to the
`lakefile.toml` named `CausalSmith`), so it is not tied to any absolute path.
The machine-specific values below are supplied via a gitignored config file and
environment variables — never hardcoded.

## Prerequisites

| Tool | Purpose | Notes |
|---|---|---|
| [`elan`](https://github.com/leanprover/elan) + `lake` | Lean toolchain / build | Toolchain pinned by `lean-toolchain` (`leanprover/lean4:v4.29.0-rc3`). |
| Node.js **≥ 20.20.2** | TypeScript pipeline runtime | Enforced by `tools/package.json` `engines`. Older node (e.g. system node 12) silently fails. |
| [`lean-lsp-mcp`](https://github.com/) on `PATH` | Lean type-checking for agents | Or point `leanLspMcpBinary` / `CAUSALSMITH_LEAN_LSP_MCP` at an absolute path. |
| `codex` CLI (OpenAI) | Discovery + proof agents | Default models `gpt-5.x` (see "Models" below). |
| `claude` CLI (Anthropic) | Reviewer / judge agents | Needs `ANTHROPIC_API_KEY`. |
| Python 3 + `sentence-transformers` | Retrieval embeddings (optional) | Only for `npm run embed:library` / semantic search. |

Build the Lean packages first (the pipeline pre-warms Lean modules):

```sh
lake exe cache get              # Mathlib build cache
lake build                      # Causalean
lake -d CausalSmith build       # CausalSmith
```

Install pipeline JS dependencies:

```sh
cd CausalSmith/tools && npm install
```

### FoML / lean-rademacher (vendored)

The one non-Mathlib Lean dependency, `FoML`, is **vendored in-tree** under
`third_party/lean-rademacher/` (an adapted, MIT-licensed copy of
`github.com/auto-res/lean-rademacher`; see its `UPSTREAM.md`). The root
`lakefile.toml` references it by relative path, so no sibling checkout or network
fetch is needed — a fresh clone builds directly.

## Machine-specific config: `tools/config/local.json`

Copy the example and edit **one file** (gitignored):

```sh
cp CausalSmith/tools/config/local.example.json CausalSmith/tools/config/local.json
```

| Field | Meaning | Default |
|---|---|---|
| `gitBashPath` | Windows only: absolute path to git-bash `bash.exe` (use forward slashes). | unset |
| `leanLspMcpBinary` | `lean-lsp-mcp` server binary (PATH name or absolute). | `lean-lsp-mcp` |
| `leanProjectPath` | Override for lean-lsp `--lean-project-path`. | repo root |
| `mcpTimeoutMs` | `MCP_TIMEOUT` for the (slow cold-starting) lean-lsp server. | `600000` |

Each field also has an environment-variable override (env wins over the file):

- `CLAUDE_CODE_GIT_BASH_PATH` → `gitBashPath`
- `CAUSALSMITH_LEAN_LSP_MCP` → `leanLspMcpBinary`
- `CAUSALSMITH_LEAN_PROJECT_PATH` → `leanProjectPath`
- `MCP_TIMEOUT` → `mcpTimeoutMs`

## Environment variables

| Variable | Required | Purpose |
|---|---|---|
| `ANTHROPIC_API_KEY` | yes (for reviewer/judge stages) | Anthropic API auth. |
| `CAUSALSMITH_CONTACT` | no | Contact string sent as the `User-Agent` to citation APIs (crossref/arXiv). Defaults to a generic project identifier. |
| `HF_HUB_OFFLINE` | no | Retrieval scripts default to `1` (offline; model weights must be cached). Set `0` to allow first-time download of embedding/reranker weights. |
| `CAUSALSMITH_SHARED_LEAN_LSP_URL` | no | Reuse a shared lean-lsp server instead of spawning per-agent. |

## Windows

- codex-cli's default `elevated` sandbox fails to spawn on Windows. Pass
  `-c windows.sandbox=unelevated` (ignored on other OSes). The pipeline's codex
  invocations already include this.
- Set `gitBashPath` in `local.json` (forward slashes, e.g.
  `C:/Program Files/Git/bin/bash.exe`).
- Note: the Python retrieval daemons use Unix-domain sockets and do not run on
  native Windows; semantic retrieval is a Linux/macOS feature.

## Models

Every model id flows through `tools/src/models.ts`, which maps five logical
roles to committed defaults (the current OpenAI `codex` + Anthropic `claude`
lineup). To run on a different lineup, set the corresponding env var — no source
edit needed:

| Env var | Role | Default | Runner |
|---|---|---|---|
| `CAUSALEAN_MODEL_CODEX_KERNEL` | hard math and formalization core (D-1.2/D0/D0.5, F2/F3, unified F2.5/F4 reviewer) | `gpt-5.6-sol` | codex |
| `CAUSALEAN_MODEL_CODEX_MECH` | mechanical / clerical discovery support plus F1.5 and F5 | `gpt-5.6-terra` | codex |
| `CAUSALEAN_MODEL_CODEX_CONSULT` | orchestrator D-stage halt-consultation (manual) | `gpt-5.6-sol` | codex |
| `CAUSALEAN_MODEL_CLAUDE_MAIN` | main reviewer / producer | `opus` | claude |
| `CAUSALEAN_MODEL_CLAUDE_MID` | mid tier | `sonnet` | claude |
| `CAUSALEAN_MODEL_CLAUDE_CHEAP` | cheap / bulk | `haiku` | claude |

codex roles take an OpenAI model id; claude roles take any `claude --model`
value (an alias like `opus`, or a pinned id like `claude-opus-4-8`).

Note: the retrieval **embedding/reranker** models (`BAAI/bge-*` in
`tools/scripts/*.py`) are intentionally *not* runtime-swappable — the committed
`doc/library_embeddings.*` vectors are tied to that specific model, so changing
it requires re-running `npm run embed:library`.

## Quick check

```sh
cd CausalSmith/tools
npm run search -- "backdoor adjustment"     # retrieval over doc/library_index.json
```
