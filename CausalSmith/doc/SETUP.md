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
| Node.js **≥ 20.20.2** | TypeScript pipeline runtime | Floor from `tools/package.json` `engines`; 22.x verified. `source tools/scripts/node_env.sh` puts a satisfying install on PATH, locating nvm via `$NVM_DIR` rather than assuming `$HOME`. Older node (e.g. system node 12) silently fails. |
| [`lean-lsp-mcp`](https://github.com/) on `PATH` | Lean type-checking for agents | Or point `leanLspMcpBinary` / `CAUSALSMITH_LEAN_LSP_MCP` at an absolute path. |
| `codex` CLI (OpenAI) | Discovery + proof agents | Default models `gpt-5.x` (see "Models" below). Billed to the CLI's own login unless you configure api auth (see "Who pays" below). |
| `claude` CLI (Anthropic) | Reviewer / judge agents | Same: billed to the CLI's stored login by default; an API key is an opt-in alternative, not a requirement. |
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

### Retrieval models (semantic search) — rebuilding on a fresh machine

The two fine-tuned retrieval models are **gitignored weights**, so a fresh clone or a
migration to a new machine has to regenerate them; only their meta sidecars are committed.
Everything is derived offline from `doc/library_index.json` (no LLM, no labels), so the
rebuild is fully reproducible — the train/test split is a deterministic hash of module
names, which is what keeps the reported numbers leak-free.

The scripts shell out to plain `python3`, so **the interpreter that has `torch` +
`sentence-transformers` installed must be the one on `PATH`** (a venv works; activate it, or
prepend its `bin/`). Otherwise semantic retrieval silently degrades to lexical-only. Weights
for the base checkpoints (`BAAI/bge-large-en-v1.5`, `BAAI/bge-reranker-base`) must be in the
HF cache; the scripts default to `HF_HUB_OFFLINE=1`, so set it to `0` for the first download.
Training needs one GPU:

```sh
cd CausalSmith/tools
python3 scripts/build_finetune_data.py --out ../../doc/retrieval_finetune
python3 scripts/train_biencoder.py --test-modules ../../doc/retrieval_finetune/test_modules.json \
        --out ../../doc/retrieval_model_ft --epochs 3 --hard-negs 4   # add --grad-checkpoint on a ≤12GB card
npm run embed:library && npm run lint:embeddings                       # re-embed the corpus with it
npm run eval:retrieval -- --test-modules ../../doc/retrieval_finetune/test_modules.json --module
```

The cross-encoder reranker is optional (opt-in, not wired into the live pipeline — see the
retrieval-v2 plan): `python3 scripts/train_reranker.py --test-modules … --out ../../doc/retrieval_reranker_ft`.

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
| `codexSandbox` | Codex local-tool sandbox (`workspace-write` / `danger-full-access`). | `workspace-write` |
| `authMode` | Who pays for model calls, for both runners: `subscription` or `api`. | `subscription` |
| `anthropicAuth` / `openaiAuth` | Per-provider override of `authMode`. | unset |
| `anthropicApiKey` / `anthropicApiKeyFile` | Anthropic key, inline or as a path to a file holding it. Read only in api mode. | unset |
| `openaiApiKey` / `openaiApiKeyFile` | Same, for OpenAI. | unset |
| `codexApiHome` | `CODEX_HOME` for codex api mode — deliberately not `~/.codex`. | `~/.codex-causalsmith-api` |

Each field also has an environment-variable override (env wins over the file):

- `CLAUDE_CODE_GIT_BASH_PATH` → `gitBashPath`
- `CAUSALSMITH_LEAN_LSP_MCP` → `leanLspMcpBinary`
- `CAUSALSMITH_LEAN_PROJECT_PATH` → `leanProjectPath`
- `MCP_TIMEOUT` → `mcpTimeoutMs`
- `CAUSALSMITH_CODEX_SANDBOX` → `codexSandbox`
- `CAUSALSMITH_AUTH_MODE` → `authMode`; `CAUSALSMITH_ANTHROPIC_AUTH` / `CAUSALSMITH_OPENAI_AUTH` → the per-provider fields
- `ANTHROPIC_API_KEY` / `OPENAI_API_KEY` → the corresponding key fields
- `CAUSALSMITH_CODEX_HOME_API` → `codexApiHome`

## Who pays for the model calls

Out of the box the pipeline spends the **interactive logins already on the machine**: whatever `claude` is signed in as, and the ChatGPT plan in `~/.codex`. Nothing to configure — sign the two CLIs in (`claude`, then `codex login`) and runs work.

To bill an **API key** instead, set the mode and supply the key in `local.json` (or by env, which wins):

```jsonc
{
  "authMode": "api",
  "anthropicApiKeyFile": "~/.secrets/anthropic.key",
  "openaiApiKeyFile": "~/.secrets/openai.key"
}
```

Per-provider values let you mix: `"anthropicAuth": "api"` with `"openaiAuth": "subscription"` puts the claude reviewers on a key and leaves codex on the ChatGPT plan. The resolved modes print at startup (`[causalsmith] auth: claude=api codex=subscription`); keys are never printed.

Three behaviours worth knowing before you switch:

- **A missing key aborts the run.** `api` mode with no key throws at startup rather than falling back to the subscription — a silent fallback would only show up on an invoice.
- **It governs pipeline-issued calls.** Everything dispatched by `causalsmith research/present/study` obeys it. A `codex exec` an orchestrator runs by hand (e.g. the `causalsmith-topics` slate gate) bypasses it and spends the machine's codex login.
- **Your subscription logins are never disturbed.** claude api calls use `--bare`, which pins that process to `ANTHROPIC_API_KEY` and never reads the keychain. Codex allows only one login method per `CODEX_HOME` and *deletes* stored ChatGPT credentials when api auth is forced on that home, so codex api mode runs against `codexApiHome` instead, bootstrapped once with `codex login --with-api-key` (your `~/.codex/config.toml` is copied in on first use). If you ever do lose the codex login, `codex login --device-auth` restores it.

## Environment variables

| Variable | Required | Purpose |
|---|---|---|
| `ANTHROPIC_API_KEY` | only in `api` mode | Anthropic key for the claude workers. Unused in the default subscription mode. |
| `OPENAI_API_KEY` | only in `api` mode | OpenAI key for the codex workers. |
| `CAUSALSMITH_AUTH_MODE` | no | `subscription` (default) or `api`; `CAUSALSMITH_ANTHROPIC_AUTH` / `CAUSALSMITH_OPENAI_AUTH` override it per provider. |
| `CAUSALSMITH_CODEX_HOME_API` | no | `CODEX_HOME` used in codex api mode. |
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
