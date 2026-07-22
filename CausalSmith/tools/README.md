# CausalSmith TypeScript Orchestrator (CausalSmith research pipeline)

Phase A of the CausalSmith refactor: a deterministic TypeScript spine for state
validation, resume, stage ordering, logging, and model worker wrappers.

## Prerequisites

- Node 20.20.2 or newer.
- `claude` CLI logged in with the user's subscription account.
- `codex` CLI logged in with the user's ChatGPT subscription account.
- No API keys are required by this package.

## Install

```bash
cd tools
npm install
```

## Commands

```bash
npm test
npm run typecheck
npx tsx bin/causalsmith.ts research panel_minimal_basis v1 --dry-run
npx tsx bin/causalsmith.ts research --resume panel_generic_minimality v2 --dry-run
```

`--dry-run` uses stub stage handlers and advances state deterministically; live
stage handlers run the real codex/claude workers.

## Active stage map (CausalSmith research)

A run is one phase sequence; each stage is owned by a module under `src/`. Discovery
(propose + solve the math) → formalization (translate to Lean + prove).

| Stage | What it does | Owning module |
| --- | --- | --- |
| D-1.1 | open-problem / gaps substrate | `discovery/stages/neg1_1.ts` |
| D-1.2 | proposal producer (typed proto-core author) | `discovery/stages/neg1_2.ts` → `discovery/stages/neg1_2_author.ts` |
| D-0.5 | proposal review (flagship rubric) | `discovery/stages/neg0_5.ts` |
| D0 | typed D0-SOLVE → D0-RENDER (the math derivation) | `discovery/stages/d0.ts` (`stages/d0_solve.ts` + `discovery/solve/` / `stages/d0_render.ts`) |
| D0.5 | post-derivation review (math + structure referees) | `discovery/stages/d0_5_core.ts` ↔ `stages/d0_r_core.ts` (directed revise) |
| F1 / F1.5 | NL formalization plan + reuse-soundness review | `formalization/stage1.ts` / `stage1_5.ts` |
| F2 | Lean scaffold (sorry-only) | `formalization/stage2.ts` |
| F2.5 | proof-review loop — owns statement reconciliation, proof fill, lint, and convergence review | `formalization/proof_review_loop.ts` |
| F5 | bank | `formalization/stage5.ts` |

Routing lives in `discovery/dispatcher.ts` + `formalization/dispatcher.ts`. Stages
3/3.5/4 remain as no-op pass-throughs (the proof-review loop in the F2.5 slot owns
that work). Shared discovery helpers: `discovery/cluster_setup.ts` (cluster routing +
setup blocks) and `discovery/theorem_review.ts` (per-theorem review propagation).

