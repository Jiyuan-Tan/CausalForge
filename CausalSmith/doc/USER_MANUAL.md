# CausalSmith User Manual

CausalSmith is a Lean 4 + TypeScript umbrella package that auto-generates and curates causal-inference theorems on top of the foundational `Causalean` library. The live pipeline is:

- **`causalsmith research`** — derive, formalize, verify, and bank causal-inference theorems end-to-end from a question id and specialization.
- **`causalsmith present`** — turn an accepted bank entry into a verified paper bundle.
- **`causalsmith study`** — build and promote one reusable Causalean substrate module.


### Two phases: discovery → formalization

Read each `causalsmith research` run as two phases of one research activity:

- **Discovery** (proposing) — propose a question, scope it against the literature, and solve the math informally. This is D-1, D0, and D0.5; by D0.5 the math claim has cleared informal review.
- **Formalization** (testing) — translate the math into Lean and prove it. This is F1 (NL formalization plan), F1.5 (review of that plan), F2 (Lean scaffold), F3 (proof fill), F4 (equivalence review), and F5 (bank + API.md). F1 is informal but already Lean-shaped — committing to types, hypotheses, and quantifier scope — so it counts as the first formalization step.

Formalization is the *verification* half of research, not a mechanical post-step: a failed F1.5 or F3 usually means the math claim itself was wrong, not that the translator broke. Stage identifiers below use the D-/F- prefix convention — "discovery" and "formalization" are just the conceptual grouping.

This manual is the user-facing entry point. For per-declaration documentation see [`doc/API.md`](API.md); for the pipeline run protocol start with the `causalsmith` skill at `.claude/skills/causalsmith/SKILL.md`. It dispatches the D- and F-stage sub-orchestrators as needed.

## Repository layout

```
CausalSmith/
  lakefile.toml             # name = "CausalSmith"; defaultTargets = ["CausalSmith"]
  CausalSmith.lean          # umbrella import; pulled in by `lake -d CausalSmith build`
  CausalSmith/              # Lean source root (namespace CausalSmith.*)
    Panel/                  # panel / linear-projection theorems (panel_* runs)
    ExactID/                # exact-identification outputs (populated by /causalsmith research eid_*)
    PartialID/              # partial-identification outputs (populated by /causalsmith research pid_*)
    Stat/                   # estimation/inference outputs — rates, efficiency, limit laws (/causalsmith research stat_*)
    Experimentation/        # design-based / randomization-inference outputs (/causalsmith research exp_*)
    Mathlib/                # Mathlib-shaped helpers awaiting promotion to Causalean
    Panel/Regression/       # regression-side helpers awaiting promotion
  doc/
    USER_MANUAL.md          # this file
    API.md                  # per-file / per-declaration documentation
    qid-naming.md           # qid conventions
    formalization/<qid>/    # per-run NL specs, state.json, reviews.jsonl
    formalization/_bank/    # banked entries by tier
    templates/              # Python+Jinja2 prompt rendering layer
    *.tex                   # source notes (panel question generator, dynamic 2SLS, …)
  tools/                    # TypeScript pipeline + supporting binaries
    bin/                    # CLI entry points (see below)
    src/                    # pipeline source
      cli.ts                # argument parsing + findRepoRoot
      pipeline.ts           # stage advancement loop
      state.ts              # state-machine schema (zod)
      bank.ts               # banking conventions
      pipeline_stages.ts    # all stage handlers + dispatcher (formerly research/index.ts)
      pipeline_support.ts   # cross-stage helpers (formerly research/support.ts)
      discovery/            # discovery-phase artifacts (D-1, D0, D0.5)
        prompts/            # Codex prompts for stage_neg1_*, stage0_*
      formalization/        # formalization-phase artifacts (F1, F1.5, F2, F3, F4, F5)
        prompts/            # Codex/Claude prompts for stage1_*, stage2_*, proof_filler/proof_reviewer, stage5_*, intervention*
        proof_review_loop.ts # unified proof-review loop (owns F2.5+F3+F3.5+F3.7+F4)
        prompts/            # prompt templates per stage
      templates/            # LaTeX skeletons (D-1, D0)
      workers/              # subagent dispatch adapters
    test/                   # vitest unit + smoke tests
```

`CausalSmith` depends on `Causalean` via `[[require]] path = ".."`. The dependency is one-way: `Causalean` never imports anything from `CausalSmith`. Promotion of a CausalSmith lemma into Causalean is a deliberate human step (copy the statement + proof into Causalean, then have CausalSmith re-import the Causalean version).

## Prerequisites

| Tool | Version | Why |
|---|---|---|
| Lean 4 | as pinned in `lean-toolchain` | Build CausalSmith + Causalean |
| Lake | bundled with Lean | Build orchestration |
| Node.js | `20.20.2` (via nvm) | TypeScript pipeline runtime — the default shell is often older and silently fails |
| Codex CLI | latest | Subagent dispatch for D-1 / D0 / F2 / F3 / F4 / F5 |

```bash
source ~/.nvm/nvm.sh && nvm use 20.20.2
```

Install TS deps once:

```bash
cd CausalSmith/tools && npm install
```

## Build

```bash
lake build Causalean                # build the foundational library
lake -d CausalSmith build        # build the CausalSmith catalogue
```

A full first build pulls down Mathlib + dependent packages and takes several minutes. Incremental builds are fast. For iteration during proof work, prefer the `lean-lsp` MCP (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`) over `lake build`.

**Warm the build cache before F1/F2/F3.** Those stages query Lean live via the `lean-lsp` MCP (see below). The first such call on a cold `.olean` cache triggers a dependency compile that can stall the stage; run `lake -d CausalSmith build` once first so the cache is warm.

## Local configuration (machine-specific paths)

Machine-specific paths live in **one** place: `tools/config/local.json` (gitignored; copy from `local.example.json`). `tools/src/local_config.ts` reads it, and every env var listed below overrides the file. `applyWorkerEnv()` runs at CLI startup to inject the worker env automatically.

| Field | Env override | Purpose |
|---|---|---|
| `gitBashPath` | `CLAUDE_CODE_GIT_BASH_PATH` | **Windows only.** Absolute path to git-bash `bash.exe`. The headless `claude` worker (F1/F1.5, intervention judge) exits empty without it. Leave `null` on Linux. |
| `leanLspMcpBinary` | `CAUSALSMITH_LEAN_LSP_MCP` | The `lean-lsp-mcp` server binary (PATH name or absolute). |
| `leanProjectPath` | `CAUSALSMITH_LEAN_PROJECT_PATH` | Optional override for lean-lsp `--lean-project-path`; `null` ⇒ the run's repoRoot (the lake project that transitively sees Causalean). |
| `mcpTimeoutMs` | `MCP_TIMEOUT` | Per-call timeout for the slow-cold-starting lean-lsp server (default 120000). |

**lean-lsp MCP wiring.** Both worker backends can query Lean live, but MCP must be configured explicitly (it is NOT auto-enabled): the `claude` worker gets a generated `--mcp-config` (F1 feasibility gate, F2 scaffold verify); the `codex` worker gets inline `-c mcp_servers.lean-lsp.*` flags when a stage passes `leanLsp: true` (F3 proof-fill). On the codex side, the network-off sandbox blocks the *search* tools (`lean_leansearch`/`lean_loogle`/`lean_leanfinder`) but the local tools (`lean_diagnostic_messages`/`lean_goal`/`lean_multi_attempt`/`lean_local_search`) work.

## Running the `causalsmith research` pipeline

The `/causalsmith research` slash command (`.claude/skills/causalsmith/SKILL.md`) is the canonical entry. The main skill owns the run lifecycle and dispatches `causalsmith-d` for discovery and `causalsmith-f` for formalization. It launches `tools/bin/causalsmith.ts research`. **The pipeline's cwd must be the CausalSmith package root** — `findRepoRoot` walks upward from cwd looking for `lakefile.toml` with `name = "CausalSmith"`.

### Direct invocation

```bash
cd <AUTOID>/CausalSmith
source ~/.nvm/nvm.sh && nvm use 20.20.2
npx --prefix tools tsx tools/bin/causalsmith.ts research <ARGS>
```

### Argument forms

Each row is a distinct **entrypoint shape**. The `research` forms enter the
theorem pipeline; `study` runs the separate substrate builder; `present` runs
the paper pipeline; `--reopen` is a pure file move; and `--discharge-gate`
re-enters theorem verification at F2.5.

| Form | Effect |
|---|---|
| `research <qid> <spec>` | Cold start a theorem run with the given question id + specialization. |
| `research --resume <qid> <spec>` | Resume after CKPT 1 / 1.5 / 2 or a `missing_architecture` block. |
| `research --propose <topic> <qid> <spec>` | Run D-1 (question proposal) first, then proceed. |
| `research --angle-action <continue\|switch\|retry\|give-up> <qid> <spec>` | Resolve a D-0.5 proposal checkpoint before another proposer starts. Add `--angle-directive <text\|->` to persist the D-orchestrator repair atomically; `retry` also accepts `--extra-revisions N`. |
| `research --propose <topic> --novelty flagship --upgrade <parent>_<spec> --upgrade-axis <axis> <qid> <spec>` | Flagship upgrade of a banked accepted/downgraded parent. `--propose <topic>` is optional here (topic auto-derived from the parent README). |
| `research --from-question <oq_id> <qid> <spec>` | Cold start from an existing OpenQuestion node. Atomically claims the OQ (`open` → `in_progress`) under the graph write lock before the pipeline begins, so it cannot be double-consumed. Mutually exclusive with `--propose` and `--upgrade`. On `--resume` the claim is a no-op. |
| `study <slug> [--resume]` | **Substrate-build mode** — builds ONE missing Causalean substrate module. The first invocation writes a blank `requirement.md` template and halts for you to fill in; re-run to proceed. Boots one shared warm `lean-lsp` for the whole run. |
| `present <qid> <spec>` | Create or resume a verified paper bundle from an accepted bank entry. |
| `research --reopen <qid> <spec>` | Pull a **banked** entry back to its working dir and clear `banked` (inverse of banking's move), so the normal toolchain operates on it again. |
| `research --discharge-gate <qid> <spec> <node_id>` | Reopen a banked entry, ungate `<node_id>`, re-verify F2.5→F5, re-bank. Use once a banked entry's gated substrate has been built. |
| `research --downgrade-tier <tier> <qid> <spec>` | Accept an achieved lower tier when D0.5 lands **below** the novelty floor (the field advance proved unreachable): lower the persisted floor to `<tier>` and re-pass D0.5, then continue per `--auto` (into F) or halt at the go/no-go. |

Useful flags:
- `--auto` — run autonomously: the orchestrator decides every checkpoint per its skill, halting only on terminal failure or CKPT 2 (bank/promote/commit). Without it the run stops at each checkpoint for a human call.
- `--novelty <incremental|subfield|field|flagship>` — D0.5 acceptance threshold for proposal mode. The vocabulary **is** the reviewer publishability-tier ladder (`flagship > field > subfield > incremental`): the target you pass is the floor tier a note must clear. Default `field`. (The pre-unification spellings `relative-to-repo` → `incremental` and `relative-to-literature` → `subfield` are still accepted and normalized, so old scripts and banked runs keep working.)
- `--proposer <codex|claude>` — override which draft runner writes the D-1 proposal. Defaults to the model configured in `models.ts`.
- `--upgrade <parent_qid>_<parent_spec>` — only with `--novelty flagship`. Starts D-1 from a banked entry; the accepted child carries a `supersedes:` link to the parent.
- `--upgrade-axis <computation|estimation|generalization|mechanism>` — required with `--upgrade`. Declares the typed delta the upgrade must deliver.
- `--clear-gate <flag>` — repeatable, **`--resume`-only**. Clears one resume-blocking cap-gate flag in `state.flags` instead of hand-editing it. A cap-gate is a deliberate halt the run must not blow through silently, so clearing it is an explicit act. Valid flags: `stage_neg1_fallback`, `general_review_halt`, `substrate_build_required`, `theorem_splits_cap_hit`, `stage0_budget_exhausted`, `stage1_rewinds_cap_hit`, `scaffold_redirect_cap_hit`. (Distinct from a *substrate*-gate — see "Discharging a gate" below; the two share the word but are unrelated mechanisms.)
- `--stop-after <stage>` — halt cleanly after the named stage completes. Valid stages (in order): `D-1.1`, `D-1.2`, `D-0.5`, `D0`, `D0.5`, `F1`, `F1.5`, `F2`, `F2.5`, `F3`, `F3.5`, `F4`, `F5`. Useful for smoke-testing one stage in isolation (e.g. `--stop-after F4` to inspect equivalence review without auto-banking; old numeric forms are accepted but deprecated). Validated at parse time; plumbed via `CAUSALSMITH_STOP_AFTER` env var.
- `--from-stage <stage>` — with `--resume` (or `--discharge-gate`, where it overrides the F2.5 default); re-enter the run AT the named stage instead of at `state.stage_completed + 1`. Same stage vocabulary as `--stop-after`. This is the clean way to re-run a stage (e.g. `--resume … --from-stage F2.5` to re-review after registering a substrate-gate) without hand-editing `state.stage_completed`. Sets `runPipeline`'s `startStage`; pair with `--stop-after` to run a single stage in isolation. No effect on a cold start.
- `--dry-run` — validate state-machine mechanics only; no Codex calls. Use for plumbing checks. NEVER `--dry-run` a live run: it fast-forwards `state.stage_completed`.

### qid conventions

| Prefix | Substrate |
|---|---|
| `panel_*` (e.g. `panel_synthetic_did_*`, `panel_event_study_*`, `panel_lp_var_*`) | Panel / linear-projection (`CausalSmith/Panel/`) |
| `eid_*` (e.g. `eid_backdoor_*`, `eid_iv_*`, `eid_shiftshare_*`, `eid_rdd_*`) | Exact identification (`CausalSmith/ExactID/`) |
| `pid_*` (e.g. `pid_manski_*`, `pid_sensitivity_*`, `pid_bunching_*`) | Partial identification (`CausalSmith/PartialID/`) |
| `stat_*` (e.g. `stat_ate_overlap_decay_*`, `stat_policy_regret_*`) | Estimation / inference theory for a causal estimand — a convergence rate, semiparametric efficiency bound, or limit law where the rate/efficiency/limit IS the kernel (`CausalSmith/Stat/`) |
| `exp_*` (e.g. `exp_aronow_samii_*`, `exp_saturation_*`, `exp_adaptive_*`) | Design-based / randomization inference (`CausalSmith/Experimentation/`) |

Full conventions: [`doc/qid-naming.md`](qid-naming.md).


The **Stat** and **Experimentation** clusters share a "method-as-kernel" framing distinct from the identification clusters: identification of the causal estimand is GIVEN, and the contribution is the estimation/inference theory. They differ in the randomness source. **Stat** is superpopulation (units sampled from a population); the kernel is a rate / efficiency bound / limit law, and a matched minimax converse is the strongest but NOT the only creditable frontier-advance — a strictly sharper upper rate, the first nontrivial bound for a method/estimand, an efficiency bound with an attaining estimator, or a nontrivial estimator for a *novel* causal estimand each also qualify. **Experimentation** is design-based (the only randomness is the treatment assignment; potential outcomes are fixed / finite-population) and the design itself is a first-class object; admissible shapes are a design-based limit law + Wald-coverage for a *given* design, an optimal / efficient *chosen* design with an optimality certificate, and adaptive / sequential inference under a *data-dependent* design (martingale CLT) — with the operative limit / optimality always DERIVED from primitive design conditions, never assumed.

### Output layout per run

Artifacts use bare, presentation-style names (the folder is already `<qid>`, so the
old `<qid>_<spec>_` prefix is dropped); the spec lives inside `state.json`. Phase
artifacts nest under `discovery/` and `formalization/`. Pre-rename runs keep their
`<qid>_<spec>_`-prefixed names and resolve transparently (back-compat).

```
CausalSmith/doc/research/active/<qid>/
  state.json                             # canonical state machine (zod-validated; carries qid + specialization)
  pipeline.jsonl                         # stage advancement log
  reviews.jsonl                          # reviewer verdicts
  review_{decision,general,math}.json    # D0.5 referee verdicts
  graph.json                             # note↔Lean formalization graph
  discovery/
    writeup.tex                          # D0 derivation
    proposal.tex                         # D-1 proposal (proposal mode only)
    gaps.json                            # D-1.1 literature scan output
    core.json / proto_core.json          # typed-D0 solved / proposal core
  formalization/
    formalization.md                     # F1 NL formalization
    plan.json                            # F1 formalization plan
CausalSmith/CausalSmith/<substrate>/<QidCamel>/   # Lean output (scaffold + proof)
CausalSmith/doc/research/MISSING_ARCHITECTURE.md   # central deferred-infra ledger (all qids)
```

The Lean output directory is computed by `canonicalLeanSubdir(qid)` in `tools/src/paths.ts`.

### Stage discipline notes

The formalization phase enforces a small set of cross-stage invariants that keep downstream stages cheap. Brief summary; canonical wording lives in the per-stage prompts under [`tools/src/formalization/prompts/`](../tools/src/formalization/prompts/).

- **Minimal-hypothesis tiering (F1).** Each T-k entry in the `.md` artifact carries two hypothesis tiers: `Load-bearing hypotheses (H1, …, Hn)` — those the .tex §11 proof step for T-k actually invokes — and a mandatory `Hypotheses dropped from T-k (drift-watch)` sub-section listing every .tex §6 Setup assumption this T-k does NOT use, with `.tex line N` cites and one-line justifications. Only the load-bearing tier is lifted into the Lean theorem signature. Catches redundant-assumption defects before they cascade to F4. (Prompt: `stage1_template.txt`.)
- **Mixed-feasibility extraction (F1).** When the .tex main theorem bundles a formalizable sub-result (e.g. a deterministic identification interval) with parts that need infrastructure that does not exist yet, F1 does NOT bounce the whole theorem as `infeasible-out-of-scope`. It returns `needs-new-infrastructure (with extraction)`: it lifts the formalizable sub-result into its own T-block (a faithful SUB-claim, never a strengthening), records the carved-out part in that T-block's drift-watch + a `deferred_conjecture` note, and lists the blocking items as `infrastructure_needed[]`. F1.5's **F** (faithfulness) check is extraction-aware — a faithful sub-claim under a recorded extraction is not a violation; only a *silently* dropped remainder, a strengthening, or a non-entailed sub-claim is. So F2 only scaffolds the extracted (formalizable) T-blocks; the deferred theorem is never scaffolded. (Prompts: `stage1_template.txt`, `stage1_5_FQPHNLX.txt`.)
- **Persistent F2 scaffold directive (orchestrator).** When the F2.5 faithfulness loop keeps escalating the SAME statement-shape drift the scaffolder re-introduces on every pass — an over-assumed premise the note DERIVES, a universal constant quantified after the model parameters, a missing mechanical domain hypothesis — and the one-shot capped `scaffold_redirect` (or a hand-edit) gets reverted by the next re-scaffold, the orchestrator injects a PERSISTENT constraint via `tools/bin/f2_directive.ts <qid> <spec> --directive "…"` (`--clear`/`--show` too). It persists on `state.flags.f2_scaffold_directive` and `runStage2` applies it verbatim as a top-priority constraint on EVERY scaffold/revise pass until cleared (uncapped, unlike `scaffold_redirect`). It is the F2 analogue of `bin/f3_directive.ts` (which hands the F3 fill loop a PROOF hint). Statement-SHAPE / faithfulness steer only — the F2.5 review + anti-laundering gates still apply. (`tools/bin/f2_directive.ts`, `src/formalization/stage2.ts`.)
- **Missing-architecture ledger.** Deferred infrastructure is mirrored to a permanent, append-only ledger at `CausalSmith/doc/research/MISSING_ARCHITECTURE.md` so a maintainer can scan it, land an item, then re-run the qid. Two writers: F1 on `needs-new-infrastructure` (writes `infrastructure_needed` + the `deferred_conjecture`), and F2 on `blocked-missing-architecture` (writes `missing_items`). Blocks are keyed by `qid:spec:source` and replaced in place on re-run, so repeated runs update rather than duplicate. (`tools/src/shared/missing_architecture_ledger.ts`.)
- **Gated vs cited substrate (D0 `status` → F1 `gate_class`).** A missing-substrate node is one of two kinds, decided at D0 and propagated by F1 (it does not re-judge). **`gated`** — a result we will DISCHARGE (a real Lean proof, possibly transcribed from a source): built before banking (background builders → discharge → rewind to F2.5), tracked in `SUBSTRATE_DEBT.md`. **`cited`** — a borrowed result we INVOKE rather than prove (D0 marks `status:"cited"`, a leaf carrying its `source`): F2 authors a `def … : Prop` that encodes the cited statement, the **F4** convergence reviewer source-MATCHES it against the citation (`cited-verified`/`cited-verified-attested`; a `cited-mismatch` or `cited-underspecified` blocks banking — see "Banking invariants" below), and on a passing match F4 records it in `CITED_DEPENDENCIES.md` — never built, never owed a build, may graduate to a real lemma later. A failing match is persisted to `state.cited_checks` and escalates; it is deliberately NOT written to the registry, which documents what a *banked* theorem assumes. In Lean the consumer remains an honest implication from the exact cited proposition. In presentation mode the cited proposition is not printed as a numbered result or ordinary hypothesis: the paper states the consumer conventionally, cites the source at the proof step, and receives a mechanically enforced theorem-local **Formalization scope** footnote saying that the source proof was not formalized and that dependent portions lose certification if the cited conclusion is false. The cited node remains visible in the web formal-dependency panel. This citation erasure applies only to source-matched `gate_class:"cited"` nodes; it never hides modeling assumptions or `gated` proof debt. The F1 plan gate (**P9**) enforces the `status:"cited"`↔`gate_class:"cited"` mapping + source resolution. (Prompts: `stage0_solve.txt`, `stage1_template.txt`, `proof_reviewer.txt`.)
- **Atomic substrate-gate registration (orchestrator).** Registering a substrate-gate by hand-editing a `.lean` theorem does NOT survive an F2 re-scaffold: the scaffolder rebuilds the statement from `plan.json`, drops the un-registered hypothesis, and the residual becomes an inline `sorry` the filler then escalates `build-substrate` on. A gate must live in the PLAN. `tools/bin/gate.ts <qid> <spec> <node_id> --consumers <id1,id2> [--class gated|cited] [--source ..] [--reason ..]` registers it atomically across all three stores in ONE idempotent operation: (1) `plan.json` — sets the node `gate:true, gate_class, lean_kind:"assumption"` and threads `<node_id>` into every consumer's `hyps` (so F2 keeps it as a hypothesis, never re-emits a `sorry`); (2) `graph.json` — sets the node `kind:"gate"` + `gate:{gate_class, source?}`, adds `proof-uses` edges, and flips consumers back to `unreviewed` so F2.5 re-checks the now-conditional statements; (3) `state.added_assumptions` + `SUBSTRATE_DEBT.md` — discloses the debt. `--class gated` (default) is our own hard fact to DISCHARGE-or-keep-as-honest-debt; `--class cited` requires `--source` for F2.5 source-matching. `--show` inspects. If `<node_id>` has no plan/graph node yet — a debt disclosed ONLY in prose (`--audit` reports "prose-only and unenforceable", the state a legacy reviewer verdict could leave behind), previously un-registerable — MINT it in the same call with `--statement "<the premise as it stands in Lean>"`, plus `--supersedes "<old prose label>"` to retire the stale disclosure so the entry does not carry two for one debt; the node is minted through the graph API and hung off the first consumer. NEVER let a model hand-edit `graph.json` (invalid enums break schema validation) — this command is the only sanctioned writer for gate registration. `bin/add_assumption.ts` cannot substitute: it only writes `state.added_assumptions`, so it now **hard-refuses** `--classification substrate-gate` and prints the `gate.ts` command instead — a disclosure with no gate behind it is the drift this pair of commands used to permit.
- **Banking invariants (enforced, not advisory).** `bankEntry` REFUSES tier `accepted` on either condition, naming each offender and printing the fix; lower tiers still park debt-carrying work. **(1) Unregistered gate** — any `state.added_assumptions` entry classified `substrate-gate` whose node lacks `gate:true` (plan) / `kind:"gate"` (graph). Disclosure alone is prose: the hypothesis is dropped by the next F2 re-scaffold and silently becomes a `sorry`. **(2) Cited mismatch** — any `state.cited_checks` entry with `cited-mismatch`/`cited-underspecified`. The F4 reviewer's verdict is now PERSISTED to `state.cited_checks`, so the documented block survives outside the review loop (it was previously in-memory only, and a `bank_entry.ts --tier accepted` or a resume re-entering at F5 banked a mismatched cited def silently). Pre-flight condition (1) any time with `tools/bin/gate.ts <qid> <spec> --audit` (exit 1 + findings, 0 when clean). "Build before banking" admits NO exemption — it applies to a gate standing in for a proof step *and* to one realizing a fact the note declares as its own `ass:`; only a non-dischargeable modeling primitive escapes, and that is not a substrate-gate at all.
- **Discharging a gate (`--discharge`/`--ungate`).** *(A `gate` here is a **substrate-gate**: a disclosed proof-debt NODE in `plan.json`/`graph.json`. It is unrelated to a **cap-gate** — the resume-blocking boolean in `state.flags` cleared by `causalsmith research --clear-gate`. The two share the word and nothing else.)* Once a `gated` node is PROVEN in Lean (or was mis-registered), reverse the registration with the SAME CLI — never by hand-clearing `graph.json`/`state.json` (a hand-clear leaves the gate marked open, so CKPT 2 falsely discloses proven work as outstanding debt). `tools/bin/gate.ts <qid> <spec> <node_id> --discharge [--lean-name <Name>]` (aliases `--ungate`, `--unset`) undoes all three stores atomically: clears `gate` from the plan + graph node (back to a plain `definition`), un-threads `<node_id>` from every consumer's `hyps`, drops the `proof-uses` edges, reopens each consumer to `unreviewed` (so F2.5/F4 re-verify it is now honestly UNCONDITIONAL — not silently still assuming it), and removes the `state.added_assumptions` + `SUBSTRATE_DEBT.md` disclosures. Consumers are **auto-detected** from the graph/plan (no need to re-supply `--consumers`), and hand-authored prose in `SUBSTRATE_DEBT.md` is preserved (only the `gate.ts`-appended bullet is removed). F5 keys its derived disclosure by the Lean type name while `gate.ts` keys its own by the node id; both clear automatically because the Lean name is **inferred** from the plan's `lean_name` (written at registration) or the graph node's `lean.decl_name` — `--lean-name <Name>` is now only a fallback for a node neither store names. Follow with `--resume --from-stage F2.5` to re-review the now-unconditional consumers. A registered `gated` node is DURABLE with no `.lean` hand-editing: the F2 scaffolder (`gatedHypsBlockFromPlan`) emits it as an explicit `_of_gate` hypothesis on every consumer on each re-scaffold, and the F2.5 delta + F4 convergence reviewers (`proof_reviewer.ts`) EXEMPT that gated hypothesis from the added-premise/drift/content-gate check — so the theorem passes review as a sorry-free CONDITIONAL on disclosed debt (tracked in `SUBSTRATE_DEBT.md`).
- **Discharging a gate on an ALREADY-BANKED entry (`--discharge-gate`).** The bullet above assumes the run is still open. When an entry was banked `accepted` with disclosed debt and its substrate is built only LATER, the same tools cannot reach it: banking `rename`-MOVES the run dir to `_bank/<tier>/<qid>_<spec>/` and sets `banked:true`, while `gate.ts` and `--resume` both resolve paths to the working `doc/research/active/<qid>/` location. Two commands close that gap. `causalsmith research --reopen <qid> <spec>` is the inverse of banking's move: it pulls the entry back to its working dir, sets `banked:false`, and stamps `reopened_from:{tier,banked_on,reopened_on}` — the crash-safety marker identifying an entry that is out of the bank but not yet re-banked. It refuses if the working dir already exists (never clobbers an in-flight run), if no banked entry is found, or if the dir is not marked `banked`. `causalsmith research --discharge-gate <qid> <spec> <node_id>` is the fused, resumable, idempotent form: reopen → `gate.ts --ungate <node_id>` → re-verify from **F2.5** (same convention as the live-run case: the ungate reopened every consumer to `unreviewed`, so the F2.5 delta/added-premise review must re-run; override with `--from-stage`, e.g. `F4`) → F5 → re-bank. Because banking is a MOVE, the banked entry retains `plan.json` / `graph.json` / `state.json` / the Lean, so it is fully re-verifiable in place. F5 does NOT auto-bank, so the wrapper owns the `bankEntry` call; the re-bank bumps a `revision` counter and appends `<node_id>` to `discharged_gates`, consuming `reopened_from`. **On a reviewer reject the entry is LEFT reopened** at the working dir — no auto-rollback, no re-bank; fix the Lean and re-invoke `--discharge-gate` (each step no-ops if already done) or `--resume --from-stage F2.5`. There is no pre-promotion existence check on the named decl: the F2.5/F4 reviewers are the sole gate.
- **Drift-watch completeness check (F1.5 D).** The F1.5 reviewer's check set is F-Q-P-H-U-N-L-X-**D**. D verifies every .tex §6 Setup assumption lands in either T-k's load-bearing list or its drift-watch list, never neither. U is tightened: a hypothesis cited only by the .tex §6 Setup (not by any §11 proof step or L-entry) is REDUNDANT and must be moved to drift-watch. Both flags route as light/mechanical-patch revises. (Prompt: `stage1_5_FQPHNLX.txt`.)
- **Statement↔note correspondence (the formalization graph).** The per-question graph (`graph.json`) is the materialized note↔Lean correspondence the proof-review loop's reviewer sources its skeleton from and writes verdicts back to (`node.review`); it replaced the old per-round flat crosswalk. Definition/assumption/theorem drift is caught by the reviewer unfolding each Lean `def`/bundle and comparing clause-by-clause to the `.md`/`.tex` — chiefly a class `def` that silently WIDENS its membership class (the safe-for-the-prover, green-but-weaker direction on a minimax converse). (`tools/src/graph/`; reviewer prompt `tools/src/formalization/prompts/proof_reviewer.txt`.)
- **Complete tex↔Lean crosswalk (F5).** At end of pipeline — F4 has passed and no stage edits Lean past here, so the lemma set is final and line numbers are accurate — F5 emits `crosswalk_full.json` + `.md`: the COMPLETE correspondence backbone for the visualization, now lemma-inclusive (definitions, assumptions, theorems, **lemmas, propositions**). Same deterministic builder as F2.5 (`buildCompleteCrosswalk` in `tools/src/formalization/crosswalk.ts`) run in `includeLemmas` mode; it re-stamps every `(file, line)` from the final files (the line re-stamp deferred at F2.5) and carries the F2.5 drift verdicts forward onto the def/assumption/theorem rows. It is DESCRIPTIVE, not a gate: F3 restructures proofs, so paper↔Lean lemmas are many-to-many — a `lean: null` row is a paper object with no Lean counterpart, a Lean-only entry is a lemma the proof introduced that the paper does not name. Faithfulness gating stays upstream (F2.5 def/theorem drift, F4 equivalence). Emitted best-effort so it never blocks API.md / the checkpoint. (`tools/src/formalization/stage5.ts`.)
- **F3.5 unused-hypothesis lint (mechanical, in-loop).** No LLM. Once every frozen theorem's uses-closure is proof-complete, the loop runs a regex/AST lint (`tools/src/formalization/unused_hypothesis_lint.ts`) over the `.lean` files. A definite **transitive** finding (a public theorem forwards a hypothesis only into a bridge where it is provably unused) blocks completion; direct/advisory findings are surfaced in the loop log but don't block, since the name-based lint can't see wildcard-tactic use (`omega`/`linarith`/`simp`). Upstream minimal-hypothesis tiering means most runs see zero blocking findings.
- **Statement-faithfulness, and its guarantee boundary.** The pipeline gates *statement*-faithfulness: Lean certifies the theorem statement is true, and the loop's reviewer keeps the `.tex`/note statement matched to the Lean one — catching laundering/weakening (an added premise that is the crux, a `def` narrowed to the proof's objects, a silently weakened theorem) so Lean↔`.tex` never agree by construction. It does NOT gate *proof*-faithfulness — a `.tex` proof step can be wrong while the statement is Lean-certified (full `.tex`-proof-vs-Lean-proof verification is a planned post-pipeline pass). The final gate is the **dual-model convergence review** (codex + claude) over the full frozen surface; reviewer output is parsed defensively (raw output logged before parse; a malformed reply escalates rather than crashes the loop).

## Bank lifecycle

After a run terminates, it lives in `doc/research/active/<qid>/`. Banked runs are moved into `doc/research/_bank/<tier>/<qid>_<spec>/`. Tiers:

| Tier | Meaning |
|---|---|
| `accepted` | F5 clean, reviewer approved. |
| `downgraded` | Run had to be downgraded from the proposed tier to a lower band. |
| `failed` | Run terminated without reaching F5; kept for diagnostics. |

### Bank tooling

```bash
# Move a run into _bank/<tier>/, patching state.json and generating a README scaffold:
npx tsx tools/bin/bank_entry.ts --qid <qid> --spec <spec> \
  --tier accepted|downgraded|failed \
  [--reason "<one-sentence verbatim verdict>"] \
  [--seeds-burned "0,3"] [--seed-burn-reason "<why>"] \
  [--dry-run]

# Compute proposal→derivation tier-drift across the bank (calibration report):
npx tsx tools/bin/bank_drift.ts            # human-readable
npx tsx tools/bin/bank_drift.ts --json     # machine-readable

# One-shot D0.5 field-reviewer for ad-hoc proposals (debugging):
npx tsx tools/bin/oneshot_stage0_5_field.ts <args>
```

`bank_entry.ts` is conservative: it refuses to re-bank an already-banked entry, refuses to overwrite an existing destination, and leaves the source untouched in `--dry-run`.

### Failed theorems become open questions

When a paper-scoped run banks a state.json whose `theorems[]` array contains
entries with `status: "failed"`, `bank_entry.ts` mints one
`OpenQuestion` node per failed theorem under
`doc/study/nodes/open_question/oq_failed_<qid>_<spec>_<theorem_local_id>.json`
and writes the resulting `oq_id` back into the corresponding `theorems[i].minted_oq_id`.
Theorems that failed at or before D0.5 (math review) are NOT minted — the
per-run failure still lives in the bank, but no OQ is produced because the
math claim itself did not clear review. The bank entry's README lists every
failed theorem in its YAML frontmatter (`failed_theorems:`) and in a body
section, distinguishing `minted` from `skipped`. Use `--no-mint-oqs` when
banking legacy or hand-authored content where OQ minting is unwanted.

## `causalsmith present` (presentation pipeline)

Turns an **accepted** bank entry into an arXiv-grade paper bundle that the website renders.

```bash
cd CausalSmith/tools
npx tsx bin/causalsmith.ts present <qid> <spec>              # cold start (P0…)
npx tsx bin/causalsmith.ts present <qid> <spec> --resume     # approve a checkpoint / continue
npx tsx bin/causalsmith.ts present <qid> <spec> --dry-run    # exercise the state machine, no models
npx tsx bin/causalsmith.ts present <qid> <spec> --stop-after P1
```

Stages: P0 builds a *verified* citation pool (retrieve-before-write; entries checked against Crossref/arXiv, unverifiable ones dropped) and a related-work brief. P1 generates the **frozen formal layer** — one `theoremv/assumptionv/lemmav/definitionv` environment per note object, obj_id-anchored, wording polished once, then hash-pinned — plus `outline.md`; halts at the **outline checkpoint**. P2 drafts body sections (opus) and Lean-faithful appendix proofs (codex + lean-lsp), writes abstract/intro last; halts at the **draft checkpoint**. P3 runs hard gates (statement equivalence vs Lean, proof faithfulness, overclaiming, citation pool + support, anchor/frozen lint) with a ≤3-round revise loop, then a soft rubric ensemble. P4 re-verifies citations, compiles the PDF, and emits the bundle: `presentation_crosswalk.json`, `lean_snippets.json`, `paper_body.html`, `assumption_table.md`, `meta.json` (all under `doc/presentation/<qid>_<spec>/`).

Invariants: every formal environment carries a bank-crosswalk obj_id (no anchor → no build); frozen bodies cannot drift after P1 (hash check at P2/P3/P4); citations outside the verified pool fail P3; the Lean side is extracted mechanically at the pinned commit. The verification badge is currently a source-level sorry scan (`axioms: null` until the axiom audit lands).

## Library explorer (Causalean demonstration)

The site's `/library` section renders every Causalean declaration as an NL-first card:
the **first paragraph of the docstring is, by convention, the natural-language
translation** of the formal statement; the formal statement (identifier-linkified) sits
beneath it, with sorry/axiom badges and a `file:line` source link. Tier-1 (definitions,
structures, classes, inductives, axioms, plus sidecar-listed headline theorems) is the
curated trust layer; lemmas/instances collapse into per-module helper lists. Design doc:
`doc/presentation/2026-06-10-library-explorer-design.md`.

Badge semantics: **reviewed** = a human stamped that the NL faithfully renders the formal
statement at its current hash; editing the decl flips it to **stale**; everything else is
**unreviewed** (machine-drafted prose, not yet certified).

Beyond the cards, the explorer ships (all live):

- **Hierarchical module tree** — each area page shows submodules as an expand-on-click
  tree (never flat leaf lists), with a per-level description: file levels use the module
  docstring's first sentence, directory levels use `namespace_intros` from the sidecar.
- **Search** — a search bar on every library page (backed by the static
  `/library/search.json`; `/library/names.json` is the machine-readable name map that
  also powers drawer cross-links), usable by humans and agents.
- **Dependency graph** — `/library/graph`: statement-level dependency edges over the
  whole library (d3 force layout; `/library/graph.json` is the data).
- **Review mode** — dev server only: a Review button on each tier-1 card POSTs to
  `/api/review` and writes the stamp into the area sidecar; production builds render
  the badges read-only.
- **Paper integration** — each paper links a *Formalization* page (its research module
  rendered library-style, from the bundle's `paper_library_index.json`, emitted by
  CausalSmith present P4), and every Lean drawer cross-links identifiers into the library.

```bash
# regenerate the index after editing Causalean (writes doc/library_index.json);
# the exe imports the compiled olean, so BUILD FIRST or you index a stale library
lake build && lake exe library_index
# integrity + per-area coverage table (--seed creates missing area sidecars).
# Also FAILS on orphaned modules: any Causalean/*.lean unreachable from the
# Causalean.lean root import graph is invisible to the explorer — wire it into
# the root (deliberately stale modules are exempted by name in the checker).
cd CausalSmith/tools && npx tsx bin/check_library_index.ts
# fill missing tier-1 NL translations via codex (dry-run without --apply);
# --module-docs-only sweeps only missing top-of-file /-! -/ headers
npx tsx bin/library_nl_sweep.ts --area <Area> [--apply] [--all] [--module-docs-only]
```

Review stamps live in `doc/library_review/<Area>.json` (`reviews[]`, `headline_theorems[]`,
`flags[]`, `intro`, `namespace_intros{}`), keyed by decl name + statement hash. The site
build fails on a sidecar entry that references a missing decl.

Maintenance rule (also in CLAUDE.md): **Causalean and this page move together** — any
change to Causalean declarations or docstrings must regenerate the index before
committing, and new files need a `/-! -/` module docstring whose first paragraph reads
for an econometrician with no Lean background.

## Tests

```bash
cd CausalSmith/tools
npx vitest run                 # full suite
npx vitest run test/state.test.ts   # one file
```

The suite covers the state machine, banking conventions, F3 classifier, and a small set of smoke tests (`*_smoke.ts`). Smoke tests do not call Codex.

## Concurrency

Multiple `/causalsmith research` runs targeting distinct `(qid, spec)` pairs can execute simultaneously. `pipeline.ts` rejects a second run for the same active `(qid, spec)` by checking for an existing `.active` heartbeat under `CausalSmith/doc/research/active/<qid>/`.

## Source-of-truth pointers

| Topic | Where |
|---|---|
| Per-declaration Lean API | [`CausalSmith/doc/API.md`](API.md) |
| qid naming conventions | [`CausalSmith/doc/qid-naming.md`](qid-naming.md) |
| State machine schema | [`CausalSmith/tools/src/state.ts`](../tools/src/state.ts) (zod) |
| Path helpers | [`CausalSmith/tools/src/paths.ts`](../tools/src/paths.ts) |
| Stage handlers + dispatcher | [`CausalSmith/tools/src/pipeline_stages.ts`](../tools/src/pipeline_stages.ts) |
| Cross-stage helpers | [`CausalSmith/tools/src/pipeline_support.ts`](../tools/src/pipeline_support.ts) |
| Proof-review loop (F2.5+F3+F3.5+F3.7+F4) | [`CausalSmith/tools/src/formalization/proof_review_loop.ts`](../tools/src/formalization/proof_review_loop.ts) (+ `proof_filler.ts`, `proof_reviewer.ts`) |
| Discovery-phase prompts (D-1, D0, D0.5) | [`CausalSmith/tools/src/discovery/prompts/`](../tools/src/discovery/prompts/) |
| Formalization-phase prompts (F1, F1.5, F2, F3, F4, F5; intervention) | [`CausalSmith/tools/src/formalization/prompts/`](../tools/src/formalization/prompts/) |
| Skeleton LaTeX templates | [`CausalSmith/tools/src/templates/`](../tools/src/templates/) |
| Slash-command entry point and lifecycle owner | `.claude/skills/causalsmith/SKILL.md` |
| Discovery sub-orchestrator | `.claude/skills/causalsmith-d/SKILL.md` |
| Formalization sub-orchestrator | `.claude/skills/causalsmith-f/SKILL.md` |
| Shared recipes (state, banking, rewinds, watcher) | `.claude/skills/causalsmith-shared/reference.md` |
| Guardrail hook (run-scoped) | `.claude/hooks/causalsmith-guardrail.sh` |

## When to update this manual

Edit this file when:
- A new CLI flag or argument form ships in `tools/bin/causalsmith.ts research` or any sibling `tools/bin/*.ts`.
- A new bank tier or banking rule is introduced.
- A new live pipeline becomes invocable.
- The repository layout changes at the directory level (file-level changes belong in `doc/API.md`).
- Prerequisites (Node / Lean / Codex versions) change.

Keep prose terse and link out rather than duplicating content from `API.md` or the skill docs.
