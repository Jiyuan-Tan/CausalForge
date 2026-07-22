# CausalSmith research orchestrator — shared reference

Recipes and lookup tables shared by the three orchestrator skills — `causalsmith` (top loop /
dispatch / terminal authority), `causalsmith-d` (discovery sub-orchestrator), and `causalsmith-f`
(formalization sub-orchestrator). Each skill links here rather than duplicating these blocks; read the
section its pointer names.

> **"SKILL.md §…" cross-references below** predate the three-skill split. Map them: the loop /
> watcher / dispatch / bank / terminal material → **`causalsmith`**; per-stage D-1/D0/D0.5 →
> **`causalsmith-d`**; F1–F5, the proof-review loop, faithfulness enforcement, and substrate building →
> **`causalsmith-f`**. "Cross-cutting actions (protected paths / substrate)" split between `causalsmith-f`
> (substrate build) and `causalsmith` (protected-path lifecycle).

The TS pipeline at [`CausalSmith/tools/`](../../../CausalSmith/tools/) owns every stage. The
**self-improving loop** — the orchestration core (run → watch → diagnose hopeless-vs-fixable → route
the fix → resume), with its per-stage bindings — lives across the three skills. This file is the
*reference store* they point to: how to recognize terminal states from `state.json`, the detailed
intervention procedure, the proof-review-loop watch, the bank tool, and the guardrail hook.
Stage-internal logic (Codex/Claude prompts, F-Q-P-H-N-L-X, the loop's filler/reviewer internals,
rewinds) lives inside TS — the orchestrators do not need to know it.

**Ratchet examples already baked into prompts** (the ratchet principle itself is in SKILL's loop): a minimax lower bound must use the witness `∃` + finite-risk premise, never a real `⨆`/`∫` over all estimators; a localPatch may audit an internal helper against the `.tex` and self-correct a sign rather than escalate.

## Invariant operational specifics

These back the always-on rules stated inline in [`SKILL.md`](SKILL.md) (§ "The loop" for watch/triage/stop; § "Cross-cutting actions" for protected paths and substrate building). Detail they abbreviate:

- **Protected paths (read-only during a run):** the exact globs are `CausalSmith/Panel/<QName>/` and `CausalSmith/doc/research/active/<qid>/*.{tex,md,lean}`; exempt are `state.json`, `PIPELINE_NOTES.md`, `doc/API.md`. The hook (see § "Guardrail hook") enforces this; the back-compat trigger is any `*_state.json` with `stage_completed != "5"` (the bare-number on-disk value for F5).
- **Triage:** `tail -n 40` the most recent `<qid>_<spec>_intervention_raw_<timestamp>.txt` (glob `<qid>_<spec>_intervention_raw_*.txt`; or `/tmp/<qid>_<spec>-*.out`).
- **Stopping a run (MAIN's terminal authority — a lease-holding sub never SIGINTs; it acts at a halt where the process has already exited):** on Linux, or when the only active child is a `claude` agent, SIGINT the pipeline node, verify the tree is down (no orphaned `codex exec`), then relaunch. On Windows the force-kill caution (CLAUDE.md) applies — TaskStop kills only the wrapper, so manually kill the `Local\OpenAI\Codex\bin` CLI codex tree + any `*sandbox-setup*` (orphaned `codex-windows-sandbox-setup.exe` breaks the next run), sparing the user's desktop `WindowsApps\…\Codex.exe`, `.vscode` Codex, and your own harness.

## Substrate building — operational detail

The triage rule (cheapest route that unblocks; small-scale/in-place codex build is DEFAULT; `--study` only for reusable+substantial substrate; gate the MINIMAL irreducible core, derive the surrounding content) lives in `causalsmith-f` § "Substrate building". `--study` PASS ends in the `coordinate` phase: a codex coordinator merges the substrate into its correct topical Causalean home, dedups, records it docstring-canonically, under a verify-or-rollback gate (`lake build` → `library_index` → `embed` → `lint:embeddings` → `doc:gen` → `doc:check`). The build-technique detail below is what ANY builder follows (in-place codex build, a builder subagent, the `--study` scaffolder/fillers, or an inline crux patch you do yourself):

- **Build strategy — a de-laundering is a dependency GRAPH, not one lemma.** Decompose it; dispatch the smallest independently-verifiable units FIRST, `lean_verify` each in isolation, and assemble the big coupled proof LAST with every leaf already green (throwing the giant assembly at codex with leaves still open just produces honest stops). On each honest codex stop, CLASSIFY the gap (missing leaf helper → build it as its own unit; wrong instance/typeclass route → search the right one; your own over-constraint → relax it) rather than re-dispatching the same prompt.
- **The over-generalization trap.** When codex stops at a *fundamental* Mathlib gap, before accepting it, check whether the SPECIFIC construction's structure sidesteps the general theorem. Example: the generic KL data-processing inequality needs conditional Jensen (Mathlib-absent), but laws that RECORD their base coordinate make the bind→marginal step a KL-preserving measurable *embedding*, needing none of it. Inspect the actual definitions before believing "impossible".
- **Gate side-conditions are discovered by building.** Sanity-check a substrate-gate is true AS STATED before assuming it: `PinskerBound` is false without `μ≪ν ∧ klDiv≠⊤` — assuming a bare `∀ μ ν` form would have banked a FALSE lemma. Attempting the build is what surfaces the side-conditions. Gates are tracked DEBT (`SUBSTRATE_DEBT.md`), often dischargeable from in-repo pieces later (`PinskerBound` was eventually proven unconditionally by `pinskerBound_of_ac_of_ne_top`, reusing the existing Scheffé `≤` + a weighted Cauchy–Schwarz).
- **CKPT 1 "verify the gap is real" example.** F1 surveys the toolbox by NAME and over-defers: it once estimated a "large ≥3-file crux" localized-maximal-inequality that `localized_uniform_deviation_sharp` already provided — the genuine residual was a small finite-class Rademacher envelope. Always `lean_local_search`/read before trusting the defer estimate.
- **Search the substrate at the RIGHT PATH before declaring it missing — the #1 false-"missing" cause.** Causalean (the foundational dependency) is a SIBLING of the CausalSmith package, NOT under it: its source root is the absolute `<AUTOID>/Causalean/` (with `Stat/`, `SCM/`, `PO/`, `Estimation/`, `Mathlib/`, …); the CausalSmith package is `<AUTOID>/CausalSmith/CausalSmith/`. An `import Causalean.X.Y` resolves to `<AUTOID>/Causalean/X/Y.lean` — e.g. `localized_uniform_deviation_sharp` is `Causalean/Stat/Concentration/UniformDeviationLocalized.lean`. When grepping for a substrate lemma, use the ABSOLUTE Causalean path or grep from the repo root `<AUTOID>/`; a `grep … Causalean/` run after `cd`-ing into a `CausalSmith/CausalSmith/Stat/…` subdir points at a NONEXISTENT `…/CausalSmith/…/Causalean/` and returns empty — do NOT read that as "substrate missing". Prefer the lean-lsp MCP (`lean_local_search`/`lean_leansearch`/`lean_declaration_file`) or read the importing file's `import Causalean.*` lines to locate it. Confirm a module's absence with `find <AUTOID>/Causalean -name '<File>.lean'`, never with a relative grep.
- **Worked precedents** (the pattern most "missing architecture" follows — buildable in one or a few focused dispatches): IntegralBind, BernoulliKL, KL-tensorisation, base-recording-bind-chain-rule.
- Codex invocation specifics (full-auto flags, lean-lsp MCP injection, pre-warming): CLAUDE.md "Codex" bullets.

## state.json — fields the meta-orchestrator reads

Schema source of truth: [`tools/src/state.ts`](../../../CausalSmith/tools/src/state.ts) (zod-validated).

| Field | Meaning |
|-------|---------|
| `stage_completed` | Last completed stage. **On-disk it is a bare number** (the internal `Stage`), NOT a D-/F- label. Order: `"-1.1","-1.2","-0.5","0","0.5","1","1.5","2","2.5","3","3.5","3.7","4","5"`. Cold-start sentinel is `"-1.2"`. The D-/F- forms are display-only (`STAGE_TO_HALT_ID`/`formatStageLabel` in `constants.ts`); match against the bare number — **F5 ≡ `"5"`, F3.7 ≡ `"3.7"`, F3 ≡ `"3"`, F1 ≡ `"1"`, D-1 ≡ `"-1.2"`, D0 ≡ `"0"`, D0.5 ≡ `"0.5"`**. |
| `next_action` | `"pending_checkpoint"` after a clean F5 (CKPT 2 awaiting the user), `"user_chose:<command>"` once acted on, else `null`. There is **no `ckpt_pending`** — `state.ts` deletes it on load and nothing writes it; never key on it. The checkpoint signal is the LAST line of the run's `pipeline.jsonl`: `"status":"checkpoint"` with a message starting `CHECKPOINT <N> reached`. |
| `flags.missing_architecture` | TS sets `true` when the scaffolder reported `blocked-missing-architecture`. `flags.missing_architecture_items` carries the verbatim items. Resume gate blocks until each item exists. |
| `flags.stage_neg1_fallback` | D-1 proposal budget spent without an acceptable proposal. Resume refuses with `STAGE_NEG1_FALLBACK BLOCKED: …`. Terminal-bank trigger: run `bank_entry.ts --tier downgraded|failed`, or (after an out-of-band proposal revision) `--resume --clear-gate stage_neg1_fallback`. |
| `flags.general_review_halt` | General-reviewer halt with its reason string. Resume refuses with a message; clear via `--resume --clear-gate general_review_halt` only after addressing the cause. |
| `flags.theorem_splits_cap_hit`, `flags.stage1_rewinds_cap_hit`, `flags.scaffold_redirect_cap_hit`, `flags.stage0_budget_exhausted` | Written when the named rewind/split/redirect cap or budget is exceeded (reason string in the value). Resume refuses with a message; clear via `--resume --clear-gate <flag>` only after addressing the cause (clearing `scaffold_redirect_cap_hit` / `stage1_rewinds_cap_hit` also resets the paired counter). **All cap gates are cleared through `--clear-gate`, NEVER a hand-edit of `state.flags` — the registry + clear semantics live in `tools/src/cap_gates.ts`.** |
| `flags.f2_scaffold_directive` | **Orchestrator-injectable, PERSISTENT F2 scaffold-faithfulness directive** — set/clear via `bin/f2_directive.ts <qid> <spec> (--directive "…" \| --directive - \| --clear \| --show)`. `runStage2` reads it on EVERY scaffold/revise pass and injects it verbatim as a top-priority constraint on top of the .md spec; it PERSISTS across resumes until you `--clear` it (unlike the one-shot, capped, self-clearing, review-loop-driven `scaffold_redirect`). Use for a recurring SCAFFOLD-side statement-shape drift the F2.5 loop cannot converge (an over-assumed premise the note DERIVES; a universal constant quantified after the model params; a missing mechanical domain hypothesis) — after injecting, rewind to F1.5 to re-run F2. Statement-SHAPE / faithfulness steer ONLY; the F2.5 review + anti-laundering gates still apply. The F3 analogue is `flags.f3_filler_directive` (via `bin/f3_directive.ts`), which is a PROOF hint for the fill loop, not a statement steer. |
| `banked` | `true` once the run has been retired into `_bank/<tier>/`. Inert: ignored by the hook and the per-qid run-ownership invariant. Also carries `banked_tier`, `banked_on`, `banked_reason`. |
| `proposed_from` | Present only for `--propose` runs. Carries `topic`, `final_verdict`, `iterations[]` (per-round history), `seed_list`. D-0.5 NO-PASS with exhausted revise rounds shows up as `stage_completed: "-1.2"` (D-1) with `proposed_from.final_verdict == "NO-PASS"`. (There is no `iteration` scalar.) |
| `design_decisions`, `added_assumptions`, `pending_sorries` | Carried for the user's reference at checkpoints. Orchestrator relays and normally does not mutate — EXCEPT after a manual de-launder (SKILL § F2–F4 de-launder note), where you disclose each added assumption so F4 scrutinizes it. **Disclose via `bin/add_assumption.ts <qid> <spec> --label "…" --statement "…" [--classification faithful-refinement\|regularity-bookkeeping] [--decision "<key>=<note>"]` — NEVER a hand-edit** (it loads + appends a schema-valid entry + saves, so it can't corrupt the array or fail the next resume; re-using a `label` replaces that entry). `--show` lists the current set. It HARD-REFUSES `--classification substrate-gate` — a gate needs plan+graph registration, so use `bin/gate.ts` (the only sanctioned writer); `bankEntry` refuses tier `accepted` on an unregistered one. |
| `cited_checks` | The F4 reviewer's CITED source-match verdicts (`{name, check_status, cite_id?}`). `cited-mismatch` / `cited-underspecified` make `bankEntry` refuse tier `accepted` — the durable form of the block, which previously lived only in the review loop's memory. Orchestrator does not mutate. |
| **Orchestrator CLIs (never hand-edit `state.json`)** | Every orchestrator-owned state mutation has a CLI so the state stays schema-valid + the action is auditable: cap-gate clears → `--resume --clear-gate <flag>`; stage re-entry → `--resume --from-stage <stage>`; substrate-gate registration → `bin/gate.ts` (discharge/de-register a proven gate → `bin/gate.ts … --discharge`); F2/F3 persistent directives → `bin/f2_directive.ts` / `bin/f3_directive.ts`; a D0 solve directive → `bin/d0_directive.ts`; a D-1.2 proposal directive → `bin/dneg1_directive.ts` (same shape, appends `{version,directive}` to `discovery/dneg1_escalation_log.jsonl`, cumulative — no `--clear`); an added-assumption disclosure → `bin/add_assumption.ts`; D0 proposed-change apply → `bin/d0_apply_change.ts`; bank → `bin/bank_entry.ts`; decision log → `bin/decision_log.ts`. If you find yourself about to open `state.json` in an editor, stop — there is a CLI. |

After TS exits, read state.json AND the **last line of the run's `pipeline.jsonl`** (that line, not stdout, is the checkpoint signal), and map:

> **Auto mode (`state.auto_mode` true).** Routine "Wait for user / Offer / Ask the user" actions collapse to "decide per the rule, then `--resume`". The complete hard-stop list is owned by SKILL § "Auto mode"; do not maintain a competing list here. The checkpoint line carries an `⚙ AUTO MODE` banner.

| Observed | Meaning | Orchestrator action |
|----------|---------|---------------------|
| `stage_completed: "5"` (F5) + last pipeline.jsonl line `"status":"checkpoint"` (`CHECKPOINT 2 reached…`) or `next_action: "pending_checkpoint"` | **CKPT 2** — pipeline complete | Print Lean file list, API.md diff path, `added_assumptions`. Ask the user: commit? promote to Causalean? bank as `accepted`? |
| `stage_completed: "5"` (F5), no pending-checkpoint signal (`next_action` null or `user_chose:…`) | CKPT 2 already acted on | Print "Pipeline complete; nothing to resume." Exit. |
| `stage_completed: "1.5"` (F1.5) + last pipeline.jsonl line `"status":"checkpoint"` (`CONSOLIDATED CKPT 1 …`, with `next_step_guidance`) | **CKPT 1** — F1 plan + F1.5 reuse review settled; ready for the DEPTH+REUSE+fidelity audit | Audit per SKILL §"CONSOLIDATED CKPT 1"; print plan path + `design_decisions` + generalization flags. Wait for user (approve / revise / abort). |
| `stage_completed: "1"` (F1) + `"status":"checkpoint"` (`SUBSTRATE-BUILD CHECKPOINT …` or no-usable-plan) | F1 self-halt (NOT the plan audit) | Substrate-build → for EACH gated Defer-item, triage to the cheapest route that unblocks (small-scale workaround / in-place codex build by DEFAULT; `--study <slug>` only for genuinely reusable+substantial substrate — SKILL §"Cross-cutting actions") + `--resume --from-stage F1.5 --clear-gate substrate_build_required` to proceed gated (SKILL §"Cross-cutting actions"); at the next checkpoint discharge each landed build (codex wires the lemma into the Lean) and rewind to **F2.5** to re-review — not F1 (plan/scaffold unchanged); must re-pass F4 before banking. No-usable-plan/blocked → inspect the artifact. |
| `stage_completed: "3"` (F3) + last pipeline.jsonl line `"status":"checkpoint"` (`CHECKPOINT 1.5 reached…`) | **CKPT 1.5** — proof-fill complete (possibly with remaining sorries) | Print closed/total sorry count + `pending_sorries` summary. Offer: (a) fill manually + resume, (b) accept current state + resume into F4, (c) abort. |
| `flags.missing_architecture: true` | Resume blocked | Print `flags.missing_architecture_items` verbatim. Build each gate via the SKILL § "Cross-cutting actions" triage (cheapest route that unblocks) + clear the block + resume gated; discharge landed builds at the next checkpoint; escalate only if genuinely intractable. |
| `flags.stage_neg1_fallback` set | D-1 proposal budget spent — terminal for this run | Bank via `bank_entry.ts --tier downgraded\|failed`, or clear the flag deliberately to retry the proposal. |
| `flags.general_review_halt` set | General reviewer halted the run | Read the reason string; resume refuses with a message. Address the cause, then clear the flag deliberately. |
| One of `flags.theorem_splits_cap_hit` / `stage1_rewinds_cap_hit` / `scaffold_redirect_cap_hit` / `stage0_budget_exhausted` set | Rewind/split/redirect cap or budget exhausted | Resume refuses with a message. Address the cause (usually a structural defect the caps were protecting against), then clear the flag deliberately. |
| `stage_completed: "-1.2"` (D-1), no advance, `proposed_from.final_verdict == "NO-PASS"` | D-0.5 NO-PASS after exhausting revise rounds | Bank as `failed` (see decision tree). |
| `stage_completed: "0.5"` (D0.5) + a terminal REJECT in `*_reviews.jsonl` (`stage_0.5_to_0`), or exhausted-revise NO-PASS | D0.5 terminal reject | Bank `failed` (correctness/structure defect) or `downgraded` (math sound, novelty over-framed) — see decision tree. NOT a row for a mid-stage `revise`/finding (that's iteration). |
| `banked: true` | Already banked | Print `banked_tier` + `banked_reason`. Do not re-enter. |
| TS exits with stderr error, state.json unchanged | Crash / invocation error | Print stderr tail. Do not auto-retry. |

## Proof-review loop watch — when to intervene

This is the loop-specific instance of SKILL's intervention threshold ("intervene only when the pipeline structurally cannot self-resolve"). The loop self-heals across iterations (filler proves sorries → reviewer judges the dirty frontier → re-refresh → repeat) and only **checkpoints** on a genuine wall — `PROOF-REVIEW LOOP ESCALATION [<route>]: <reason>`. Default: let it run; intervene per `<route>` (hint / build-substrate / fix-source / bank-partial / abandon) or when a checkpoint's diagnosis is wrong.

**Intervene when a faithful fix is one the loop's lanes structurally cannot make** — e.g. a decl loops with no goal-state movement because its honest fix needs a frozen-`theorem`-meaning change or a core-`def` strengthen (a statement edit the filler refuses as substrate-level), or the reviewer keeps flagging drift the filler can't resolve without changing the spec. A `route=user`/`fix-source` checkpoint whose OWN diagnosis points at an INTERNAL helper needing only a T-block-PRESERVING fix (a sign correction on a stated equality, a bookkeeping `Integrable`/positivity premise threadable from an existing `_h_int_*` ledger) is yours to audit and fix per SKILL's self-resolve-vs-escalate principle — don't defer just because the `.md` doesn't pin it.

**Watch the codex FILLER's localized statement/`def` edits closely** — the laundering-modes list + the audit-`added_assumptions`-don't-self-cert rule are in `causalsmith-f` § "Faithfulness". Loop-specific addition: the dual-model convergence review is a backstop, not a substitute for your read — when a localized edit touched a load-bearing statement, read the convergence verdict before banking.

(Routing the fix — general class → prompt, tricky instance → hand patch — the patching contract and the mid-run-edit caveat are in SKILL's self-improving loop; this section is the loop-specific *how*.)

**How to intervene (respects SKILL's protected-path rule — read-only while a run is active):**
1. **You act at a HALT — the process has already exited at its checkpoint, so this IS the "run stopped" window** where protected-path edits are permitted (you never SIGINT a live run — that is main's terminal authority). If a `.run.active` heartbeat is somehow still present from a crashed prior run, reap the stale tree first (§ "Stale / lingering processes").
2. **Patch faithfully** (SKILL's patching contract — strengthen-to-spec only, never weaken/invent/gerrymander). First confirm the `.tex`/`.md` actually defines or uses the thing (the Bucket-5(c) "spec-uses-it" test), then restore/encode only what the spec specifies.
   - **Internal-helper correctness audit** (the `route=user`-on-helper case above): DERIVE the correct statement from the `.tex` definitions + first principles — condition the relevant pseudo-outcome / score on `X`, expand the estimand — and CORRECT the helper in place (e.g. a flipped sign `(a − b)` → `(b − a)`). Then **CASCADE** the correction through every dependent SIGNED helper that propagated the same error (the build will flag each consumer whose hardcoded proof/conclusion mismatches), stopping at the first `|·|` / sign-insensitive consumer, which absorbs it. T-block-preserving iff no theorem assumption changes (consumed via `|·|`, or premises from an existing ledger). Document the derivation in a comment. **`lake -d CausalSmith build <module>` the whole chain green** (sorries OK) before resuming — a hand sign-flip is itself error-prone, so the build is the proof you got it right.
3. **Leave it compiling** (sorries OK) with `BLOCKER` hints pointing the filler at the now-available tool, then **resume**. The pipeline fills the now-honest proofs.

## Over-decomposition watch (F3 helper hygiene)

Separately from routing, watch helper growth across rounds — but judge by QUALITY, not count. Rising sorry/helper count is NOT itself over-decomposition: splitting a hard goal into isolated, provable sub-goals is GOOD and temporarily raises the count (check for gap-isolation first). Flag over-decomposition only when a NEW helper is (a) REDUNDANT — duplicates an existing module/Causalean lemma; (b) TRIVIAL — a one-liner that should be inlined; or (c) ORPHANED — proved/sorried but referenced by nothing (confirm with Grep). Action: note it for a prune at a clean boundary (loop checkpoint or run end) — bloated files slow type-check and burn tokens. (File LENGTH is a separate, manual concern — split an oversized file with `bin/split_lean_file.ts`; this watch is about helper QUALITY/redundancy.) Do NOT disrupt a run mid-decomposition. The loop's filler prunes dead helpers WITHIN the run's module; it does not self-prune across modules; this is a meta-orchestrator responsibility.

### Dead `CausalSmith/Mathlib/` stub cleanup (cross-module — meta-orchestrator duty)

The per-job deletion can NOT reach `CausalSmith/Mathlib/` stubs: F3 scans only `state.lean_subdir`, and the proof-fill agent's edit boundary is the run's module. So an abandoned decomposition can leave `by sorry` stubs in `CausalSmith/CausalSmith/Mathlib/` that no live proof path references (e.g. a Bochner `integral_bind_*` stub bypassed once a proof reroutes through `lintegral_bind`). These never block F5 (out of scan scope) but are sorry'd dead code.

Run this cleanup ONLY during an intervention or after ALL F3 jobs finish (never mid-decomposition — a stub may be re-referenced as the proof shape settles):
- For each `by sorry` stub in a `CausalSmith/Mathlib/` file the run touched, `grep` for its name across the **whole CausalSmith package** (all research modules + every banked theorem — the stubs are SHARED). Delete it ONLY if referenced by NO declaration anywhere.
- GUARDS: only delete a `by sorry` stub. Never delete a PROVED Mathlib lemma even if currently unreferenced (it may be promotable to `Causalean/Mathlib/` or used by a future run — leave to human promotion review). Never delete one with any package-wide reference.

## Watching a live run — watcher recipes (principle: SKILL § "The loop", step 1)

**The current resume-lease holder arms the watcher** — and because main GRANTS the lease to the D/F sub in
the SAME turn as the launch / cross-boundary resume, that sub is the watcher-armer for the WHOLE of its
phase, **including the cold-start→first-halt window** (main does not watch it). The sub resumes its own
rounds, so it must watch its own run. Main arms a watcher itself only when it directly holds the process
with no sub dispatched (a `--study` side-run, or orphan recovery before the fresh sub is up). Exactly one
watcher per qid at a time — whoever last resumed that qid. Different qids have independent watchers and
may run concurrently. On a lease hand-off, the returner stops
watching and the new holder arms it. Set up ONE of the two watchers below in the same turn as the
launch/resume so a *meaningful pipeline event* wakes you instantly (the `run_in_background` completion
notification only fires on process EXIT — no signal during a long F3/F4/F5, and even the exit signal can
LAG under codex contention with a concurrent run, so the watcher is your PRIMARY event signal):

**⚠ NESTED-SUBAGENT CAVEAT (a dispatched D/F/topics sub — NOT top-level main).** A sub that starts a `run_in_background` task and then ENDS ITS TURN is NOT re-woken: the completion notification misroutes to the PARENT (main), stalling the sub idle (observed live 2026-07-10). A sub must STAY IN ITS TURN and self-drive with FOREGROUND, BLOCKING calls — launch the long node process so it OUTLIVES both harness time-caps, then FOREGROUND-poll-watch it (`pgrep` + `wc -l` on `pipeline.jsonl` / `reviews/reviews.jsonl`), re-issuing the poll if it hits the time-cap — never yield-and-wait-for-the-notification. **⚠ The node `--resume` must be launched DETACHED via `setsid`, NOT a plain `run_in_background` and NOT foreground:** a foreground `--resume` dies at the ~10-min Bash cap, and a plain `run_in_background` node process is KILLED by the harness at a **~60-minute cap** (observed live 2026-07-10 — long F2.5/F3 fills died at exactly 60 min, twice). Detached survives both (verified 63 min past the cap): `setsid bash -c 'source ~/.nvm/nvm.sh && nvm use 20.20.2 && npx --prefix tools tsx tools/bin/causalsmith.ts research --resume --from-stage <stage> --auto <qid> <spec> > <logfile> 2>&1' < /dev/null & disown`. **NEVER pipe the node command through `| grep …`** — the pipeline's exit code becomes grep's (1 on no-match), masking a real success as a failure and risking a SIGPIPE kill; redirect to `<logfile>` and inspect it. State ratchets forward across stages, so on ANY death (either cap, or cluster contention) just re-resume detached from the current stage. Dispatch any codex consult FOREGROUND for the same reason. (Top-level MAIN is exempt — it receives its own background-task notifications; the two recipes below are for main or an in-turn watcher. A sub must NOT arm a background `Monitor`/`until`-loop and then stop.)

**Host-specific architectural rule.** Under Claude, ONLY MAIN dispatches Claude subagents: completion
does not route back to a nested Claude orchestrator, so a sub drives detached OS processes and returns
`{escalation:"dispatch-request", spec:…}` when it genuinely needs a Claude worker. Under Codex, the
managed collaboration API is different: a Codex main or Codex sub-orchestrator may `spawn_agent` a
bounded Codex child and drive it with `wait_agent`/messages when model and reasoning effort are
unspecified. The current managed API does not expose per-child selection, so use `codex exec` whenever
the task or skill specifies a model or effort. Assign disjoint edit scopes whichever route is selected,
and respect the managed concurrency limit. A detached OS process is still the route for the long
TypeScript pipeline node itself, which is not a Codex worker. Under Claude, a sub dispatches codex DETACHED via `setsid`, redirects
to a logfile, and foreground-polls all node/build processes together; it must never
`run_in_background`+end-turn.

**⚠ A DENIED / CANCELLED codex call is an ESCALATION, never a silent pivot.** The harness auto-mode
classifier can refuse a `codex exec` dispatch outright (`Create Unsafe Agents` / `Auto-Mode Bypass`, a
permission denial, or a user-cancelled tool call). That does NOT tell you codex is unusable — it tells you
the RUN needs the user to grant permission, and it is the ONLY thing standing between you and the proof.
**Do NOT route around it**: do not fall back to hand-proving the goal yourself, do not weaken/downgrade the
target, do not `sorry`/gate the node to skip it, and do not silently re-attempt with a different flag set.
Every one of those silently trades away proof quality on a wall that a single user keystroke removes.
Instead, STOP and hand the lease back at once with
`{escalation:"codex-blocked", receipts:[<verbatim denial text>, <the exact codex command you tried>, <what it was for>]}`.
**Main escalates to the USER — a hard stop even in `--auto`** (permission is user-owned, like CKPT 2). Once
the user grants it, re-issue the SAME codex dispatch unchanged and continue. Retrying the identical command
without a permission change just re-trips the classifier — one denial is enough to escalate.

- **Rich, per-event (preferred for active monitoring / dead-end intervention) — the `Monitor` tool.** Watch **both** files — `reviews/reviews.jsonl` (per-round `revise`/`reject`/`accept` verdicts) AND `pipeline.jsonl` (stage status) — never just one: a within-stage review verdict is written ONLY to `reviews.jsonl` and produces NO `pipeline.jsonl` line (that log gets a line only on stage *completion*), so a pipeline-only watcher silently misses every review-iteration event — the most common per-event obligation you must act on. **`pipeline.jsonl` is at the run-dir root `doc/research/active/<qid>/`; `reviews.jsonl` — with the per-referee verdicts `review_math.json` / `review_rubric.json` / `review_general.json` — lives in the `reviews/` subfolder, which does NOT exist until the first review lands (30+ min into a cold start).**

  **⚠ Use a POLL-based line-count watcher, NOT `tail -F | grep` — the latter has bitten repeatedly and silently MISSES verdicts two ways:** (1) at cold start `reviews/reviews.jsonl` (and its `reviews/` dir) does not exist when you arm the watcher, so `tail -F`'s follow-by-name may never attach; (2) worse, these files are SPARSE — a lone verdict (e.g. the first D-1 `reject`) followed by silence leaves the line stuck in `tail`'s block buffer, so the piped `grep` never receives it until the file writes AGAIN or `tail` exits (the classic "tail | grep goes quiet after one match" trap — the buffered line flushes only when you STOP the monitor, far too late to act on). Poll the line counts instead — it re-reads appended lines directly, with no output buffering and no attach race:

      DIR=doc/research/active/<qid>; pl=0; rv=0
      [ -f "$DIR/pipeline.jsonl" ] && pl=$(wc -l <"$DIR/pipeline.jsonl")
      [ -f "$DIR/reviews/reviews.jsonl" ] && rv=$(wc -l <"$DIR/reviews/reviews.jsonl")
      while true; do sleep 15
        for e in "pl:$DIR/pipeline.jsonl" "rv:$DIR/reviews/reviews.jsonl"; do
          v=${e%%:*}; f=${e#*:}; [ -f "$f" ] || continue
          n=$(wc -l <"$f"); old=$(eval echo \$$v)
          [ "$n" -gt "$old" ] && { sed -n "$((old+1)),\$p" "$f"; eval $v=$n; }
        done
      done

  Initialize the counts to current size so you get only NEW events. The review/pipeline lines are sparse and each is important, so emit them ALL (no `grep` filter — a filter that misses an unanticipated verdict shape is yet another silent-blind failure). Detect exit with `pgrep -f "causalsmith.ts research.*<qid>"` (match on `causalsmith.ts research` so the watch loop's own command, which contains the qid, does not self-match). `persistent: true`. Pair with a second `Monitor` polling process liveness + newest-file mtime to catch a silent hang (process alive, no writes, no live `codex exec`), which neither the verdict watcher nor the exit notification surfaces.
- **Lightweight, terminal-event only — a background `until`-loop.** When you only need to be woken on bank / checkpoint / exit (e.g. you are also doing other work), launch a `run_in_background` Bash watcher that polls `state.json` and exits the instant the event appears (its exit fires the task-notification):

      DIR=doc/research/active/<qid>
      STATE=$DIR/state.json
      PLOG=$DIR/pipeline.jsonl
      until ! pgrep -f "causalsmith.ts research.*<qid>" >/dev/null \
         || python3 -c "
      import json,sys
      d=json.load(open('$STATE'))
      try: last=json.loads(open('$PLOG').read().strip().splitlines()[-1])
      except Exception: last={}
      sys.exit(0 if (d.get('banked') or d.get('next_action')=='pending_checkpoint' or last.get('status')=='checkpoint') else 1)"; do
        sleep 15
      done
      # then echo the trigger (process-exit vs ckpt/bank) + stage_completed/next_action/banked + the last pipeline.jsonl line

Either way: launch the watcher in the SAME turn as the run, then yield. Re-poll by hand only if a watcher is somehow not running.

## Liveness — "working" vs "stuck"

Flat file mtimes during F3 are NORMAL, not a stall: workers run many MCP/lake elaboration cycles (minutes each on big files) before writing. Before concluding "stuck", confirm motion via BOTH live `lean`/`lake`/`codex` processes at non-trivial CPU AND recent appends to `reviews.jsonl` (round classifies) or `state.json`/`.lean` writes. Genuinely stuck = no live workers AND nothing changed for well beyond one elaboration cycle. A widening gap between writes is the long-file tax (any oversized file — `Helpers.lean` or a ballooning T-block) — a file-split signal, not a hang. Splitting is now a manual step: at a clean boundary, run `bin/split_lean_file.ts` to break an oversized file into `_Part<n>` siblings + a thin re-export aggregator (verify the build after).

## Stale / lingering processes — symptoms + reap procedure (principle: SKILL § "The loop", step 3 — reap)

A finished run does NOT always exit cleanly: after the orchestrator logs its terminal message (CKPT message / "finished at stage N"), the node process can LINGER for a long time, held open by orphaned `lean --worker` / `lake` / `lean --server` children that were never reaped. Symptoms (all seen together): the latest `pipeline.jsonl` line is a terminal/checkpoint message, `state.json` has not been written for well beyond one elaboration cycle, no live `codex exec` under THIS qid's process tree, the `lean` children sit at low/idle CPU — yet `pgrep -f "causalsmith.ts research.*<qid>"` still matches. In that state the background-task completion notification has NOT fired (the process tree is technically alive); a watcher keyed on the pipeline.jsonl tail (`"status":"checkpoint"`) DOES catch the checkpoint, but a state.json-only (`banked`) watcher will not. So treat **"stage_completed advanced AND no state write for >> one elaboration cycle AND no live `codex exec`"** as a terminal trigger in its own right — verify the lingering tree is idle, then REAP only THIS qid's tree (`TaskStop` the run's background task; if children survive, kill the `lean`/`lake` tree under that qid — never another qid's node/codex/lean workers, your own lean-lsp MCP server, or a separate codex) before reading the terminal state and resuming. Reaping also keeps you under the cluster caps (process count < 500, open files < 2048 — CLAUDE.md): stale `lean` workers accumulate across runs and exhaust file handles, which silently breaks the next run's elaboration. Distinguish from a genuinely-active run: there, that qid's `codex exec` is live and `reviews.jsonl`/`state.json`/`.lean` are still being written — do NOT reap that (and never force-kill mid-`codex`, which orphans its children). Different qids are not stale siblings and never block one another.

## Rewind discipline — verification procedure (principle: SKILL § "Per-stage event → action", F2–F4 fix-source)

To check whether a rewind was necessary: read the rewind verdict (`stage_4*`/`stage_2*` entries in `reviews.jsonl` + the `pipeline.jsonl` rewind message), locate the flagged declaration in the Lean, and INDEPENDENTLY reproduce the conflict against the `.md`/`.tex`. A good verdict is auditable — it cites the `.md`/`.tex` line, the Lean line, and why they conflict; reproduce that chain yourself rather than trusting it. Concrete drift signatures to test for: a hypothesis over-quantified to unsatisfiability (e.g. `∀ n` where the spec says *eventually* — satisfiable only for a trivial parameter, making the headline vacuous), a dropped/extra term, a wrong sign, a `def` gerrymandered to the proof's own objects. Legitimate → let the re-scaffold/re-grind run, then re-read the patched declaration against the spec and confirm the build is still 0-sorry. False → stop, restore the pre-rewind state (`state.json` `.bak` + targeted `git restore` of only the rewound files), carry the clean state forward (and prompt-fix the reviewer if it recurs).

## Checkpoint recognition

Do NOT classify from the final stdout line — the CLI prints `CausalSmith research finished at stage <N>.` on exit. (On a halt the pipeline ALSO echoes a `[CausalSmith research] halt at <stage> (checkpoint). NEXT STEPS:` block to the console — a convenience re-grounding mirror of the JSON field below; still classify from the JSON.) The authoritative signal is the **last line of the run's `pipeline.jsonl`**: a JSON record with `"status":"checkpoint"`, a `message`, and — on a halt — a `next_step_guidance` field with the condensed what-to-do-next reminder (post-F5 also `next_action: "pending_checkpoint"` in state.json). Read it, classify against the recognition table above, and relay the message + the resume command (`/causalsmith research --resume <qid> <specialization>`) to the user.

## Bank decision tree

Banking is mechanical — always use the bank tool, never hand-roll.

Bank `accepted` only after clean F5 and explicit CKPT 2 approval. For every other tier, bank only on the
verdict the run *terminated* on; `revise` is iteration, not a bank trigger. "Final state" below means a
hard REJECT, revise rounds exhausted (NO-PASS), or a hopeless-TOPIC judgment—not a streamed mid-stage verdict.

| Final state | Tier | Trigger |
|-------------|------|---------|
| F5 complete (CKPT 2 approved) | `accepted` | Bank first; then execute any user-approved F7 promotion against the immutable bank receipt. |
| D-0.5 ACCEPT but D0.5 terminal REJECT (or exhausted-revise NO-PASS) on novelty (still mathematically sound) | `downgraded` | Bank once the run has terminated; record `seeds_burned[]` for collapsed angles. |
| D-0.5 NO-PASS, or D0.5 REJECT on correctness/structure | `failed` | Bank with a one-sentence epitaph; `reusable_artifacts[]` usually empty. |

From the CausalSmith package root:

```bash
cd <AUTOID>/CausalSmith
source ~/.nvm/nvm.sh && nvm use 20.20.2 >/dev/null 2>&1

# Standard bank (accepted | downgraded | failed)
npx --prefix tools tsx tools/bin/bank_entry.ts \
  --qid <qid> --spec <spec> --tier <tier> \
  --reason "<one-sentence verdict; verbatim where possible>" \
  [--achieved-tier <incremental|subfield|field|flagship>] \
  [--seeds-burned "0,3" --seed-burn-reason "<why these seeds are burned>"] \
  [--reusable <solver_blocked|not_reusable|unknown>] \
  [--reraise-status <re-raise|retry|true-negative|unknown>] \
  [--proposal-promise-gap <gap>] [--no-mint-oqs] \
  [--dry-run]

# Tier-drift snapshot (audit only)
npx --prefix tools tsx tools/bin/bank_drift.ts          # human table
npx --prefix tools tsx tools/bin/bank_drift.ts --json   # machine-readable

```

`bank_entry.ts` atomically: (1) patches `banked: true`, `banked_tier`, `banked_on`, `banked_reason` into state.json; (2) moves the run directory to `_bank/<tier>/<qid>_<spec>/`; (3) generates a README scaffold with TODOs for `gap_reasons[]`, `reusable_artifacts[]`, `proof_attempt_summary`; (4) on `--seeds-burned`, flags the seed entries and emits a top-level `seeds_burned[]` array — cold-start D-1 reads this to filter future proposals (no manual wiring). Refuses to re-bank an already-banked state or overwrite an existing destination.

Extra flags: `--achieved-tier <incremental|subfield|field|flagship>` — persist the validity-gate's achieved tier on a below-floor bank so later upgrades can enforce a strictly higher target; `--reraise-status <re-raise|retry|true-negative|unknown>` — your hopeless-vs-fixable call (`true-negative` = hopeless topic/deterrent; `re-raise` = sound math, novelty over-framed; `retry` = sound math, one construction fell short — drives the `/causalsmith-topics` saturation check; default `unknown` forces a future reviews-skim); `--reusable <solver_blocked|not_reusable|unknown>` — tag whether the proposal is worth retrying with a stronger solver (default auto-inferred from the proposal-promise gap); `--proposal-promise-gap <gap>` — override the README's `proposal_promise_gap` field (otherwise parsed from the reviews log); `--no-mint-oqs` — skip minting failed-theorem OpenQuestions into the study graph.

Schema and per-entry README format: [`_bank/README.md`](../../../CausalSmith/doc/research/_bank/README.md). Worked example: [`_bank/downgraded/stat_sa_cate_pointwise_v1/README.md`](../../../CausalSmith/doc/research/_bank/downgraded/stat_sa_cate_pointwise_v1/README.md).

**Fill the README TODOs.** Auto-generated bank READMEs leave `gap_reasons[]`, `reusable_artifacts[]`, `proof_attempt_summary` as TODO markers. Fill them before treating an entry as downstream-reusable; the bank's value over `rm -rf` is precisely those structured-fact fields.

## Guardrail hook (during a run)

[`.claude/hooks/causalsmith-guardrail.sh`](../../hooks/causalsmith-guardrail.sh) is a `PreToolUse` hook that denies `Edit/Write/MultiEdit` on paths owned by an active pipeline run. "Active" is signalled by a fresh heartbeat file: CausalSmith research writes `.run.active` under `CausalSmith/doc/research/active/<qid>/logs/`; study-mode runs write `.active` under `CausalSmith/doc/study/runs/<run_id>/`. A heartbeat is fresh iff mtime is within 5 min AND its PID is alive — stale heartbeats are ignored automatically. As a back-compat fallback, the hook also denies edits inside `research/active/<qid>/` if any `*_state.json` in that dir has `stage_completed != "5"` (bare-number F5; state.json / PIPELINE_NOTES.md are exempt).

- Orchestrator interaction: none. The TS pipeline manages the heartbeat; there is no `.subagent_dispatch_count` mechanism in the current hook.
- Hook denied a Read-only intent? It only fires on `Edit/Write/MultiEdit`, never on Read. A denial means you tried to mutate a protected path — re-read [`SKILL.md`](SKILL.md) § "Cross-cutting actions" (protected paths).

## What lives where

| Concern | Path |
|---------|------|
| TS pipeline source | [`CausalSmith/tools/src/`](../../../CausalSmith/tools/src/) |
| Stage dispatcher + cross-phase helpers | [`pipeline_stages.ts`](../../../CausalSmith/tools/src/pipeline_stages.ts), [`pipeline_support.ts`](../../../CausalSmith/tools/src/pipeline_support.ts) |
| Codex / agent prompts | [`src/discovery/prompts/`](../../../CausalSmith/tools/src/discovery/prompts/) (D-1, D0, D0.5), [`src/formalization/prompts/`](../../../CausalSmith/tools/src/formalization/prompts/) (F1/F1.5/F2, `proof_filler.txt` + `proof_reviewer.txt` for the loop, F5) + [`proof_review_loop.ts`](../../../CausalSmith/tools/src/formalization/proof_review_loop.ts) (the unified loop) |
| Templates (skeletons) | [`CausalSmith/tools/src/templates/`](../../../CausalSmith/tools/src/templates/) |
| State schema (zod) | [`CausalSmith/tools/src/state.ts`](../../../CausalSmith/tools/src/state.ts) |
| Pipeline driver | [`CausalSmith/tools/src/pipeline.ts`](../../../CausalSmith/tools/src/pipeline.ts) |
| Stage order constant | [`CausalSmith/tools/src/constants.ts`](../../../CausalSmith/tools/src/constants.ts) |
| Bank tools | [`CausalSmith/tools/bin/bank_*.ts`](../../../CausalSmith/tools/bin/) |
| Bank archive | [`CausalSmith/doc/research/_bank/`](../../../CausalSmith/doc/research/_bank/) |
| Hook | [`.claude/hooks/causalsmith-guardrail.sh`](../../hooks/causalsmith-guardrail.sh) |
| Per-run logs (reviewer-call debug log, run-liveness heartbeat) | `<qid>/logs/` — the pipeline creates this at run start; keeps the qid root holding only durable spec/state/graph/review artifacts. Any manual stdout redirect or pid file you create for a run goes HERE (`<qid>/logs/`), never the qid root. |
| Pipeline-failure notes (append observations here) | [`CausalSmith/doc/research/PIPELINE_NOTES.md`](../../../CausalSmith/doc/research/PIPELINE_NOTES.md) |
