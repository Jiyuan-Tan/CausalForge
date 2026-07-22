---
name: causalsmith
description: Run the CausalSmith pipeline. Invoke on `/causalsmith research` with a qid and specialization to discover, formalize, verify, and bank a causal theorem; `/causalsmith present` with a qid and specialization to turn an accepted entry into a verified paper bundle; or `/causalsmith study` with a slug to build reusable Causalean substrate. Also invoke on conversational requests to launch, resume, present, or study a CausalSmith result. Research owns the D-/F-stage workflow and dispatches `causalsmith-d` and `causalsmith-f`; presentation details live in `causalsmith-present/SKILL.md`.
---

# /causalsmith research — main orchestrator (top of the hierarchy)

You are the three-layer system's **main orchestrator**: own this qid's node process, watcher, and every
**terminal/cross-boundary** decision. Phase sub-orchestrators read verdicts and return receipts. Your job:
**route, resume, record.**

- **Sub-skills:** `causalsmith-topics` (no-qid proposal selection) · `causalsmith-d`
  (discovery: D-1/D0/D0.5) · `causalsmith-f` (formalization: F1…F5).
- **Shared recipes:** [`.claude/skills/causalsmith-shared/reference.md`](../causalsmith-shared/reference.md) — watcher recipes, `state.json` fields, bank decision tree, rewind discipline, stale-process reaping, substrate-build detail. Read the section a pointer names. [`f7-substrate-promotion.md`](f7-substrate-promotion.md) — the F7 dispatch payload (§ "F7").
- **Design:** `internal/plans/superpowers/specs/2026-07-09-causalsmith-hierarchical-orchestrator-design.md`.

**Mode routing:** for `causalsmith present`, load and follow
[`causalsmith-present/SKILL.md`](../causalsmith-present/SKILL.md) instead of
the research procedure below. For `causalsmith study`, use this skill's
[`study` section](#study--substrate-build-side-run-main-launches-f-escalates).

State is externalized: on compaction/respawn, re-ground from `state.json` and
`orchestrator/decision_log.jsonl` (§ "Recording"); never rely on an agent handle.

## The loop

**One holder per qid:** main normally owns the node process + watcher, but can grant a phase-scoped
`resume-lease`. The holder alone arms the watcher and calls `--resume`, self-driving only its own phase
(D0; F2–F4). A lease never grants terminal authority (bank, stop, SIGINT, cross-boundary rewind), which
always stays with main; phase boundary, escalation, or terminal returns it.

**Different qids run concurrently.** `<run-dir>/logs/.run.active` rejects only a duplicate of the SAME
qid; scope all liveness/reap checks to it. Global `pgrep` is diagnostic, never a gate. Shared build/graph
locks serialize contention—wait, never kill/postpone another qid. Manual Codex/Lean work follows
CLAUDE.md import-closure/build-safety rules.

At launch/resume + dispatch, the sub ATTACHES its watcher to that live process and does not `--resume`
until its stage halt. “Invoke” D/F means invoke the skill, not a second node process.
`CAUSALSMITH_ALLOW_PARALLEL=1` never bypasses a same-qid heartbeat; ambiguity means inspect heartbeat +
argv, return the lease to main, and do not race.

1. **Launch** (§ "Launch") in background; in the **same turn** dispatch D and grant/log
   `dispatch`/`subtype:"lease-grant"`, then yield. D arms the watcher and owns discovery including its
   first halt. Ignore main's exit notification unless D died (§ "Orphan recovery").
2. The leaseholder reads verdicts, applies levers, and repeatedly resumes its phase without a main hop.
   It returns only one `{escalation, receipts}`—`go-no-go`, terminal, `codex-blocked`,
   `rewind:fix-source`, `cap-block`/`substrate-unbuildable`, `substrate-build:study`,
   `citation-instantiation-overflow`, `f5-clean`, `pipeline-bug`, `dispatch-request`, or
   `request-reseed`—not routine rounds. It asks main to dispatch any Claude subagent.
3. Main handles that escalation (§ "Handling escalations"); crossing a boundary resumes and re-dispatches
   the next sub **in the same turn**. Clear caps only with resume's `--clear-gate <flag>`, never by editing
   `state.flags`.
4. A leaseholder that dies without returning it triggers § "Orphan recovery".

## Dispatching sub-orchestrators

- **Cold:** use Claude's Agent/Codex `spawn_agent`; on Codex use `codex exec` only when a specified model
  or effort must be enforced. Grant and log the lease.
- **Warm:** under Codex, use `followup_task` to restart an idle/completed agent; `send_message` only amends
  a currently running turn and does not trigger a new one. Under Claude, use `SendMessage`. Warm reuse is
  only an optimization—state remains `decision_log` + `state.json`.
- **Re-seed:** default at D→F; also on returned `request-reseed` or orphan. A sub self-loops its phase,
  so never respawn it mid-phase unless it returned the lease.

## Orphan recovery (leaseholder died mid-phase)

If a background sub dies without a clean lease-return, its node process may be unwatched. (1) Inspect only
that qid's `pgrep -f "causalsmith.ts research.*<qid>"` + heartbeat: let live mid-run finish; reap idle
linger. (2) Re-ground from `state.json` (stage/flags/round) and `decision_log.ts read` tail. (3) Re-arm,
re-dispatch from that log, grant the lease, and log `command`/`subtype:"lease-reclaim"`.

**Dispatch-prompt templates** (fill `<qid>`/`<spec>`/`<bool>`). Keep them to the non-derivable payload —
the sub loads the rest (self-resume loop, watcher, faithfulness, lease-return conditions) from its own
skill on `Invoke skill`:

> **D-orch:** You are the CausalSmith research **D-stage orchestrator** for run `<qid>`/`<spec>` and you HOLD THE
> RESUME-LEASE for discovery. Invoke skill `causalsmith-d` and follow it exactly, including its re-ground step
> and its lease-return conditions. auto_mode=`<bool>`.

> **F-orch:** identical, with **F-stage** / skill `causalsmith-f` / "formalization"; you hold the resume-lease
> for F.

## Topic-selection escalation loop (pre-launch `--propose`)

For a no-qid `--propose`, dispatch a topic-selection subagent and have it invoke `causalsmith-topics`.
Main owns ≤4 re-steers beyond that initial dispatch. On `ESCALATION`, read receipts,
ranked untried levers with headroom, and tier-honest fallback; choose one highest-EV steer
(refine/re-seed/jump/transplant/reframe), warm-continue with accumulated anti-constraints, and track burned
levers. Steer; do not redo its deep reads/gate. `DONE` launches its command. `BLOCKED` fixes tooling and
retries the same round. Empty genuine headroom or four rounds is a hard user-stop, even `--auto`, reporting
burned levers, fallback, and remaining choices. Never lower tier to manufacture acceptance. Record the
selection summary in the first decision-log entry.

## Handling escalations

Every escalation is a decision-log entry carrying **verbatim receipts** (the reviewer phrase naming the
collapsed conjecture, the `.tex` line audited). If receipts are missing, send it back — an unsupported
"hopeless" is a bug, not a verdict.

| Escalation | By | Your action |
|---|---|---|
| `go-no-go` (D0.5 PASS) | D | Decide commit-to-F (auto: decide; non-auto: may ask user), then `--resume` into F1 + dispatch an F-orch **+ re-grant the lease**. |
| `request-reseed` | D/F | The leaseholder is degrading — respawn a fresh sub for the SAME phase + re-grant the lease, seeded from the log. Not a terminal. |
| `dispatch-request` | D/F | Only main dispatches Claude subagents (shared reference § "Architectural rule"). Do so, wait, warm-send its result, and re-grant. This is rare: subs self-drive their own Codex/node processes. |
| `codex-blocked` | D/F | Not a math finding and not validity-gated. Hard user-stop even `--auto`: quote denial, exact command, and impact; harness-level permission (accept prompt/leave auto) is required—chat permission cannot clear it. Then re-grant and re-issue the SAME command; reject any hand-proof/weakened-gate workaround. |
| `terminal:tex-claim-wrong` | D/F | **codex-validity-gate** → bank `failed`. |
| `terminal:below-floor` | D | codex-validity-gate first. Then **surface** the fact to the user (never silently lower `--novelty`) and let them choose: bank `downgraded` (stop), or accept the achieved tier and continue to F via **`causalsmith research --downgrade-tier <achieved-tier> <qid> <spec>`** (lowers the floor, re-passes D0.5, then continues per `--auto` / halts at the go/no-go). |
| `terminal:laundering` (claim-level) | D/F | codex-validity-gate → bank `failed`. |
| `rewind:fix-source` | F | Verify it's necessary, then dispatch a D-orch to execute it (§ "Cross-boundary rewind"). |
| `cap-block` / `substrate-unbuildable` | D/F | Only main resets caps, except the D-1 leaseholder's explicit persisted `--angle-action retry --extra-revisions N --angle-directive -` checkpoint lane (causalsmith-d §D-0.5 CLI checkpoints). Diagnose receipts/root first: scaffolder drift → persistent `bin/f2_directive.ts`; reviewer wrong → general `pipeline-bug` prompt fix; plan wrong → rewind. Clear via resume's `--clear-gate` only after a root change; log that change. Identical rerun is laundering, not retry. Same defect after two resets → validity-gate then user. |
| `substrate-build:study` | F | Launch the `--study` side-run yourself (§ "`--study`") and relay the Causalean path back. |
| `citation-instantiation-overflow` | F | Independently classify from contribution + downstream graph (`crux:true` is insufficient) and audit the cited boundary. Source-match a stronger paper-agnostic source interface if available; otherwise gate/attempt only a minimal uncited reusable bridge that is headline-critical (study only substantial/reusable). Secondary → stop spend and disclose UNDELIVERED. Paper-specific residual → prove, UNDELIVERED, or correct source—never gate. F4 still must run; inability to represent/review an undelivered subset is a pipeline bug. |
| `f5-clean` | F | Verify F4 exists: a F2.5 escalation followed by stages 3/3.5/3.7/4 skipped, absent this-round `reviews.jsonl` verdict, or absent dual F4 receipts voids it. Send void claims back to resolve the root and re-enter F2.5; no sub-audit substitutes for F4. With F4: run S6 for remaining `gated` debt (auto in `--auto`), then CKPT 2 user-stop with Lean/API/assumptions/F4/tier receipts. After an `accepted` bank run F7 promotion. |
| `reviewer-dispute` | F | Main independently reproduces; reviewer right → comply. Reviewer wrong → first-instance `pipeline-bug`: while stopped, add a concise GENERAL reviewer-prompt rule, record `PIPELINE_NOTES.md`, and re-enter F2.5/F4. Never instance-exempt a node or weaken re-review; undecidable math → user. |
| `pipeline-bug` | D/F | Fix the prompt/code while the run is stopped (§ "Pipeline-bug fixes"), then re-dispatch. |

**Codex-validity-gate:** only `terminal:*`/`cap-block`, never `go-no-go`/`f5-clean`. Before banking or
user escalation, consult `gpt-5.6-sol` **high** (`CAUSALEAN_MODEL_CODEX_CONSULT`, `-c model_reasoning_effort=high`;
this consultation tier only — all other codex agents stay medium) with raw halt, verbatim
receipts, and a neutral terminal-vs-fixable prompt that states the case to continue. Different resolving
load-bearing defects mean keep going; the same recurring defect, laundering, or wrong-direction pivot may
stop. Re-attributed recurring themes are root gaps, not noise; a lower tier is not hopelessness—converge and
bank `downgraded`. A concrete fix becomes a dispatch/rewind (or root-earned `--clear-gate`), not a bank.
Codex cannot override faithfulness. D0.5 hygiene-only rotation while novelty/tier keeps passing is likewise
convergence, not terminal.

## Auto mode (`--auto`)

Autonomous run (user said "auto" / "don't ask me"). **Pass `--auto` on the launch command and on every
`--resume`** — it latches onto `state.auto_mode`. Apply each escalation's normal rule unchanged, just
decide it yourself and `--resume`/act **without pausing to ask the user**; only the "wait for user / ask
/ offer" half is overridden — the math/proof judgment (sub + codex) is identical. Propagate
`auto_mode=<bool>` into every dispatch template.

**Hard stops even in `--auto` — ONLY these seven. Everything else you decide and drive yourself.**
1. **CKPT 2** (after S6) — bank / promote / commit ALWAYS wait. The one routine stop; report the per-gate
   and per-core outcomes there.
2. **Kernel dead** — the math CLAIM itself is refuted / false / unprovable (codex-validity-gate confirmed).
   No directive can save it; the topic is over.
3. **Serious pipeline defect** — the TS/prompt machinery is structurally broken and cannot self-resolve
   (§ "Pipeline-bug fixes"; the edit needs the run stopped).
4. **`codex-blocked`** — permission is user-owned; never self-grant it.
5. **Topic-selection exhaustion** — no genuine untried headroom after the capped topic loop.
6. **Below-floor tier choice** — surface the achieved tier; the user chooses whether to bank downgraded or
   continue under an explicitly lowered floor.
7. **Unresolvable reviewer dispute** — after independent reproduction cannot decide the mathematics, the
   user must adjudicate; disagreement that is reproducibly reviewer-right/wrong follows the normal route.

**NOT stops — drive these yourself, even in `--auto`:**
- **Unfaithful scaffold / wrong model encoding / statement drift while the NOTE is correct** → an ORDINARY
  F2 rewind: inject `bin/f2_directive.ts`, rewind to F1.5/F2.5, re-scaffold + re-prove. A formalization bug
  is the pipeline WORKING (formalization IS verification) — never a user question.
- **Missing substrate / a gate S6 cannot discharge** → build it when headline/headline-support; otherwise
  apply the citation-overflow stop-spend rule. A true cited dependency may leave its consumer honestly
  CONDITIONAL; a paper-specific conclusion may only be PROVED or explicitly UNDELIVERED.
- **A core that won't close** → keep attacking with the substrate built; if it still won't, it is UNDELIVERED
  content reported at CKPT 2 — never a user escalation, and never gated (§ causalsmith-f "Substrate building").

**UNDELIVERED safeguard.** Runtime may persist `delivery_status:"undelivered"` only for (a) a theorem
independently classified `secondary`, or (b) a `cited` node. It is forbidden for `headline` and
`headline-support`, and no delivered theorem/lemma may depend on it. Keep the node and reason in the
core/plan/graph, emit no Lean declaration/`@node` tag, and exclude it from F2.5/F3/F4 Lean/proof
obligations. It is NOT excluded from F4 altogether: both convergence reviewers must independently audit
the core's contribution framing and full reverse dependency closure and agree that it is secondary/cited,
not headline/headline-support, and unconsumed by delivered results. Render it as a disclosed `remarkv` in
presentation — never as a theorem, assumption, or contribution.

No progress across successive resumes ⇒ terminal. Every checkpoint carries an `⚙ AUTO MODE` banner — see it
⇒ decide + act, don't ask.

## Cross-boundary rewind

On a `rewind:fix-source` from F: **verify the rewind is necessary first** (shared reference § "Rewind
discipline" — independently reproduce the Lean↔`.tex` conflict). If false, send it back (restore + fix
the reviewer/scaffolder is the sub's job). If real, log a `command` (`cmd:"rewind-D0"`, `target:<node>`,
`note:"incremental — patch the node + dependents, keep the sound rest, re-validate"`) and dispatch a
D-orch to execute it. Never re-derive the whole discovery from scratch.

## Bank (CKPT 2 acceptance or terminal outcomes)

Banking is mechanical — always use the bank tool, never hand-roll. Bank `accepted` only after a clean F5
and explicit CKPT 2 approval; complete that accepted bank before F7 promotion. All other tiers require a
**terminal** outcome (a hard REJECT, revise-exhausted NO-PASS, or a codex-gate-confirmed hopeless-TOPIC) —
never bank mid-pipeline while a run can still pivot/downgrade/revise. Classify per the shared reference § "Bank decision tree",
then run [`bank_entry.ts`](../../../CausalSmith/tools/bin/bank_entry.ts): `failed` for
correctness/structure/NO-PASS, `downgraded` for sound-but-not-novel. Pass `--reraise-status` from the
sub's hopeless-vs-fixable receipts (`true-negative` / `re-raise` / `retry`). Fill the generated
`_bank/<tier>/<qid>_<spec>/README.md` `gap_reasons` (verbatim reviewer phrases) + `proof_attempt_summary`.
For a below-floor `downgraded` bank, pass `--achieved-tier` from the validity-gate receipt so a later
`--upgrade` can enforce that its target is strictly higher.
Append a `terminal` decision-log entry. Bank `failed` only if the *math claim* is wrong.

## S6 — SUBSTRATE ATTEMPT (MAIN-owned; post-F5, BEFORE CKPT 2)

**S6 is main-owned, not an F-stage.** It is a second, honest attempt at a genuinely hard minimal
`gated` substrate debt—not a deferral lane. F1–F5 must first attempt every obligation; never pre-gate
winnable work.

For each eligible gate, main chooses either a dedicated `gpt-5.6-sol` agent (one-off/run-specific) or
`--study <slug>` (substantial reusable standard primitive; also promotes it). Triage from the core's
contribution and downstream graph (`crux:true` alone is insufficient): attempt only `headline`/
`headline-support` gates needed for an unconditional delivered headline. Skip secondary-only and
`oeq:`/deliberately-open gates unless user elects them; disclose at CKPT 2. Never send `cited` or
paper-specific residuals to S6.

Dispatch one agent/study run per gate, grouped by difficulty with separate `TMPDIR`/Codex sessions; no
worktrees, and serialize coupled import closures. In `--auto` dispatch without asking. Each agent builds a
general reusable, axiom-clean, zero-sorry lemma (leaves first; `lake build <module>` green), not a
theorem-shaped workaround; then `causalsmith research --discharge-gate <qid> <spec> <node_id> --lean-name
<BuiltLemmaName>` (must re-pass F4→F5) and promotes it. It reports `still-gated`, never guesses/re-gates,
if attempts fail, the faithful general statement is unclear, or discharge needs a theorem-statement change
(then fix F). Main owns the wait: monitor long `sol` workers, re-seed on context bloat, and take every
discharged/still-gated outcome to CKPT 2.

## F7 — SUBSTRATE PROMOTION (part of CKPT 2, right after an `accepted` bank)

Un-promoted substrate is re-derived at full cost. F7 is user-approved like banking: even `--auto` presents
the set before action. Dispatch a fresh, bounded, no-lease agent with
[`f7-substrate-promotion.md`](f7-substrate-promotion.md).

**Main selects by reusability:** grep a helper for run types (`ParamSpace`, `CumVec`, class defs) and ignore
vestigial imports. Promote as-is if uncoupled or recurring; tag `generalize` if a faithful recurring/
Mathlib-adjacent general object can decouple—restate it over a general ambient and re-import the run-specific
version as a specialization; leave coupled speculative one-offs. Present the `helper → target` list/tags at
CKPT 2 or auto banner before dispatch. Place each result in the narrowest existing domain hierarchy (`Mathlib/`, `Stat/`, `SCM/`, `PO/`,
`Estimation/`, etc.), or create a properly named topic module inside that hierarchy when none exists.

**Dispatch:**

> **F7 promotion agent:** Read [`.claude/skills/causalsmith/f7-substrate-promotion.md`](f7-substrate-promotion.md)
> and follow it exactly. Run `<qid>`/`<spec>`. Promotion SET: `<helper → target Causalean module list>`.

On return, main verifies itself: `#print axioms` on the banked flagship, no new signature binder, intact
conjuncts, full build green, and fit (no paper-named duplicate of a Mathlib/Causalean primitive; shared
names free of run jargon). Regression returns to the agent; never patch around it. Record
`reusable_artifacts` in the bank README and a `command` decision-log entry.

## Pipeline-bug fixes (main's job; sub flags)

**When debugging ANYTHING, check the I/O log FIRST — before inferring cause from `state.json`,
`sorry`/stage counts, or a halt signal.** The agent's OWN I/O (`doc/research/_agent_logs/`,
`_reviewer_calls.log`, stage stdout) shows what the model actually saw and decided, surfacing bugs the
state hides (empty/fail-open prompts, self-admitted laundering, a graded-vs-applied count mismatch). This
is the CLAUDE.md universal rule; make it your first move on every diagnosis, not a fallback.

The sub sees a recurrence (it reads the reviews); the edit is cross-run learning and needs the run
stopped, so main applies it. Diagnose from the agent's OWN I/O: read
`doc/research/_agent_logs/`, diff EMITTED vs PERSISTED. Classify: **code bug** (id-mapping drop,
fail-open-to-empty-prompt) → fix the TS; **prompt problem** → edit that stage's prompt with a GENERAL
rule, concise, not overfit. **Recurrence threshold:** 1st occurrence → record in
[`PIPELINE_NOTES.md`](../../../CausalSmith/doc/research/PIPELINE_NOTES.md); promote to a
prompt/code rule on the 2nd instance or across two qids. Prompts are re-read per dispatch → edit only
while stopped.

## Recording (decision_log)

Main appends via [`decision_log.ts`](../../../CausalSmith/tools/bin/decision_log.ts):
`npx --prefix tools tsx tools/bin/decision_log.ts append <qid> <spec> --json '<entry>'`. Main's entry
types: **`dispatch`** (on every spawn/lease-grant — `{type:"dispatch",from:"main",phase,subtype:"lease-grant",note}`),
**`command`** (rewind/seed/lease-reclaim orders — `{type:"command",from:"main",cmd,target,subtype,note}`;
`subtype:"lease-reclaim"` on an orphan recovery), **`terminal`** (bank —
`{type:"terminal",from:"main",tier,reraise,why}`). This log + `state.json` is main's own resumable state;
there is no separate main-state file. The lease is **soft state recorded here, not a file lock** — on any
respawn, read the tail to know who holds the lease (last `lease-grant`/`lease-reclaim` vs a lease-return
escalation) plus every terminal/rewind already committed.

## Argument forms

| Form | Effect |
|------|--------|
| `<qid> <spec>` | Cold start. |
| `--resume <qid> <spec>` | Resume after CKPT 1 / 1.5 / 2 or a `missing_architecture` block. |
| `--propose <topic> <qid> <spec>` | Run with D-1 question proposal first. |
| `--propose <topic> --novelty <higher-tier> --upgrade <parent_qid>_<parent_spec> --upgrade-axis <axis> <qid> <spec>` | Upgrade a banked accepted / downgraded parent. `<higher-tier>` must be strictly above the parent's `banked_novelty_tier`. |
| `--from-question <oq_id> <qid> <spec>` | Phase 3 — seed from a graph-resident OpenQuestion. Atomically claims the OQ. On clean F5 the `close_open_question` hook mints a BankedTheorem. Repair a `close_oq_failed` via `close_oq.ts <qid> <spec> <oq_id>`. |
| `--downgrade-tier <tier> <qid> <spec>` | Accept an achieved lower tier on a `terminal:below-floor` run: lower the persisted novelty floor to `<tier>` and re-pass D0.5, then continue per `--auto` (into F) or halt at the go/no-go. Guarded — `<tier>` must be strictly below the current floor AND ≤ the reviewer-assessed tier; logs a `command` decision-log entry. Use after the codex-validity-gate confirms + the user opts to carry the sound sub-tier result into F rather than bank `downgraded`. |
| `--angle-action <continue\|switch\|retry\|give-up> <qid> <spec>` | Resolve a persisted D-0.5 checkpoint. `continue` acknowledges a routine REVISE; `switch` archives the exhausted angle; `retry --extra-revisions N` persists a per-angle cap; `give-up` writes a terminal proposal block. Add `--angle-directive <text\|->` to persist the D-orchestrator repair before any next proposer starts. Non-give-up actions resume in the same CLI process. |

Optional pass-through flags: `--auto` (§ "Auto mode"); `--novelty <incremental|subfield|field|flagship>` (D0.5 threshold = the floor tier, default `field`; the vocabulary IS the reviewer tier ladder — legacy `relative-to-repo`→`incremental` / `relative-to-literature`→`subfield` still accepted); `--upgrade <parent>` + `--upgrade-axis <computation|estimation|generalization|mechanism>` (requires an explicit novelty target strictly above the parent's achieved `banked_novelty_tier`); `--stop-after <stage>` (`D-1.1`,`D-1.2`,`D-0.5`,`D0`,`D0.5`,`F1`,`F1.5`,`F2`,`F2.5`,`F3`,`F3.5`,`F4`,`F5`); `--from-stage <stage>` (resume-entry override — re-run a stage instead of hand-editing `stage_completed`); `--clear-gate <flag>` (resume-only, repeatable — clears a cap-gate flag as part of the resume instead of hand-editing `state.flags`; flags: `substrate_build_required`, `scaffold_redirect_cap_hit`, `stage1_rewinds_cap_hit`, `theorem_splits_cap_hit`, `stage0_budget_exhausted`, `general_review_halt`, `stage_neg1_fallback`, **`proof_loop_cap_hit`**; clearing `scaffold_redirect_cap_hit`/`stage1_rewinds_cap_hit` also resets its paired counter. **`proof_loop_cap_hit` covers EVERY proof-review-loop iteration budget** — total iters, Phase-A scaffold-reroute rounds, per-node strikes, tag reroutes, the no-progress bound — all now PERSISTED in `state.flags.proof_loop_counters` and cumulative across resumes; clearing it resets them all. **Clearing ANY iteration cap is MAIN's authority alone** (a sub escalates `cap-block`; see that row) and is legitimate only once the ROOT cause has changed — a reset that re-runs the identical scaffold/review is a re-roll, not a retry); `--proposer <codex|claude>`; `--from-study-gaps`; `--dry-run` (state-machine mechanics only, no Codex — **NEVER use `--dry-run` to move the stage pointer on a live run: it fast-forwards `stage_completed` and corrupts the run; use `--from-stage` to re-enter a stage**). Parsing failure → stop and report; do NOT invent a qid.

## Launch

```bash
cd <AUTOID>/CausalSmith
source ~/.nvm/nvm.sh && nvm use 20.20.2 >/dev/null 2>&1
npx --prefix tools tsx tools/bin/causalsmith.ts research $ARGUMENTS      # slash form; substitute literal args for conversational
```

**cwd must be the CausalSmith package root** (`<AUTOID>/CausalSmith/`, a sibling of `Causalean/`) —
`cli.ts:findRepoRoot` walks upward for the `CausalSmith` `lakefile.toml`. `--prefix tools` keeps `npx`
reading `tools/package.json`. Node 20.20.2 is mandatory (default shell is node 12; the CLI silently
fails otherwise). Run in background (`run_in_background: true`) — the completion notification fires only
on process **exit**, so **dispatch the D-orch (which arms the watcher) in the same turn** and hand it the
run; main itself does not watch the cold-start→first-halt window. Do NOT wrap with `... > log 2>&1 &`.

Before launch, check only for a live owner of the SAME qid (the CLI's per-qid heartbeat is authoritative).
Processes for different qids are expected and MUST NOT delay this launch or its immediate sub-orchestrator
dispatch. Cross-qid `lake build` calls serialize internally via the shared build mutex while the rest of
the stages continue concurrently.

**Run-artifact paths (canonical):** run dir = `CausalSmith/doc/research/active/<qid>/`.
`state.json` + `pipeline.jsonl` live at the root; ALL
review artifacts under `reviews/`; D0 artifacts under `discovery/`; the orchestrator judgment log under
`orchestrator/decision_log.jsonl`. When unsure: `find doc/research -path '*<qid>*' -name '*.jsonl'`.

## After TS exits

After **every** TS exit — full run, early `--stop-after`, or crash: read `state.json` + the LAST
`pipeline.jsonl` line (the checkpoint signal, not stdout; on a halt it carries `next_step_guidance`).
Classify the terminal state from `stage_completed` (bare number on-disk), the tail, `next_action`,
`flags.*`, `banked` (shared reference § "state.json — fields" + the recognition table). A halt ≠ a clean
result — a review-gated stage can dead-end (D-0.5 NO-PASS, D0.5 terminal REJECT, revise-exhausted
NO-PASS) looking identical to "stopped" until you read the verdict; a *single* F1.5/F4 reject is
iteration. Route to the phase sub-orch to read the verdict body; for unrecoverable terminations bank per
§ "Bank".

$ARGUMENTS

## `study` — substrate-build side-run (main launches; F escalates)

A standalone mode that builds a reusable Causalean substrate module from a plain-English requirement,
bypassing the D/F pipeline. Because it is a **node process**, main launches it (the invariant). The
F-orch only escalates `substrate-build:study` when a gate is genuinely reusable AND substantial (a
self-contained standard primitive multiple runs will want) — the common small-scale build the F-orch
does itself. On the escalation, F hands up the `requirement.md` content + a slug; you:

```bash
npx --prefix tools tsx tools/bin/causalsmith.ts study <slug>           # cold start / re-run
npx --prefix tools tsx tools/bin/causalsmith.ts study <slug> --resume  # continue after interruption
```

Run dir `CausalSmith/doc/study/<slug>/`. On first invocation if `requirement.md` is absent
the pipeline writes a blank template and exits — fill it from F's escalation and re-run. State only the
requirement; **do not choose or set a `## Target module` manually.** After review passes, the coordinator
searches Causalean, deduplicates against existing declarations, and chooses the narrowest faithful
merge-first home (or a genuinely new topic module inside the appropriate domain hierarchy) before
integration. The loop (configured scaffolder →
codex fillers → codex reviewer → codex coordinator; build ≤10, review→revise ≤3) self-heals within caps;
no intervention expected. The coordinator's placement then passes the verify-or-rollback gate (`lake build`
→ `library_index` → `embed` → `lint:embeddings` → `doc:gen` → `doc:check`); relay the pass + Causalean path (or the
failing step) back to the F-orch so it can discharge the gate.

**HARD LAYERING INVARIANT — NO PAPER IMPORTS IN REUSABLE SUBSTRATE.** During staging, generated files may
import Mathlib, Causalean, and modules from the same temporary neutral study tree; they must NEVER import a
specific `CausalSmith/*_Research` / paper module. If the study needs a reusable helper that currently exists only in
the paper folder, STOP the study before scaffolding on that import. Extract/generalize the helper first into
the same neutral **temporary** staging tree `CausalSmith/CausalSmith/Substrate/<Slug>/`, replace the paper helper with a
thin import/re-export or paper-specific specialization so existing consumers keep their names/signatures,
and verify the neutral module has no reverse paper dependency. This staging tree is never a final reusable
destination: the coordinator chooses the proper Causalean subject hierarchy for the complete closure. Then
resume the study on top of the neutral prerequisite. Do not copy a second incompatible definition. At
promotion, move/promote the WHOLE reusable dependency closure so every final Causalean module again imports
only Mathlib/Causalean; `rg '^import CausalSmith\..*_Research'` over the promoted set must be empty.

## Mathlib helper staging

New Mathlib-shaped helpers produced during F3 land in `CausalSmith/CausalSmith/Mathlib/`, not
`Causalean/Mathlib/`. Promotion to Causalean is a deliberate human step requiring (a) ≥2 independent
call sites or a fully general statement, and (b) no CausalSmith-specific dependencies.

## Phase 4 — CHECKPOINT_NEXT

After F5 closes cleanly the pipeline writes `CHECKPOINT_NEXT.md` under `doc/research/active/<qid>/`
proposing 1-3 next actions plus Stop. Nothing auto-launches; the user picks and invokes the printed
command in a fresh run.
</content>
