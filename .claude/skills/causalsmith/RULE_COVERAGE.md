# CausalSmith research split — rule-coverage audit

Audit for the 2026-07-09 split of the monolith `CausalSmith research` skill into `causalsmith` / `causalsmith-d` /
`causalsmith-f` + `causalsmith-shared/reference.md`. Confirms every load-bearing rule from the old
`SKILL.md` + `causalsmith-shared/reference.md` landed in exactly one destination. **Result: 45/45 mapped, 0
dropped** (mechanical grep verification, re-runnable — see the `chk` loop in the Task 6 commit).

## main (`causalsmith/SKILL.md`)

| Rule | Verified anchor |
|---|---|
| The loop — launch + wake-on-event watcher | "Watching a live run" pointer |
| Per-qid invariant: one leaseholder owns that qid's node process + watcher; different qids run concurrently | "Different qids run concurrently" |
| Auto mode — pass `--auto`, latch `auto_mode` | "latches onto … auto_mode" |
| Auto stop-only: CKPT2 / codex-confirmed terminal | "CKPT 2 … bank … ALWAYS wait" |
| Codex-validity-gate + neutral prompt + recurrence-is-real | "codex-validity-gate", "Prompt neutrally" |
| Whack-a-mole D0.5 not terminal | "whack-a-mole", "hygiene-only rotation" |
| Bank tool + tiers (terminal only) | "bank_entry", tier rules |
| Argument forms | "from-question", "upgrade-axis" |
| Launch — cwd = CausalSmith root, node 20.20.2, run-artifact paths | "cwd must be the CausalSmith", "20.20.2" |
| After TS exits | "After TS exits", "next_step_guidance" |
| Mathlib helper staging | "Mathlib helper staging" |
| Phase 4 CHECKPOINT_NEXT | "CHECKPOINT_NEXT" |
| `--study` main-launched side-run | "Because it is a … node process" |
| Pipeline-bug — diagnose own I/O, recurrence threshold | "EMITTED vs PERSISTED", "_agent_logs" |
| Cross-boundary rewind — verify first | "Rewind discipline", "rewind-D0" |

## d (`causalsmith-d/SKILL.md`)

| Rule | Verified anchor |
|---|---|
| Read verdict BODY / classify / record | "READ the verdict BODY" |
| D-1 proposal | "stage_neg1" |
| Delegate D-stage math to codex | "Delegate every D-stage math call" |
| D0 three checkpoints (proposed-change / open_obligation / MAXIMALITY) | those three literals |
| Adjust the target, never trivialize | "Adjust the target, never trivialize" |
| D0.5 verdict — two shapes (below-floor / go-no-go) | "BELOW NOVELTY FLOOR", "go/no-go" |
| D-side faithfulness → detect+prove, escalate not bank | "detect and prove" |

## f (`causalsmith-f/SKILL.md`)

| Rule | Verified anchor |
|---|---|
| F1 substrate self-halt | "substrate_build_required" |
| CONSOLIDATED CKPT 1 — reuse / cited / depth | "CITED classification", "REUSE" |
| Size + unbundle each gate | "UNBUNDLE", "research-scale-external" |
| F2–F4 routes (hint / build-substrate / fix-source) | "f3_directive", "fix-source" |
| F2.5 incremental — reset count, don't rewind | "F2.5 IS INCREMENTAL", "scaffold_redirect_count" |
| Strengthen-if-dischargeable | "Strengthen-if-dischargeable" |
| Faithfulness enforcement machinery + laundering modes | "laundering modes", "hand-de-launder" |
| Lean↔note sync | "Lean↔note sync" |
| Re-render Lean-hostile scaffold | "Re-render a Lean-hostile" |
| Build `gated`, never `cited` | "Build `gated`, never `cited`" |
| Concurrent substrate building (small-scale default / `--study` escalate) | "Small-scale workaround = DEFAULT" |
| Split every compound gate | "Split every compound gate" |
| Keep what you build short + `split_lean_file` | "split_lean_file", "would cross ~300" |
| Keep the graph current | "Keep the graph current", "@node" |
| ScheduleWakeup unreliable | "ScheduleWakeup is unreliable" |

## shared (`causalsmith-shared/reference.md`, relocated verbatim from `causalsmith-shared/reference.md`)

state.json fields · bank decision tree · rewind discipline · stale-process reap · search-substrate-right-path ·
guardrail hook · proof-review loop watch · over-decomposition watch — all present (8/8).

## Correction (2026-07-09) — anchor-audit was insufficient

The original "45/45, 0 dropped" pass matched anchor *phrases*, not operational *substance*, and so
green-lit four rules whose actionable content never landed. Caught on a re-audit and restored:

| Rule | Restored to | Was |
|---|---|---|
| `gate.ts` atomic gate-registration (never hand-edit Lean alone → else re-scaffold drops the hyp = endless scaffold-fight) | `causalsmith-f` § Substrate building | dropped entirely |
| whack-a-mole D0.5 **root-fix disciplines** (wholesale comparator set / one cross-node hygiene audit) | `causalsmith-d` § D0.5 | only the "don't stop" framing survived in main |
| codex-validity-gate neutrality self-check ("state the case AGAINST your verdict or the consult is invalid") | `causalsmith` § codex-validity-gate | dropped |
| "trust your own hand-derivation over the pipeline's failure on a bad setup" | `causalsmith-d` § D0 open_obligation | dropped |

Lesson: future coverage audits must diff operational substance clause-by-clause, not grep for anchors.

## Validation

- **Dry-run** from the new entry point: `causalsmith.ts research --dry-run eid_backdoor_demo v1` → exit 0,
  "dry-run finished at stage F5". The TS pipeline is unchanged; the split is skills-only, so mechanics
  are identical.
- **decision_log.ts** unit tests: 6/6 pass; typecheck clean.

## Retirement complete (2026-07-12)

The deprecated `.claude/skills/causalsmith/` monolith has been removed. Start every `/causalsmith research` run
through `causalsmith`; it owns lifecycle decisions and dispatches `causalsmith-d` or `causalsmith-f`
for phase-scoped work.
