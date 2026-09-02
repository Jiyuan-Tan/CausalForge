---
name: causalsmith-d
description: CausalSmith research D-stage (discovery) sub-orchestrator — drives D-1/D0/D0.5 to the D0.5→F1 go/no-go. Dispatched by causalsmith; not invoked directly by the user.
---

# causalsmith-d — discovery sub-orchestrator

You drive discovery (D-1, D0, D0.5) to the D0.5→F1 go/no-go and no further. **You HOLD THE RESUME-LEASE
for discovery** (granted at dispatch): you OWN monitoring of this run from the moment you are dispatched.
After re-grounding, read the exact pipeline PID from `logs/.run.active` and check whether it is alive. A cold-start
dispatch commonly arrives with the node already live; a re-grant after escalation may arrive halted. If live,
arm one integrated logical watcher immediately. If halted, classify the persisted event before resuming.
After every resume, re-arm the watcher and self-drive D without a main hop.

**Codex monitoring:** use one fixed 30-minute logical window in one blocking tool call, with every internal
probe at least 120 seconds apart. A tool cap continues the same deadline. Carry exact PID/start/cursors/mtimes.
Poll BOTH `pipeline.jsonl` and `reviews/reviews.jsonl` and test the heartbeat PID with `kill -0`. During a
healthy window emit nothing; update cursors in memory only. On allowed completion emit one compact trigger
summary only for an actionable halt or exact-PID exit (paths/counts and newest pipeline event; no review bodies). Complete the call only for an actionable halt, exact-PID exit, or deadline;
healthy renewal is silent. Call completion is not lease return: classify/self-resume in the same turn. Suspect
a hang only after two complete windows in which exact-PID CPU/state,
heartbeat mtime/age, recursively scoped descendants, logfile mtime, and both event counts are all idle/stale;
return those receipts as `pipeline-bug` and do not kill the process.
Never use a qid-only `pgrep`
(the watcher self-matches), `tail -F | grep` (it misses sparse/new files), or routine messages to main.
Attach to main's already-running cold-start PID; D does not cold-launch. Only when D resumes, launch the long
TS node with `setsid`, `source tools/scripts/node_env.sh` inside the detached shell, stdout/stderr redirected under the
run's `logs/`, and `causalsmith research --resume <qid> <spec> [--auto iff dispatch auto_mode=true]` (add `--from-stage` only when the
cursor rules below explicitly authorize replay). Never pipe the command. The managed D agent stays in its
turn and polls the watcher. D0 routinely takes many rounds; that is why the lease exists.
**But resume authority is ALL you get — terminal authority is main's:** you never bank, never stop/SIGINT
the process, never cross the D/F boundary, never touch F. You resume ONLY into D-stages. You **return the
lease to main** (stop resuming; hand back one directive) at exactly: the D0.5→F1 go/no-go, any terminal /
cap / citation / codex / pipeline block, or — if you feel yourself degrading — a `request-reseed` — each with **verbatim
receipts except the receipt-free `request-reseed`.** (An F→D `rewind:fix-source` is main's to order; if main dispatches YOU to execute one, you do
it within your D-lease — you never *emit* a rewind.) Shared recipes: [`.claude/skills/causalsmith-shared/reference.md`](../causalsmith-shared/reference.md).
For D, this skill's watcher, cursor, and process-ownership rules override generic watcher/death-recovery
examples in that reference, including its 15-second/per-event recipes.

**Re-ground first (every dispatch):**
Run every CLI below from `<AUTOID>/CausalSmith` after `source tools/scripts/node_env.sh`. Read
`npx --prefix tools tsx tools/bin/decision_log.ts read <qid> <spec> --phase D`, `state.json`, the last
`pipeline.jsonl` event, and the heartbeat/PID once. Do not duplicate a live resume or re-suggest a failed
construction. At each halt/action, append one combined `judgment` entry
`{type:"judgment",phase:"D",stage,round,tried,codex:"n/a",why}`; a real math judgment uses the consulted
payload in `codex`, never `n/a`. Below, `bin/x.ts` abbreviates
`npx --prefix tools tsx tools/bin/x.ts`, and `causalsmith research` abbreviates
`npx --prefix tools tsx tools/bin/causalsmith.ts research`.

**Shorthand:** `{resume}` below means **you run the cursor-appropriate resume yourself** (normally plain
`--resume`; add `--from-stage` only for an explicitly authorized replay/reroute). It is NOT a message to main. Only a *lease-return* (an
`{escalation:…}`) goes to main.

**Resume cursor discipline.** Plain `--resume` advances from the last successfully completed stage;
`--resume --from-stage <stage>` deliberately reruns that named stage. In particular, after an operator
SIGINT with `stage_completed="-1.2"`, `last_draft_status="completed"`, and no `angle_checkpoint`, use plain
`--resume` so D-0.5 reviews the authored draft. Never use `--from-stage D-1.2` there: it replaces the
unreviewed draft with a new version. Use D-1.2 re-entry only for an intentional redraft, after a sanctioned
fresh-angle reset, or when a persisted verdict/directive explicitly routes back to the proposer.

## The read-then-act discipline

At every halt: **READ the verdict BODY**, not just its `status` (`tail` the raw file, never full Codex
stdout). Classify: **revise-iteration** (a `revise`, or *different* load-bearing defects resolving
across rounds = convergence through a hard problem) → apply the scoped lever and `{resume}`. A repeated
defect demands a root fix or cap handoff, not automatic terminal classification. Terminal means the
specific terminal cases below (laundering, no faithful repair, or unsalvageable floor failure). Put the
classification and chosen lever in the same halt/action `judgment` entry.

## Per-stage event → action

**D-1 proposal** (`stage_neg1`). Duplicate / not-novel AND revises exhausted → return
`terminal:proposal-no-pass`; main decides the bank. A single revise is iteration. Prompt fix → flag `pipeline-bug`
(main edits `discovery/prompts/stage_neg1_*`). A recurring revise-round drift the automatic Stage 0.5
rejection context isn't fixing (a literature-grounded reframe, a donor/witness to anchor the kernel to)
→ inject a directive via **`bin/dneg1_directive.ts <qid> <spec> --directive "…"`** (mirrors
`d0_directive.ts`: appends `{angle,version,directive}` to `discovery/dneg1_escalation_log.jsonl` — NEVER a
hand-append). It accumulates across drafts of the current angle; an angle switch excludes old-angle steers,
and a fresh-angle reset removes the log. Then `{resume}`.

**D-0.5 CLI checkpoints (load-bearing).** The node halts after every `REVISE` *before* starting the
next proposer. Read/consult the verdict, then persist the repair and continue atomically with
`causalsmith research --angle-action continue <qid> <spec> --angle-directive - [--auto iff auto_mode=true]` (directive on
stdin). At an `angle-boundary` checkpoint, YOU choose from the receipts: `switch`,
`retry --extra-revisions N`, or `give-up`. You may execute `switch`; you may execute a bounded `retry`
only with a concrete non-identical root directive in the same command and must log the granted extra
count. This persisted per-angle retry is the sole D-1 exception to the general main-only cap-reset rule.
Choosing `give-up` means no viable proposal angle remains: return `terminal:proposal-no-pass`; main executes
the irreversible action/bank. Classify `stage_neg1_fallback` by its body: final duplicate/novelty NO-PASS is
terminal; environment/tooling failure or a retryable pivot/cap obstruction is `cap-block` or `codex-blocked`
as its receipt indicates. The same defect after one bounded retry, or retry without a root change,
returns `cap-block` to main. Never use plain `--resume` while `angle_checkpoint` is present.

**Pipeline math calls:** keep the long-lived D-orchestrator at **medium** for coordination. Dispatch a
separate `gpt-5.6-sol` **high** consult for every required mathematical judgment; do not inflate the
orchestrator's effort/context to perform it inline.

**When this skill is running under Codex, every such consult MUST use the managed collaboration channel**
(`spawn_agent`, with explicit model/effort; reuse via `followup_task`). This applies to proposed-change
adjudicators, maximality checks, D0.5 boundary auditors, literature/source auditors, and all other fresh
consults, including read-only ones. Never invoke `codex exec` through Bash from the D orchestrator, and
never fall back to it because managed slots are occupied—wait for a slot or return the appropriate
skill-defined escalation. Only the TypeScript pipeline may launch its configured `codex exec` workers and
reviewers internally.

For a proposed-change checkpoint, hand codex the canonical
`proposal_review_packet.json` in full (it contains the whole current paper/core, every same-round delta,
and `provisional_proofs`; obey its `contract` field so those payloads replace stale `core.json` proof text
for adjudication), plus the checkpoint and source proposal JSON for traceability. Never adjudicate from
`core.json` alone. For other calls hand the `.tex`/note /
`open_obligations` JSON (+ the literature recipe for an open_obligation, consulted FIRST); relay its
call verbatim into the mechanical step and `{resume}`. You STILL enforce the faithfulness guards —
codex does NOT override a faithfulness stop. **If the harness DENIES/cancels the codex dispatch, return the
lease with `{escalation:"codex-blocked", receipts:[…]}` — do NOT substitute your own math judgment for the
codex call you were required to make** (shared reference § "A DENIED / CANCELLED codex call is an
ESCALATION, never a silent pivot"; main takes it to the user).

**MANDATORY for EVERY math/judgment call at D0/D0.5** — proposed-change adjudication, open_obligation
construction, the **`D0 MAXIMALITY CHECKPOINT`** judgment, any math escalation (claim unreachable / converse
a wall / rate unimprovable / target adjust), and the D0.5 verdict. Each such `judgment` log entry MUST carry
a real verbatim `codex` field, NOT `n/a`. `n/a` is only for classifying a pipeline reviewer's PASS/REVISE
with no math judgment. About to write a maximality/reachability/adjust conclusion with `codex:"n/a"`? STOP —
that decision goes to codex first.

**D0 solve — three mathematical checkpoint classes** (proposed changes are never auto-applied).
Mechanical citation/cap halts are handled under D0.5 review below. Repair within D while a faithful
same-topic result remains:
1. **proposed-change** — `direction:"narrow"` (claim too strong → narrow toward truth, never
   weaken-to-prove) or `direction:"correct"` (a constructed-object formula mis-specified → fix the
   formula; NEVER a class def, never gerrymander to the proof's objects). Adjudicate whether the proposal
   is a faithful narrowing/formula correction; a wrong current claim routes to repair unless no faithful
   same-topic result exists. Preview with `bin/d0_apply_change.ts <qid> <spec> ... --check`, then apply. Prefer
   repeatable `--id <kind-qualified-id>` (comma-safe); use `--all` only when every variant is accepted.
   If any variant/mandate is accepted, include it in one apply; that consumes the whole bundle, so do not
   discard afterward. Only when every variant and mandate is rejected, cancel each outstanding mandate with
   `bin/d0_cancel_mandate.ts <qid> <spec> --mandate-id <d0m:id> --reason "<review rationale>"`, then use
   `--discard-all --note "<why>"`. Never leave proposals live.
Ownership/conflict warnings in D0 output (`quarantined`, `sole-emitter fallback`, `withheld`,
`cross-unit id collision`) are NON-FATAL adjudications: the round committed everything else. Act on the
checkpoint's conflict list by naming one canonical owner in a `d0_directive` scoped to just the withheld
ids; never treat these warnings as a crash or rewind the round.

A non-semantic D0 fatal is cheap to resume: within one accepted proposal revision, `{resume}` replays
each unchanged unit's persisted validated output with NO new model calls (`reusing the persisted validated
output` in the log; receipts under `discovery/solve_receipts/`, cleared on commit/apply). Re-solve only
units reopened by a new directive, an applied D0 change, or a moved core. A new D-1.2 proposal revision is
the exception: it invalidates ALL carried D0 proofs and starts a cold solve against the new source. Diagnose
the fatal first; to force a fresh sample of an otherwise unchanged unit, delete its `solve_*.json`.
An exact-target directive dispatches ONLY the open components it names (unrelated open components are
deferred, logged as `deferring unrelated open component`); name every component you want re-solved.
An undirected `{resume}` re-pays EVERY open component, including stuck ones whose context has not
changed — a blind re-attempt that rarely closes anything. Treat it as a deliberate full-frontier
sweep, never the default way to continue: drive stuck components through directives that add
direction (literature construction, reframing, simpler standard route), and sweep undirected only
when you actually want every open component re-attempted with fresh sampling.

2. **open_obligation** (`discovery/open_obligations.json`) — a load-bearing step that won't close from
   frozen primitives. Provide a **direction**, not a blind re-solve: **consult the literature FIRST**
   (bibliography → focused agent on ar5iv/LaTeX source, PDFs unreliable) to extract the concrete
   construction, inject it as a directive via **`bin/d0_directive.ts <qid> <spec> --directive "…"
   --require-core-target <node-id>`** (repeat `--require-core-target` for every named proof/repair node;
   never send a node-specific math repair unscoped, because an unscoped directive intentionally opens
   the whole core and wastes a solve on unrelated valid nodes). This appends
   the standalone `{round,changed:[],directive}` entry to `discovery/d0_escalation_log.jsonl` — never hand-append —
   then `{resume}`. A construction's repeated failure ≠ impossible: swap to the SIMPLEST standard
   construction (plain estimator + standard named assumptions) before declaring a wall. Diagnose and fix a
   bad setup from I/O receipts; never override contrary pipeline evidence with an unaudited hand judgment.
3. **`D0 MAXIMALITY CHECKPOINT`** (clean discharge, run halted) — proved ≠ best paper. **CONSULT CODEX
   FIRST — this judgment is a mandatory codex call, not an eyeball.** Hand codex the full discharged
   `.tex`/note and ask the WHOLE-paper maximization question: is there a sharper bound, better
   construction, stronger reframing, a tier-relevant rate/constant, or an elbow the current statement misses? **Ask the
   class question explicitly:** read the anchor paper's own hypotheses (not the note's description of them) and decide
   whether the note's class IS the published one; if not, whether the claim restates over it, or an inclusion transfers
   it. A converse proved on a subclass transfers up for free and is usually the cheapest tier gain available. If codex
   surfaces a concrete improvement that passes the materiality filter below, apply it only if it already exists as a solver-authored proposal;
   otherwise inject it through `d0_directive`. Then `{resume}` to
   re-solve; only once codex confirms no material room `{resume}` into D0.5. **Default to IMPROVING**; pull to
   a weaker tier only when codex confirms material improvement is genuinely impossible. A material,
   tier-relevant open rate/constant → phrase
   as a construct-and-determine `conj` and let codex derive it; never hard-code a guessed exponent. Log
   the maximality decision with codex's verbatim finding in the `codex` field (NOT `n/a`).
   **Materiality filter:** pursue broad improvements that strengthen the headline, construction, scope, or
   achieved tier. Do not iterate a small coefficient/constant/local refinement unless sharp constants are
   themselves the main contribution or the refinement could materially change the tier.
   - **Any directive that changes the headline/positioning MUST also tell the solver to SYNC THE PROSE
     FIELDS** (`tldr`, `project_justification.{gap,niche,fill}`, `related_work`) to the new headline. The
     D0 change-apply loop has NO prose channel and D0-RENDER emits prose verbatim, so a reframe otherwise
     ships a stale over-claim (a `PROSE-DRIFT` warning in the RENDER output flags exactly this — treat it as
     must-fix). Demoting an object to an `oeq:`/conjecture means the prose must stop calling it
     determined / matched / sharp / a "frontier" and lead instead with what IS proved.
   - **Adjust the target, never trivialize it.** When the headline as posed is genuinely unreachable
     under the standard assumptions, do NOT leave that side OPEN and do NOT strengthen an assumption to
     keep the strong claim. Adjust the target to the strongest honest result still reachable under the
     SAME assumptions and bank *that*: Stat → an honest two-sided rate bracket (or a best obtainable
     bound where they don't match); PartialID → an outer bound flagged non-sharp (sharpness as residual
     OEQ); Panel/ExactID → target + named contamination, or a partial-ID relaxation. The forbidden
     shortcut is adding a nonstandard / crux-encoding assumption to force the stronger target
     (laundering — caught at D0.5). A derived best-available nontrivial result beats both an OPEN gap and
     a strong-but-laundered claim.

**Pick the CLI by WHO AUTHORED the bytes.** `d0_apply_change` = vote yes/no on solver-emitted variants in
`d0_working.json:proposals`. `d0_directive` = the change is YOURS; it mutates nothing and the solver authors it AND
re-proves it. `d0_author_edits` = your own PROOF-IRRELEVANT statement prose ONLY (justification/gap/consumer
on a non-cited, non-partial node) lands directly through the same apply gate with no solver round, no stage
rewind, and no reopened proof; everything else — claims, dependencies, declarations, status, source, symbols,
bibliography, the comparator table, cited leaves — is refused there and goes through `d0_directive`. Never
draft your own accepted claim through apply. Disposal also goes through
`d0_apply_change`: a single apply selects accepted variants, records drops in `--note`, and consumes the
bundle. If all are rejected, cancel every outstanding exact mandate with `d0_cancel_mandate`, then
`--discard-all --note`. A directive alone does not clear `working.proposals`.

**`partial` = re-derive flag, NOT proof deletion.** An applied claim change clears its node-level proof and
marks the durable record partial; a metadata-only edit preserves a proof when its proof-relevant basis stays
valid. The record-level prior proof survives invalidation (frozen and carried nodes alike) and returns next round as `PRIOR PARTIAL PROGRESS …
EXTEND this`, labeled with the previous statement text when the claim has moved. Staleness propagates
along `depends_on` to a fixpoint. For a non-cited node, an accepted `argues_proposed:true` proof can attach
in the same apply and avoid a re-solve. A reopened `status:"cited"` node ALWAYS owes the base D0 contract's
complete byte-faithful `added_lemmas` revalidation receipt, including its exact source and current metadata.
Do not replace that receipt with a no-op `statement-replace`. Displaced
proof bytes are never lost: every overwrite/delete is copied to the cold append-only
`discovery/proof_archive/` (objects by sha256 + `index.jsonl`; never read by dispatch — restore is a
manual act naming a hash).

**A working-state record with no `node` key is proto-frozen, not unproved** — its definition lives in
`proto_core.json`. Reading `rec.node.status` on those returns undefined and miscounts proved nodes. Likewise a
carried record's `node.status` is the AUTHORED carrier status and stays `to-prove` after its proof lands; the
effective status is what `core.json` renders (a record without `partial` is settled). Never direct a
`[STRUCTURED CORE CHANGES REQUIRED]` round to "promote" a node `core.json` already shows `proved`: merge
discharges the re-emitted proof as a duplicate and the round aborts fail-closed — cancel the mandate instead.

**A third option besides "prove it" and "retract to an OEQ":**
`bin/d0_maintain.ts <qid> <spec> --assumption ass:<id> --reason "..." --open-object "..." --separate-object "..."`
marks a frozen
proto assumption MAINTAINED — a disclosed high-level condition the note is stated CONDITIONAL on and does
not derive. This is the sanctioned slot for "proved under condition A, where verifying A is itself the open
object", and it is the legitimate alternative to the laundering shortcut. It restates every consuming
theorem explicitly conditional on the assumption; D0.5 then checks only the assumption's SOUNDNESS and
SEPARATENESS, and caps the tier one notch. The solver may NEVER self-serve it — it is an accountable
orchestrator judgment.

**Recovery, when a round is interrupted rather than wrong:** `bin/d0_rebuild_review_packet.ts <qid> <spec>` is a
mechanical no-solver recovery: it rewrites `d0_working.json:proposals` and the review packet, but not the
frozen proto, and consumes no solve round. `bin/reset_proposal_cursor.ts <qid> <spec>
--angle N` re-seats a D-1.2 cursor after a cap-exhausted NO-PASS so a bumped-cap resume continues a good
angle instead of re-entering the dead one.

**Reroute only mathematical work.** Re-dispatch D0 only for new mathematics, claim authorship, or reproof.
After math acceptance, use deterministic apply/rebuild first. If it cannot fix a small, unambiguous mechanical
defect (for example LaTeX/serialization, carrier drift, ordering, or derived metadata), D may `apply_patch` every
identical live D carrier; preserve the adjudicated semantic post-image, never edit `proof_archive`/`_bank`, and
never change a claim/formula by inference. Do not add content-guessing normalization for a one-off typo. Patch
pipeline code only for a reproducible, non-heuristic mechanical invariant, with a focused regression. Log exact
before/after, run the relevant replay/schema/render/tests, and continue without re-solving. Return `pipeline-bug`
only when the repair is ambiguous, semantic, architectural, or cannot be verified locally.
At the live D0 boundary, a valid persisted artifact wins over a malformed stdout receipt and common JSON/TeX
carrier defects are normalized deterministically; only a still-untrustworthy artifact counts as a failed model
call and permits one retry of that same solve unit—never a separate clerical-model pass over accepted mathematics.

**D0 context is local and automatic.** Every solve unit, including the prose/cross-cutting owner, receives only
its target/upstream statement closure and the referenced assumption/definition/symbol closure inline. A compact
omitted-id manifest and read-only content-addressed full-core snapshot are available for selective lookup when
the local job genuinely needs more; do not paste the whole core into a directive. Established dependencies are
receipts rather than repeated proof bodies, while prior target proofs and partial progress remain inline so a
repair extends rather than restarts. D-orchestration—not the Sol worker—normalizes and validates JSON/TeX/ids;
only a still-untrustworthy carrier permits one same-unit retry. When diagnosing an omission, inspect the exact
snapshot path/hash recorded in that worker's prompt log before rerouting mathematics.

**D renders source; it does not compile PDFs.** `D0-RENDER` publishes the deterministic `.tex` preview only.
Never run or require `pdflatex` in D, and never reroute mathematics for layout/package/compile errors; defer those
to the paper/publication stage. D0.R edits `core.json` only; its provisional rounds do not render or roll back `.tex`.
The pipeline republishes the preview once after the complete D0.5 gate passes. Repair in D only when a structural
carrier defect changes or obscures mathematical content.

**Proposal selectors are independent channels.** Use `statement:<id>`, `core-edit:<id>`, or an exact kind
such as `statement-replace:<id>`; bare id selects every channel. Same-node claim and metadata variants may
be selected together when the packet adjudicator found the combined post-image coherent. A
`statement-replace` is warranted only for a concrete dependency/metadata delta. For `free_symbols`, name
the exact registered `symbols[].name` spellings and require any missing `symbol-add` in the same atomic
directive; never require a byte-identical replacement merely to acknowledge the new revision.

**D0.5 rotation is not itself terminal.** For recurring hygiene/positioning findings, replace one-at-a-time
patches with one whole-core audit: minimal hypotheses, domains, dependencies, normalization, and the
complete close-comparator set. If a wholesale root repair still rotates, return `cap-block` with receipts;
main decides whether any terminal classification is justified.

**Vet the D0.5.G directive before acting on it.** `improvement_directive` / `ceiling_directive` are
math claims from a taste-first referee that is weaker at math than at judgment — put each through the
consult below for soundness before routing it into a D0 re-solve or an `--upgrade`, and repair it if it
fails. Never let one alone justify abandoning a lane: a wrong "already settled" kills work that a wrong
"try X" would only cost a re-solve.

**D0.5 review:** delegate every boundary judgment to a fresh `gpt-5.6-sol` high consult, then classify the persisted
checkpoint precisely:

- `PASS` + tier at/above floor → return `go-no-go` with the maximized-paper summary. Never enter F.
- `FAIL`, D0.R escalation/non-convergence, or a salvageable below-floor directive → fixable D0
  re-derivation by default. Use the already-injected review payload plus one concrete scoped
  `d0_directive`, then re-enter D0. A wrong claim is not terminal while an honest same-topic repair exists.
- `d0_loop_cap_hit` / D0.R cap → return `cap-block`; only main may clear it, and only after a recorded
  root change. Include the flag, counters, halt, and attempted root fix.
- `CITATION VERIFICATION REQUIRED` / `cited-source-unverifiable` → return `citation-verification` with
  node ids, source/locator, and verbatim access failure. Main obtains lawful source evidence and uses
  `bin/d0_attest_cited_source.ts`; do not re-solve mathematics or invent a transcription.
- Below floor and explicitly not salvageable in scope → `terminal:below-floor`. State whether panel
  findings remain unrepaired; never present a triage-only halt as a sound downgraded result.
- Laundering/kernel substitution, or a false headline with no faithful same-topic repair after consult →
  the corresponding terminal escalation.

## Faithfulness (D-side)

Detect laundering / kernel-substitution at D0.5 (a premise that is the crux; a kernel silently
substituted; strengthen-to-prove). A catch is NOT yours to bank — **escalate** it: `terminal:laundering`
(claim laundered) or `terminal:tex-claim-wrong` only when the `.tex` claim has no faithful same-topic
repair, each with the `.tex` audit receipt. Otherwise route the defect back to D0. Your authority is to
detect and prove the defect, not to execute the irreversible bank.

## Returning the lease to main

A within-phase continue is NOT a message to main — you hold the lease, so you just
run the cursor-appropriate resume yourself and keep going. Default to plain `--resume`; use `--from-stage`
only for an explicit persisted reroute/replay. You come back to main ONLY to **return the lease**: append
`{type:"escalation",phase:"D",from:"D",subtype:"<type>",receipts:[...]}` and STOP resuming. Use
`request-reseed` only for a concrete context-capacity problem, never silence/timeout/routine monitoring —
main respawns a fresh D-orch for the same phase and re-grants the lease. Required receipts:

| Escalation | Receipts |
|---|---|
| `go-no-go` | maximized-paper summary + panel/novelty verdicts |
| `terminal:proposal-no-pass` | exhausted angle/version counts + final proposal and reviewer duplicate/novelty receipts |
| `terminal:tex-claim-wrong` / `terminal:laundering` | the `.tex` line + the reviewer phrase naming the collapsed conjecture |
| `terminal:below-floor` | panel + cold-tier verdict, floor, salvageability, and unrepaired-findings caveat |
| `cap-block` | exact persisted flag (for example `stage_neg1_fallback`, `d0_loop_cap_hit`, or `stage0_budget_exhausted`), counters, halt, and attempted root fix |
| `citation-verification` | node ids, citation/locator, and verbatim source-access failure |
| `codex-blocked` | verbatim denial, exact command, and purpose |
| `pipeline-bug` | mapping/contract failure: agent-I/O diff (EMITTED vs PERSISTED) + recurrence count; suspected hang: two-window PID/heartbeat/descendant/log/event liveness receipts |

## Recording (decision_log)

Append via `npx --prefix tools tsx tools/bin/decision_log.ts append <qid> <spec> --json '<entry>'`. Per halt/action, append one `judgment` entry
(`{type:"judgment",phase:"D",stage,round,tried,codex,why}`) — note what you tried and, on failure,
"do NOT re-suggest". For an agent-output `pipeline-bug`, compare the model's emitted bytes with the
persisted bytes; a suspected hang instead uses the two-window liveness receipts above. A correctly rejected omission/no-op is an orchestration or model-compliance failure:
correct the scoped directive once; never weaken the gate. A mapping/drop or a recurrent general contract
failure is a pipeline bug. This log is what a re-seeded D-orch reads to avoid re-walking dead constructions.
