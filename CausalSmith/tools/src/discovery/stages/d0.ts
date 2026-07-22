// Typed-core D0 phase wiring (the only D0 path).
//
// D-1.2 emits a `proto_core.json` and D0 runs the typed path:
//   stage "0"   → runStage0Typed   = D0-SOLVE then D0-RENDER
//   stage "0.5" → runStage0_5Typed = typed D0.5 review ↔ directed D0.R revise loop
// Maps each to a StageResult the pipeline loop understands. A D0-SOLVE proposed
// statement change, or a D0.5 `fail` / revise-cap exhaustion, surfaces as a
// checkpoint (advance:false) — the human/orchestrator resolves it.
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { readFile, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import { appendReview, artifactPaths, type StageDeps } from "../../pipeline_support.js";
import { runStage0Solve } from "./d0_solve.js";
import { runStage0Render } from "./d0_render.js";
import { runStage0_5Core } from "./d0_5_core.js";
import type { Stage0_5CoreResult } from "./d0_5_core.js";
import {
  runGeneralReview,
  buildGeneralTierVerdict,
  tierRank,
  TARGET_FLOOR_LABEL,
} from "./d0_5_general.js";
import { runStage0RCore } from "./d0_r_core.js";
import { coreJsonPath } from "./d0_core.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import { resolveInDir } from "../../paths.js";
import { saveState } from "../../state.js";
import {
  readProposedChanges,
  coreEditTarget,
  type RawChange,
  type RawAssumption,
  type RawCoreEdit,
} from "./d0_apply.js";
import {
  loadWorkingState,
  saveWorkingState,
  pruneOrphanLemmas,
  findDanglingCitations,
  appendEscalationLog,
  readEscalationLog,
  type WorkingState,
} from "./d0_working.js";
import { type Core, CoreSchema } from "../core/schema.js";
import { readTypedCore } from "../core/core_io.js";
import {
  loadSemanticManifest,
  validateCoreManifest,
  validateRenderedManifest,
  validateWorkingManifest,
} from "../semantic_manifest.js";

export function citationVerificationCheckpoint(review: Stage0_5CoreResult): StageResult | null {
  if (review.citation_verification_required.length === 0) return null;
  return {
    stage: "0.5",
    status: "checkpoint",
    advance: false,
    message:
      "CITATION VERIFICATION REQUIRED — D0.5 could not retrieve the source of record for: " +
      review.citation_verification_required.map((c) => c.node_id).join(", ") +
      ". This is not revise/fail. Main must try a lawful source (arXiv/author copy/repository); " +
      "if unavailable, ask the user for the cited page or exact theorem statement, persist it as " +
      "source.verbatim_statement with provenance, then rerun D0.5. Agent memory is not verification.",
  };
}

/** Max directed D0.R revise rounds before the typed D0.5 loop checkpoints.
 *  Default 3: D0.R now OWNS the dependency graph / wiring (add/drop `depends_on` edges,
 *  re-route lemmas, faithful def-alignment) and fixes those in place durably — a passed
 *  D0.5 advances with no re-solve (see stage0_R_core prompt). So the common trailing
 *  D0.5-referee class (redundant/hidden dependency, redundant-assumption-declaration) is
 *  genuinely in-place-fixable, and the extra round closes the graph-hygiene tail instead
 *  of escalating. STATEMENT/CONCLUSION findings (overclaim / ill-typed target / narrow-a-
 *  premise) stay OUT of D0.R scope — it escalates those to the orchestrator (a proto edit),
 *  so they do not thrash the revise budget. The no-net-progress / persistent-finding
 *  backstops still escalate immediately when a round makes no headway (see the loop in
 *  runStage0_5Typed). Override via `CAUSALSMITH_D0_REVISE_CAP`. */
export const D0_REVISE_CAP = (() => {
  const v = parseInt(process.env.CAUSALSMITH_D0_REVISE_CAP ?? "", 10);
  return Number.isFinite(v) && v > 0 ? v : 3;
})();

/** Persist the exact review payload before returning any D0.5 checkpoint that
 * routes back to D0. The content hash makes retries idempotent, and typed target
 * ids keep the next D0 solve off unrelated valid nodes. */
async function injectD0ReviewDirective(args: {
  ctx: PipelineContext;
  reason: string;
  payload: unknown;
  targetIds?: string[];
  /** Record the verdict WITHOUT making it a re-solve directive. See
   *  `EscalationLogEntry.provenance_only` — an untargeted directive force-opens the whole
   *  paper, so bookkeeping entries must opt out explicitly. */
  provenanceOnly?: boolean;
}): Promise<string> {
  // Fingerprint the WHOLE dispatch, not just the payload.
  //
  // Hashing `payload` alone made the dedup actively harmful. The `fail`,
  // persistent-finding, no-net-progress and cap-exhausted call sites all pass the
  // identical payload shape {stage, overall, verdicts}, so the second to fire was
  // suppressed along with its materially different `reason`. Worse, a verdict that
  // is byte-identical across rounds IS the persistent-finding case — the strongest
  // signal in the system ("this survived a full re-derivation") was the one most
  // certain to be dropped. Including reason, targets and round keeps genuine
  // re-delivery while still collapsing a true duplicate append.
  const working = await loadWorkingState(args.ctx);
  const encoded = JSON.stringify({
    payload: args.payload,
    reason: args.reason,
    targets: [...(args.targetIds ?? [])].sort(),
    round: working?.round ?? 0,
  });
  const fingerprint = createHash("sha256").update(encoded).digest("hex").slice(0, 16);
  const marker = `[D0.5 REVIEW ${fingerprint}]`;
  const prior = await readEscalationLog(args.ctx);
  if (prior.some((entry) => entry.directive?.includes(marker))) return marker;

  const core = await readTypedCore(coreJsonPath(args.ctx));
  const targets = partitionReviewTargets([...(args.targetIds ?? [])], core);
  const requiredCoreTargets = targets.required;
  await appendEscalationLog(args.ctx, {
    round: working?.round ?? 0,
    changed: [],
    directive: [
      `${marker} ${args.reason}`,
      "The following is the complete current reviewer payload. Treat every finding as directed D0 input;",
      "repair the same paper and do not substitute a different target.",
      // Targets D0 cannot bind to an exact-emission check are named explicitly rather
      // than dropped: a finding on a def:/ass: node is still directed input, and the
      // orchestrator must be able to see that it was raised but is unenforced.
      ...(targets.nonStatement.length > 0
        ? [
            `UNENFORCED TARGETS (non-statement core nodes — repair these too; D0's exact-target check ` +
              `cannot bind them): ${targets.nonStatement.join(", ")}`,
          ]
        : []),
      ...(targets.unknown.length > 0
        ? [
            `UNRESOLVED TARGETS (named by a referee but present in no core store — treat as a reviewer ` +
              `id error, do NOT invent these nodes): ${targets.unknown.join(", ")}`,
          ]
        : []),
      JSON.stringify(args.payload, null, 2),
    ].join("\n"),
    ...(requiredCoreTargets.length > 0 ? { required_core_targets: requiredCoreTargets } : {}),
    ...(args.provenanceOnly === true ? { provenance_only: true } : {}),
  });
  return marker;
}

function reviewTargetIds(review: Stage0_5CoreResult): string[] {
  return review.verdicts.flatMap((verdict) =>
    verdict.findings.flatMap((finding) => finding.node_id ? [finding.node_id] : []),
  );
}

/** Max incomplete proof-carry rounds in D0 before checkpointing. Proposed changes halt immediately. */
export const D0_SOLVE_CAP = (() => {
  const v = parseInt(process.env.CAUSALSMITH_D0_SOLVE_CAP ?? "", 10);
  return Number.isFinite(v) && v > 0 ? v : 15;
})();

/** Heuristic: does a proposed statement REWRITE convert the node's own load-bearing
 *  claim into an ASSUMED hypothesis of itself — "X holds" → "Suppose X (or the hard
 *  property that delivers X). Then [a now-trivial reduction]"? That is an assume-the-crux
 *  narrowing (a laundering-adjacent move): it promotes the open proof obligation into a
 *  premise instead of restricting scope/regime. Detected by a new leading conditional
 *  premise ("Suppose/Assume … such that / with …", or a new leading Assume/Suppose clause)
 *  that the prior statement did not have. Conservative — false positives route to review. */
export function isAssumeTheCruxNarrowing(c: RawChange): boolean {
  const prem = /\b(suppose|assume)\b[^.]*\b(such that|with|so that)\b/i;
  const leadingPrem = /^\s*(suppose|assume)\b[^.]*\./i;
  const leadingClause = (s: string | undefined) => s?.match(/^\s*(?:suppose|assume)\b[^.]*\./i)?.[0] ?? "";
  const addedPremise = leadingClause(c.proposed).trim();
  const currentText = c.current ?? "";
  const cruxProofObject = /\b(chi[-\s]?square|χ²|least[-\s]?favo[u]?rable|separation|le\s*cam|fano|two[-\s]?point|packing|testing|witness|construction|family)\b/i;
  const regimeWhitelist = /^\s*(suppose|assume)\b[^.]*\b(regime|setting|case|class|model|iid|i\.i\.d\.|independent|compact|finite|measurable|overlap|positivity|regularity|smooth|margin|sparsity|sub-?gaussian|well-specified|realizable|bounded|support|moment|integrable|dominated|tail|continuous|differentiable)\b[^.]*\./i;
  const hadPremise = c.current !== undefined && prem.test(c.current);
  const hasPremise = prem.test(c.proposed);
  const hadLeadingPremise = c.current !== undefined && leadingPrem.test(c.current);
  const hasLeadingPremise = leadingPrem.test(c.proposed);
  const addedCruxPremise = addedPremise.length > 0 && !currentText.includes(addedPremise) && cruxProofObject.test(addedPremise);
  if (addedCruxPremise) return true; // why: generic words like bounded/family cannot whitelist proof-object premises that buy the crux.
  // AUDIT-B: whitelist only obvious regime restrictions; uncertain leading assumptions gate for review.
  return (hasPremise && !hadPremise) || (hasLeadingPremise && !hadLeadingPremise && !regimeWhitelist.test(c.proposed));
}

/** The DUAL of assume-the-crux: a narrowing that DROPS the node's load-bearing RESULT
 *  (a minimax/lower-bound risk assertion, an equivalence, or an iff) — keeping only an
 *  easy surviving fragment — and would then be marked "proved". This degrades the result
 *  class (the anti-laundering case in the open-kernel re-tiering rule) and must be gated:
 *  the result belongs in the node (open if unproven), not silently removed to discharge.
 *  Detects a load-bearing construct present in `current` but absent in `proposed`. */
export function isResultClassDegradation(c: RawChange): boolean {
  if (c.current === undefined) return false;
  // load-bearing result constructs (minimax risk bound, equivalence, iff)
  const constructs: RegExp[] = [
    /inf[_{\s].*sup[_{\s].*\bE_?P?\b/i, // inf_hat sup_P E|...|  (a minimax-risk assertion)
    />=\s*c[_0-9]*\s*R_?n?\^?\*/i, //  >= c R_n^*  (a lower-bound on the rate)
    /\bequivalent\b.*\bR_?n?\^?\*/i, // "equivalent ... to R_n^*"
    /\bif and only if\b|\biff\b/i,
  ];
  for (const re of constructs) {
    if (re.test(c.current) && !re.test(c.proposed)) return true;
  }
  return false;
}

/** Classify D0-SOLVE proposed changes for a checkpoint message.
 * Every proposed change is gated; only the orchestrator may adjudicate and
 * explicitly apply it with d0_apply_change. */
export function partitionProposedChanges(
  proto: Core,
  statements: RawChange[],
  definitions: RawChange[],
  assumptions: RawAssumption[] = [],
  coreEdits: RawCoreEdit[] = [],
): { auto: Set<string>; gated: Array<{ id: string; why: string }> } {
  void proto;
  const auto = new Set<string>();
  const gated: Array<{ id: string; why: string }> = [];
  for (const c of definitions) {
    gated.push({
      id: c.id,
      why: c.direction === "correct"
        ? "constructed-object definition correction requires orchestrator adjudication"
        : `definition change direction='${c.direction ?? "?"}' (expected 'correct')`,
    });
  }
  for (const c of statements) {
    if (c.direction !== "narrow") {
      gated.push({ id: c.id, why: `statement change direction='${c.direction ?? "?"}' (expected 'narrow')` });
    } else if (isAssumeTheCruxNarrowing(c)) {
      gated.push({ id: c.id, why: `assume-the-crux narrowing (${c.id}) — adds a new assume/suppose premise that may promote the open obligation into a hypothesis; review (state the result + leave the construction an open obligation, do not assume it)` });
    } else if (isResultClassDegradation(c)) {
      gated.push({ id: c.id, why: `result-class degradation (${c.id}) — drops the node's load-bearing result (minimax/lower-bound/equivalence/iff) to a surviving fragment; review + tier honestly (keep the result, mark it open if unproven, do not silently discharge a weaker claim)` });
    } else {
      gated.push({ id: c.id, why: "statement narrowing requires orchestrator adjudication" });
    }
  }
  for (const a of assumptions) {
    gated.push({ id: a.id, why: "new assumption requires orchestrator adjudication" });
  }
  for (const edit of coreEdits) {
    gated.push({ id: coreEditTarget(edit), why: `structured core edit '${edit.kind}' requires orchestrator adjudication` });
  }
  return { auto, gated };
}

async function renderAndComplete(args: { ctx: PipelineContext; state: StateJson; message: string; corePath: string }): Promise<StageResult> {
  // Orphan-lemma prune (safe ONLY here, on the clean discharge): drop lemmas no longer
  // reachable from any non-lemma claim — an abandoned proof route's helper lemmas would
  // otherwise leak into the rendered paper. Done BEFORE render so the .tex is clean.
  let pruneNote = "";
  // The core and the working state are read FAIL-LOUD, outside the best-effort
  // prune below. They were previously read inside it, with `coreForGate` assigned
  // as the try's last statement — so a failure reading a DIFFERENT file
  // (proto_core.json, the try's first statement) left `coreForGate` null and
  // silently skipped the cite-without-emit consistency gate entirely. That gate
  // exists precisely to avoid an expensive D0.5 repair round; disabling it on an
  // unrelated read error is the opposite of best-effort.
  const coreForGate: Core = await readTypedCore(args.corePath);
  const workingForGate: WorkingState | null = await loadWorkingState(args.ctx);
  try {
    const proto = await readTypedCore(protoCoreJsonPath(args.ctx));
    const core = coreForGate;
    const working = workingForGate;
    if (working) {
      const { pruned, protoOrphans } = pruneOrphanLemmas(core, working, proto);
      if (pruned.length > 0) {
        await writeFile(args.corePath, JSON.stringify(core, null, 2), "utf8");
        await saveWorkingState(args.ctx, working);
        pruneNote =
          `\nPruned ${pruned.length} orphan lemma(s) no longer reachable from any result: ${pruned.join(", ")}.` +
          (protoOrphans.length > 0
            ? ` Of these, ${protoOrphans.join(", ")} also live in the frozen proto — remove them from the proto to keep a re-solve from re-assembling them.`
            : "");
      }
    }
  } catch (err) {
    // Genuinely best-effort now: this catch covers ONLY the proto read and the
    // orphan prune. The gate below runs regardless, on an already-parsed core.
    console.warn(`[D0] orphan-lemma prune skipped: ${err instanceof Error ? err.message : String(err)}`);
  }

  // CONSISTENCY GATE (deterministic, ~0 cost): catch "cite-without-emit" dangling citations
  // — a proof that INVOKES a helper the solver never EMITTED as a member — at the cheapest
  // point, BEFORE the expensive D0.5 panel. Such a core reads as "fully proved" yet carries
  // an unproven step; without this gate it fails D0.5 and triggers a full repair re-solve
  // (PIPELINE_NOTES 2026-06-30). On detection: ONE capped, targeted self-heal (re-solve only
  // the citing node(s) with a directive to emit the missing member); if that does not clear
  // it, HALT with a precise defect — never loop / burn unbounded re-solves.
  {
    const dangling = findDanglingCitations(coreForGate, {
      alsoKnown: Object.keys(workingForGate?.resolved_oeqs ?? {}),
    });
    if (dangling.length > 0) {
      const citers = [...new Set(dangling.map((d) => d.node))];
      const missing = [...new Set(dangling.map((d) => d.ref))];
      const pairs = dangling.map((d) => `${d.node}→${d.ref}`).join(", ");
      // Counter lives in `flags.d0_loop_counters` (not `design_decisions`) so the
      // `d0_loop_cap_hit` cap gate can reset it. It was previously wedge-only: capped at 1,
      // stored where no CapGate `clear` could reach it, so once tripped the ONLY escape was
      // hand-editing state.json. `Number(dd[...])` also yielded NaN on a non-numeric value,
      // and `NaN < 1` is false — silently skipping the heal and going straight to the halt.
      const heals = d0Counters(args.state).consistency_heals;
      if (workingForGate && heals < 1) {
        for (const id of citers) delete workingForGate.solved[id];
        await saveWorkingState(args.ctx, workingForGate);
        await appendEscalationLog(args.ctx, {
          round: 0,
          changed: [],
          directive:
            `D0 CONSISTENCY GATE (auto-heal). The following proofs CITE ids that are NOT defined ` +
            `members of the core (cite-without-emit): ${dangling.map((d) => `${d.node} -> ${d.ref}`).join("; ")}. ` +
            `Re-prove the citing node(s) [${citers.join(", ")}] and EMIT every cited helper as a defined ` +
            `member (a lemma with its own proof), AND list it in the citing node's depends_on. Do NOT delete ` +
            `the citation to make it parse — supply the missing member. No proof may reference an id absent from the core.`,
          // TARGETED heal, structurally. Without explicit targets, the dispatcher's
          // untargeted-directive branch forces EVERY core statement open — a whole-paper
          // re-derivation for a defect this gate has already localized to `citers`
          // (observed: 3 whole-paper reopens in one run, each "reused 0 carried member
          // proof(s)"). The citing nodes are the exact repair frontier; the missing
          // helpers are emitted as additions under them.
          required_core_targets: citers,
          note: "auto-heal: cite-without-emit dangling citations detected at D0 discharge",
        });
        args.state.flags.d0_loop_counters = { ...d0Counters(args.state), consistency_heals: heals + 1 };
        args.state.stage_completed = "-0.5"; // rewind to D0-SOLVE (advance:false keeps this reset)
        return {
          stage: "0",
          status: "rewound",
          advance: false,
          completedStage: "-0.5",
          message:
            `D0 CONSISTENCY GATE — ${dangling.length} dangling citation(s) (${pairs}); auto-invalidated citing ` +
            `node(s) [${citers.join(", ")}] + emit-directive, re-solving BEFORE the D0.5 panel.`,
        };
      }
      // Cap reached (or no working state to target): do NOT loop. Halt for the orchestrator.
      // Raise the cap gate so the halt is a real circuit breaker with a CLI escape. Without
      // it this state was a permanent wedge: the cursor is pinned at "-0.5", so every resume
      // re-entered D0 and returned this identical checkpoint, and the counter lived where no
      // `--clear-gate` could reach it.
      args.state.flags.d0_loop_cap_hit = "D0 consistency-gate self-heal exhausted";
      return {
        stage: "0",
        status: "checkpoint",
        advance: false,
        message:
          `D0 CONSISTENCY GATE — dangling citation(s) persist after auto-heal: ${pairs}. The solver keeps ` +
          `citing un-emitted member(s) ${missing.join(", ")}. Orchestrator: invalidate the citing node(s) ` +
          `[${citers.join(", ")}] and inject a directive to EMIT the missing member(s), or rewind D0. Do NOT ` +
          `advance to D0.5 with a dangling core (it will fail the panel and force a full repair re-solve). ` +
          `Once repaired, resume with --clear-gate d0_loop_cap_hit.`,
      };
    }
  }

  const rendered = await runStage0Render({ ctx: args.ctx, state: args.state });
  // D0 → D0.5 MAXIMALITY CHECKPOINT. A clean discharge means the paper is PROVED, not
  // that it is the BEST paper — so HALT here (status "checkpoint") for the orchestrator
  // to review whole-paper maximality before the (expensive) D0.5 review. `advance` is
  // left default (true) so `stage_completed` becomes "0" and `--resume` proceeds to D0.5;
  // this is NOT a defect checkpoint (no proposed change / open gap) — it is the review gate.
  return {
    stage: "0",
    status: "checkpoint",
    message:
      `${args.message}; ${rendered.message}.${pruneNote}\nD0 MAXIMALITY CHECKPOINT — the paper is fully proved/discharged. ` +
      `Review whether the WHOLE paper is maximized (no room to improve) BEFORE D0.5; iterate D0 if not, ` +
      `else --resume to proceed to the D0.5 review. (No defect — this is the review gate, not an escalation.)`,
    artifacts: [args.corePath, rendered.texPath],
  };
}

/** Stage "0" (typed): the D0 SOLVE-REVISE loop. Solve → if it discharges cleanly,
 * render and complete. An incomplete proof-only round carries progress and retries;
 * every proposed change checkpoints for orchestrator adjudication before mutation. */
export async function runStage0Typed(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // Budget is CARRIED across resumes: `round` starts where the last invocation stopped.
  const solveStart = d0Counters(args.state).solve_rounds;
  for (let round = solveStart; round < D0_SOLVE_CAP; round++) {
    args.state.flags.d0_loop_counters = { ...d0Counters(args.state), solve_rounds: round + 1 };
    // Persist the increment BEFORE dispatch: a merge-gate throw escapes this loop and
    // the driver saves state only after a handler returns, so an in-memory-only
    // counter made every thrown round budget-free — a repeated mechanical abort
    // (e.g. an unsatisfiable exact-target directive) re-dispatched forever without
    // ever tripping the d0_loop_cap_hit circuit breaker.
    await saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);
    const solved = await runStage0Solve(args);
    // Clean discharge (Stage0SolveResult has no `status` field).
    if (!("status" in solved)) {
      return renderAndComplete({ ctx: args.ctx, state: args.state, message: solved.message, corePath: solved.coreJsonPath });
    }
    // GENUINE OPEN GAP — the solver isolated an obstruction it cannot close and asked
    // for guidance. Do NOT auto-loop (a blind re-solve reproduces it); return the
    // checkpoint so the orchestrator supplies a direction via the D0 directive.
    if ((solved.artifacts ?? []).some((a) => a.endsWith("open_obligations.json"))) {
      return solved;
    }
    // An incomplete-round checkpoint (some targets unproved, no proposed change) just
    // needs another solve pass — progress is saved, so continue the loop.
    // WITHHELD CONTENT halts, even with no proposals. A round can withhold a colliding
    // helper or an OEQ answer and emit no proposal at all;
    // the emptiness test below then continued the loop and the diagnostic was discarded,
    // so the run could later advance on a core the solver had already flagged.
    if ((solved.artifacts ?? []).some((a) => a.endsWith("withheld_content.json"))) {
      return solved;
    }
    // NOT a marker reason: a class-targeted definition change rejected by the A6 firewall.
    // That is a documented contract, not withheld content -- the change is refused, the
    // round discharges cleanly, and the completion message says it was ignored. An earlier
    // comment here wrongly listed it alongside the withheld cases.
    const { statements, definitions, assumptions, coreEdits } = await readProposedChanges(args.ctx);
    if (statements.length === 0 && definitions.length === 0 && assumptions.length === 0 && coreEdits.length === 0) {
      if (round + 1 < D0_SOLVE_CAP) continue;
      return solved; // cap hit on an incomplete round
    }
    // Proposed changes always halt. The orchestrator reads the mathematical
    // proposal, then explicitly applies accepted ids with d0_apply_change.
    const proto = await readTypedCore(protoCoreJsonPath(args.ctx));
    const { auto, gated } = partitionProposedChanges(proto, statements, definitions, assumptions, coreEdits);
    if (auto.size !== 0 || gated.length === 0) {
      throw new Error("D0 proposed-change classifier invariant failed: every proposal must be gated");
    }
    return {
      ...solved,
      message:
        `${solved.message}\nD0 revise loop GATED ${gated.length} change(s) for orchestrator review; ` +
        `no proposal was auto-applied:\n` + gated.map((g) => `  - ${g.id}: ${g.why}`).join("\n"),
    };
  }
  args.state.flags.d0_loop_cap_hit = `D0 solve cap (${D0_SOLVE_CAP} rounds) exhausted`;
  return {
    stage: "0",
    status: "checkpoint",
    advance: false,
    message:
      `D0 solve loop hit the cap (${D0_SOLVE_CAP} incomplete proof-carry rounds, CARRIED across resumes) ` +
      `without a clean discharge. Circuit breaker: re-resuming is a re-roll of a non-deterministic ` +
      `solver, not a retry. Fix the root cause, then resume with --clear-gate d0_loop_cap_hit.`,
  };
}

/** Stage "0.5" (typed): review ↔ directed-revise loop on the solved core. */

/** Persisted D-phase loop counters. These were plain in-process `for` bounds, so a resume
 *  silently granted a fresh budget; see `flags.d0_loop_counters` and the `d0_loop_cap_hit`
 *  cap gate. Reading through a helper keeps the default shape in one place. */
function d0Counters(state: StateJson): { solve_rounds: number; revise_rounds: number; consistency_heals: number } {
  const c = state.flags.d0_loop_counters;
  return {
    solve_rounds: c?.solve_rounds ?? 0,
    revise_rounds: c?.revise_rounds ?? 0,
    consistency_heals: c?.consistency_heals ?? 0,
  };
}

export async function runStage0_5Typed(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // D0.R edits are provisional until a subsequent core panel passes. Snapshot every
  // artifact and in-memory state field D0.R may mutate so a non-converging/failing
  // review cannot contaminate the authoritative D0 package or a same-revision resume.
  const corePath = coreJsonPath(args.ctx);
  const texPath = artifactPaths(args.ctx, args.state).tex;
  const pendingPath = resolveInDir(path.dirname(corePath), "d0r_pending_changes.json", [
    `${args.ctx.qid}_d0r_pending_changes.json`,
  ]);
  const semanticManifest = await loadSemanticManifest(args.ctx);
  if (semanticManifest) {
    const proto = await readTypedCore(protoCoreJsonPath(args.ctx));
    const core = await readTypedCore(corePath);
    const working = await loadWorkingState(args.ctx);
    validateCoreManifest(semanticManifest, "proto", proto);
    validateCoreManifest(semanticManifest, "core", core);
    if (!working) throw new Error("Stage 0 semantic manifest working: d0_working.json is absent");
    validateWorkingManifest(semanticManifest, working);
    if (!existsSync(texPath)) throw new Error("Stage 0 semantic manifest render: writeup.tex is absent");
    validateRenderedManifest(semanticManifest, await readFile(texPath, "utf8"));
  }
  const transaction = {
    core: await readFile(corePath, "utf8"),
    tex: existsSync(texPath) ? await readFile(texPath, "utf8") : null,
    pending: existsSync(pendingPath) ? await readFile(pendingPath, "utf8") : null,
    designDecisions: structuredClone(args.state.design_decisions),
    addedAssumptions: structuredClone(args.state.added_assumptions),
  };
  // The worker edits core.json through the path embedded in its prompt. Treat the
  // transaction as dirty BEFORE dispatch: it may write the file and then return
  // malformed output, time out, or leave a schema-invalid core. Waiting until a
  // successful return to arm rollback lets exactly those failure paths leak an
  // unvetted edit into the next resume.
  let d0rTouched = false;
  let d0_5Passed = false;
  const rollbackUnvettedD0R = async (): Promise<void> => {
    if (!d0rTouched || d0_5Passed) return;
    await writeFile(corePath, transaction.core, "utf8");
    if (transaction.tex === null) await rm(texPath, { force: true });
    else await writeFile(texPath, transaction.tex, "utf8");
    if (transaction.pending === null) await rm(pendingPath, { force: true });
    else await writeFile(pendingPath, transaction.pending, "utf8");
    args.state.design_decisions = transaction.designDecisions;
    args.state.added_assumptions = transaction.addedAssumptions;
  };

  try {
  let prevKeys = new Set<string>();
  let lastReview: Stage0_5CoreResult | null = null;
  const reviseStart = d0Counters(args.state).revise_rounds;
  for (let round = reviseStart; round < D0_REVISE_CAP; round++) {
    args.state.flags.d0_loop_counters = { ...d0Counters(args.state), revise_rounds: round + 1 };
    const review = await runStage0_5Core(args);
    lastReview = review;
    const citationCheckpoint = citationVerificationCheckpoint(review);
    if (citationCheckpoint) {
      // Source access failure is not evidence that the cited claim is false and
      // must not be routed through D0.R as a mathematical revise. Stop at the
      // D boundary so main can seek a lawful source; if still unavailable, main
      // escalates to the user for the relevant page/exact statement. Once
      // attested in source.verbatim_statement, the same D0.5 audit reruns.
      //
      // Record the panel's verdicts before returning. This checkpoint fires on a
      // SOURCE-ACCESS problem, but `review` is a fully-paid panel result that may also
      // carry genuine math findings (including the cited-* findings synthesized into
      // math.findings). Returning without an escalation entry discarded all of them:
      // recoverable only because a rerun re-executes the whole panel — i.e. by paying
      // for it twice. The entry is provenance, not a re-solve directive, so it carries
      // no targets.
      await injectD0ReviewDirective({
        ctx: args.ctx,
        reason:
          "D0.5 halted on citation source-access, not on mathematics. These panel verdicts are recorded for " +
          "provenance so a resume does not re-pay for them; do not re-solve on this entry alone.",
        payload: { stage: "D0.5.citation", overall: review.overall, verdicts: review.verdicts },
        targetIds: [],
        provenanceOnly: true,
      });
      return citationCheckpoint;
    }
    if (review.overall === "pass") {
      // D0.5.G — cold tier referee. The core panel checked math soundness node by
      // node; this INDEPENDENT referee answers "is the delivered note actually good,
      // and at the target level?". It is TOLD the novelty floor and assesses the tier
      // of the PROVED content, then gates the pass on it. Recorded on every run so the
      // tier is greppable history (the gap the core panel's concise verdict left).
      const target = args.ctx.noveltyTarget ?? "field";
      const floor = TARGET_FLOOR_LABEL[target];
      const gen = await runGeneralReview({
        ctx: args.ctx,
        state: args.state,
        deps: args.deps,
        attempt: round + 1,
      });
      const meetsFloor = tierRank(gen.tier) >= tierRank(floor);
      if (meetsFloor) {
        // D0.R writes only core.json + a deterministic TeX preview. Before its
        // provisional transaction commits, rebuild the verified publication
        // bundle so a passing D0.5 cannot advance with PDF/log files from the
        // pre-revision core. runStage0Render publishes nothing on compile failure.
        if (d0rTouched) await runStage0Render({ ctx: args.ctx, state: args.state });
        // D0.R is transactional across the ENTIRE D0.5 gate. Core-panel approval
        // alone is insufficient: a below-floor cold review leaves the run at D0,
        // so its provisional edits must not replace the authoritative package.
        d0_5Passed = true;
        // Record the tier on PASS too (greppable history), then advance.
        await appendReview(args.ctx, "stage_0.5.G", round + 1, {
          status: "pass",
          notes:
            `D0.5.G cold referee tier=${gen.tier} ≥ floor=${floor} (target=${target})` +
            `${gen.flagship_potential ? " | flagship_potential" : ""}`,
        }).catch(() => {});
        // CKPT (D0.5 → F1 go/no-go). A passing D0.5 (math panel + novelty floor BOTH
        // cleared) does NOT auto-flow into the expensive F1–F5 formalization. Return a
        // `checkpoint` (not `completed`) so the dispatch loop HALTS and the orchestrator
        // explicitly decides whether to commit to F1. `advance` is left default (not
        // false) so `stage_completed` still advances to "0.5"; on `--resume`,
        // nextStage("0.5") = "1" enters F1 and this never re-fires. (A below-floor tier
        // halts separately above as the BELOW-NOVELTY-FLOOR checkpoint.)
        return {
          stage: "0.5",
          status: "checkpoint",
          message:
            `Stage 0.5 (typed) PASS after ${round} directed-revise round(s) — ` +
            `D0.5.G tier=${gen.tier} ≥ floor=${floor} (target=${target}). ` +
            `CKPT (D0.5→F1 go/no-go): the maximized note cleared the panel AND the novelty floor; ` +
            `decide whether to commit to F1–F5, then \`--resume\` to enter F1.` +
            (gen.flagship_potential && gen.flagship_directive
              ? ` Flagship upside (not auto-pursued): ${gen.flagship_directive}`
              : ""),
        };
      }
      // tier < floor → the delivered note does not clear the novelty bar.
      // buildGeneralTierVerdict transcribes it into the revise/reject ReviewResult
      // the D0.5 boundary knows; we log it and halt for the operator carrying the
      // tier + critique + (when salvageable) the directed improvement to re-solve with.
      const canReroute = gen.salvageable && !!gen.improvement_directive;
      const verdict = buildGeneralTierVerdict(gen, target, canReroute);
      await appendReview(args.ctx, "stage_0.5.G", round + 1, verdict).catch(() => {});
      // Record the verdict on BOTH branches. Previously a non-salvageable below-floor
      // result wrote no escalation entry at all, so the referee's critique survived
      // only in a human-readable message and reviews/review_general.json — neither of
      // which D0 reads. If the run is later resumed or rewound, that paid verdict is
      // simply gone. `parseGeneralReview` also fail-safes a malformed response to
      // tier=incremental / salvageable=false, so a PARSE failure lands here too and
      // would vanish the same way.
      await injectD0ReviewDirective({
        ctx: args.ctx,
        reason: canReroute
          ? "The cold whole-paper referee placed the current paper below the requested novelty floor and supplied this directed improvement."
          : "The cold whole-paper referee placed the current paper below the requested novelty floor and judged it NOT salvageable in scope. Recorded for provenance; do not re-solve on this entry alone.",
        payload: { stage: "D0.5.G", target, floor, general_review: gen },
        targetIds: canReroute ? gen.flagged_conjecture_labels : [],
        // A non-salvageable tier carries no targets by nature; without this it would
        // force-open the whole paper on the next resume.
        provenanceOnly: !canReroute,
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0.5 (typed) BELOW NOVELTY FLOOR — D0.5.G tier=${gen.tier} < floor=${floor} ` +
          `(target=${target}). Critique: ${gen.critique}` +
          (canReroute
            ? `\nSalvageable — inject this as a D0 directive and re-solve D0 to lift: ` +
              `${gen.improvement_directive}` +
              (gen.flagged_conjecture_labels.length > 0
                ? ` [targets: ${gen.flagged_conjecture_labels.join(", ")}]`
                : "")
            : `\nNot salvageable within scope — bank downgraded, or re-anchor the proposal (rewind D-1.2).`),
      };
    }
    if (review.overall === "fail") {
      await injectD0ReviewDirective({
        ctx: args.ctx,
        reason: "The D0.5 whole-paper/core panel found a load-bearing defect that requires D0 re-derivation.",
        payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
        targetIds: reviewTargetIds(review),
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0.5 (typed) FAIL on round ${round} — the math note has a defect the directed ` +
          `revise cannot fix in place. Findings: ${summarize(review.verdicts)}.` +
          ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.`,
      };
    }
    // Loop-level non-convergence escalation (robust early-escalation): if a finding
    // (node+code) SURVIVED the previous round's D0.R edit and is still flagged, the
    // directed editor is not resolving it — escalate NOW rather than churn to the cap.
    // (D0.R self-escalation via `revised.escalate` only fires when D0.R itself reports
    // "failed"; this catches the case where D0.R keeps producing edits that don't land.)
    const curKeys = findingKeys(review.verdicts);
    const convergence = decideReviseConvergence(round > 0 ? prevKeys : null, curKeys);
    {
      if (convergence.kind === "persistent-findings") {
        const persistent = convergence.persistent;
        await injectD0ReviewDirective({
          ctx: args.ctx,
          reason: `D0.R did not clear persistent finding(s): ${persistent.join(", ")}. Re-derive them in D0 from the complete review below.`,
          payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
          targetIds: reviewTargetIds(review),
        });
        return {
          stage: "0.5",
          status: "checkpoint",
          advance: false,
          message:
            `Stage 0.5 (typed) non-converging — finding(s) survived a D0.R edit and are still flagged on ` +
            `round ${round}: ${persistent.slice(0, 8).join(", ")}. The directed revise cannot resolve these ` +
            `in place (likely a genuine open gap needing a new idea). Open findings: ${summarize(review.verdicts)}.` +
            ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.`,
        };
      }
      // No-net-progress backstop — see decideReviseConvergence.
      if (convergence.kind === "no-net-progress") {
        await injectD0ReviewDirective({
          ctx: args.ctx,
          reason: `D0.R made no net progress (${prevKeys.size} to ${curKeys.size} findings). Apply the complete review at D0 rather than another in-place edit.`,
          payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
          targetIds: reviewTargetIds(review),
        });
        return {
          stage: "0.5",
          status: "checkpoint",
          advance: false,
          message:
            `Stage 0.5 (typed) non-converging — D0.R round ${round} made no net progress ` +
            `(${prevKeys.size} → ${curKeys.size} findings; different findings each round = whack-a-mole, ` +
            `typically a class of fixes that needs proto/def changes or new math beyond an in-place core edit). ` +
            `Open findings: ${summarize(review.verdicts)}.` +
            ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.`,
        };
      }
    }
    prevKeys = curKeys;
    // revise → directed D0.R edit (edits core in place + re-renders), then re-review.
    d0rTouched = true;
    const revised = await runStage0RCore({ ctx: args.ctx, state: args.state, deps: args.deps, review });
    // D0.R early-escalation: if the directed edit reports the findings are NOT fixable
    // in place (needs real math / re-derivation / substrate), checkpoint NOW — do not
    // burn the rest of the revise cap thrashing on something it cannot solve.
    if (revised.escalate) {
      await injectD0ReviewDirective({
        ctx: args.ctx,
        reason: `D0.R escalated: ${revised.escalate.reason}. Re-derive the reviewed targets in D0.`,
        payload: { stage: "D0.5", overall: review.overall, verdicts: review.verdicts },
        targetIds: reviewTargetIds(review),
      });
      return {
        stage: "0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage 0.5 (typed) D0.R escalated on round ${round} (before cap) — the directed revise cannot fix ` +
          `the findings in place: ${revised.escalate.reason}\nOpen findings: ${summarize(review.verdicts)}.` +
          ` Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.`,
      };
    }
  }
  if (lastReview) {
    await injectD0ReviewDirective({
      ctx: args.ctx,
      reason: `The D0.R revise cap (${D0_REVISE_CAP}) was exhausted. Re-derive the remaining reviewed targets in D0.`,
      payload: { stage: "D0.5", overall: lastReview.overall, verdicts: lastReview.verdicts },
      targetIds: reviewTargetIds(lastReview),
    });
  }
  args.state.flags.d0_loop_cap_hit = `D0.5 revise cap (${D0_REVISE_CAP} rounds) exhausted`;
  return {
    stage: "0.5",
    status: "checkpoint",
    advance: false,
    message: `Stage 0.5 (typed) revise cap exhausted (${D0_REVISE_CAP} rounds, CARRIED across resumes) without PASS — likely a genuine open gap. Provide guidance via the D0 directive (a new direction / a paper to adapt / a reframing) and re-run, or rewind D0/D-1.2.`,
  };
  } finally {
    await rollbackUnvettedD0R();
  }
}

/** Split reviewer-supplied target ids by what D0 can actually ENFORCE.
 *
 *  `ReviewFindingSchema.node_id` validates against every core node id — statements,
 *  assumptions AND definitions. But D0's exact-target enforcement
 *  (`stage0_solve`'s `emittedTargets` check) is statement-shaped, so a finding on a
 *  `def:`/`ass:` node used to be filtered out here and delivered as prose only:
 *  structurally unenforceable, and silent about it. Splitting instead of filtering
 *  keeps the enforceable set exact while making the remainder visible in the
 *  directive, so the orchestrator can see a target was raised but not bound. */
/** Pure convergence decision for the D0.5 review↔D0.R loop.
 *
 *  - a finding (node+code key) that SURVIVED the previous round's D0.R edit means
 *    the directed editor is not resolving it — escalate now, don't churn to cap;
 *  - a round that does not strictly REDUCE the finding count is whack-a-mole
 *    (D0.R fixes one nit, the reviewer surfaces another) — also escalate;
 *  - genuine convergence shrinks the count every round. */
export function decideReviseConvergence(
  prevKeys: ReadonlySet<string> | null,
  curKeys: ReadonlySet<string>,
):
  | { kind: "continue" }
  | { kind: "persistent-findings"; persistent: string[] }
  | { kind: "no-net-progress"; before: number; after: number } {
  if (prevKeys === null) return { kind: "continue" };
  const persistent = [...curKeys].filter((k) => prevKeys.has(k));
  if (persistent.length > 0) return { kind: "persistent-findings", persistent };
  if (curKeys.size >= prevKeys.size) return { kind: "no-net-progress", before: prevKeys.size, after: curKeys.size };
  return { kind: "continue" };
}

export function partitionReviewTargets(
  targetIds: string[],
  core: { statements?: Array<{ id?: string }>; assumptions?: Array<{ id?: string }>; definitions?: Array<{ id?: string }> },
): { required: string[]; nonStatement: string[]; unknown: string[] } {
  const statementIds = new Set((core.statements ?? []).map((s) => s.id));
  const otherIds = new Set([...(core.assumptions ?? []), ...(core.definitions ?? [])].map((n) => n.id));
  const allIds = [...statementIds, ...otherIds].filter((id): id is string => typeof id === "string");
  // Referees do not all emit ids the same way — D0.5.G historically emitted bare
  // labels (`foo`) while core nodes are prefixed (`thm:foo`). Resolve a bare label to
  // its core id when that is UNAMBIGUOUS; an ambiguous label (`foo` matching both
  // `thm:foo` and `lem:foo`) stays unknown rather than binding to a guess.
  const resolve = (raw: string): string | null => {
    if (statementIds.has(raw) || otherIds.has(raw)) return raw;
    if (raw.includes(":")) return null;
    const matches = allIds.filter((id) => id.slice(id.indexOf(":") + 1) === raw);
    return matches.length === 1 ? matches[0] : null;
  };
  const required: string[] = [];
  const nonStatement: string[] = [];
  const unknown: string[] = [];
  for (const raw of [...new Set(targetIds)]) {
    const id = resolve(raw);
    if (id !== null && statementIds.has(id)) required.push(id);
    else if (id !== null && otherIds.has(id)) nonStatement.push(id);
    else unknown.push(raw);
  }
  return { required, nonStatement, unknown };
}

/** Normalized discriminator for a finding that anchors to no core node. Without it,
 *  every note-global finding keys to the same `?@?` and N distinct defects collapse
 *  to one — which made a whack-a-mole D0.R round read as convergence to both
 *  backstops below. Normalizing (rather than hashing raw text) keeps a genuinely
 *  PERSISTING finding on the same key across a re-word that changes only spacing
 *  or punctuation. */
function noteGlobalDiscriminator(oneLine: string | undefined): string {
  return (oneLine ?? "")
    .toLowerCase()
    .replace(/[^a-z0-9\s]/g, "")
    .replace(/\s+/g, " ")
    .trim()
    .slice(0, 80);
}

/** Stable per-finding keys (node+code) across a review's verdicts — used to detect a
 *  finding that survived a D0.R edit (non-convergence). Node id falls back to `node`
 *  then `node_id` (verdict-shape tolerant); a finding anchored to no node is keyed by
 *  its normalized `one_line` so distinct note-global findings stay distinct. */
export function findingKeys(
  verdicts: Array<{ findings: Array<{ code?: string; node?: string; node_id?: string; one_line?: string }> }>,
): Set<string> {
  const keys = new Set<string>();
  for (const v of verdicts) {
    for (const f of v.findings) {
      const node = f.node ?? f.node_id;
      keys.add(node ? `${f.code ?? "?"}@${node}` : `${f.code ?? "?"}@~${noteGlobalDiscriminator(f.one_line)}`);
    }
  }
  return keys;
}

function summarize(verdicts: Array<{ referee: string; findings: Array<{ code?: string; node?: string; node_id?: string }> }>): string {
  return verdicts
    .flatMap((v) => v.findings.map((f) => `${f.code ?? "?"}@${f.node ?? f.node_id ?? "?"}`))
    .slice(0, 8)
    .join(", ");
}
