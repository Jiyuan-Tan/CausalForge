// D0-SOLVE step 4/5 — runGates (spec §Stage kernel).
//
// The deterministic checks the round runs over the assembled core, moved
// verbatim from stage0_solve.ts in the T1 carve: the mechanical dead-assumption
// prune + derived-metadata finalization + manifest validation, the
// store-coherence reconcile + round-invariant self-check executed by every
// commit, the checkpoint-time closure gate + symbol preflight, the bibliography
// auto-heal, and the final structural gate (`requireDischarged: true`).
import type { Core } from "../core/schema.js";
import { pruneDeadAssumptions } from "../core/gate.js";
import { rebuildAssumptionUsedBy } from "../core/dependencies.js";
import {
  checkProposalClosure,
  type ClosureReport,
  reconcileProofStores,
} from "../core/coherence.js";
import { runGates, type GateViolation } from "../framework/gates.js";
import { roundInvariantsGate, structuralGate, symbolPreflightGate } from "../framework/gate_registrations.js";
import { refreshSnapshots } from "../working_writer.js";
import { validateCoreManifest, validateWorkingManifest } from "../semantic_manifest.js";
import { coreEditTarget } from "../stages/d0_apply.js";
import type { SolveRoundContext } from "./context.js";
import type { SolveMergeResult } from "./merge.js";

/** Post-merge final assembly: prune, rebuild derived metadata, refresh the reuse
 *  snapshots, and validate both stores against the run's semantic manifest. */
export function runFinalAssemblyGates(sctx: SolveRoundContext): void {
  const { proto, core, next, semanticManifest } = sctx;
  // MECHANICAL dead-assumption prune: drop isolated assumptions no statement uses
  // (transitively). They belong to no result; carrying them only widens the
  // faithfulness surface (an unconstrained hypothesis whose Lean encoding is never
  // checked against a proof). Statements and definitions are never pruned.
  {
    const res = pruneDeadAssumptions(core);
    if (res && res.pruned.length) {
      core.assumptions = res.core.assumptions;
      console.warn(`[D0-SOLVE] dead-assumption prune: removed isolated unused assumption(s) ${res.pruned.join(", ")}.`);
    }
  }

  // `used_by` is derived metadata, never solver-authored truth. Rebuild it only
  // after OEQ replacement, proof citation wiring, self-containment, id healing,
  // and pruning have all finished. This prevents a requested proto rebuild from
  // going stale again during final assembly.
  rebuildAssumptionUsedBy(core);
  // Final pass: snapshot against `proto` (this loop also used `core`), so every record
  // leaves the round with a snapshot `computeValidNodes` can actually compare.
  // skipPartial matches the in-merge refresh: a partial's snapshot is the basis the
  // agent argued (possibly a PREVIOUS statement text) — refreshing it here silently
  // retargeted the obligation and suppressed dispatch's "realign" warning.
  refreshSnapshots(next, proto, core, { skipPartial: true });

  validateCoreManifest(semanticManifest, "core", core);
  validateWorkingManifest(semanticManifest, next);
}

/** The commit-time self-check: repair store divergence and warn on every round
 *  invariant violation. Runs inside `commitRound`, after reconciliation and
 *  before anything is persisted. */
export function reconcileAndWarnRound(sctx: SolveRoundContext): void {
  const { proto, core, prev, next } = sctx;
  const recovered = reconcileProofStores(core, proto, next);
  if (recovered.length > 0) {
    console.warn(
      `[D0-SOLVE] store-coherence repair: ${recovered.length} proved core node(s) had no working record ` +
        `and would have been lost next round: ${recovered.join(", ")}. Recovered from core.json.`,
    );
  }
  // SELF-CHECK EVERY REAL ROUND. The twelve faults found on 2026-07-19 were all
  // invisible until something downstream broke, sometimes rounds later. These checks
  // run here — after reconciliation, before anything is persisted — so a live run
  // reports its own incoherence with receipts instead of carrying it silently.
  // The soak suite asserts the SAME function, so a scenario and a real run can never
  // disagree about what "broken" means.
  //
  // Warn, do not throw: the danger is silence, not survivable damage, and aborting a
  // round that cost real agent time over a repairable inconsistency is a worse trade.
  // (`reconcileProofStores` above already throws on the one unrepairable case.)
  for (const violation of runGates([roundInvariantsGate], { proto, core, before: prev, after: next }).warn) {
    console.warn(violation.detail);
  }
}

/** CLOSURE GATE (deterministic, ~0 tokens). `d0_apply_change` composes
 *  proto_core.json + the proposal payload; it cannot see core.json. So an atomic
 *  apply is sound only if every core node is carried by proto or by a proposal.
 *  On the 2026-07-18 run that invariant broke three times and was caught only by
 *  gpt-5.6-sol adjudication AFTER a full solve round each time — rounds 30-33 were
 *  spent re-litigating a plumbing fault as a mathematical one. Checking it here
 *  puts the same verdict in the checkpoint the orchestrator reads first. */
export function checkpointClosure(sctx: SolveRoundContext, mr: SolveMergeResult): ClosureReport {
  const { core, proto, next } = sctx;
  const { proposedChanges, defChanges, proposedAssumptions, proposedCoreEdits, deferredProofs } = mr;
  return checkProposalClosure({
    core,
    proto,
    proposalIds: new Set<string>([
      ...proposedChanges.map((c) => c.id),
      ...defChanges.map((c) => c.id),
      ...proposedAssumptions.map((a) => a.id),
      ...proposedCoreEdits.map((e) => coreEditTarget(e)),
      ...deferredProofs.map((p) => p.id),
      // `d0_working.json` is the THIRD carrier, and omitting it made this gate
      // over-report. `clearRoundOutputs` deletes core.json but KEEPS the working
      // state, and the next round rebuilds agent-added nodes from
      // `working.solved[].node` (see the `rec.node && validIds.has(id)` reinjection
      // above). So a node held there is durable across an apply even though it
      // appears in neither proto nor the proposal payload — exactly the shape this
      // check was flagging as a silent drop.
      ...Object.entries(next.solved)
        .filter(([, rec]) => rec.node !== undefined)
        .map(([id]) => id),
    ]),
  });
}

/** Deterministic structural preflight, same principle as the closure gate: enforce
 *  the symbol-table membership rule here rather than spending a whole solve round
 *  before discovering it (round 36). Runs the registered `symbol-preflight` gate. */
export function checkpointPreflight(core: Core): GateViolation[] {
  return runGates([symbolPreflightGate], core).hard;
}

/** Auto-heal the only NON-structural gate check before sanity-gating: a `standard.cite`
 *  that names a missing bibliography key (G6) is bibliographic metadata, not a soundness
 *  defect — a trivial gap should not abort a clean discharge (it forces a manual edit for
 *  something the run can self-fix). Append a stub bib entry (citation text filled at
 *  write-up) and WARN so it stays visible; genuine structural violations (G1–G5, G7,
 *  schema) still throw in `runPostSolveGate`. */
export function healMissingBibCites(core: Core): void {
  const bibKeys = new Set((core.bibliography ?? []).map((b) => b.key));
  const healedCites = Array.from(
    new Set(
      [
        ...core.assumptions.map((a) => a.standard?.cite),
        ...core.statements.filter((s) => s.status === "cited").map((s) => s.source?.cite),
      ]
        .filter((c): c is string => !!c && !bibKeys.has(c)),
    ),
  );
  if (healedCites.length > 0) {
    core.bibliography = [...(core.bibliography ?? []), ...healedCites.map((key) => ({ key }))];
    console.warn(
      `[D0-SOLVE] auto-healed ${healedCites.length} missing bibliography cite(s) (stubbed; complete at write-up): ${healedCites.join(", ")}`,
    );
  }
}

/** Everything discharged → sanity-gate the structure, then it's a clean discharge.
 *  Runs the registered `structural-gate` with `requireDischarged: true` (the D0
 *  final assembly is the strict call site; the registry default is false). */
export function runPostSolveGate(core: Core): void {
  const { hard } = runGates([structuralGate], { core, requireDischarged: true });
  if (hard.length > 0) {
    const lines = hard.map((v) => `  ${v.detail}`).join("\n");
    throw new Error(`Stage 0-SOLVE produced a core that fails the post-solve gate:\n${lines}`);
  }
}
