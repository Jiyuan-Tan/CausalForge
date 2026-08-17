// D0-SOLVE step 4/5 — runGates (spec §Stage kernel).
//
// The deterministic checks the round runs over the assembled core, moved
// verbatim from stage0_solve.ts in the T1 carve: the mechanical dead-assumption
// prune + derived-metadata finalization + manifest validation, the
// store-coherence reconcile + round-invariant self-check executed by every
// commit, the checkpoint-time closure gate + symbol preflight, the bibliography
// auto-heal, and the final structural gate (`requireDischarged: true`).
import type { Core } from "../core/schema.js";
import { runGates, type GateViolation } from "../framework/gates.js";
import { assembleCore } from "../core/assemble.js";
import { roundInvariantsGate, structuralGate, symbolDriftGate, symbolPreflightGate } from "../framework/gate_registrations.js";
import { validateCoreManifest, validateWorkingManifest } from "../semantic_manifest.js";
import type { SolveRoundContext } from "./context.js";

/** Post-merge validation: check both stores against the run's semantic
 *  manifest. (Batch B: the workspace prune/derived-metadata passes are gone —
 *  the RENDER owns dead-assumption pruning and `used_by` rebuilding, so the
 *  manifest is validated over what will actually be published.) */
export function runFinalAssemblyGates(sctx: SolveRoundContext): void {
  const { proto, next, semanticManifest } = sctx;
  validateCoreManifest(semanticManifest, "core", assembleCore(proto, next));
  validateWorkingManifest(semanticManifest, next);
}

/** The commit-time self-check: warn on every round invariant violation, judged
 *  over the RENDERED core (the artifact the commit publishes). Runs inside
 *  `commitRound`, before anything is persisted.
 *
 *  (Retired here, Phase 1: `reconcileProofStores` — the published core is now a
 *  pure render of (proto, working), so a proof present in the core but absent
 *  from the cursor is unrepresentable; its throw case — a resolution naming a
 *  theorem no store holds — moved to `saveWorkingState`'s single-store
 *  invariant. Also retired: the proposal-closure gate — `ids(core) ⊆ ids(proto)
 *  ∪ ids(working)` holds by construction of `assembleCore`.) */
export function warnRoundInvariants(sctx: SolveRoundContext, rendered: Core): void {
  const { proto, prev, next } = sctx;
  // Resolving an agent-authored OEQ intentionally retires its source record
  // from `solved`: `resolved_oeqs` becomes the durable semantic carrier and
  // `assembleCore` publishes the replacement theorem.  Treat only those
  // consumed sources as allowed losses; every other disappeared authored node
  // must still trigger `silent-node-loss`.
  const allowedLoss = Object.keys(prev?.solved ?? {}).filter(
    (id) => prev?.solved[id]?.node && !next.solved[id] && next.resolved_oeqs?.[id] !== undefined,
  );
  // SELF-CHECK EVERY REAL ROUND. The faults found on 2026-07-19 were all
  // invisible until something downstream broke, sometimes rounds later. These checks
  // run here — before anything is persisted — so a live run reports its own
  // incoherence with receipts instead of carrying it silently. The soak suite
  // asserts the SAME function, so a scenario and a real run can never disagree
  // about what "broken" means.
  //
  // Warn, do not throw: the danger is silence, not survivable damage, and aborting a
  // round that cost real agent time over a repairable inconsistency is a worse trade.
  for (const violation of runGates(
    [roundInvariantsGate],
    { proto, core: rendered, before: prev, after: next, allowedLoss },
  ).warn) {
    console.warn(violation.detail);
  }
}

/** Deterministic structural preflight, same principle as the closure gate: enforce
 *  the symbol-table membership rule here rather than spending a whole solve round
 *  before discovering it (round 36). Runs the registered `symbol-preflight` gate. */
export function checkpointPreflight(core: Core): GateViolation[] {
  return runGates([symbolPreflightGate], core).hard;
}

/** Advisory companion to `checkpointPreflight`: nodes whose text mentions a symbol they
 *  do not declare. Warn-tier — `free_symbols` is what scopes symbol invalidation, so a
 *  rotting declaration must be visible, but the check is a text scan and is wrong often
 *  enough on correct cores that it may never block a round (see the gate registration). */
export function checkpointSymbolDrift(core: Core): GateViolation[] {
  return runGates([symbolDriftGate], core).warn;
}

// (Moved, Phase 1: `healMissingBibCites` — the missing-bib stub is part of the
// render now; `assembleCore` applies the same rule deterministically.)

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
