// Explicit D-stage gate declarations. Runtime call sites import the gate they
// execute; no global registry or import-order side effect is involved.
import { defineGate, type GateViolation } from "./gates.js";
import { runStructuralGate } from "../core/gate.js";
import { runProposalGate } from "../core/proposal_gate.js";
import { checkSymbolDeclarations, checkSymbolDeclarationDrift } from "../core/preflight.js";
import { checkRoundInvariants, formatRoundViolation, type RoundInvariantInput } from "../core/coherence.js";
import { checkProseConsistency } from "../core/prose_consistency.js";
import type { Core } from "../core/schema.js";

function toViolations(
  gateId: string,
  vs: Array<{ code: string; where: string; message: string }>,
): GateViolation[] {
  return vs.map((v) => ({ gateId, detail: `[${v.code}] ${v.where}: ${v.message}` }));
}

/** G1–G7 structural gate over a (possibly not-yet-schema-valid) core.
 *  `requireDischarged` defaults to false; the D0 final assembly and the D0.R
 *  post-edit re-check pass `requireDischarged: true` at their call sites. */
export const structuralGate = defineGate<{ core: unknown; requireDischarged?: boolean }>({
  id: "structural-gate",
  tier: "hard",
  stages: ["-1.2", "0", "0.5"],
  evidence:
    "D0_CORE_REDESIGN.md G1–G7; PIPELINE_NOTES 2026-07-18 (G1 free-symbol escape discovered only after a paid solve round) and 2026-07-20 (G2 over-broad 'standard' token ban exhausted the proposal-gate retries)",
  check: ({ core, requireDischarged }) =>
    toViolations("structural-gate", runStructuralGate(core, { requireDischarged: requireDischarged ?? false }).violations),
});

/** GP1 (standardness tags) + GP2 (all-to-prove) + GP3 (prose fields present),
 *  layered over the structural gate, for the D-1.2 authored proposal core. */
export const proposalGate = defineGate<unknown>({
  id: "proposal-gate",
  tier: "hard",
  stages: ["-1.2"],
  evidence:
    "D0_CORE_REDESIGN.md §12 (single-artifact producer: gate runs inside the author, loud by design); PIPELINE_NOTES 2026-07-18 (grouped free_symbols exhausted the retry budget — gate feedback must be re-authorable)",
  check: (core) => toViolations("proposal-gate", runProposalGate(core).violations),
});

// (Retired, Phase 1 of the store consolidation: the `proposal-closure` gate.
// The published core is `assembleCore(proto, working)`, so
// `ids(core) ⊆ ids(proto) ∪ ids(working)` holds by construction — the state the
// gate policed is unrepresentable. See test/discovery/assemble.test.ts.)

/** G1 symbol-table membership, hoisted to run BEFORE a solve dispatch. */
export const symbolPreflightGate = defineGate<Parameters<typeof checkSymbolDeclarations>[0]>({
  id: "symbol-preflight",
  tier: "hard",
  stages: ["0"],
  evidence:
    "PIPELINE_NOTES 2026-07-18 round 36 (free symbols absent from proto_core.symbols found only after a complete solve round was paid for)",
  check: (core) =>
    checkSymbolDeclarations(core).map((v) => ({ gateId: "symbol-preflight", detail: `[${v.check}] ${v.detail}`, ids: v.ids })),
});

/** ADVISORY drift lint over the SAME declaration the invalidation path now trusts:
 *  a symbol whose name occurs in a node's text but is absent from its `free_symbols`.
 *  warn-tier by measurement, not by preference — a boundary-anchored text scan
 *  contradicts the author's own declaration on 10.1% of the 1186 declaring assumptions
 *  in the real corpus even after de-noising, so blocking on it would burn the D0 round
 *  budget the scoping is meant to save. See `checkSymbolDeclarationDrift`. */
export const symbolDriftGate = defineGate<Parameters<typeof checkSymbolDeclarationDrift>[0]>({
  id: "symbol-declaration-drift",
  tier: "warn",
  stages: ["0"],
  evidence:
    "2026-07 symbol-invalidation scoping: `free_symbols` became the edge that scopes symbol invalidation " +
    "(d0_working.declaredSymbolScope), so an under-declared node silently keeps a proof of a claim whose " +
    "symbol moved; corpus measurement over doc/research/{active,_bank} set the tier to warn (10.1% " +
    "disagreement with ground-truth declarations)",
  check: (core) =>
    checkSymbolDeclarationDrift(core).map((v) => ({ gateId: "symbol-declaration-drift", detail: `[${v.check}] ${v.detail}`, ids: v.ids })),
});

/** Round invariants over the rendered core (dangling-resolution, hollow proof,
 *  silent node loss, snapshot basis, oeq-answer-churn, dependency-cycle).
 *  Policy: DETECT AND WARN, never throw — see core/coherence.ts header. */
export const roundInvariantsGate = defineGate<RoundInvariantInput>({
  id: "round-invariants",
  tier: "warn",
  stages: ["0"],
  evidence:
    "PIPELINE_NOTES 2026-07-19 (the two stores diverge silently, and TERMINAL results are the victims; detection landed as warn-tier by design)",
  // `detail` is the exact operator-facing warn line, so the D0 commit logs the
  // registry output verbatim (byte-identical to the pre-wiring behaviour).
  check: (input) =>
    checkRoundInvariants(input).map((v) => ({ gateId: "round-invariants", detail: formatRoundViolation(v), ids: v.ids })),
});

/** Prose↔formal drift lint (PROSE-DANGLING-REF / PROSE-OPEN-OVERCLAIM). */
export const proseConsistencyGate = defineGate<Core>({
  id: "prose-consistency",
  tier: "warn",
  stages: ["0"],
  evidence:
    "PIPELINE_NOTES 2026-07-15 (solver could prove a reframe but not synchronize its prose) + 6b37bdb9 (stop flagging a well-scoped open question)",
  check: (core) =>
    checkProseConsistency(core).map((w) => ({ gateId: "prose-consistency", detail: `[${w.code}] ${w.field}: ${w.message}` })),
});
