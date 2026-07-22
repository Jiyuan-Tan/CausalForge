// Registry entries for the D-stage gates (spec §Gate registry). Each entry
// DELEGATES to the existing gate implementation — the registry adds the
// enumerable declaration (id / tier / stages / evidence), not a second
// implementation. Import this module for its side effect; entries accumulate
// here as each stage is ported.
import { registerGate, type GateViolation } from "./gates.js";
import { runStructuralGate } from "../core/gate.js";
import { runProposalGate } from "../core/proposal_gate.js";
import { checkProposalClosure, type ClosureCoreView } from "../core/coherence.js";
import { checkSymbolDeclarations } from "../core/preflight.js";
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
export const structuralGate = registerGate<{ core: unknown; requireDischarged?: boolean }>({
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
export const proposalGate = registerGate<unknown>({
  id: "proposal-gate",
  tier: "hard",
  stages: ["-1.2"],
  evidence:
    "D0_CORE_REDESIGN.md §12 (single-artifact producer: gate runs inside the author, loud by design); PIPELINE_NOTES 2026-07-18 (grouped free_symbols exhausted the retry budget — gate feedback must be re-authorable)",
  check: (core) => toViolations("proposal-gate", runProposalGate(core).violations),
});

/** Atomic-apply closure invariant: ids(core) ⊆ ids(proto) ∪ ids(proposals) ∪
 *  durable agent nodes. Checked deterministically at D0 surface time. The D0
 *  checkpoint invokes `checkProposalClosure` directly (not via runGates): it
 *  consumes the full ClosureReport — including the advisory `protoOnly`
 *  direction, which is deliberately NOT a violation. */
export const closureGate = registerGate<{ core: ClosureCoreView; proto: ClosureCoreView; proposalIds: Set<string> }>({
  id: "proposal-closure",
  tier: "hard",
  stages: ["0"],
  evidence:
    "PIPELINE_NOTES 2026-07-18 (invariant broke 3×, each caught only by paid adjudication AFTER a full solve round — rounds 30-33 re-litigated a plumbing fault as math)",
  check: (input) => {
    const report = checkProposalClosure(input);
    return report.ok ? [] : [{ gateId: "proposal-closure", detail: `closure violated`, ids: report.uncarried }];
  },
});

/** G1 symbol-table membership, hoisted to run BEFORE a solve dispatch. */
export const symbolPreflightGate = registerGate<Parameters<typeof checkSymbolDeclarations>[0]>({
  id: "symbol-preflight",
  tier: "hard",
  stages: ["0"],
  evidence:
    "PIPELINE_NOTES 2026-07-18 round 36 (free symbols absent from proto_core.symbols found only after a complete solve round was paid for)",
  check: (core) =>
    checkSymbolDeclarations(core).map((v) => ({ gateId: "symbol-preflight", detail: `[${v.check}] ${v.detail}`, ids: v.ids })),
});

/** Cross-store round invariants (store-incoherent, dangling-resolution, hollow
 *  proof, silent node loss, ...). Policy: DETECT AND WARN, never throw — see
 *  core/coherence.ts header; `reconcileProofStores` is the hard tier of the same module. */
export const roundInvariantsGate = registerGate<RoundInvariantInput>({
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
export const proseConsistencyGate = registerGate<Core>({
  id: "prose-consistency",
  tier: "warn",
  stages: ["0"],
  evidence:
    "PIPELINE_NOTES 2026-07-15 (solver could prove a reframe but not synchronize its prose) + 6b37bdb9 (stop flagging a well-scoped open question)",
  check: (core) =>
    checkProseConsistency(core).map((w) => ({ gateId: "prose-consistency", detail: `[${w.code}] ${w.field}: ${w.message}` })),
});
