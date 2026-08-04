// Framework primitive 2 of 3: explicit declarations for D-stage gates.
// tier "hard" = the stage fails closed on any violation; "warn" = advisory,
// logged but non-blocking. `evidence` cites the incident that justifies the
// gate (PIPELINE_NOTES date or design-doc section) — registration REFUSES a
// gate with no evidence, which is the evidence-based-prune criterion made
// structural. Call sites import and run only the gates they need.
import type { Stage } from "../../types.js";

export type GateTier = "hard" | "warn";

export interface GateViolation {
  gateId: string;
  detail: string;
  ids?: string[];
}

export interface GateDef<I> {
  id: string;
  tier: GateTier;
  stages: Stage[];
  /** Incident/provenance link, e.g. "PIPELINE_NOTES 2026-07-18 — G1 free-symbol escape". */
  evidence: string;
  check: (input: I) => GateViolation[];
}

/** Define one explicit gate. Callers pass gate objects directly to `runGates`;
 * there is no process-global registry or import-order side effect. */
export function defineGate<I>(def: GateDef<I>): GateDef<I> {
  if (def.evidence.trim().length === 0) {
    throw new Error(
      `gate '${def.id}' defined without evidence — every gate must cite the incident or design decision that justifies it`,
    );
  }
  return Object.freeze(def);
}

export function runGates<I>(gates: Array<GateDef<I>>, input: I): { hard: GateViolation[]; warn: GateViolation[] } {
  const hard: GateViolation[] = [];
  const warn: GateViolation[] = [];
  for (const g of gates) (g.tier === "hard" ? hard : warn).push(...g.check(input));
  return { hard, warn };
}
