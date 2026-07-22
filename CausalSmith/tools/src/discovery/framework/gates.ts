// Framework primitive 2 of 3: one enumerable declaration of every D-stage gate.
// tier "hard" = the stage fails closed on any violation; "warn" = advisory,
// logged but non-blocking. `evidence` cites the incident that justifies the
// gate (PIPELINE_NOTES date or design-doc section) — registration REFUSES a
// gate with no evidence, which is the evidence-based-prune criterion made
// structural. Population happens per stage port; phase 0 lands mechanics only.
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

const REGISTRY = new Map<string, GateDef<never>>();

export function registerGate<I>(def: GateDef<I>): GateDef<I> {
  if (REGISTRY.has(def.id)) throw new Error(`duplicate gate id '${def.id}'`);
  if (def.evidence.trim().length === 0) {
    throw new Error(
      `gate '${def.id}' registered without evidence — every gate must cite the incident or design decision that justifies it`,
    );
  }
  REGISTRY.set(def.id, def as GateDef<never>);
  return def;
}

export function allGates(): Array<GateDef<never>> {
  return [...REGISTRY.values()];
}

export function runGates<I>(gates: Array<GateDef<I>>, input: I): { hard: GateViolation[]; warn: GateViolation[] } {
  const hard: GateViolation[] = [];
  const warn: GateViolation[] = [];
  for (const g of gates) (g.tier === "hard" ? hard : warn).push(...g.check(input));
  return { hard, warn };
}

/** Test hook: the registry is module-global so production registrations are
 *  singletons; tests must isolate. */
export function _resetRegistryForTests(): void {
  REGISTRY.clear();
}
