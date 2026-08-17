import { StatementSchema, type CoreStatement } from "../core/schema.js";

/** Mathematical identity of an OEQ source; prose metadata is intentionally absent. */
export function oeqSourceFingerprint(s: CoreStatement): string {
  return JSON.stringify({
    kind: s.kind,
    statement: s.statement,
    depends_on: [...new Set(s.depends_on)].sort(),
  });
}

/** Recover the minimal mathematical source catalog from a canonical OEQ
 * fingerprint.  Both solve-context recovery and adjudicated answer deletion use
 * this one decoder so a retired agent-authored question can be reopened without
 * inventing metadata or depending on the answer theorem that is being removed. */
export function agentOeqSourceFromFingerprint(sourceId: string, fingerprint: string): CoreStatement | null {
  try {
    const prior = JSON.parse(fingerprint) as { kind?: unknown; statement?: unknown; depends_on?: unknown };
    if (prior.kind !== "openendedquestion" || typeof prior.statement !== "string") return null;
    if (!Array.isArray(prior.depends_on) || !prior.depends_on.every((x) => typeof x === "string")) return null;
    return StatementSchema.parse({
      id: sourceId,
      kind: "openendedquestion",
      statement: prior.statement,
      depends_on: prior.depends_on,
      status: "to-prove",
    });
  } catch {
    return null;
  }
}
