import { StatementSchema, type CoreStatement } from "../core/schema.js";

type DurableStatementCatalogState = {
  solved: Record<string, { node?: CoreStatement; owner?: string }>;
  resolved_oeqs?: Record<string, string | { theorem_id: string; source_fingerprint: string }>;
};

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

/** The complete durable statement identity catalog shared by merge and APPLY.
 * Publication views omit reversible records, so they are not authoritative. */
export function authoritativeStatementCatalog(
  protoStatements: readonly CoreStatement[],
  working: DurableStatementCatalogState | null | undefined,
): Map<string, CoreStatement> {
  const catalog = new Map(protoStatements.map((statement) => [statement.id, statement] as const));
  for (const [id, record] of Object.entries(working?.solved ?? {})) {
    if (record.node !== undefined && !catalog.has(id)) catalog.set(id, record.node);
  }
  for (const [sourceId, resolution] of Object.entries(working?.resolved_oeqs ?? {})) {
    if (typeof resolution === "string" || catalog.has(sourceId)) continue;
    const answer = working?.solved[resolution.theorem_id];
    if (answer?.owner !== sourceId || answer.node?.id !== resolution.theorem_id) continue;
    const recovered = agentOeqSourceFromFingerprint(sourceId, resolution.source_fingerprint);
    if (recovered !== null) catalog.set(sourceId, recovered);
  }
  return catalog;
}

/** Normalize a surviving replacement endpoint through a live OEQ resolution.
 * If either endpoint is deleted by the same atomic bundle, the question is
 * reopening/retiring and must remain the endpoint for transaction validation. */
export function resolvedStatementReplacementEndpoint(
  id: string | undefined,
  working: DurableStatementCatalogState | null | undefined,
  atomicDeleteIds: ReadonlySet<string>,
): string | undefined {
  if (id === undefined || atomicDeleteIds.has(id)) return id;
  const resolution = working?.resolved_oeqs?.[id];
  if (resolution === undefined || typeof resolution === "string") return id;
  if (atomicDeleteIds.has(resolution.theorem_id)) return id;
  const answer = working?.solved[resolution.theorem_id];
  return answer?.node?.id === resolution.theorem_id ? resolution.theorem_id : id;
}
