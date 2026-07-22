/*!
 * Module/area fallback tier (Phase 3 of the retrieval-v2 plan). When decl-level retrieval is
 * low-confidence (the gate decides), the consumer is far better served by a relevant MODULE/area
 * to read than by specific decls that probably don't fit — this is the "return a rough module for
 * the model to look at" behaviour the tool was asked for.
 *
 * Module score = MEAN of its top-k member-decl scores from the CURRENT query (top-3 pooling). Per
 * the plan this "beats centroids decisively": a centroid blurs a 40-decl module into mush, whereas
 * top-3 pooling says "this module contains several individually-relevant things" — exactly the
 * fallback semantics wanted. It reuses the strong fused decl-level scores rather than a weak
 * lexical-over-docstring pass. A docstring-similarity channel can be folded in via `max` by the
 * caller. Each module also exposes up to 3 prototype member names as "e.g." anchors.
 */

export interface ModuleCandidate {
  module: string;
  /** Pooled relevance: mean of the module's top-k member-decl scores for this query. */
  score: number;
  /** How many retrieved decls fell in this module (context for the consumer). */
  memberCount: number;
  /** Up to 3 highest-scoring member decl names — shown as "e.g." anchors. */
  prototypes: string[];
  /** Module `/-! -/` overview docstring, when the caller supplies it. */
  overview?: string;
}

/**
 * Group scored decl candidates by their module and rank modules by the mean of each module's
 * top-`poolK` member scores. `cands` are the fused decl-level results (already query-scored).
 * Exported for testing.
 */
export function poolModules(
  cands: { module: string; name: string; score: number }[],
  topN: number,
  poolK = 3,
): ModuleCandidate[] {
  const byMod = new Map<string, { name: string; score: number }[]>();
  for (const c of cands) {
    if (!c.module) continue;
    let arr = byMod.get(c.module);
    if (!arr) byMod.set(c.module, (arr = []));
    arr.push({ name: c.name, score: c.score });
  }
  const out: ModuleCandidate[] = [];
  for (const [module, members] of byMod) {
    members.sort((a, b) => b.score - a.score || a.name.localeCompare(b.name));
    const top = members.slice(0, poolK);
    const score = top.reduce((s, m) => s + m.score, 0) / top.length;
    out.push({ module, score, memberCount: members.length, prototypes: members.slice(0, 3).map((m) => m.name) });
  }
  out.sort((a, b) => b.score - a.score || a.module.localeCompare(b.module));
  return out.slice(0, topN);
}
