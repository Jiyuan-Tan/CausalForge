import type { APIRoute } from "astro";
import {
  loadLibrary,
  libraryRoot,
  declArea,
  declPagePath,
  isTier1,
  reviewStatus,
} from "../../lib/library.js";
import { nlOf } from "../../lib/docmd.js";

/**
 * Statement-level dependency graph payload (tier-1 only — the meaning graph).
 * nodes: n=name, s=short, k=kind, a=area, m=module, r=review status, x=sorry,
 *        d=NL snippet (tooltip)
 * edges: [from, to] index pairs into nodes, oriented dependency → dependent
 *        (used → user): an edge points from a declaration to the ones whose
 *        statements mention it. This matches the leanblueprint / mathlib
 *        import-graph convention — foundational declarations are sources whose
 *        arrows fan out to everything built on them.
 * areaEdges: [fromArea, toArea, count] aggregated cross-area dependencies,
 *        same orientation (used-area → user-area).
 */
export const GET: APIRoute = () => {
  const lib = loadLibrary(libraryRoot());
  const t1 = lib.entries.filter((e) => isTier1(e, lib.sidecars));
  const idx = new Map(t1.map((e, i) => [e.name, i]));
  const nodes = t1.map((e) => ({
    n: e.name,
    s: e.name.split(".").pop(),
    k: e.kind,
    a: declPagePath(e, lib),
    m: e.module,
    r: reviewStatus(e, lib.sidecars),
    x: e.usesSorry,
    d: (nlOf(e.doc) ?? "").slice(0, 200),
  }));
  const edges: [number, number][] = [];
  const areaCount = new Map<string, number>();
  for (const e of t1) {
    const user = idx.get(e.name)!;
    // e's statement mentions r, so r is USED BY e. Orient the edge used → user
    // (dependency → dependent), so foundational declarations are sources whose
    // arrows fan out to their dependents — the leanblueprint / import-graph convention.
    for (const r of e.refs) {
      const used = idx.get(r);
      if (used === undefined) continue; // tier-2 or filtered dependency
      edges.push([used, user]);
      const aUsed = nodes[used].a;
      const aUser = nodes[user].a;
      if (aUsed !== aUser) {
        const key = `${aUsed}→${aUser}`;
        areaCount.set(key, (areaCount.get(key) ?? 0) + 1);
      }
    }
  }
  const areaEdges = [...areaCount.entries()].map(([k, c]) => {
    const [f, t] = k.split("→");
    return [f, t, c] as [string, string, number];
  });
  const areas = [...new Set(nodes.map((n) => n.a))].sort();
  return new Response(JSON.stringify({ commit: lib.commit, areas, nodes, edges, areaEdges }), {
    headers: { "Content-Type": "application/json" },
  });
};
