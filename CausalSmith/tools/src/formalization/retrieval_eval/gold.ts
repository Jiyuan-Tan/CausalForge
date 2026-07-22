import type { Library } from "../../library/schema.js";
import { CLUSTER_SUBSTRATE_ROOTS, type ClusterKey } from "../../constants.js";

export const EVAL_KS = [1, 3, 5, 10] as const;
export const GOLD_KINDS = new Set(["def", "structure", "inductive", "class", "abbrev", "theorem"]);
export const IDF_FLOOR = 2.3;

export interface GoldPair {
  theorem: string;
  cluster: ClusterKey | null;
  gold: string[]; // sorted, deduped Causalean decl names the STATEMENT is built on
  doc: string;    // first-paragraph docstring (query source for the `doc` rendering)
  statement: string;
}

/**
 * Map a file path to the cluster whose most-specific substrate root contains it, else null.
 *
 * EVAL-HARNESS ONLY — do NOT filter retrieval with this. Cluster substrates overlap
 * (`Causalean/PO/` is a root of five clusters), so collapsing a file to ONE label hands every
 * equal-length tie to whichever cluster is declared first and hides the shared substrate from
 * the rest. This is sound here only because gold bookkeeping wants one label per decl. To ask
 * "is this file in cluster X?", use `inClusterSubstrate` from constants.ts — the single predicate
 * every retrieval tier filters through.
 */
export function fileToCluster(file: string): ClusterKey | null {
  let best: { key: ClusterKey; rootLength: number } | null = null;
  for (const key of Object.keys(CLUSTER_SUBSTRATE_ROOTS) as ClusterKey[]) {
    for (const r of CLUSTER_SUBSTRATE_ROOTS[key]) {
      const rr = r.replace(/\/+$/, "");
      const hit = rr.endsWith(".lean") ? file === rr : file === rr || file.startsWith(rr + "/");
      if (hit && (!best || rr.length > best.rootLength)) best = { key, rootLength: rr.length };
    }
  }
  return best?.key ?? null;
}

function firstPara(doc: string | null): string {
  return (doc ?? "").split(/\n\s*\n/)[0].trim();
}

export function buildGoldPairs(lib: Library): GoldPair[] {
  const byName = new Map(lib.entries.map((e) => [e.name, e]));
  const out: GoldPair[] = [];
  for (const e of lib.entries) {
    if (e.kind !== "theorem") continue;
    const gold = new Set<string>();
    for (const r of e.refs ?? []) {
      if (r === e.name) continue;                        // self
      const ref = byName.get(r);
      if (!ref) continue;                                // non-index (Mathlib / pure namespace)
      if (e.name.startsWith(r + ".")) continue;          // own-namespace ancestor
      if (!GOLD_KINDS.has(ref.kind)) continue;           // instance / other non-API
      gold.add(r);
    }
    if (gold.size === 0) continue;
    out.push({
      theorem: e.name,
      cluster: fileToCluster(e.file),
      gold: [...gold].sort(),
      doc: firstPara(e.doc),
      statement: e.statement,
    });
  }
  return out;
}

/** Document-frequency IDF of each gold decl across all pairs: ln((N+1)/(df+1)).
 *  A decl in nearly every statement (carrier type) → idf≈0; a rare decl → high idf. */
export function computeGoldIdf(pairs: GoldPair[]): Map<string, number> {
  const df = new Map<string, number>();
  for (const p of pairs) for (const g of p.gold) df.set(g, (df.get(g) ?? 0) + 1);
  const N = pairs.length;
  const idf = new Map<string, number>();
  for (const [d, c] of df) idf.set(d, Math.log((N + 1) / (c + 1)));
  return idf;
}

/** The discriminating subset of a pair's gold: decls with idf ≥ floor (carriers dropped). */
export function coreGold(gold: string[], idf: Map<string, number>, floor = IDF_FLOOR): string[] {
  return gold.filter((g) => (idf.get(g) ?? Infinity) >= floor);
}
