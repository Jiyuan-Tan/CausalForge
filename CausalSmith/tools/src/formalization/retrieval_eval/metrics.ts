import { EVAL_KS, IDF_FLOOR } from "./gold.js";
import type { ClusterKey } from "../../constants.js";

export type Rendering = "doc" | "para";
export type Stratum = "bridgeable" | "gap";

export interface Ranked { recallAt: Record<number, number>; hitAt3: boolean; rr: number; }
export interface PerQuery extends Ranked {
  qid: string; theorem: string; rendering: Rendering; variant: number;
  stratum: Stratum; cluster: ClusterKey | null;
}

/** Score a ranked candidate-name list against the gold set.
 *  recall@k is IDF-WEIGHTED: each gold decl contributes its idf, so a ubiquitous carrier
 *  (idf≈0) barely moves the metric. hit@3 and rr are measured on CORE gold (idf ≥ floor)
 *  so a freebie carrier cannot trivially satisfy them. */
export function scoreRanking(ranked: string[], gold: Set<string>, idf: Map<string, number>, floor = IDF_FLOOR): Ranked {
  const w = (g: string) => idf.get(g) ?? 0;
  const denom = [...gold].reduce((s, g) => s + w(g), 0) || 1;
  const recallAt: Record<number, number> = {};
  for (const k of EVAL_KS) {
    let num = 0;
    for (let i = 0; i < Math.min(k, ranked.length); i++) if (gold.has(ranked[i])) num += w(ranked[i]);
    recallAt[k] = num / denom;
  }
  const core = new Set([...gold].filter((g) => w(g) >= floor));
  let rr = 0;
  for (let i = 0; i < ranked.length; i++) if (core.has(ranked[i])) { rr = 1 / (i + 1); break; }
  let hitAt3 = false;
  for (let i = 0; i < Math.min(3, ranked.length); i++) if (core.has(ranked[i])) { hitAt3 = true; break; }
  return { recallAt, hitAt3, rr };
}

function mean(xs: number[]): number { return xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : 0; }

function meanBlock(rows: PerQuery[]) {
  const recallAt: Record<number, number> = {};
  for (const k of EVAL_KS) recallAt[k] = mean(rows.map((r) => r.recallAt[k]));
  return { n: rows.length, recallAt, hitAt3: mean(rows.map((r) => (r.hitAt3 ? 1 : 0))), mrr: mean(rows.map((r) => r.rr)) };
}

/** Paraphrase robustness: mean over theorems of the std-dev of hit@3 across that theorem's `para` variants. */
export function paraphraseVariance(rows: PerQuery[]): number {
  const byThm = new Map<string, number[]>();
  for (const r of rows) if (r.rendering === "para") (byThm.get(r.theorem) ?? byThm.set(r.theorem, []).get(r.theorem)!).push(r.hitAt3 ? 1 : 0);
  const stds: number[] = [];
  for (const hs of byThm.values()) {
    if (hs.length < 2) continue;
    const m = mean(hs);
    stds.push(Math.sqrt(mean(hs.map((h) => (h - m) ** 2))));
  }
  return mean(stds);
}

export function aggregate(rows: PerQuery[]) {
  const by = <T extends string>(key: (r: PerQuery) => T) => {
    const groups: Record<string, PerQuery[]> = {};
    for (const r of rows) (groups[key(r)] ??= []).push(r);
    return Object.fromEntries(Object.entries(groups).map(([k, v]) => [k, meanBlock(v)]));
  };
  return {
    overall: meanBlock(rows),
    byRendering: by((r) => r.rendering),
    byStratum: by((r) => r.stratum),
    byCluster: by((r) => r.cluster ?? "none"),
    paraphraseVariance: paraphraseVariance(rows),
  };
}
