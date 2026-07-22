import { resolve } from "node:path";
import { readFileSync } from "node:fs";
import { createRetrieval } from "../src/formalization/reuse_retrieval.js";
import { loadSemanticTier, embedQueries } from "../src/formalization/semantic_tier.js";

/**
 * Goal-mode premise-selection benchmark.
 *
 * Derives a leak-free eval directly from the index's `proofRefs` graph: for a held-out sample of
 * theorems, the "goal" is the theorem's statement and the gold premises are the constants its
 * proof actually used (`proofRefs`). We measure how well `--goal` mode retrieves those premises.
 *
 *   npx tsx bin/premise_eval.ts [--frac 0.09] [--k 10] [--min-refs 2] [--root <causaleanRoot>]
 *
 * Reports two arms:
 *   goal+semantic  — the shipped hybrid premise selector (proofRefs of similar theorems ⊕ symbol overlap)
 *   goal fallback  — symbol-overlap only (what `--goal` did before, and the no-embeddings degrade path)
 *
 * IMPORTANT: each query theorem is passed via `exclude` so it cannot be its own top neighbour and
 * leak its own proofRefs — without this the hybrid arm is inflated (~0.42 vs the honest ~0.28).
 * Needs fresh embeddings (`npm run embed:library`); without them the semantic arm == fallback.
 */

const argv = process.argv.slice(2);
const flag = (name: string, def: string): string => {
  const i = argv.indexOf(name);
  return i >= 0 && argv[i + 1] !== undefined ? argv[i + 1] : def;
};

const root = resolve(flag("--root", resolve(import.meta.dirname, "..", "..", "..")));
const frac = Number(flag("--frac", "0.09"));
const K = Number(flag("--k", "10"));
const minRefs = Number(flag("--min-refs", "2"));

const idx = JSON.parse(readFileSync(resolve(root, "doc", "library_index.json"), "utf8")) as {
  entries: { name: string; kind: string; statement?: string; proofRefs?: string[] }[];
};

// deterministic FNV-1a sample so the test set is stable across runs
const hash = (s: string): number => {
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
  return (h >>> 0) / 2 ** 32;
};
const test = idx.entries.filter(
  (e) => e.kind === "theorem" && (e.proofRefs?.length ?? 0) >= minRefs && e.statement && hash(e.name) < frac,
);

const r = createRetrieval(root);
if (!r.library) { console.error(`No index at ${root}/doc/library_index.json`); process.exit(1); }
const tier = loadSemanticTier(root, (n) => r.get(n)?.file);
if (!tier) console.error("[premise_eval] semantic tier unavailable/stale — the semantic arm will equal fallback (run `npm run embed:library`).");
const vecs = tier ? embedQueries(test.map((e) => e.statement!), root) : [];

type Acc = { rec: number; hit: number; mrr: number; n: number };
const mk = (): Acc => ({ rec: 0, hit: 0, mrr: 0, n: 0 });
const hybrid = mk(), fallback = mk();
const tally = (a: Acc, ranked: string[], gold: Set<string>) => {
  a.n++;
  const top = ranked.slice(0, K);
  const inter = top.filter((n) => gold.has(n)).length;
  a.rec += inter / gold.size;
  if (inter > 0) a.hit++;
  const first = top.findIndex((n) => gold.has(n));
  if (first >= 0) a.mrr += 1 / (first + 1);
};

test.forEach((e, k) => {
  const self = e.name;
  const gold = new Set((e.proofRefs ?? []).filter((n) => n !== self));
  if (gold.size === 0) return;
  const exclude = new Set([self]);
  const names = (hits: { name: string }[]) => hits.map((h) => h.name).filter((n) => n !== self);
  const sem = tier ? { tier, queryVec: vecs[k] } : undefined;
  tally(hybrid, names(r.search({ mode: "goal", goalType: e.statement! }, { topK: 40, semantic: sem, exclude })), gold);
  tally(fallback, names(r.search({ mode: "goal", goalType: e.statement! }, { topK: 40, exclude })), gold);
});

const p = (a: Acc, key: keyof Acc) => (a.n ? (a[key] as number) / a.n : 0).toFixed(3);
console.log(`premise-selection eval · ${test.length} held-out theorems (goal=statement, gold=proofRefs, self-excluded) · recall@${K}`);
console.log(`  goal+semantic (hybrid)   recall@${K}=${p(hybrid, "rec")}  hit@${K}=${p(hybrid, "hit")}  MRR=${p(hybrid, "mrr")}`);
console.log(`  goal fallback (symbol)   recall@${K}=${p(fallback, "rec")}  hit@${K}=${p(fallback, "hit")}  MRR=${p(fallback, "mrr")}`);
