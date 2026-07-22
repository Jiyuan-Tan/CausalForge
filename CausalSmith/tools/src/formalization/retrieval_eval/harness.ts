import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { createRetrieval, loadLibraryLenient, applyRerank, type Candidate } from "../reuse_retrieval.js";
import { loadSemanticTier } from "../semantic_tier.js";
import { rerankBatch, rerankerAvailable, loadRerankerMeta } from "../reranker_tier.js";
import { poolModules } from "../module_tier.js";
import { buildGoldPairs, computeGoldIdf, coreGold, IDF_FLOOR } from "./gold.js";
import { renderDocQueries, renderParaphraseQueries, type QueryRecord } from "./queries.js";
import { scoreRanking, aggregate, type PerQuery, type Stratum, type Rendering } from "./metrics.js";
import type { ClusterKey } from "../../constants.js";

const GENERIC = new Set(["the", "a", "of", "for", "and", "is", "to", "in", "on", "with"]);

function stratum(queryText: string, gold: string[]): Stratum {
  const qt = new Set(queryText.toLowerCase().split(/[^a-z0-9]+/).filter((t) => t.length > 2 && !GENERIC.has(t)));
  for (const g of gold) {
    const tail = g.split(".").pop()!.replace(/([a-z0-9])([A-Z])/g, "$1 $2");
    for (const t of tail.toLowerCase().split(/[^a-z0-9]+/)) if (t.length > 2 && qt.has(t)) return "bridgeable";
  }
  return "gap";
}

// `root` = Causalean package root (holds doc/library_index.json + doc/library_embeddings.*);
// from CausalSmith/tools that is "../..". `evalDir` = where reports/anchor live (CausalSmith doc).
export interface HarnessOpts { root: string; evalDir: string; paraphraseSample: number; nPara: number; topK: number; querySample?: number; lexConfident?: number; testModulesPath?: string; simFloor?: number; kSem?: number; rerank?: boolean; graphProp?: number; fusion?: "rrf" | "weighted"; wLex?: number; wDense?: number; module?: boolean; gate?: boolean; }

export interface AnchorRow { item: string; cluster: ClusterKey | null; gold: string[]; }

/** Parse the hand-labeled anchor set (one JSON object per line). */
export function loadAnchor(p: string): AnchorRow[] {
  return fs.readFileSync(p, "utf8").split(/\r?\n/).filter((l) => l.trim()).map((l) => JSON.parse(l) as AnchorRow);
}

/** Embed query texts via the python sentence-transformers helper; returns a per-row vector getter. */
function embedTexts(texts: string[], tag: string, dim: number): (i: number) => Float32Array {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), `reval_${tag}_`));
  try {
    const txt = path.join(dir, "queries.txt");
    const out = path.join(dir, "queries.f32");
    fs.writeFileSync(txt, texts.map((t) => t.replace(/\n/g, " ")).join("\n"));
    // A stuck model load or a wedged embed daemon must NOT stall the eval forever: cap the
    // subprocess (mirrors embedQueries in semantic_tier.ts). On timeout execFileSync throws,
    // which the callers catch to degrade the semantic arms to lexical.
    execFileSync("python3", ["scripts/embed_text.py", "--out", out], {
      input: fs.readFileSync(txt), cwd: process.cwd(),
      timeout: 180_000, maxBuffer: 64 * 1024 * 1024,
    });
    const buf = fs.readFileSync(out);
    const all = new Float32Array(buf.buffer, buf.byteOffset, buf.byteLength / 4);
    return (i: number) => all.subarray(i * dim, (i + 1) * dim);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

type EvalItem = {
  qid: string; theorem: string; rendering: Rendering; variant: number;
  text: string; gold: Set<string>; cluster: ClusterKey | null;
};

export async function runHarness(o: HarnessOpts) {
  const lib = loadLibraryLenient(o.root);
  if (!lib) throw new Error(`missing library_index.json under ${path.join(o.root, "doc")}`);
  // O(1) name→file: the semantic tier's cluster filter calls this per decl per query, so a
  // linear `entries.find` here is O(nDecls² · nQueries) — the eval's real bottleneck.
  const fileByName = new Map(lib.entries.map((e) => [e.name, e.file]));
  const fileOf = (n: string) => fileByName.get(n);
  const allPairs = buildGoldPairs(lib);
  const idf = computeGoldIdf(allPairs);
  const pairs = allPairs.filter((p) => coreGold(p.gold, idf).length > 0);
  const goldOf = new Map(pairs.map((p) => [p.theorem, new Set(p.gold)]));
  const clusterOf = new Map(pairs.map((p) => [p.theorem, p.cluster]));

  const docQ = renderDocQueries(pairs);
  const step = Math.max(1, Math.floor(pairs.length / Math.max(1, o.paraphraseSample)));
  const sample = o.paraphraseSample > 0 ? pairs.filter((_, i) => i % step === 0).slice(0, o.paraphraseSample) : [];
  const paraQ = await renderParaphraseQueries(sample, o.nPara);
  let allQueries: QueryRecord[] = [...docQ, ...paraQ];
  // Leak-free eval: restrict to held-out (test) modules — used to measure a fine-tuned encoder
  // on modules it never trained on (the refs graph is both training signal and eval gold).
  if (o.testModulesPath) {
    const moduleOf = new Map(lib.entries.map((e) => [e.name, e.module]));
    const testSet = new Set(JSON.parse(fs.readFileSync(o.testModulesPath, "utf8")) as string[]);
    allQueries = allQueries.filter((q) => testSet.has(moduleOf.get(q.theorem) ?? ""));
  }
  // Optional deterministic stride subsample of the evaluated queries — for a fast signal
  // while iterating (the semantic arm's JS cosine is O(nQueries · nDecls · dim)). idf/gold
  // are still computed over the FULL corpus, so per-query metrics stay faithful.
  const qs = o.querySample ?? 0;
  const queries: QueryRecord[] =
    qs > 0 && qs < allQueries.length
      ? allQueries.filter((_, i) => i % Math.floor(allQueries.length / qs) === 0).slice(0, qs)
      : allQueries;

  const tier = loadSemanticTier(o.root, fileOf);
  const r = createRetrieval(o.root);
  const noVec = () => new Float32Array();
  const moduleOf = new Map(lib.entries.map((e) => [e.name, e.module]));

  // Phase 3 module fallback arm: pool the fused decl results to modules (top-3 pooling) and ask
  // whether a top-k module CONTAINS a gold decl — the "warm" floor the plan expects to be far
  // higher than decl-level hit@k. Gated behind --module. Uses the production fused (semantic) stack.
  const moduleHit = (items: EvalItem[], qvec: (i: number) => Float32Array, idfMap: Map<string, number>, withSemantic = true) => {
    const rows = items.map((it, i) => {
      const cands = r.search({ mode: "concept", title: it.text }, {
        cluster: it.cluster, topK: 50, exclude: new Set([it.theorem]),
        semantic: withSemantic && tier ? { tier, queryVec: qvec(i), lexConfident: o.lexConfident, simFloor: o.simFloor, kSem: o.kSem } : undefined,
      });
      const mods = poolModules(cands.map((c) => ({ module: c.module, name: c.name, score: c.score })), 3, 3).map((m) => m.module);
      const goldMods = new Set([...it.gold].map((g) => moduleOf.get(g)).filter(Boolean));
      return {
        stratum: stratum(it.text, coreGold([...it.gold], idfMap)),
        h1: mods.length > 0 && goldMods.has(mods[0]),
        h3: mods.slice(0, 3).some((m) => goldMods.has(m)),
      };
    });
    const agg = (s: typeof rows) => ({ n: s.length, hit1: s.filter((x) => x.h1).length / (s.length || 1), hit3: s.filter((x) => x.h3).length / (s.length || 1) });
    return { overall: agg(rows), gap: agg(rows.filter((x) => x.stratum === "gap")), bridgeable: agg(rows.filter((x) => x.stratum === "bridgeable")) };
  };

  // Phase 3 gate: per-query confidence FEATURES from the raw channels (the fused score is a poor
  // signal — bimodal pinned-lexical≥40 vs RRF≈0.01), the production decl-hit@3 LABEL, and the
  // module-fallback hit. Feed a risk–coverage curve: at coverage C (answer the most-confident C at
  // decl level, fall back to modules for the rest) what is decl-hit on answered vs module-hit on
  // fallback, and the combined selective-system hit.
  type GateRow = { top1Dense: number; denseMargin: number; top1Lex: number; agreement: number; qLen: number; declHit3: boolean; moduleHit3: boolean };
  const gateRows = (items: EvalItem[], qvec: (i: number) => Float32Array): GateRow[] =>
    items.map((it, i) => {
      const ex = new Set([it.theorem]);
      const dense = tier ? tier.topK(qvec(i), { k: 10, floor: -1, cluster: it.cluster, exclude: ex }) : [];
      const lex = r.search({ mode: "concept", title: it.text }, { cluster: it.cluster, topK: 10, exclude: ex });
      const fused = r.search({ mode: "concept", title: it.text }, {
        cluster: it.cluster, topK: 50, exclude: ex,
        semantic: tier ? { tier, queryVec: qvec(i), lexConfident: o.lexConfident, simFloor: o.simFloor, kSem: o.kSem } : undefined,
      });
      const d5 = new Set(dense.slice(0, 5).map((h) => h.name));
      const mods = poolModules(fused.map((c) => ({ module: c.module, name: c.name, score: c.score })), 3, 3).map((m) => m.module);
      const goldMods = new Set([...it.gold].map((g) => moduleOf.get(g)).filter(Boolean));
      return {
        top1Dense: dense[0]?.sim ?? 0,
        denseMargin: (dense[0]?.sim ?? 0) - (dense[1]?.sim ?? 0),
        top1Lex: lex[0]?.score ?? 0,
        agreement: lex.slice(0, 5).filter((c) => d5.has(c.name)).length / 5,
        qLen: it.text.split(/\s+/).filter(Boolean).length,
        declHit3: fused.slice(0, 3).some((c) => it.gold.has(c.name)),
        moduleHit3: mods.slice(0, 3).some((m) => goldMods.has(m)),
      };
    });
  const riskCoverage = (rows: GateRow[], conf: (r: GateRow) => number) => {
    const sorted = [...rows].sort((a, b) => conf(b) - conf(a));
    return [0.3, 0.5, 0.7, 1.0].map((cov) => {
      const nAns = Math.max(1, Math.round(sorted.length * cov));
      const answered = sorted.slice(0, nAns), fallback = sorted.slice(nAns);
      const declAns = answered.filter((r) => r.declHit3).length;
      const modFb = fallback.filter((r) => r.moduleHit3).length;
      return {
        cov, nAns,
        declHitAnswered: declAns / (answered.length || 1),
        moduleHitFallback: fallback.length ? modFb / fallback.length : 1,
        combined: (declAns + modFb) / sorted.length, // decl on answered + module on fallback
      };
    });
  };

  // Phase 2c reranked arm: rerank the fused top-`POOL` (bi-encoder recall pool) with the
  // cross-encoder, then take the display top-K. Only runs when opted in AND the model is present.
  const rerankOn = !!o.rerank && !!tier && rerankerAvailable(o.root);
  const POOL = loadRerankerMeta(o.root)?.pool ?? 50;

  // Shared scorer: run one arm over a list of items, given their query-vector getter + idf map.
  const scoreItems = (items: EvalItem[], qvec: (i: number) => Float32Array, idfMap: Map<string, number>, withSemantic: boolean): PerQuery[] =>
    items.map((it, i) => {
      const hits = r.search({ mode: "concept", title: it.text }, {
        cluster: it.cluster,
        topK: o.topK,
        exclude: new Set([it.theorem]),
        semantic: withSemantic && tier ? { tier, queryVec: qvec(i), lexConfident: o.lexConfident, simFloor: o.simFloor, kSem: o.kSem, graphProp: o.graphProp, fusion: o.fusion, wLex: o.wLex, wDense: o.wDense } : undefined,
      });
      return {
        qid: it.qid, theorem: it.theorem, rendering: it.rendering, variant: it.variant,
        stratum: stratum(it.text, coreGold([...it.gold], idfMap)), cluster: it.cluster,
        ...scoreRanking(hits.map((h) => h.name), it.gold, idfMap),
      };
    });

  // Reranked scorer: build the fused top-POOL per item, batch-rerank all pools in one call, take
  // display top-K. A rerank failure (null scores) degrades to the fused order — never worse.
  const scoreRerankedItems = (items: EvalItem[], qvec: (i: number) => Float32Array, idfMap: Map<string, number>): PerQuery[] => {
    const pools: Candidate[][] = items.map((it, i) =>
      r.search({ mode: "concept", title: it.text }, {
        cluster: it.cluster, topK: POOL, exclude: new Set([it.theorem]),
        semantic: tier ? { tier, queryVec: qvec(i), lexConfident: o.lexConfident, simFloor: o.simFloor, kSem: o.kSem, graphProp: o.graphProp, fusion: o.fusion, wLex: o.wLex, wDense: o.wDense } : undefined,
      }));
    const scores = rerankBatch(pools.map((cands, i) => ({ query: items[i].text, names: cands.map((c) => c.name) })));
    return items.map((it, i) => {
      const reranked = scores ? applyRerank(pools[i], scores[i], pools[i].length, o.topK) : pools[i].slice(0, o.topK);
      return {
        qid: it.qid, theorem: it.theorem, rendering: it.rendering, variant: it.variant,
        stratum: stratum(it.text, coreGold([...it.gold], idfMap)), cluster: it.cluster,
        ...scoreRanking(reranked.map((h) => h.name), it.gold, idfMap),
      };
    });
  };

  // ── main arms: dependency-graph proxy (doc + paraphrase queries) ──
  const mainItems: EvalItem[] = queries.map((q) => ({
    qid: q.qid, theorem: q.theorem, rendering: q.rendering, variant: q.variant, text: q.text,
    gold: goldOf.get(q.theorem)!, cluster: clusterOf.get(q.theorem)!,
  }));
  const meta = tier ? JSON.parse(fs.readFileSync(path.join(o.root, "doc", "library_embeddings.meta.json"), "utf8")) as { dim: number } : null;
  const dim = meta?.dim ?? 0;
  let mainVec: (i: number) => Float32Array = noVec;
  let mainSemOk = false;
  if (tier) {
    try { mainVec = embedTexts(mainItems.map((it) => it.text), "q", dim); mainSemOk = true; }
    catch (e) { console.error(`[eval] semantic embed failed (${(e as Error).message}); degrading main arms to lexical`); }
  }
  const arms = {
    lexical: aggregate(scoreItems(mainItems, noVec, idf, false)),
    semantic: mainSemOk ? aggregate(scoreItems(mainItems, mainVec, idf, true)) : null,
    reranked: rerankOn && mainSemOk ? aggregate(scoreRerankedItems(mainItems, mainVec, idf)) : null,
    moduleHit: o.module ? moduleHit(mainItems, mainSemOk ? mainVec : noVec, idf, mainSemOk) : null,
    moduleHitLex: o.module ? moduleHit(mainItems, noVec, idf, false) : null,
  };

  // ── anchor arm: real F1 items hand-labeled with verified Causalean gold (transfer gate) ──
  let anchor: { n: number; lexical: ReturnType<typeof aggregate>; semantic: ReturnType<typeof aggregate> | null; reranked: ReturnType<typeof aggregate> | null; moduleHit: ReturnType<typeof moduleHit> | null; moduleHitLex: ReturnType<typeof moduleHit> | null } | null = null;
  const anchorPath = path.join(o.evalDir, "anchor.jsonl");
  if (fs.existsSync(anchorPath)) {
    const rows = loadAnchor(anchorPath);
    const anchorIdf = new Map(idf); // hand-labeled gold not in the corpus idf is treated as core
    for (const row of rows) for (const g of row.gold) if (!anchorIdf.has(g)) anchorIdf.set(g, IDF_FLOOR);
    const aItems: EvalItem[] = rows.map((row, i) => ({
      qid: `anchor#${i}`, theorem: `anchor#${i}`, rendering: "doc", variant: 0, text: row.item,
      gold: new Set(row.gold), cluster: row.cluster,
    }));
    let aVec: (i: number) => Float32Array = noVec;
    let aSemOk = false;
    if (tier) {
      try { aVec = embedTexts(aItems.map((it) => it.text), "anchor", dim); aSemOk = true; }
      catch (e) { console.error(`[eval] semantic embed failed (${(e as Error).message}); degrading anchor arms to lexical`); }
    }
    anchor = {
      n: rows.length,
      lexical: aggregate(scoreItems(aItems, noVec, anchorIdf, false)),
      semantic: aSemOk ? aggregate(scoreItems(aItems, aVec, anchorIdf, true)) : null,
      reranked: rerankOn && aSemOk ? aggregate(scoreRerankedItems(aItems, aVec, anchorIdf)) : null,
      moduleHit: o.module ? moduleHit(aItems, aSemOk ? aVec : noVec, anchorIdf, aSemOk) : null,
      moduleHitLex: o.module ? moduleHit(aItems, noVec, anchorIdf, false) : null,
    };
  }

  // Phase 3 gate risk–coverage: dump per-query features for offline logistic fitting, and report
  // the risk–coverage curve for candidate single-feature confidence signals on the main queries.
  fs.mkdirSync(o.evalDir, { recursive: true });
  let gate: { n: number; signals: Record<string, ReturnType<typeof riskCoverage>> } | null = null;
  if (o.gate && tier) {
    const rows = gateRows(mainItems, mainVec);
    fs.writeFileSync(path.join(o.evalDir, "gate_data.jsonl"), rows.map((r) => JSON.stringify(r)).join("\n"));
    gate = { n: rows.length, signals: {
      denseMargin: riskCoverage(rows, (r) => r.denseMargin),
      top1Dense: riskCoverage(rows, (r) => r.top1Dense),
      agreement: riskCoverage(rows, (r) => r.agreement),
    } };
  }

  const report = { nPairs: pairs.length, nQueries: queries.length, arms, anchor, gate };
  fs.writeFileSync(path.join(o.evalDir, "report.json"), JSON.stringify(report, null, 2));
  return report;
}
