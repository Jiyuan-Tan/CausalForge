import { runHarness } from "../src/formalization/retrieval_eval/harness.js";

function flag(name: string, def: number): number {
  const i = process.argv.indexOf(`--${name}`);
  return i >= 0 ? Number(process.argv[i + 1]) : def;
}

(async () => {
  const root = process.argv.includes("--root") ? process.argv[process.argv.indexOf("--root") + 1] : "../..";
  const evalDir = "../doc/research/retrieval_eval";
  const lexConfidentRaw = flag("lex-confident", NaN);
  const tmIdx = process.argv.indexOf("--test-modules");
  const testModulesPath = tmIdx >= 0 ? process.argv[tmIdx + 1] : undefined;
  const simFloorRaw = flag("sim-floor", NaN);
  const kSemRaw = flag("k-sem", NaN);
  const graphPropRaw = flag("graph-prop", NaN);
  const wLexRaw = flag("w-lex", NaN);
  const wDenseRaw = flag("w-dense", NaN);
  const fusion = process.argv.includes("--fusion") ? (process.argv[process.argv.indexOf("--fusion") + 1] as "rrf" | "weighted") : undefined;
  const res = await runHarness({ root, evalDir, paraphraseSample: flag("paraphrase-sample", 200), nPara: flag("n-para", 3), topK: flag("k", 10), querySample: flag("query-sample", 0), lexConfident: Number.isNaN(lexConfidentRaw) ? undefined : lexConfidentRaw, testModulesPath, simFloor: Number.isNaN(simFloorRaw) ? undefined : simFloorRaw, kSem: Number.isNaN(kSemRaw) ? undefined : kSemRaw, rerank: process.argv.includes("--rerank"), graphProp: Number.isNaN(graphPropRaw) ? undefined : graphPropRaw, fusion, wLex: Number.isNaN(wLexRaw) ? undefined : wLexRaw, wDense: Number.isNaN(wDenseRaw) ? undefined : wDenseRaw, module: process.argv.includes("--module"), gate: process.argv.includes("--gate") });
  const row = (label: string, b: any) =>
    `${label.padEnd(10)} hit@3=${b.hitAt3.toFixed(3)} wR@3=${b.recallAt[3].toFixed(3)} wR@10=${b.recallAt[10].toFixed(3)} MRR=${b.mrr.toFixed(3)} (n=${b.n})`;
  console.log(`pairs=${res.nPairs} queries=${res.nQueries}`);
  for (const arm of ["lexical", "semantic", "reranked"] as const) {
    const a = res.arms[arm];
    if (!a) continue;
    console.log(`\n== ${arm} ==`);
    console.log(row("overall", a.overall));
    for (const [k, v] of Object.entries(a.byStratum)) console.log(row(` ${k}`, v as any));
    for (const [k, v] of Object.entries(a.byRendering)) console.log(row(` ${k}`, v as any));
    console.log(` paraphrase-variance(hit@3 std) = ${a.paraphraseVariance.toFixed(3)}`);
  }
  const modRow = (label: string, m: { n: number; hit1: number; hit3: number }) =>
    `${label.padEnd(12)} moduleHit@1=${m.hit1.toFixed(3)} moduleHit@3=${m.hit3.toFixed(3)} (n=${m.n})`;
  if (res.arms.moduleHit) {
    console.log(`\n== module fallback (top-3 pooling — does a top-k module contain a gold decl?) ==`);
    console.log(modRow("fused", res.arms.moduleHit.overall));
    console.log(modRow(" gap", res.arms.moduleHit.gap));
    console.log(modRow(" bridgeable", res.arms.moduleHit.bridgeable));
    if (res.arms.moduleHitLex) console.log(modRow("lexical", res.arms.moduleHitLex.overall));
  }
  if (res.gate) {
    console.log(`\n== gate risk–coverage (answer confident C at decl level, else module fallback; n=${res.gate.n}) ==`);
    for (const [sig, curve] of Object.entries(res.gate.signals)) {
      console.log(` signal=${sig}`);
      for (const p of curve as any[])
        console.log(`   cov=${p.cov.toFixed(2)} (n=${p.nAns})  declHit@3(answered)=${p.declHitAnswered.toFixed(3)}  moduleHit@3(fallback)=${p.moduleHitFallback.toFixed(3)}  combined=${p.combined.toFixed(3)}`);
    }
  }
  if (res.anchor) {
    console.log(`\n== anchor (n=${res.anchor.n}, hand-labeled real F1 items — transfer gate) ==`);
    console.log(row("lexical", res.anchor.lexical.overall));
    if (res.anchor.semantic) console.log(row("semantic", res.anchor.semantic.overall));
    if (res.anchor.reranked) console.log(row("reranked", res.anchor.reranked.overall));
    if (res.anchor.moduleHit) console.log(modRow("module(fused)", res.anchor.moduleHit.overall));
    if (res.anchor.moduleHitLex) console.log(modRow("module(lex)", res.anchor.moduleHitLex.overall));
  }
})();
