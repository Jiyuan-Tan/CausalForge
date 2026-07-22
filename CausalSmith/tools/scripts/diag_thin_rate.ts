// One-off diagnostic: how often is the lexical result "thin" (so the semantic tier fires)?
import { loadLibraryLenient, createRetrieval } from "../src/formalization/reuse_retrieval.js";
import { buildGoldPairs, computeGoldIdf, coreGold } from "../src/formalization/retrieval_eval/gold.js";

const ROOT = "../..";
const STRONG = 6, THIN_TOP = 6, MIN_STRONG = 2;
const GENERIC = new Set(["the", "a", "of", "for", "and", "is", "to", "in", "on", "with"]);
function stratum(text: string, core: string[]): "bridgeable" | "gap" {
  const qt = new Set(text.toLowerCase().split(/[^a-z0-9]+/).filter((t) => t.length > 2 && !GENERIC.has(t)));
  for (const g of core) {
    const tail = g.split(".").pop()!.replace(/([a-z0-9])([A-Z])/g, "$1 $2");
    for (const t of tail.toLowerCase().split(/[^a-z0-9]+/)) if (t.length > 2 && qt.has(t)) return "bridgeable";
  }
  return "gap";
}

const lib = loadLibraryLenient(ROOT)!;
const all = buildGoldPairs(lib);
const idf = computeGoldIdf(all);
const pairs = all.filter((p) => coreGold(p.gold, idf).length > 0 && p.doc.length > 0);
const r = createRetrieval(ROOT);

let n = 0, thin = 0, gapN = 0, gapThin = 0, topSum = 0;
const tops: number[] = [];
for (const p of pairs) {
  const hits = r.search({ mode: "concept", title: p.doc }, { cluster: p.cluster, topK: 10, exclude: new Set([p.theorem]) });
  const top = hits[0]?.score ?? 0;
  const strong = hits.filter((h) => h.score >= STRONG).length;
  const isThin = hits.length === 0 || top < THIN_TOP || strong < MIN_STRONG;
  const st = stratum(p.doc, coreGold([...p.gold], idf));
  n++; topSum += top; tops.push(top);
  if (isThin) thin++;
  if (st === "gap") { gapN++; if (isThin) gapThin++; }
}
tops.sort((a, b) => a - b);
console.log(JSON.stringify({
  queries: n,
  thinRate: +(thin / n).toFixed(3),
  gapQueries: gapN,
  gapThinRate: +(gapThin / gapN).toFixed(3),
  avgTopScore: +(topSum / n).toFixed(2),
  medianTopScore: tops[Math.floor(n / 2)],
  thresholds: { THIN_TOP, MIN_STRONG, STRONG },
}, null, 2));
