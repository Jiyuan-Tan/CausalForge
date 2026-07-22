import { resolve } from "node:path";
import { readFileSync } from "node:fs";
import { createRetrieval, type Query } from "../src/formalization/reuse_retrieval.js";
import { reuseCandidateBlock } from "../src/formalization/reuse_render.js";
import { loadSemanticTier, embedQueries } from "../src/formalization/semantic_tier.js";
import { poolModules } from "../src/formalization/module_tier.js";
import type { ClusterKey } from "../src/constants.js";

/**
 * Interactive CLI for the Causalean reuse/lemma search engine (reuse_retrieval.ts).
 * Lets a human exercise the same retrieval the Stage 2 scaffold brief uses.
 *
 *   npx tsx bin/causalean_search.ts <concept words...>      # concept mode (default)
 *   npx tsx bin/causalean_search.ts --type "<pattern>"      # loogle-style symbol match
 *   npx tsx bin/causalean_search.ts --goal "<goal type>"    # goal-directed (F3 mode)
 *   npx tsx bin/causalean_search.ts --block <f1.md>         # render the scaffold candidate block
 *   npx tsx bin/causalean_search.ts --scope module "<words>" # module/file-level orientation search
 *
 * Flags: --cluster <panel|exactid|partialid|stat>  --k <N>  --root <causaleanRoot>
 *   --scope decl|module|file : decl-level lemma search (default) vs per-file orientation
 *     (ranks over module `/-! -/` docstrings; returns module path · decl count · overview)
 */

const argv = process.argv.slice(2);
const flag = (name: string): string | undefined => {
  const i = argv.indexOf(name);
  if (i < 0) return undefined;
  const v = argv[i + 1];
  argv.splice(i, 2);
  return v;
};

// boolean flag (no value) — strip it before positional parsing
const boolFlag = (name: string): boolean => {
  const i = argv.indexOf(name);
  if (i < 0) return false;
  argv.splice(i, 1);
  return true;
};
const useSemantic = boolFlag("--semantic");

const root = resolve(flag("--root") ?? resolve(import.meta.dirname, "..", "..", ".."));
const kRaw = flag("--k");
const k = kRaw === undefined ? 8 : Number(kRaw);
if (!Number.isInteger(k) || k < 1) {
  console.error(`--k must be a positive integer (got "${kRaw}").`);
  process.exit(1);
}
const block = flag("--block");
const typePattern = flag("--type");
const goal = flag("--goal");

const clusterArg = flag("--cluster");
const CLUSTERS = ["panel", "exactid", "partialid", "stat", "experimentation", "scm"];
if (clusterArg && !CLUSTERS.includes(clusterArg)) {
  console.error(`--cluster must be one of ${CLUSTERS.join(", ")} (got "${clusterArg}"); ignoring.`);
}
const cluster = (clusterArg && CLUSTERS.includes(clusterArg) ? clusterArg : null) as ClusterKey | null;

// --scope decl (default) | module|file : decl-level lemma search vs module/file-level orientation.
// Parse BEFORE positional so the scope value is stripped and never leaks into the query.
const scopeArg = flag("--scope") ?? "decl";
if (scopeArg !== "decl" && scopeArg !== "module" && scopeArg !== "file") {
  console.error(`--scope must be decl|module|file (got "${scopeArg}").`);
  process.exit(1);
}

const positional = argv.filter((a) => !a.startsWith("--")).join(" ").trim();

if (scopeArg === "module" || scopeArg === "file") {
  // Module/file-level orientation — "which area do I read?" rather than "which lemma?". Ranks
  // modules by the MEAN of each module's top-3 member-decl scores from the fused decl search
  // (Phase 3 module fallback, top-3 pooling), showing the module `/-! -/` overview + a few
  // prototype ("e.g.") member decls. Pooling the fused (semantic+lexical) decl scores lands a
  // gold-containing module in the top-3 ~0.80 of the time vs ~0.50 for the old lexical-over-
  // docstring ranking. Semantic is used automatically when embeddings are fresh; else it pools
  // the lexical scores. `--cluster` is now honoured (the decl search restricts to the cluster).
  if (!positional) {
    console.error('module search needs query words, e.g. `--scope module "weak overlap rate"`.');
    process.exit(1);
  }
  const idxPath = resolve(root, "doc", "library_index.json");
  let idx: { modules: Record<string, string>; entries: { module: string; name: string; kind: string }[]; commit: string };
  try {
    idx = JSON.parse(readFileSync(idxPath, "utf8"));
  } catch {
    console.error(`No usable index at ${idxPath} (run \`lake exe library_index\`).`);
    process.exit(1);
  }
  const r = createRetrieval(root);
  if (!r.library) {
    console.error(`No usable index at ${idxPath} (run \`lake exe library_index\`).`);
    process.exit(1);
  }
  const KINDS = new Set(["theorem", "def", "lemma", "structure", "inductive", "instance", "abbrev"]);
  const isAuto = (n: string): boolean =>
    /\.(congr_simp|congr|noConfusion|rec|recAux|casesOn|below|brecOn|sizeOf|eq_def|ext_iff)$|^Causalean\.inst(DecidableEq|Repr)/.test(n);
  const declCount: Record<string, number> = {};
  for (const e of idx.entries) {
    if (!KINDS.has(e.kind) || isAuto(e.name)) continue;
    declCount[e.module] = (declCount[e.module] ?? 0) + 1;
  }
  // Fused decl search (semantic auto-on when fresh), then pool the results to modules.
  let semanticOpt: { tier: ReturnType<typeof loadSemanticTier> & object; queryVec: Float32Array } | undefined;
  let semanticOn = false;
  const tier = loadSemanticTier(root, (n) => r.get(n)?.file);
  if (tier) {
    try {
      const [vec] = embedQueries([positional], root);
      semanticOpt = { tier, queryVec: vec };
      semanticOn = true;
    } catch (e) {
      console.error(`module: query embedding failed (${(e as Error).message}); pooling lexical scores.`);
    }
  } else if (useSemantic) {
    console.error("module: embeddings unavailable/stale (run `npm run embed:library`); pooling lexical scores.");
  }
  const cands = r.search({ mode: "concept", title: positional }, { cluster, topK: 80, semantic: semanticOpt });
  const mods = poolModules(cands.map((c) => ({ module: c.module, name: c.name, score: c.score })), k, 3);
  const short = (n: string): string => n.split(".").slice(-1)[0];
  console.log(
    `index @ ${idx.commit.slice(0, 7)} · ${Object.keys(idx.modules).length} modules · mode=${scopeArg}` +
      `${cluster ? ` · cluster=${cluster}` : ""}${semanticOn ? " · +semantic" : ""} · top-3 pooled · showing ${mods.length}/${k}`,
  );
  for (const m of mods) {
    const overview = String(idx.modules[m.module] ?? "").split(/\n\s*\n/)[0].replace(/^#+\s*/, "").replace(/\s+/g, " ").trim();
    console.log(`\n  [${m.score.toFixed(3)}] ${m.module}   (${m.memberCount} matched · ${declCount[m.module] ?? "?"} decls)`);
    if (overview) console.log(`      ${overview.slice(0, 200)}`);
    if (m.prototypes.length) console.log(`      e.g. ${m.prototypes.map(short).join(", ")}`);
  }
  if (!mods.length) console.log("\n  (no matches)");
  process.exit(0);
}

if (block) {
  const out = reuseCandidateBlock(root, resolve(block), cluster, { semantic: useSemantic });
  console.log(out || "(empty — index/F1 artifact unavailable, or no P-/L- items in the file)");
  process.exit(0);
}

const r = createRetrieval(root);
if (!r.library) {
  console.error(`No usable index at ${root}/doc/library_index.json (run \`lake exe library_index\`).`);
  process.exit(1);
}

let q: Query;
if (typePattern !== undefined) q = { mode: "typePattern", pattern: typePattern };
else if (goal !== undefined) q = { mode: "goal", goalType: goal };
else if (positional) q = { mode: "concept", title: positional };
else {
  console.error('usage: causalean_search [<concept words> | --type "<pat>" | --goal "<type>" | --block <f1.md> | --scope module "<words>"] [--cluster X] [--k N] [--semantic]');
  process.exit(1);
}

let semanticOpt: { tier: ReturnType<typeof loadSemanticTier> & object; queryVec: Float32Array } | undefined;
let semanticOn = false;
if (q.mode === "goal") {
  const tier = loadSemanticTier(root, (n) => r.get(n)?.file);
  if (!tier) {
    console.error("--goal: embeddings unavailable or stale (run `npm run embed:library`); using symbol-overlap only.");
  } else {
    try {
      const [vec] = embedQueries([q.goalType], root);
      semanticOpt = { tier, queryVec: vec };
      semanticOn = true;
    } catch (e) {
      console.error(`--goal: query embedding failed (${(e as Error).message}); using symbol-overlap only.`);
    }
  }
} else if (useSemantic) {
  if (q.mode !== "concept") {
    console.error("--semantic applies to concept mode only; ignoring for --type.");
  } else {
    const tier = loadSemanticTier(root, (n) => r.get(n)?.file);
    if (!tier) {
      console.error("--semantic: embeddings unavailable or stale (run `npm run embed:library`); using lexical only.");
    } else {
      try {
        const [vec] = embedQueries([positional], root);
        semanticOpt = { tier, queryVec: vec };
        semanticOn = true;
      } catch (e) {
        console.error(`--semantic: query embedding failed (${(e as Error).message}); using lexical only.`);
      }
    }
  }
}

const hits = r.search(q, { cluster, topK: k, semantic: semanticOpt });
console.log(
  `index @ ${r.library.commit.slice(0, 7)} · ${r.library.entries.length} decls · mode=${q.mode}` +
    `${cluster ? ` · cluster=${cluster}` : ""}${semanticOn ? " · +semantic" : ""} · showing ${hits.length}/${k}`,
);
for (const h of hits) {
  console.log(`\n  [${Number.isInteger(h.score) ? h.score : h.score.toFixed(3)}] ${h.name}   (${h.matchedVia})`);
  console.log(`      ${h.statement.replace(/\s+/g, " ").slice(0, 140)}`);
  console.log(`      ${h.file}${h.tier1 ? " · tier-1" : ""}${h.usesSorry ? " · ⚠usesSorry" : ""}`);
  if (h.docFirstPara) console.log(`      ${h.docFirstPara.slice(0, 160)}`);
}
if (!hits.length) console.log("\n  (no matches)");
