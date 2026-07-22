// scripts/dev/f25_review_probe.ts — run the F2.5 reviewer ALONE, with NO rewind.
//
// Calls `reviewWithCodex` directly (the reviewer half of F2.5), bypassing
// `runReviewBoundary` — so the F2 producer never runs, nothing loops, and the Lean
// scaffold is never edited. Faithful to the live gate: it reuses the exact crosswalk
// skeleton (incl. AUX hidden-def rows) and `crosswalkReviewInstruction`. Use it to
// test prompt / detector changes against a real scaffold and read the raw verdict.
//
// For a BANKED entry the research dir (which `artifactPaths` reads) has been cleaned,
// so this reconstitutes <qid>_<spec>.{tex,md} + _state.json from the bank into the
// research dir, then removes exactly what it created (unless --keep).
//
// Usage (run from tools/, node 20; pre-warm `lake build` of the target modules first
// so codex's lean-lsp probes don't cold-start):
//   npx tsx scripts/dev/f25_review_probe.ts <qid> <spec> [--tex <path>] [--keep]
import path from "node:path";
import { fileURLToPath } from "node:url";
import { existsSync } from "node:fs";
import { copyFile, mkdir, readdir, rm } from "node:fs/promises";
import { loadState } from "../../src/state.js";
import { defaultDeps, artifactPaths } from "../../src/pipeline_support.js";
import { reviewWithCodex } from "../../src/formalization/review_codex.js";
import { buildCrosswalkSkeleton, crosswalkReviewInstruction } from "../../src/formalization/crosswalk.js";
import { formalizationDir, statePath, mdPath, texPath } from "../../src/paths.js";
import type { PipelineContext } from "../../src/types.js";

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..", ".."); // CausalSmith/

const argv = process.argv.slice(2);
const keep = argv.includes("--keep");
const texIdx = argv.indexOf("--tex");
const texOverride = texIdx >= 0 ? argv[texIdx + 1] : undefined;
const positional = argv.filter((a, i) => !a.startsWith("--") && argv[i - 1] !== "--tex");
const [qid, spec] = positional;
if (!qid || !spec) {
  console.error("usage: npx tsx scripts/dev/f25_review_probe.ts <qid> <spec> [--tex <path>] [--keep]");
  process.exit(2);
}

const bankDir = path.join(repoRoot, "doc/research/_bank/accepted", `${qid}_${spec}`);
const resDir = formalizationDir(repoRoot, qid);
const stateFile = statePath(repoRoot, qid, spec);
const mdFile = mdPath(repoRoot, qid, spec);
const texFile = texPath(repoRoot, qid, spec);

// Reconstitute any missing research artifact from the bank; track what we created.
const created: string[] = [];
const dirPreexisted = existsSync(resDir);
async function ensure(target: string, sources: string[]): Promise<void> {
  if (existsSync(target)) return;
  const src = sources.find((s) => existsSync(s));
  if (!src) throw new Error(`cannot reconstitute ${path.basename(target)} — no bank source found in ${bankDir}`);
  await mkdir(path.dirname(target), { recursive: true });
  await copyFile(src, target);
  created.push(target);
}

async function texSources(): Promise<string[]> {
  if (texOverride) return [path.isAbsolute(texOverride) ? texOverride : path.join(repoRoot, texOverride)];
  const fixed = [
    path.join(bankDir, `${qid}_${spec}.tex`),
    path.join(bankDir, `${qid}_${spec}_LOCKED_d05accept_field.tex`),
    path.join(bankDir, `${qid}_${spec}_d0r_best.tex`),
  ];
  // Fallback: any `<qid>_<spec>*field*.tex` in the bank (the accepted note snapshot).
  const globbed = existsSync(bankDir)
    ? (await readdir(bankDir))
        .filter((f) => f.startsWith(`${qid}_${spec}`) && f.endsWith(".tex") && f.includes("field"))
        .map((f) => path.join(bankDir, f))
    : [];
  return [...fixed, ...globbed];
}

try {
  await ensure(stateFile, [path.join(bankDir, `${qid}_${spec}_state.json`)]);
  await ensure(mdFile, [path.join(bankDir, `${qid}_${spec}.md`)]);
  await ensure(texFile, await texSources());

  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: false };
  const state = await loadState(repoRoot, qid, spec);
  const deps = defaultDeps(ctx);
  const leanDir = artifactPaths(ctx, state).leanDir;

  const skeleton = await buildCrosswalkSkeleton(leanDir, artifactPaths(ctx, state).md);
  const instruction = crosswalkReviewInstruction(skeleton);
  console.error(`[probe] qid=${qid} spec=${spec} leanDir=${leanDir}`);
  console.error(`[probe] skeleton obj_ids: ${skeleton.map((e) => e.obj_id).join(", ")}`);
  console.error("[probe] invoking F2.5 reviewer (reviewWithCodex, no rewind)…");

  const review = await reviewWithCodex({ ctx, state, deps }, "stage2_5_AH.txt", "2.5", instruction);
  console.log("\n================ F2.5 VERDICT ================");
  console.log(JSON.stringify(review, null, 2));
} finally {
  if (!keep) {
    for (const f of created) await rm(f, { force: true });
    // Remove the research dir only if WE created it and it is now empty.
    if (!dirPreexisted && existsSync(resDir) && (await readdir(resDir)).length === 0) {
      await rm(resDir, { recursive: true, force: true });
    }
    if (created.length > 0) console.error(`[probe] cleaned up ${created.length} reconstituted file(s).`);
  } else if (created.length > 0) {
    console.error(`[probe] --keep: left ${created.length} reconstituted file(s) in ${resDir}`);
  }
}
