#!/usr/bin/env -S node --import tsx
/**
 * One-off: run the UNIFIED reviewer in DELTA mode (F2.5 alone — single reviewer,
 * no proof-filling, no rewind, no F4 dual pass) over a built graph, and print the
 * per-node faithfulness verdicts. Used to review a migrated tree (Lean linked to
 * an existing F1 plan) without invoking the loop machinery.
 *
 * Usage: node --import tsx tools/bin/f25_delta.ts <qid> <spec> <leanDir>
 * Makes a live Codex call. Run from the CausalSmith package root.
 */
import path from "node:path";
import { existsSync, readFileSync } from "node:fs";
import { loadState } from "../src/state.js";
import { artifactPaths, defaultDeps } from "../src/pipeline_support.js";
import { coreJsonPath } from "../src/discovery/stages/d0_core.js";
import { refreshGraphForGate } from "../src/graph/refresh.js";
import { runReviewer } from "../src/formalization/proof_reviewer.js";
import { saveGraph, graphPath } from "../src/graph/store.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


async function main() {
  const [qid, spec, leanDirArg] = process.argv.slice(2).filter((a) => !a.startsWith("--"));
  if (!qid || !spec || !leanDirArg) {
    console.error("Usage: f25_delta.ts <qid> <spec> <leanDir>");
    process.exit(1);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const ctx = { repoRoot, qid, specialization: spec, dryRun: false, resume: true, noveltyTarget: "field" as const };
  const paths = artifactPaths(ctx, state);
  const deps = defaultDeps(ctx);
  const leanDir = path.isAbsolute(leanDirArg) ? leanDirArg : path.join(repoRoot, leanDirArg);

  const refreshed = await refreshGraphForGate({
    formalizationDir: paths.formalizationDir,
    qid,
    spec,
    leanDir,
    mdPath: paths.md,
  });
  if (!refreshed.graph) {
    console.error(`[f25-delta] no graph for ${qid}_${spec} — build it first.`);
    process.exit(2);
  }
  // Incremental: review only the dirty frontier (nodes whose Lean hash changed
  // since their last passed verdict, + dependents). Pass `--full` to force a
  // complete re-review (every eligible target). Default incremental keeps settled
  // matched nodes stable instead of re-grading them under reviewer non-determinism.
  const full = process.argv.includes("--full");
  const dirty = full ? refreshed.graph.nodes.map((n) => n.id) : refreshed.dirty;
  console.log(`[f25-delta] reviewing ${qid}_${spec}: ${refreshed.graph.nodes.length} nodes, ${dirty.length} ${full ? "(forced full)" : "dirty"}, leanDir=${leanDir}`);

  const reviewed = await runReviewer({
    ctx,
    deps,
    graph: refreshed.graph,
    skeleton: refreshed.skeleton,
    dirty,
    hashes: refreshed.hashes,
    leanDir,
    mode: "delta",
    texPath: paths.tex,
    corePath: coreJsonPath(ctx),
  });

  // Persist verdicts so matched nodes carry passed_hash and are NOT re-reviewed
  // next time (only dirty/changed nodes re-enter the frontier).
  await saveGraph(graphPath(paths.formalizationDir, qid, spec), reviewed.graph);

  console.log(`\n=== F2.5 DELTA VERDICT: ${qid}_${spec} ===`);
  console.log(`overall ok:       ${reviewed.ok}`);
  console.log(`blocking (drift): ${reviewed.blocking.length ? reviewed.blocking.join(", ") : "(none)"}`);
  console.log(`substrate gates:  ${reviewed.substrateGates.length}`);
  for (const g of reviewed.substrateGates) console.log(`  - gate: ${JSON.stringify(g)}`);
  if (reviewed.escalate) console.log(`escalate:         ${reviewed.escalate.kind}: ${reviewed.escalate.reason}`);
  console.log(`\nper-node review.status:`);
  for (const n of reviewed.graph.nodes.filter((x) => ["theorem", "lemma", "assumption", "definition", "setup"].includes(x.kind))) {
    console.log(`  ${n.id.padEnd(5)} ${n.kind.padEnd(11)} ${(n.lean?.decl_name ?? "(unlinked)").slice(0, 40).padEnd(40)} review=${n.review.status}`);
  }
  process.exit(0);
}

main().catch((err) => {
  console.error(err);
  process.exit(70);
});
