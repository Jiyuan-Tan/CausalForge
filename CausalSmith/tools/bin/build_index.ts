#!/usr/bin/env -S npx tsx
/**
 * Rebuild `doc/study/index.json` deterministically from `doc/study/nodes/`.
 * Idempotent — running twice produces identical bytes modulo the
 * `generated_at` timestamp.
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import {
  loadAllNodes,
  buildIndex,
  writeIndexAtomic,
} from "../src/shared/graph.js";
import { withGraphWriteLock } from "../src/shared/graph_lock.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


async function main() {
  const args = process.argv.slice(2);
  const dirFlagIdx = args.indexOf("--dir");
  const studyDir =
    dirFlagIdx >= 0
      ? path.resolve(args[dirFlagIdx + 1])
      : path.join(findCausalSmithRoot(process.cwd()), "doc", "study");

  await withGraphWriteLock(studyDir, async () => {
    const nodes = await loadAllNodes(studyDir);
    const index = buildIndex(nodes);
    await writeIndexAtomic(studyDir, index);
    console.log(
      `Wrote ${path.join(studyDir, "index.json")} (${nodes.length} nodes).`,
    );
  });
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
