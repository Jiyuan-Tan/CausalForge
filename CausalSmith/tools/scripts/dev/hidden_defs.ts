// scripts/dev/hidden_defs.ts — inspect the F2.5 hidden-def surface for a scaffold.
//
// Runs the deterministic `findHiddenStatementDefs` BFS (no LLM, no codex) and
// prints every build-inline def/structure/ℝ-quantity reached from a theorem
// STATEMENT that would be surfaced as an `AUX-` crosswalk row. Use it to see what
// F2.5 / F4 will audit, and to debug the reachability filter.
//
// Usage (run from tools/, node 20):
//   npx tsx scripts/dev/hidden_defs.ts <qid> <spec>       # resolve leanDir from state
//   npx tsx scripts/dev/hidden_defs.ts --lean-dir <path>  # any Lean dir (abs or repo-relative)
import path from "node:path";
import { fileURLToPath } from "node:url";
import { existsSync } from "node:fs";
import { findHiddenStatementDefs } from "../../src/formalization/crosswalk.js";
import { loadState } from "../../src/state.js";
import { leanTheoremDir } from "../../src/paths.js";

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..", ".."); // CausalSmith/

function usage(): never {
  console.error(
    "usage:\n" +
      "  npx tsx scripts/dev/hidden_defs.ts <qid> <spec>\n" +
      "  npx tsx scripts/dev/hidden_defs.ts --lean-dir <path>",
  );
  process.exit(2);
}

const argv = process.argv.slice(2);
let leanDir: string;
if (argv[0] === "--lean-dir" && argv[1]) {
  leanDir = path.isAbsolute(argv[1]) ? argv[1] : path.join(repoRoot, argv[1]);
} else if (argv.length >= 2) {
  const [qid, spec] = argv;
  const state = await loadState(repoRoot, qid, spec);
  leanDir = leanTheoremDir(repoRoot, state.lean_subdir);
} else {
  usage();
}

if (!existsSync(leanDir)) {
  console.error(`[hidden_defs] Lean dir not found: ${leanDir}`);
  process.exit(1);
}

const hidden = await findHiddenStatementDefs(leanDir);
console.log(`Lean dir: ${leanDir}`);
console.log(`Hidden statement defs surfaced (${hidden.length}):`);
for (const h of hidden) {
  console.log(
    `  [${h.flavor.padEnd(11)}] ${h.name}  (${h.file}:${h.line})  reachedFrom=${h.reachedFrom.join(",")}`,
  );
}
