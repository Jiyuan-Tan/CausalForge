// CLI for the D-stage replay harness (2026-07-30 migration plan, Phase 0).
// The engine lives in src/discovery/replay.ts so its behaviors are unit-testable;
// this file only parses flags, streams the report, and sets the exit code.
//
// Usage: npm run replay [-- --only <substr>] [--verbose]
// Not part of `npm run check` (too slow — it walks ~50 runs and every solve/packet file).

import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { parseReplayArgs, runReplay } from "../src/discovery/replay.js";

const REPO_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const RESEARCH_ROOT = path.join(REPO_ROOT, "doc", "research");

const parsed = parseReplayArgs(process.argv.slice(2));
if ("error" in parsed) {
  console.error(`${parsed.error}\nUsage: npm run replay [-- --only <substr>] [--verbose]`);
  process.exit(2);
}
const { only, verbose } = parsed;

if (!existsSync(RESEARCH_ROOT)) {
  console.error(`research root not found: ${RESEARCH_ROOT}`);
  process.exit(2);
}

const summary = await runReplay({
  researchRoot: RESEARCH_ROOT,
  only,
  verbose,
  log: (line) => console.log(line),
});

console.log("");
console.log(
  `Summary: ${summary.runTotal} runs, ${summary.solveTotal} solve outputs, ${summary.packetTotal} packets.`,
);
if (summary.warnings.length > 0) {
  console.log(`${summary.warnings.length} warning(s) on frozen history (review, not gating):`);
  for (const w of summary.warnings) console.log(`  warn: ${w}`);
}
if (summary.failures.length > 0) {
  console.log(`${summary.failures.length} FAILURE(s):`);
  for (const f of summary.failures) console.log(`  FAIL: ${f}`);
  process.exit(1);
}
console.log("Replay green.");
