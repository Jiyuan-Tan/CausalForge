#!/usr/bin/env -S npx tsx
/** Fail when test counts drift from the committed baseline (lockfile semantics).
 *
 * Motivation: repair batches in this repo have repeatedly deleted or skipped
 * passing tests instead of updating them (coverage laundering) — a green suite
 * cannot notice its own shrinkage. Any drift (shrink, growth, added or removed
 * file) requires rerunning with `--update` and committing the baseline diff,
 * which makes every coverage change visible in review.
 *
 * Counting is AST-based (src/shared/test_coverage.ts): comments, strings, and
 * template literals never count, and `.skip`/`.todo` cases are excluded so
 * parking a test registers as a loss.
 *
 * Usage: check_test_coverage.ts [--update]
 */
import process from "node:process";
import { readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { countTestCases } from "../src/shared/test_coverage.js";

const TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TEST_DIR = path.join(TOOLS_ROOT, "test");
const BASELINE_PATH = path.join(TEST_DIR, "coverage_baseline.json");

async function currentCounts(): Promise<Record<string, number>> {
  const entries = await readdir(TEST_DIR, { recursive: true, withFileTypes: true });
  const counts: Record<string, number> = {};
  for (const entry of entries) {
    if (!entry.isFile() || !entry.name.endsWith(".test.ts")) continue;
    const abs = path.join(entry.parentPath, entry.name);
    const rel = path.relative(TOOLS_ROOT, abs).replaceAll(path.sep, "/");
    counts[rel] = countTestCases(await readFile(abs, "utf8"), rel);
  }
  return Object.fromEntries(Object.entries(counts).sort(([a], [b]) => a.localeCompare(b)));
}

async function main(): Promise<void> {
  const current = await currentCounts();
  if (process.argv.includes("--update")) {
    await writeFile(BASELINE_PATH, `${JSON.stringify(current, null, 2)}\n`, "utf8");
    console.log(`check_test_coverage: baseline updated (${Object.keys(current).length} files).`);
    return;
  }
  let baseline: Record<string, number>;
  try {
    baseline = JSON.parse(await readFile(BASELINE_PATH, "utf8"));
  } catch {
    throw new Error(`check_test_coverage: missing/unreadable ${BASELINE_PATH}; run with --update to create it`);
  }
  const drift: string[] = [];
  for (const file of new Set([...Object.keys(baseline), ...Object.keys(current)])) {
    const was = baseline[file];
    const now = current[file];
    if (was === now) continue;
    if (now === undefined) drift.push(`  - ${file}: removed (baseline ${was})`);
    else if (was === undefined) drift.push(`  - ${file}: new file with ${now} test(s), not in baseline`);
    else drift.push(`  - ${file}: ${was} -> ${now}${now < was ? " (SHRANK)" : ""}`);
  }
  if (drift.length > 0) {
    throw new Error(
      "check_test_coverage: test counts drifted from the committed baseline:\n" +
        drift.join("\n") +
        "\nIf every change is intentional, rerun with --update and commit the baseline diff.",
    );
  }
  console.log(`check_test_coverage: OK (${Object.keys(current).length} files match the baseline).`);
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : error);
  process.exitCode = 1;
});
