#!/usr/bin/env node
/**
 * Post-Stage-3 lint: flag named hypotheses in a Lean file that never appear in
 * their corresponding proof body. Deterministic, fast, name-based — does not
 * invoke Lean.
 *
 * Usage:
 *   npx tsx CausalSmith/tools/bin/lint_unused_hypotheses.ts <lean-file> [<lean-file> …]
 *   npx tsx CausalSmith/tools/bin/lint_unused_hypotheses.ts --json <lean-file>
 *
 * Exit codes:
 *   0  no findings
 *   1  at least one finding (definite or advisory — both warrant review)
 *   2  invocation error (no files, unreadable, etc.)
 */
import { readFileSync, existsSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import {
  formatLintReport,
  lintUnusedHypotheses,
  type LintResult,
} from "../src/formalization/unused_hypothesis_lint.js";

function main(): void {
  const argv = process.argv.slice(2);
  const jsonMode = argv.includes("--json");
  const files = argv.filter((a) => a !== "--json");
  if (files.length === 0) {
    process.stderr.write(
      "usage: lint_unused_hypotheses.ts [--json] <lean-file> [<lean-file> …]\n",
    );
    process.exit(2);
  }
  let exitCode = 0;
  const allResults: Array<{ file: string; result: LintResult }> = [];
  for (const f of files) {
    if (!existsSync(f)) {
      process.stderr.write(`error: file not found: ${f}\n`);
      process.exit(2);
    }
    const src = readFileSync(f, "utf8");
    const result = lintUnusedHypotheses(src);
    allResults.push({ file: f, result });
    if (result.findings.length > 0) exitCode = 1;
  }
  if (jsonMode) {
    process.stdout.write(JSON.stringify(allResults, null, 2) + "\n");
  } else {
    for (const { file, result } of allResults) {
      const rel = path.relative(process.cwd(), file);
      process.stdout.write(`=== ${rel} ===\n`);
      process.stdout.write(formatLintReport(result) + "\n\n");
    }
  }
  process.exit(exitCode);
}

main();
