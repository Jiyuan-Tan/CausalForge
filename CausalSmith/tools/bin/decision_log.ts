#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only: append to / read the hierarchical orchestrator's judgment log at
 * `<run dir>/orchestrator/decision_log.jsonl`. This is the durable working memory of the
 * main / D-stage / F-stage orchestrators (see the causalsmith-main skill). Entry types:
 * judgment | escalation | command | terminal | dispatch.
 *
 * Usage:
 *   npx tsx tools/bin/decision_log.ts append <qid> <spec> --json '<json>'   # or --json -  (stdin)
 *   npx tsx tools/bin/decision_log.ts read   <qid> <spec> [--phase D|F] [--type <t>] [--tail N]
 */
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { appendEntry, readEntries, type DecisionLogEntry } from "../src/decision_log.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";


function main(): void {
  const [sub, ...rest] = process.argv.slice(2);
  const cli = readArgs(rest);
  const [qid, spec] = cli.positionals();
  const repoRoot = findCausalSmithRoot(process.cwd());

  if (sub === "append") {
    let raw = cli.value("--json");
    if (raw === "-") raw = readFileSync(0, "utf8").trim();
    if (!qid || !raw) {
      console.error("Usage: decision_log.ts append <qid> <spec> --json '<json>'");
      process.exitCode = 1;
      return;
    }
    const stamped = appendEntry(repoRoot, qid, JSON.parse(raw) as DecisionLogEntry, spec);
    console.log(JSON.stringify(stamped));
    return;
  }
  if (sub === "read") {
    if (!qid) {
      console.error("Usage: decision_log.ts read <qid> <spec> [--phase D|F] [--type <t>] [--tail N]");
      process.exitCode = 1;
      return;
    }
    const tail = cli.value("--tail");
    const entries = readEntries(repoRoot, qid, {
      phase: cli.value("--phase") as "D" | "F" | undefined,
      type: cli.value("--type") as DecisionLogEntry["type"] | undefined,
      tail: tail !== undefined ? Number(tail) : undefined,
    }, spec);
    for (const e of entries) console.log(JSON.stringify(e));
    return;
  }
  console.error("Usage: decision_log.ts <append|read> <qid> <spec> ...");
  process.exitCode = 1;
}
main();
