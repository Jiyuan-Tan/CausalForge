#!/usr/bin/env -S npx tsx
/** Orchestrator-only guarded repair for redundant write targets in a pending D0 directive. */
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { narrowPendingDirectiveTargets } from "../src/discovery/stages/d0_working.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const owner = cli.value("--owner");
  const drops = cli.values("--drop-target");
  if (!qid || !spec || !owner || drops.length === 0) {
    throw new Error(
      "Usage: d0_narrow_pending_directive.ts <qid> <spec> --owner <id> --drop-target <id> [...]",
    );
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  const result = await narrowPendingDirectiveTargets(ctx, { owner, dropTargets: drops });
  console.log(JSON.stringify(result, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_narrow_pending_directive: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
