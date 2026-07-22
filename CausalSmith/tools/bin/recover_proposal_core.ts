#!/usr/bin/env -S npx tsx
/** Recover the latest exact proto core embedded in the D-0.5 reviewer transcript. */
import process from "node:process";
import { recoverProposalCoreFromLatestReviewPrompt } from "../src/discovery/proposal_source_correction.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

async function main(): Promise<void> {
  const [qid, specialization] = process.argv.slice(2);
  if (!qid || !specialization) throw new Error("Usage: recover_proposal_core.ts <qid> <spec>");
  const result = await recoverProposalCoreFromLatestReviewPrompt(
    findCausalSmithRoot(process.cwd()), qid, specialization,
  );
  console.error(
    `[recover-proposal-core] restored ${result.corePath} from ${result.sourceLog}; backup=${result.backupPath}`,
  );
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exitCode = 1;
});
