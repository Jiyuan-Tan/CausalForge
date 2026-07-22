#!/usr/bin/env -S npx tsx
/** Sanctioned D-0.5 reviewer-only rewind after a demonstrated plumbing failure. */
import process from "node:process";
import { invalidateCurrentProposalReview } from "../src/discovery/proposal_review_invalidation.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const reasonIndex = args.indexOf("--reason");
  const reason = reasonIndex >= 0 ? args[reasonIndex + 1] : undefined;
  if (reasonIndex >= 0) args.splice(reasonIndex, 2);
  const [qid, specialization] = args;
  if (!qid || !specialization || !reason) {
    throw new Error(
      "Usage: invalidate_proposal_review.ts <qid> <spec> --reason <demonstrated-plumbing-failure>",
    );
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const result = await invalidateCurrentProposalReview(repoRoot, qid, specialization, reason);
  console.error(
    `[invalidate-proposal-review] ${qid}/${specialization}: reopened D-0.5 angle ${result.angle} ` +
      `v${result.version}; removed ${result.removedIterations} derived iteration row(s); ` +
      `archived receipt=${result.archivedReview}`,
  );
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exitCode = 1;
});
