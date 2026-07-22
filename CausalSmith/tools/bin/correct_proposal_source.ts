#!/usr/bin/env -S npx tsx
/** Apply a guarded literature-only correction without authoring a new proposal version. */
import process from "node:process";
import { applyProposalSourceCorrection } from "../src/discovery/proposal_source_correction.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";

function take(args: string[], flag: string): string | undefined {
  const i = args.indexOf(flag);
  if (i < 0) return undefined;
  const value = args[i + 1];
  if (!value || value.startsWith("--")) throw new Error(`${flag} requires a value`);
  args.splice(i, 2);
  return value;
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const from = take(args, "--from");
  const to = take(args, "--to");
  const [qid, specialization] = args;
  if (!qid || !specialization || !from || !to) {
    throw new Error("Usage: correct_proposal_source.ts <qid> <spec> --from <exact-text> --to <replacement>");
  }
  const result = await applyProposalSourceCorrection(
    findCausalSmithRoot(process.cwd()),
    qid,
    specialization,
    from,
    to,
  );
  console.error(
    `[proposal-source-correction] ${qid}/${specialization}: ${result.coreReplacements} core + ` +
      `${result.handoffReplacements} handoff replacement(s); core=${result.corePath}`,
  );
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exitCode = 1;
});
