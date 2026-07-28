#!/usr/bin/env -S npx tsx
/** Main-orchestrator writer for a stale proposal topic that remains injected into D0 prompts. */
import process from "node:process";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { loadState, saveState } from "../src/state.js";

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const topic = cli.value("--topic");
  const expectContains = cli.value("--expect-contains");
  if (!qid || !spec || !topic?.trim() || !expectContains?.trim()) {
    throw new Error("Usage: d0_update_proposed_topic.ts <qid> <spec> --expect-contains <old-fragment> --topic <audited-topic>");
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const state = await loadState(repoRoot, qid, spec);
  const prior = state.proposed_from?.topic;
  if (typeof prior !== "string" || !prior.includes(expectContains)) {
    throw new Error(`current proposed_from.topic does not contain expected fragment ${JSON.stringify(expectContains)}`);
  }
  if (!state.proposed_from) throw new Error("missing proposed_from state");
  const beforeWithoutTopic = JSON.stringify({ ...state, proposed_from: { ...state.proposed_from, topic: undefined } });
  state.proposed_from.topic = topic.trim();
  const afterWithoutTopic = JSON.stringify({ ...state, proposed_from: { ...state.proposed_from, topic: undefined } });
  if (beforeWithoutTopic !== afterWithoutTopic) throw new Error("topic writer changed another state field; refusing save");
  await saveState(repoRoot, qid, spec, state);
  console.log(JSON.stringify({ before: prior, after: state.proposed_from.topic }, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_update_proposed_topic: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
