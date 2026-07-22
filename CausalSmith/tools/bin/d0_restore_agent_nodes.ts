#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only recovery for a D0 cursor created before agent-authored nodes
 * were made durable across round cleanup.
 *
 * This command is deliberately narrow: it restores only MISSING, non-proto
 * statements, marks them partial/to-prove, validates their dependency closure,
 * checks the expected working round, and commits with saveWorkingState's atomic
 * rename. It never overwrites a surviving proof or mutates the frozen proto.
 *
 * Usage:
 *   npx tsx tools/bin/d0_restore_agent_nodes.ts <qid> <spec> \
 *     --nodes-json <statements.json> --owner <owner-id> --expect-round <n>
 */
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { CoreSchema, StatementSchema, coreNodeIds } from "../src/discovery/core/schema.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import {
  loadWorkingState,
  saveWorkingState,
  snapshotMember,
} from "../src/discovery/stages/d0_working.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


function flag(args: string[], name: string): string | undefined {
  const i = args.indexOf(name);
  return i === -1 ? undefined : args[i + 1];
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const positional = args.filter((a, i) => !a.startsWith("--") && !args[i - 1]?.startsWith("--"));
  const [qid, spec] = positional;
  const nodesJson = flag(args, "--nodes-json");
  const owner = flag(args, "--owner");
  const expectedRoundRaw = flag(args, "--expect-round");
  if (!qid || !spec || !nodesJson || !owner || expectedRoundRaw === undefined) {
    throw new Error(
      "Usage: d0_restore_agent_nodes.ts <qid> <spec> --nodes-json <statements.json> " +
        "--owner <owner-id> --expect-round <n>",
    );
  }
  const expectedRound = Number(expectedRoundRaw);
  if (!Number.isSafeInteger(expectedRound) || expectedRound < 0) {
    throw new Error(`--expect-round must be a nonnegative integer; got ${expectedRoundRaw}`);
  }

  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  const working = await loadWorkingState(ctx);
  if (!working) throw new Error(`No D0 working cursor exists for ${qid}`);
  if (working.round !== expectedRound) {
    throw new Error(`D0 cursor moved: expected round ${expectedRound}, found ${working.round}; no changes written`);
  }

  const proto = CoreSchema.parse(JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")));
  const nodes = StatementSchema.array().min(1).parse(JSON.parse(await readFile(nodesJson, "utf8")));
  const protoIds = coreNodeIds(proto);
  const duplicateInput = nodes.find((node, i) => nodes.findIndex((other) => other.id === node.id) !== i);
  if (duplicateInput) throw new Error(`Duplicate recovery node id: ${duplicateInput.id}`);
  for (const node of nodes) {
    if (protoIds.has(node.id)) {
      throw new Error(`Refusing to restore frozen proto statement ${node.id} as an agent-authored node`);
    }
    if (working.solved[node.id]) {
      throw new Error(`Refusing to overwrite surviving D0 cursor record ${node.id}`);
    }
  }

  const availableIds = new Set(protoIds);
  for (const rec of Object.values(working.solved)) if (rec.node) availableIds.add(rec.node.id);
  for (const node of nodes) availableIds.add(node.id);
  for (const node of nodes) {
    const missing = node.depends_on.filter((id) => !availableIds.has(id));
    if (missing.length > 0) {
      throw new Error(`Cannot restore ${node.id}; missing dependencies: ${missing.join(", ")}`);
    }
  }

  for (const source of nodes) {
    const node = { ...source, status: "to-prove" as const, proof_tex: undefined };
    working.solved[node.id] = {
      proof_tex: source.proof_tex ?? "",
      snapshot: snapshotMember(proto, node),
      node,
      owner,
      partial: true,
    };
  }
  await saveWorkingState(ctx, working);
  console.log(`Restored ${nodes.length} missing D0 agent node(s) at round ${working.round}: ${nodes.map((n) => n.id).join(", ")}`);
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exitCode = 1;
});
