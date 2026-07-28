#!/usr/bin/env -S npx tsx
/** Guarded canonical fingerprint recovery for a resolved, agent-authored OEQ. */
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { StatementSchema } from "../src/discovery/core/schema.js";
import { oeqSourceFingerprint } from "../src/discovery/solve/context.js";
import { escalationLogPath, loadWorkingState, saveWorkingState } from "../src/discovery/stages/d0_working.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import { readFile } from "node:fs/promises";

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const sourceId = cli.value("--source-id");
  const rawEntry = cli.value("--from-escalation-entry");
  const fromProto = cli.bool("--from-proto");
  const changeSide = cli.value("--change-side") ?? "from";
  if (!qid || !spec || !sourceId || (!fromProto && (rawEntry === undefined || !/^\d+$/.test(rawEntry))) ||
      (fromProto && rawEntry !== undefined) || !["from", "to"].includes(changeSide)) {
    throw new Error(
      "Usage: d0_repair_agent_oeq_fingerprint.ts <qid> <spec> --source-id <oeq:id> (--from-proto | --from-escalation-entry <zero-based-index> [--change-side from|to])",
    );
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
  const working = await loadWorkingState(ctx);
  if (!working) throw new Error("missing d0 working state");
  const mapping = working.resolved_oeqs?.[sourceId];
  if (!mapping || typeof mapping === "string") throw new Error(`missing structured resolution for ${sourceId}`);
  const theorem = working.solved[mapping.theorem_id];
  if (!theorem?.node || theorem.owner !== sourceId || theorem.node.id !== mapping.theorem_id) {
    throw new Error(`answer theorem ${mapping.theorem_id} does not durably belong to ${sourceId}`);
  }
  const proto = JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")) as { statements?: unknown[] };
  const protoSource = (proto.statements ?? []).find((statement) =>
    statement !== null && typeof statement === "object" && (statement as { id?: string }).id === sourceId,
  );
  if (fromProto !== (protoSource !== undefined)) {
    throw new Error(fromProto
      ? `${sourceId} is not frozen in proto_core`
      : `${sourceId} is frozen in proto_core; use --from-proto instead of a journal snapshot`);
  }
  // Read the raw journal row: readEscalationLog intentionally repairs LaTeX strings
  // recursively, but `changed.from/to` is itself JSON text and must remain opaque until
  // its own JSON.parse below.
  let source;
  if (fromProto) {
    source = StatementSchema.parse(protoSource);
  } else {
    const entryIndex = Number(rawEntry);
    const rawRows = (await readFile(escalationLogPath(ctx), "utf8"))
      .split("\n").filter((line) => line.trim().length > 0);
    const entry = rawRows[entryIndex] ? JSON.parse(rawRows[entryIndex]) as {
      changed: Array<{ id: string; kind: string; from: string; to: string }>;
    } : undefined;
    if (!entry) throw new Error(`missing escalation entry ${entryIndex}`);
    const changes = entry.changed.filter((change) => change.id === sourceId && change.kind === "statement");
    if (changes.length !== 1) throw new Error(`expected exactly one statement change for ${sourceId} in entry ${entryIndex}`);
    source = StatementSchema.parse(JSON.parse(changeSide === "from" ? changes[0].from : changes[0].to));
  }
  if (source.id !== sourceId || source.kind !== "openendedquestion" || source.status !== "to-prove") {
    throw new Error(`${fromProto ? "proto_core" : `entry ${rawEntry}`} does not contain the exact pre-resolution OEQ ${sourceId}`);
  }
  const before = mapping.source_fingerprint;
  const after = oeqSourceFingerprint(source);
  if (before === after) throw new Error("fingerprint is already canonical; refusing no-op repair");
  mapping.source_fingerprint = after;
  await saveWorkingState(ctx, working);
  console.log(JSON.stringify({ sourceId, theoremId: mapping.theorem_id, beforeLength: before.length, afterLength: after.length }, null, 2));
}

main().catch((error: unknown) => {
  console.error(`d0_repair_agent_oeq_fingerprint: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
