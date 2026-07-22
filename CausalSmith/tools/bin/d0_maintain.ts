#!/usr/bin/env -S npx tsx
/**
 * Orchestrator-only sanction: mark a frozen proto assumption as MAINTAINED — a
 * disclosed, high-level condition the note is stated CONDITIONAL on and does NOT
 * derive (the legitimate slot for "proved under condition A, where verifying A is
 * itself the open object"). The solver may NEVER self-serve this (stage0_solve.txt);
 * it is an accountable human/orchestrator judgment.
 *
 * Effect (atomic): sets `maintained` on the assumption (clearing standard/novel),
 * surfaces the open object in `honest_scope`, appends an escalation directive telling
 * the next D0 solve to restate every consuming theorem EXPLICITLY conditional on it,
 * flags exactly the assumption's transitive consumers for re-derivation, and resets the
 * stage so `--resume` re-solves. Proofs that do not consume the assumption are
 * PRESERVED — this used to wipe `solved` wholesale. D0.5 then only checks
 * the assumption's SOUNDNESS + SEPARATENESS (not its derivation) and caps the tier one
 * notch (conditional result). See stage0_5_math_review.txt / stage0_5_general_review.txt.
 *
 * Usage:
 *   npx tsx tools/bin/d0_maintain.ts <qid> <spec> --assumption ass:<id> \
 *     --reason "<why this is a legitimate maintained condition>" \
 *     --open-object "<the OEQ: derive/verify A from primitives>" \
 *     --separate-object "<why A constrains a SEPARATE object, not the target's own asymptotics>" \
 *     [--dry-run]
 */
import { existsSync, readFileSync } from "node:fs";
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import { appendEscalationLog, loadWorkingState, saveWorkingState } from "../src/discovery/stages/d0_working.js";
import { CoreSchema } from "../src/discovery/core/schema.js";
import { dependentsOf } from "../src/discovery/core/graph_walk.js";
import { loadState, saveState } from "../src/state.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";


async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cli = readArgs(args);
  const dryRun = args.includes("--dry-run");
  const assId = cli.value("--assumption");
  const reason = cli.value("--reason");
  const openObject = cli.value("--open-object");
  const separateObject = cli.value("--separate-object");
  const positional = args.filter((a, i) => !a.startsWith("--") && !args[i - 1]?.startsWith("--"));
  const [qid, spec] = positional;
  if (!qid || !spec || !assId || !reason || !openObject || !separateObject) {
    console.error(
      'Usage: d0_maintain.ts <qid> <spec> --assumption ass:<id> --reason "..." --open-object "..." --separate-object "..." [--dry-run]',
    );
    process.exitCode = 1;
    return;
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: false };
  const protoPath = protoCoreJsonPath(ctx);
  if (!existsSync(protoPath)) {
    console.error(`No proto at ${protoPath}`);
    process.exitCode = 1;
    return;
  }
  // Parse through CoreSchema, not raw JSON: this CLI writes a CANONICAL store, and an
  // unvalidated write here surfaces as a schema abort inside the next solve, far from
  // the edit that caused it.
  const proto = CoreSchema.parse(JSON.parse(readFileSync(protoPath, "utf8")));
  const ass = (proto.assumptions ?? []).find((a: { id: string }) => a.id === assId);
  if (!ass) {
    console.error(`Assumption ${assId} not found in proto (have: ${(proto.assumptions ?? []).map((a: { id: string }) => a.id).join(", ")})`);
    process.exitCode = 1;
    return;
  }
  // Set the maintained tag (three-way exclusive: clear standard/novel).
  delete ass.standard;
  delete ass.novel;
  ass.maintained = { flag: true, reason, open_object: openObject, separate_object: separateObject, sanctioned_by: "orchestrator" };
  // Surface the open object in honest_scope (the disclosed limitation). The schema
  // types this as an optional string, so there is no array form to handle.
  const disclosure = `OPEN (maintained condition ${assId}): ${openObject}`;
  proto.honest_scope = proto.honest_scope ? `${proto.honest_scope.trimEnd()} ${disclosure}` : disclosure;

  // Only the assumption's transitive consumers need restating; every other proof in
  // the run is untouched by this sanction.
  const working = await loadWorkingState(ctx);
  const affected = working ? [...dependentsOf(proto, [assId])].filter((id) => working.solved[id]) : [];

  if (dryRun) {
    console.log(`[dry-run] would mark ${assId} maintained; honest_scope disclosure + conditional-restate directive.`);
    console.log(
      affected.length > 0
        ? `[dry-run] would flag ${affected.length} consuming proof(s) for re-derivation: ${affected.join(", ")}`
        : `[dry-run] no solved proof consumes ${assId}; nothing to re-derive.`,
    );
    return;
  }
  await writeJsonAtomic(protoPath, proto);

  // Directive: the next solve must restate every consuming theorem EXPLICITLY conditional.
  await appendEscalationLog(ctx, {
    round: 0,
    changed: [],
    directive:
      `ORCHESTRATOR MAINTAINED SANCTION on ${assId}. It is now a MAINTAINED (disclosed, high-level) condition ` +
      `the note is stated CONDITIONAL on and does NOT derive (open object: "${openObject}"; separate object: "${separateObject}"). ` +
      `RESTATE every headline theorem that consumes ${assId} to read EXPLICITLY "under ${assId}, ..."; ensure ${assId} is ` +
      `surfaced in honest_scope and posed as an oeq. Do NOT try to derive ${assId} or re-classify it standard/novel — it is a ` +
      `granted maintained condition; the result is honestly CONDITIONAL on it (tier capped one notch).`,
    note: `orchestrator maintained-sanction: ${assId}`,
  });
  // Flag ONLY the consuming proofs for re-derivation. This used to assign
  // `solved = {}`, discarding every proof in the run — including the ones that never
  // referenced this assumption and were therefore still sound. `partial: true` is the
  // sanctioned re-derive flag: the record and its `proof_tex` survive and are fed back
  // as prior progress, so the next solve EXTENDS the existing argument with the
  // conditional restatement instead of rebuilding the note from nothing.
  if (working && affected.length > 0) {
    for (const id of affected) working.solved[id] = { ...working.solved[id], partial: true };
    await saveWorkingState(ctx, working);
  }
  const state = await loadState(repoRoot, qid, spec);
  state.stage_completed = "-0.5";
  await saveState(repoRoot, qid, spec, state);
  console.log(`Marked ${assId} MAINTAINED (orchestrator-sanctioned). Surfaced in honest_scope + conditional-restate directive logged.`);
  console.log(
    affected.length > 0
      ? `Flagged ${affected.length} consuming proof(s) for re-derivation (other proofs preserved): ${affected.join(", ")}`
      : `No solved proof consumes ${assId}; all existing proofs preserved.`,
  );
  console.log(`Reset stage. Re-run: causalsmith research --resume ${qid} ${spec} --auto --stop-after D0.5`);
  console.log(`D0.5 will check the condition's SOUNDNESS + SEPARATENESS (not its derivation) and cap the tier one notch (conditional).`);
}

main().catch((err: unknown) => {
  console.error(`d0_maintain: ${err instanceof Error ? err.message : String(err)}`);
  process.exitCode = 1;
});
