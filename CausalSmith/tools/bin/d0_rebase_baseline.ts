#!/usr/bin/env -S npx tsx
/** Rebase an accepted historical D0 core as the frozen baseline for an extension. */
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import { readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { readArgs } from "../src/shared/cli_args.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { parseTypedCore, readTypedCore } from "../src/discovery/core/core_io.js";
import { coreJsonPath } from "../src/discovery/stages/d0_core.js";
import { protoCoreJsonPath } from "../src/discovery/stages/neg1_2_author.js";
import {
  loadWorkingState,
  proposalRevision,
  readEscalationLog,
  workingPath,
  type WorkingState,
} from "../src/discovery/stages/d0_working.js";
import { prepareD0BaselineRebase } from "../src/discovery/stages/d0_rebase_baseline.js";
import { loadState } from "../src/state.js";
import { writeJsonAtomic } from "../src/shared/json_atomic.js";
import type { PipelineContext } from "../src/types.js";
import { commitD0StoreReplacement, recoverPendingApply } from "../src/discovery/stages/d0_apply.js";

const exec = promisify(execFile);

function csv(value: string | undefined): string[] {
  return (value ?? "").split(",").map((x) => x.trim()).filter(Boolean);
}

function required(value: string | undefined, name: string): string {
  if (!value) throw new Error(`d0_rebase_baseline: ${name} is required`);
  return value;
}

async function gitText(repoRoot: string, commit: string, absolutePath: string): Promise<string> {
  const { stdout: top } = await exec("git", ["-C", repoRoot, "rev-parse", "--show-toplevel"]);
  const gitRoot = top.trim();
  const rel = path.relative(gitRoot, absolutePath).split(path.sep).join(path.posix.sep);
  if (rel.startsWith("../")) throw new Error(`artifact ${absolutePath} is outside git root ${gitRoot}`);
  const { stdout } = await exec("git", ["-C", repoRoot, "show", `${commit}:${rel}`], { maxBuffer: 64 * 1024 * 1024 });
  return stdout;
}

export async function main(argv: readonly string[] = process.argv.slice(2)): Promise<void> {
  const knownFlags = new Set([
    "--source-commit", "--expect-source-revision", "--expect-source-round", "--expect-source-ids",
    "--expect-source-proto-ids",
    "--expect-current-revision", "--expect-current-round", "--expect-current-escalation-count",
    "--expect-current-stage", "--expect-current-ids", "--check",
    "--expect-source-stage", "--expect-discard-current-ids", "--expect-discard-current-solved-ids",
    "--retire-f-state",
    "--expect-current-proto-sha256", "--expect-current-working-sha256",
    "--expect-source-state-revision", "--ack-source-revision-divergence",
  ]);
  const unknownFlags = argv.filter((arg) => arg.startsWith("--") && !knownFlags.has(arg));
  if (unknownFlags.length > 0) {
    throw new Error(`d0_rebase_baseline: unknown flag(s): ${unknownFlags.join(", ")}`);
  }
  const cli = readArgs(argv);
  const [qid, spec] = cli.positionals();
  if (!qid || !spec || !/^[a-z0-9_]+$/.test(qid) || !/^[a-z0-9_]+$/.test(spec)) {
    throw new Error("Usage: d0_rebase_baseline.ts <qid> <spec> --source-commit <commit> --expect-source-stage <stage> --expect-source-revision <rev> --expect-source-round <n> --expect-source-ids <csv> --expect-source-proto-ids <csv> --expect-current-revision <rev> --expect-current-round <n> --expect-current-escalation-count <n> --expect-current-stage -0.5 --expect-current-ids <csv> --expect-discard-current-ids <csv> --expect-discard-current-solved-ids <csv> --retire-f-state [--check]");
  }
  const sourceCommitArg = required(cli.value("--source-commit"), "--source-commit");
  const sourceRevision = required(cli.value("--expect-source-revision"), "--expect-source-revision");
  const sourceStateRevision = required(
    cli.value("--expect-source-state-revision"), "--expect-source-state-revision",
  );
  const sourceStage = required(cli.value("--expect-source-stage"), "--expect-source-stage");
  const acceptedSourceStages = new Set(["0.5", "1", "1.5", "2", "2.5", "3", "3.5", "3.7", "4", "5"]);
  if (!acceptedSourceStages.has(sourceStage)) {
    throw new Error("d0_rebase_baseline: historical source must be at or beyond a passed D0.5 stage");
  }
  const currentRevision = required(cli.value("--expect-current-revision"), "--expect-current-revision");
  const expectedCurrentProtoHash = required(
    cli.value("--expect-current-proto-sha256"), "--expect-current-proto-sha256",
  );
  const expectedCurrentWorkingHash = required(
    cli.value("--expect-current-working-sha256"), "--expect-current-working-sha256",
  );
  const expectedStage = required(cli.value("--expect-current-stage"), "--expect-current-stage");
  const sourceRound = Number(required(cli.value("--expect-source-round"), "--expect-source-round"));
  const currentRound = Number(required(cli.value("--expect-current-round"), "--expect-current-round"));
  const currentEscalationEntries = Number(required(
    cli.value("--expect-current-escalation-count"),
    "--expect-current-escalation-count",
  ));
  const sourceIds = csv(required(cli.value("--expect-source-ids"), "--expect-source-ids"));
  const sourceProtoIds = csv(required(cli.value("--expect-source-proto-ids"), "--expect-source-proto-ids"));
  const currentIds = csv(required(cli.value("--expect-current-ids"), "--expect-current-ids"));
  if (!cli.bool("--retire-f-state")) {
    throw new Error("d0_rebase_baseline: --retire-f-state is required for a cross-boundary D0 rebase");
  }
  const discardCurrentIds = csv(required(
    cli.value("--expect-discard-current-ids"), "--expect-discard-current-ids",
  ));
  const discardCurrentSolvedIds = csv(required(
    cli.value("--expect-discard-current-solved-ids"), "--expect-discard-current-solved-ids",
  ));
  if (![sourceRound, currentRound, currentEscalationEntries].every((n) => Number.isSafeInteger(n) && n >= 0)) {
    throw new Error("d0_rebase_baseline: expected rounds/counts must be nonnegative integers");
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  const { stdout: resolvedOut } = await exec("git", ["-C", repoRoot, "rev-parse", "--verify", `${sourceCommitArg}^{commit}`]);
  const sourceCommit = resolvedOut.trim();

  await withRunHeartbeat(repoRoot, qid, spec, async () => {
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
    const pendingApplyPath = path.join(path.dirname(coreJsonPath(ctx)), "d0_apply_transaction.json");
    if (cli.bool("--check") && existsSync(pendingApplyPath)) {
      throw new Error(`d0_rebase_baseline: preview refuses pending transaction at ${pendingApplyPath}`);
    }
    const recovered = await recoverPendingApply(ctx);
    if (recovered !== null) {
      console.log("Recovered an interrupted pre-existing D0 apply transaction; re-run the rebase against its post-image.");
      return;
    }
    const state = await loadState(repoRoot, qid, spec);
    const currentRevisionActual = proposalRevision(state);
    if (expectedStage !== "-0.5" || state.stage_completed !== expectedStage) {
      throw new Error(`d0_rebase_baseline: expected current stage ${expectedStage}, found ${state.stage_completed}`);
    }
    if (currentRevisionActual !== currentRevision) {
      throw new Error(`d0_rebase_baseline: expected state revision ${currentRevision}, found ${currentRevisionActual ?? "<none>"}`);
    }
    const currentWorking = await loadWorkingState(ctx);
    if (!currentWorking) throw new Error(`d0_rebase_baseline: no current cursor at ${workingPath(ctx)}`);
    const currentWorkingBytes = await readFile(workingPath(ctx), "utf8");
    const hash = (text: string): string => createHash("sha256").update(text).digest("hex");
    if (hash(currentWorkingBytes) !== expectedCurrentWorkingHash) {
      throw new Error("d0_rebase_baseline: current working-state content hash mismatch");
    }
    const currentProtoPath = protoCoreJsonPath(ctx);
    const currentProtoBytes = await readFile(currentProtoPath, "utf8");
    if (hash(currentProtoBytes) !== expectedCurrentProtoHash) {
      throw new Error("d0_rebase_baseline: current proto content hash mismatch");
    }
    const currentProto = await readTypedCore(currentProtoPath);
    const escalationLog = await readEscalationLog(ctx);
    const actualEscalationEntries = escalationLog.length;
    if (actualEscalationEntries !== currentEscalationEntries) {
      throw new Error(
        `d0_rebase_baseline: expected ${currentEscalationEntries} escalation rows, found ${actualEscalationEntries}`,
      );
    }
    const sourceCorePath = coreJsonPath(ctx);
    const sourceWorkingPath = workingPath(ctx);
    const sourceProtoPath = protoCoreJsonPath(ctx);
    const stateFile = path.join(path.dirname(path.dirname(sourceCorePath)), "state.json");
    const sourceCore = parseTypedCore(
      await gitText(repoRoot, sourceCommit, sourceCorePath),
      `${sourceCommit}:${path.basename(sourceCorePath)}`,
    );
    const sourceWorking = JSON.parse(await gitText(repoRoot, sourceCommit, sourceWorkingPath)) as WorkingState;
    const sourceProto = parseTypedCore(
      await gitText(repoRoot, sourceCommit, sourceProtoPath),
      `${sourceCommit}:${path.basename(sourceProtoPath)}`,
    );
    const sourceState = JSON.parse(await gitText(repoRoot, sourceCommit, stateFile)) as {
      stage_completed?: string; qid?: string; specialization?: string;
      proposed_from?: { current_angle_index?: number; current_version?: number };
    };
    if (sourceState.stage_completed !== sourceStage || sourceState.qid !== qid || sourceState.specialization !== spec) {
      throw new Error(
        `d0_rebase_baseline: historical state identity/stage mismatch; expected ${qid}/${spec} stage ${sourceStage}`,
      );
    }
    const historicalStateRevision = proposalRevision(sourceState);
    if (historicalStateRevision !== sourceStateRevision) {
      throw new Error(
        `d0_rebase_baseline: expected historical state revision ${sourceStateRevision}, found ` +
          `${historicalStateRevision ?? "<none>"}`,
      );
    }
    if (sourceStateRevision !== sourceRevision && !cli.bool("--ack-source-revision-divergence")) {
      throw new Error(
        "d0_rebase_baseline: historical state/working revisions diverge; explicit " +
          "--ack-source-revision-divergence is required",
      );
    }
    if (sourceStateRevision === sourceRevision && cli.bool("--ack-source-revision-divergence")) {
      throw new Error("d0_rebase_baseline: divergence acknowledgement supplied but no divergence exists");
    }
    const plan = prepareD0BaselineRebase({
      sourceCore,
      sourceProto,
      sourceWorking,
      currentProto,
      currentWorking,
      currentPendingEscalations: escalationLog.slice(currentWorking.escalation_entries_consumed ?? 0),
      expectations: {
        sourceRevision, sourceRound, sourceIds, sourceProtoIds, currentRevision, currentRound,
        currentEscalationEntries, currentIds,
        discardCurrentIds, discardCurrentSolvedIds, qid, specialization: spec,
      },
    });

    if (cli.bool("--check")) {
      console.log(`Validated D0 baseline rebase from ${sourceCommit}; no files mutated.`);
      return;
    }

    const stateAfter = structuredClone(state);
    stateAfter.stage_completed = "-0.5";
    stateAfter.flags.d0_loop_counters = { solve_rounds: 0, revise_rounds: 0, consistency_heals: 0 };
    delete stateAfter.flags.d0_loop_cap_hit;
    stateAfter.flags.proof_loop_counters = {
      iters: 0, scaffold_rounds: 0, stale: 0, tag_reroutes: 0,
      node_strikes: {}, review_error_strikes: {}, last_build_error_sig: "",
    };
    delete stateAfter.flags.proof_loop_cap_hit;
    stateAfter.flags.proof_review_escalation_pending = null;
    stateAfter.flags.missing_architecture = false;
    delete stateAfter.flags.missing_architecture_items;
    stateAfter.flags.f1_revise_directive = null;
    stateAfter.flags.f2_scaffold_directive = null;
    stateAfter.flags.f3_filler_directive = null;
    stateAfter.flags.statement_correction_directive = null;
    stateAfter.flags.general_review_halt = null;
    delete stateAfter.flags.stage0_too_many_conjectures;
    delete stateAfter.flags.redo_math_witness;

    const transactionId = await commitD0StoreReplacement({
      ctx,
      expectedProtoBytes: currentProtoBytes,
      protoAfter: plan.proto,
      workingAfter: plan.working,
      stateAfter,
      note: `REBASED ACCEPTED D0 BASELINE FROM ${sourceCommit}; current-only ids/proofs explicitly discarded by operator expectation`,
    });
    await writeJsonAtomic(path.join(path.dirname(coreJsonPath(ctx)), "d0_baseline_rebase_receipt.json"), {
      transaction_id: transactionId,
      source_commit: sourceCommit,
      source_revision: sourceRevision,
      source_state_revision: sourceStateRevision,
      source_round: sourceRound,
      current_revision: currentRevision,
      current_proto_sha256: expectedCurrentProtoHash,
      current_working_sha256: expectedCurrentWorkingHash,
      current_round: currentRound,
      ids: plan.sourceIds,
      discarded_current_ids: discardCurrentIds,
      discarded_current_solved_ids: discardCurrentSolvedIds,
      rebased_at: new Date().toISOString(),
    });
    console.log(
      `Rebased ${plan.sourceIds.length} accepted core node(s) from ${sourceCommit} onto ` +
        `${currentRevision} round ${currentRound}; stage pinned to D0.`,
    );
  });
}

if (process.argv[1] !== undefined && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  await main().catch((err: unknown) => {
    console.error(err instanceof Error ? err.message : String(err));
    process.exitCode = 1;
  });
}
