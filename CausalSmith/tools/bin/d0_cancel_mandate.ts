#!/usr/bin/env -S npx tsx
/** Orchestrator-only: retire one exact D0 edit mandate after mandatory review rejects it. */
import process from "node:process";
import type { PipelineContext } from "../src/types.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";
import { readArgs } from "../src/shared/cli_args.js";
import { withRunHeartbeat } from "../src/shared/run_heartbeat.js";
import { loadState, saveState } from "../src/state.js";
import {
  appendEscalationLog,
  loadWorkingState,
  readEscalationLog,
} from "../src/discovery/stages/d0_working.js";
import {
  makeRequiredCoreEditMandateCancellation,
  assertMandateCancellationIntegrity,
  assertMandateIntegrity,
} from "../src/discovery/solve/mandates.js";

async function main(): Promise<void> {
  const cli = readArgs(process.argv.slice(2));
  const [qid, spec] = cli.positionals();
  const mandateId = cli.value("--mandate-id");
  const reason = cli.value("--reason");
  if (!qid || !spec || !mandateId || !reason?.trim()) {
    throw new Error(
      'Usage: d0_cancel_mandate.ts <qid> <spec> --mandate-id d0m:<sha256> --reason "<mandatory-review rationale>"',
    );
  }
  const repoRoot = findCausalSmithRoot(process.cwd());
  await withRunHeartbeat(repoRoot, qid, spec, async () => {
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, dryRun: false, resume: true };
    const working = await loadWorkingState(ctx);
    if (!working) throw new Error("d0_cancel_mandate: no durable D0 working cursor");
    const [journal, state] = await Promise.all([
      readEscalationLog(ctx),
      loadState(repoRoot, qid, spec),
    ]);
    const consumed = Math.min(working.escalation_entries_consumed ?? 0, journal.length);
    const pending = journal.slice(consumed);
    // Do not resolve/validate the whole live set before locating the requested
    // mandate. This command is the recovery path for a conflicting mandate set:
    // whole-set validation necessarily fails until every rejected conflict has
    // been retired. Verify the immutable records and cancellation history here,
    // then let the ordinary resolver validate the remaining set on the next D0
    // resume.
    const mandates = [
      ...(working.required_core_edit_mandates ?? []),
      ...pending.flatMap((entry) => entry.required_core_edit_mandates ?? []),
    ];
    const uniqueMandates = new Map<string, (typeof mandates)[number]>();
    for (const mandate of mandates) {
      assertMandateIntegrity(mandate);
      uniqueMandates.set(mandate.mandate_id, mandate);
    }
    const cancelled = new Set<string>();
    for (const cancellation of pending.flatMap((entry) => entry.cancelled_core_edit_mandates ?? [])) {
      assertMandateCancellationIntegrity(cancellation);
      if (!uniqueMandates.has(cancellation.mandate_id)) {
        throw new Error(
          `d0_cancel_mandate: cancellation ${cancellation.cancellation_id} names no outstanding mandate ` +
          cancellation.mandate_id,
        );
      }
      cancelled.add(cancellation.mandate_id);
    }
    if (!uniqueMandates.has(mandateId) || cancelled.has(mandateId)) {
      throw new Error(`d0_cancel_mandate: ${mandateId} is not an outstanding exact mandate`);
    }
    const cancellation = makeRequiredCoreEditMandateCancellation({ mandateId, reason });
    if (state.stage_completed !== "-0.5") {
      state.stage_completed = "-0.5";
      await saveState(repoRoot, qid, spec, state);
    }
    await appendEscalationLog(ctx, {
      round: working.round,
      changed: [],
      note: `CANCELLED REQUIRED CORE-EDIT MANDATE ${mandateId}: ${cancellation.reason}`,
      cancelled_core_edit_mandates: [cancellation],
      provenance_only: true,
    });
    console.log(`Cancelled D0 mandate ${mandateId} with audit event ${cancellation.cancellation_id}.`);
  });
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
