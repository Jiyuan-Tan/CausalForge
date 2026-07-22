#!/usr/bin/env -S npx tsx
/**
 * Orchestrator helper: reset the proposal cursor after a converged-but-
 * cap-exhausted D-0.5 NO-PASS, so a bumped-cap `--resume` continues the good
 * angle instead of re-entering the dead cursor (which re-NO-PASSes) or forcing
 * a bank. Sanctioned, schema-valid writer — never hand-edit `proposed_from`.
 *
 * Re-seats the cursor on `--angle` (default 0), clears `final_verdict`,
 * un-exhausts the angle, and restores that angle's archived draft
 * (`proposal_angle<N>_rejected.tex`) as the active `proposal.tex`.
 *
 * Typical use (after the codex-validity-gate rules a NO-PASS FIXABLE):
 *   npx tsx tools/bin/reset_proposal_cursor.ts <qid> <spec> --angle 0
 *   CAUSALSMITH_NEG1_REVISE_CAP=8 npx tsx tools/bin/causalsmith.ts research --resume --propose "<topic>" <qid> <spec> --novelty field --auto
 *
 * Usage:
 *   reset_proposal_cursor.ts <qid> <spec> [--angle N] [--version V] [--mode revise|pivot|draft-rebuild|kernel-replace] [--no-restore] [--fresh-angle]
 */
import { existsSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { resetProposalCursor, type ProposalMode } from "../src/discovery/proposal_cursor.js";
import { findCausalSmithRoot } from "../src/shared/repo_root.js";


function takeOpt(args: string[], flag: string): string | undefined {
  const i = args.indexOf(flag);
  if (i === -1) return undefined;
  const v = args[i + 1];
  // Guard the lookahead. `--angle --fresh-angle` used to swallow the NEXT FLAG as this
  // option's value and splice it away, so the swallowed flag silently had no effect
  // (a `--fresh-angle` that never ran) while this option got a nonsense value.
  if (v === undefined || v.startsWith("--")) {
    throw new Error(`${flag} requires a value (got ${v === undefined ? "nothing" : `the flag '${v}'`}).`);
  }
  args.splice(i, 2);
  return v;
}

const VALID_MODES: ReadonlySet<string> = new Set([
  "cold-start",
  "revise",
  "pivot",
  "kernel-replace",
  "draft-rebuild",
]);

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const angleRaw = takeOpt(args, "--angle");
  const versionRaw = takeOpt(args, "--version");
  const modeRaw = takeOpt(args, "--mode");
  const noRestoreIdx = args.indexOf("--no-restore");
  const restoreArchived = noRestoreIdx === -1;
  if (noRestoreIdx !== -1) args.splice(noRestoreIdx, 1);
  const freshAngleIdx = args.indexOf("--fresh-angle");
  const freshAngle = freshAngleIdx !== -1;
  if (freshAngleIdx !== -1) args.splice(freshAngleIdx, 1);

  const [qid, spec] = args.filter((a) => !a.startsWith("--"));
  if (!qid || !spec) {
    console.error(
      "Usage: reset_proposal_cursor.ts <qid> <spec> [--angle N] [--version V] [--mode revise|pivot|draft-rebuild|kernel-replace] [--no-restore] [--fresh-angle]",
    );
    process.exitCode = 1;
    return;
  }
  if (modeRaw !== undefined && !VALID_MODES.has(modeRaw)) {
    console.error(`Invalid --mode '${modeRaw}'. Valid: ${[...VALID_MODES].join(", ")}.`);
    process.exitCode = 1;
    return;
  }

  const angle = angleRaw !== undefined ? Number.parseInt(angleRaw, 10) : undefined;
  const version = versionRaw !== undefined ? Number.parseInt(versionRaw, 10) : undefined;
  if (angleRaw !== undefined && !Number.isInteger(angle)) {
    console.error(`Invalid --angle '${angleRaw}' (expected an integer).`);
    process.exitCode = 1;
    return;
  }
  if (versionRaw !== undefined && !Number.isInteger(version)) {
    console.error(`Invalid --version '${versionRaw}' (expected an integer).`);
    process.exitCode = 1;
    return;
  }
  if (freshAngle && (versionRaw !== undefined || modeRaw !== undefined)) {
    console.error("--fresh-angle resets to v0/cold-start and cannot be combined with --version or --mode.");
    process.exitCode = 1;
    return;
  }

  const repoRoot = findCausalSmithRoot(process.cwd());
  const result = await resetProposalCursor(repoRoot, qid, spec, {
    angle,
    version,
    mode: modeRaw as ProposalMode | undefined,
    restoreArchived,
    freshAngle,
  });

  console.error(
    `[reset_proposal_cursor] ${qid}/${spec}: cursor -> angle ${result.angle} v${result.version} mode=${result.mode}; ` +
      `cleared verdict=${result.clearedVerdict ?? "(none)"}; exhausted_angles=[${result.exhausted_angles.join(",")}]; ` +
      `restored .tex=${result.restored ?? "(no archive)"}; restored proto_core=${result.restoredProtoCore ?? "(no archive)"}; ` +
      (result.freshAngle
        ? "cleared angle artifacts/cursor and preserved D-1.1 gaps; resume normally to start D-1.2 v1."
        : "cleared stale draft handoff + set last_draft_status=completed. Resume with a raised CAUSALSMITH_NEG1_REVISE_CAP to give the angle more revise rounds."),
  );
}

main().catch((err) => {
  console.error(err instanceof Error ? err.message : String(err));
  process.exitCode = 1;
});
