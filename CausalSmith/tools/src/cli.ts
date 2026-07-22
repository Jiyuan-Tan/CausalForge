import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { fileURLToPath, pathToFileURL } from "node:url";
import { createRequire } from "node:module";
import { runPipeline } from "./pipeline.js";
import { CAP_GATE_FLAGS } from "./cap_gates.js";
import { applyWorkerEnv, leanProjectPathFor } from "./local_config.js";
import {
  formatStageLabel,
  resolveStageHaltId,
  STAGE_HALT_IDS,
  STAGE_HALT_ID_TO_INTERNAL,
  STAGE_ORDER,
  type StageHaltId,
} from "./constants.js";
import type { UpgradeFrom } from "./types.js";
import { isDraftRunner, type DraftRunner } from "./workers/draftAdapter.js";
import { normalizeNoveltyTarget, REVIEWER_TIER_RANK, type NoveltyTarget } from "./novelty.js";
import { isInsightStyleQid } from "./paths.js";
import type { ProposalAngleAction } from "./discovery/proposal_angle_checkpoint.js";
import { findCausalSmithRoot } from "./shared/repo_root.js";


/**
 * Bounded warm-up of the Lean project's `.lake` before a study run, so a cold
 * worktree is detected up front instead of a lean-lsp stage silently parking on
 * a from-scratch `lake serve` compile. Runs `lake build` with a wall-clock cap
 * (`CAUSALSMITH_LEANLSP_WARMUP_MS`, default 10 min; set to 0 to disable when a cold
 * compile is intended and the wait is acceptable). A cap breach → throw with a
 * clear "warm the .lake first" message. A non-timeout build failure is NOT fatal
 * (the tree may carry a pre-existing error unrelated to this run) — warn and let
 * the pipeline's own targeted builds surface real errors.
 */
async function warmUpLeanOrThrow(projectPath: string): Promise<void> {
  const rawCapMs = process.env.CAUSALSMITH_LEANLSP_WARMUP_MS ?? String(10 * 60_000);
  const capMs = Number(rawCapMs);
  if (!Number.isFinite(capMs)) {
    // why: a typo here used to disable the warm-up guard by producing NaN.
    throw new Error(`Invalid CAUSALSMITH_LEANLSP_WARMUP_MS: ${rawCapMs} (expected a number of milliseconds)`);
  }
  if (!(capMs > 0)) return; // opted out: cold compile intended, operator will wait
  const { spawnWithInactivityTimeout } = await import("./workers/spawn.js");
  // Route through the shared spawn helper so a cap breach tree-kills the whole
  // `lake → lean` group. Inactivity is set beyond the cap: a cold build emits
  // steady progress, so ONLY the wall-clock cap should fire.
  const r = await spawnWithInactivityTimeout("lake", ["build"], {
    cwd: projectPath,
    env: process.env,
    inactivityTimeoutMs: capMs + 60_000,
    maxTotalMs: capMs,
  });
  if (r.killedDueToTotalTimeout) {
    throw new Error(
      `lean-lsp cold-start guard: \`lake build\` in ${projectPath} exceeded ` +
        `${Math.round(capMs / 60_000)} min — the worktree's .lake is COLD (a from-scratch compile). ` +
        `Warm it first (\`lake build\` to completion) or run \`causalsmith study\` in the main warm tree. ` +
        `Set CAUSALSMITH_LEANLSP_WARMUP_MS to raise the cap, or 0 to disable this guard.`,
    );
  }
  if (r.exitCode !== 0) {
    // A non-timeout build failure is NOT fatal: the tree may carry a pre-existing
    // error unrelated to this run. Warn and let the pipeline's own targeted
    // builds surface real errors.
    console.warn(
      `[study] warm-up \`lake build\` failed (exit ${r.exitCode}) — proceeding; the ` +
        `pipeline's targeted builds will surface real errors. ${r.stderr.trim().slice(-300)}`,
    );
  }
}

interface CliArgs {
  qid: string;
  specialization?: string;
  resume: boolean;
  dryRun: boolean;
  /** `--auto`: run autonomously (orchestrator decides every checkpoint per the skill; stops only on terminal failure or CKPT 2). */
  auto: boolean;
  proposeTopic?: string;
  noveltyTarget?: NoveltyTarget;
  upgradeFrom?: UpgradeFrom;
  proposerOverride?: DraftRunner;
  fromQuestionOqId?: string;
  /** Debugging knob: halt the pipeline immediately after this stage completes.
   * Pre-existing as the `CAUSALSMITH_STOP_AFTER` env var; the flag is the
   * preferred surface and overrides the env var when both are set. */
  stopAfter?: StageHaltId;
  /** Resume-entry override: begin the (resumed) run AT this stage instead of
   * `nextStage(state.stage_completed)`. Saves hand-editing `state.stage_completed`
   * to re-run a stage (e.g. `--resume --from-stage F2.5`). Only meaningful with
   * `--resume`; ignored on a cold start. Maps to `runPipeline`'s `startStage`. */
  fromStage?: StageHaltId;
  /** `--clear-gate <flag>` (repeatable): clear a resume-blocking cap-gate flag as
   * part of the resume, instead of hand-editing `state.flags`. Each name must be a
   * `CAP_GATES` flag. Resume-only. Maps to `runPipeline`'s `clearGates`. */
  clearGates?: string[];
  /** `--reopen <qid> <spec>`: pull a banked entry back to its working dir and clear `banked`
   *  (inverse of banking's move), so the normal toolchain can operate on it again. */
  reopenMode?: boolean;
  /** `--discharge-gate <qid> <spec> <node_id>`: reopen a banked entry, ungate `<node_id>`,
   *  re-verify from F2.5 (override with `--from-stage`) through F5, and re-bank.
   *  Fused, resumable, idempotent. */
  dischargeGateMode?: boolean;
  /** Lean type name of the gate, forwarded to `gate.ts --ungate --lean-name` so the F5-keyed
   *  disclosure is cleared alongside the node-id-keyed one. Optional. */
  dischargeLeanName?: string;
  /** Gate node id to discharge; set only in `--discharge-gate` mode. */
  dischargeGateNode?: string;
  /** `--downgrade-tier <tier> <qid> <spec>`: lower an existing run's novelty floor to the
   *  achieved tier and re-pass D0.5 (guarded: strictly-below the current floor AND <= the
   *  reviewer-assessed tier). Then continues per `--auto` / halts per `--stop-after`. */
  downgradeTierMode?: boolean;
  /** Target floor tier for `--downgrade-tier` mode. */
  downgradeTier?: NoveltyTarget;
  /** `--angle-action`: resolve a persisted D-0.5 checkpoint and, except for
   * give-up, resume the proposal loop in the same CLI process. */
  angleActionMode?: boolean;
  angleAction?: ProposalAngleAction;
  angleDirective?: string;
  angleDirectiveNote?: string;
  extraRevisions?: number;
}

function warnDeprecatedStopAfter(token: string, id: StageHaltId): void {
  console.warn(
    `[deprecation] --stop-after '${token}' uses the old bare-number form; please use '${id}' instead. The old form will be removed in a future release.`,
  );
}

function parseStopAfterToken(token: string): StageHaltId {
  const resolved = resolveStageHaltId(token);
  if (resolved === null) {
    throw new Error(
      `--stop-after: unrecognized stage '${token}'. Expected one of: ${STAGE_HALT_IDS.join(", ")}`,
    );
  }
  if (resolved.deprecated) warnDeprecatedStopAfter(token, resolved.id);
  return resolved.id;
}

function toInternalStopAfter(id: StageHaltId): (typeof STAGE_ORDER)[number] {
  const internal = STAGE_HALT_ID_TO_INTERNAL[id];
  if (internal === undefined) {
    // TODO(stage-rename-phase-3): wire substage halt IDs through runPipeline.
    throw new Error(
      `--stop-after ${id}: substage halt points (F3.group/fill, F4.codex/claude/d) are not yet supported in this release; use the umbrella stage (e.g. F3, F4) instead.`,
    );
  }
  return internal;
}

function splitParentToken(token: string): { parent_qid: string; parent_spec: string } {
  const idx = token.lastIndexOf("_");
  if (idx <= 0 || idx === token.length - 1) {
    throw new Error(
      `--upgrade expects <parent_qid>_<parent_spec> (e.g. pid_dynamic_iv_compliance_v2); got: ${token}`,
    );
  }
  return { parent_qid: token.slice(0, idx), parent_spec: token.slice(idx + 1) };
}

export function parseArgs(argv: string[]): CliArgs {
  const args = [...argv];
  const dryRunIndex = args.indexOf("--dry-run");
  const dryRun = dryRunIndex !== -1;
  if (dryRun) args.splice(dryRunIndex, 1);

  const autoIndex = args.indexOf("--auto");
  const auto = autoIndex !== -1;
  if (auto) args.splice(autoIndex, 1);

  const proposeIndex = args.indexOf("--propose");
  let proposeTopic: string | undefined;
  if (proposeIndex !== -1) {
    proposeTopic = args[proposeIndex + 1];
    args.splice(proposeIndex, 2);
    if (!proposeTopic)
      throw new Error(
        "Usage: causalsmith research --propose <topic> <qid> <specialization> [--dry-run]",
      );
  }

  const noveltyIndex = args.indexOf("--novelty");
  let noveltyTarget: NoveltyTarget | undefined;
  if (noveltyIndex !== -1) {
    const raw = args[noveltyIndex + 1];
    args.splice(noveltyIndex, 2);
    // Canonical vocabulary is the tier ladder; the two legacy spellings
    // (relative-to-repo / relative-to-literature) are still accepted and normalized.
    const norm = normalizeNoveltyTarget(raw);
    if (!norm) {
      throw new Error("Usage: --novelty <incremental|subfield|field|flagship>");
    }
    noveltyTarget = norm;
  }

  const proposerIndex = args.indexOf("--proposer");
  let proposerOverride: DraftRunner | undefined;
  if (proposerIndex !== -1) {
    const raw = args[proposerIndex + 1];
    args.splice(proposerIndex, 2);
    if (!raw || !isDraftRunner(raw)) {
      throw new Error("Usage: --proposer <codex|claude>");
    }
    proposerOverride = raw;
  }

  const upgradeIndex = args.indexOf("--upgrade");
  let upgradeParent: { parent_qid: string; parent_spec: string } | undefined;
  if (upgradeIndex !== -1) {
    const raw = args[upgradeIndex + 1];
    args.splice(upgradeIndex, 2);
    if (!raw)
      throw new Error("Usage: --upgrade <parent_qid>_<parent_spec>");
    upgradeParent = splitParentToken(raw);
  }

  const axisIndex = args.indexOf("--upgrade-axis");
  let upgradeAxis: UpgradeFrom["upgrade_axis"] | undefined;
  if (axisIndex !== -1) {
    const raw = args[axisIndex + 1];
    args.splice(axisIndex, 2);
    if (
      raw !== "computation" &&
      raw !== "estimation" &&
      raw !== "generalization" &&
      raw !== "mechanism"
    ) {
      throw new Error(
        "Usage: --upgrade-axis <computation|estimation|generalization|mechanism>",
      );
    }
    upgradeAxis = raw;
  }

  if (upgradeParent && !upgradeAxis) {
    throw new Error(
      "--upgrade requires --upgrade-axis <computation|estimation|generalization|mechanism>",
    );
  }
  if (upgradeAxis && !upgradeParent) {
    throw new Error("--upgrade-axis requires --upgrade <parent_qid>_<parent_spec>");
  }
  if (upgradeParent && !noveltyTarget) {
    throw new Error(
      "--upgrade requires --novelty <incremental|subfield|field|flagship>; " +
        "the selected tier must be strictly above the parent's achieved banked tier",
    );
  }

  const fromQuestionIndex = args.indexOf("--from-question");
  let fromQuestionOqId: string | undefined;
  if (fromQuestionIndex !== -1) {
    const raw = args[fromQuestionIndex + 1];
    args.splice(fromQuestionIndex, 2);
    if (!raw)
      throw new Error(
        "Usage: causalsmith research --from-question <oq_id> <qid> <specialization> [--dry-run]",
      );
    fromQuestionOqId = raw;
  }

  // Debugging knob: halt right after the named stage completes. The CLI
  // surface accepts canonical prefixed halt IDs and deprecated bare-number
  // aliases; substages are parsed here but rejected at the dispatch bridge
  // until Phase 3 wires them into runPipeline.
  const stopAfterIndex = args.indexOf("--stop-after");
  let stopAfter: CliArgs["stopAfter"];
  if (stopAfterIndex !== -1) {
    const raw = args[stopAfterIndex + 1];
    args.splice(stopAfterIndex, 2);
    if (!raw) {
      throw new Error(`Usage: --stop-after <stage>  (one of: ${STAGE_HALT_IDS.join(", ")})`);
    }
    stopAfter = parseStopAfterToken(raw);
  }

  // Resume-entry override: `--from-stage <stage>` begins the resumed run AT the
  // named stage (via runPipeline's `startStage`), instead of manually rewriting
  // `state.stage_completed`. Same stage-id vocabulary as `--stop-after`.
  const fromStageIndex = args.indexOf("--from-stage");
  let fromStage: CliArgs["fromStage"];
  if (fromStageIndex !== -1) {
    const raw = args[fromStageIndex + 1];
    args.splice(fromStageIndex, 2);
    if (!raw) {
      throw new Error(`Usage: --from-stage <stage>  (one of: ${STAGE_HALT_IDS.join(", ")})`);
    }
    fromStage = parseStopAfterToken(raw);
  }

  // `--lean-name <Name>`: forwarded to `gate.ts --ungate` by `--discharge-gate`. F5 keys its
  // derived disclosure by the Lean type name while gate.ts keys its own by the node id, so
  // without this the fused wrapper re-banks with the F5 disclosure still in
  // `state.added_assumptions` — the entry reads as gated after the gate is proven.
  const leanNameIndex = args.indexOf("--lean-name");
  let leanName: string | undefined;
  if (leanNameIndex !== -1) {
    const raw = args[leanNameIndex + 1];
    args.splice(leanNameIndex, 2);
    if (!raw) throw new Error("Usage: --lean-name <Name>");
    leanName = raw;
  }

  // Resume-time cap-gate clears: `--clear-gate <flag>`, repeatable. Collected here
  // (each occurrence consumes its value) and validated against CAP_GATES at apply
  // time in runPipeline. Replaces hand-editing state.flags to unblock a resume.
  const clearGates: string[] = [];
  for (;;) {
    const i = args.indexOf("--clear-gate");
    if (i === -1) break;
    const raw = args[i + 1];
    args.splice(i, 2);
    if (!raw || raw.startsWith("--")) {
      throw new Error(
        `Usage: --clear-gate <flag>  (one of: ${CAP_GATE_FLAGS.join(", ")})`,
      );
    }
    if (!CAP_GATE_FLAGS.includes(raw)) {
      throw new Error(
        `--clear-gate: unknown gate '${raw}'. Known gates: ${CAP_GATE_FLAGS.join(", ")}`,
      );
    }
    clearGates.push(raw);
  }

  const reopenIndex = args.indexOf("--reopen");
  const reopenMode = reopenIndex !== -1;
  if (reopenMode) args.splice(reopenIndex, 1);

  const dischargeGateIndex = args.indexOf("--discharge-gate");
  const dischargeGateMode = dischargeGateIndex !== -1;
  if (dischargeGateMode) args.splice(dischargeGateIndex, 1);

  const downgradeTierIndex = args.indexOf("--downgrade-tier");
  const downgradeTierMode = downgradeTierIndex !== -1;
  let downgradeTier: NoveltyTarget | undefined;
  if (downgradeTierMode) {
    const raw = args[downgradeTierIndex + 1];
    args.splice(downgradeTierIndex, 2);
    const norm = normalizeNoveltyTarget(raw);
    if (!norm) {
      throw new Error(
        "Usage: causalsmith research --downgrade-tier <incremental|subfield|field|flagship> <qid> <spec> [--auto] [--stop-after <stage>] [--dry-run]",
      );
    }
    downgradeTier = norm;
  }

  const angleActionIndex = args.indexOf("--angle-action");
  const angleActionMode = angleActionIndex !== -1;
  let angleAction: ProposalAngleAction | undefined;
  if (angleActionMode) {
    const raw = args[angleActionIndex + 1];
    args.splice(angleActionIndex, 2);
    if (raw !== "continue" && raw !== "switch" && raw !== "retry" && raw !== "give-up") {
      throw new Error("Usage: --angle-action <continue|switch|retry|give-up>");
    }
    angleAction = raw;
  }
  const angleDirectiveIndex = args.indexOf("--angle-directive");
  let angleDirective: string | undefined;
  if (angleDirectiveIndex !== -1) {
    angleDirective = args[angleDirectiveIndex + 1];
    args.splice(angleDirectiveIndex, 2);
    if (angleDirective === undefined) throw new Error("Usage: --angle-directive <text|->");
  }
  const angleDirectiveNoteIndex = args.indexOf("--angle-directive-note");
  let angleDirectiveNote: string | undefined;
  if (angleDirectiveNoteIndex !== -1) {
    angleDirectiveNote = args[angleDirectiveNoteIndex + 1];
    args.splice(angleDirectiveNoteIndex, 2);
    if (!angleDirectiveNote) throw new Error("Usage: --angle-directive-note <text>");
  }
  const extraRevisionsIndex = args.indexOf("--extra-revisions");
  let extraRevisions: number | undefined;
  if (extraRevisionsIndex !== -1) {
    const raw = args[extraRevisionsIndex + 1];
    args.splice(extraRevisionsIndex, 2);
    extraRevisions = Number(raw ?? "");
    if (!Number.isInteger(extraRevisions) || extraRevisions <= 0) {
      throw new Error("Usage: --extra-revisions <positive-integer>");
    }
  }
  if ((angleDirective !== undefined || angleDirectiveNote !== undefined || extraRevisions !== undefined) && !angleActionMode) {
    throw new Error("--angle-directive/--angle-directive-note/--extra-revisions require --angle-action");
  }
  if (extraRevisions !== undefined && angleAction !== "retry") {
    throw new Error("--extra-revisions is valid only with --angle-action retry");
  }
  if (angleAction === "retry" && extraRevisions === undefined) {
    throw new Error("--angle-action retry requires --extra-revisions <positive-integer>");
  }
  if (angleAction === "retry" && angleDirective === undefined) {
    throw new Error("--angle-action retry requires --angle-directive <text|->");
  }
  if (angleActionMode && fromStage !== undefined) {
    throw new Error("--from-stage is not valid with --angle-action; the action resumes at D-1.2");
  }

  // Position-independent, like `--dry-run` above: `--resume` may appear
  // anywhere, not only as the first token.
  const resumeIndex = args.indexOf("--resume");
  const resume = resumeIndex !== -1;
  if (resume) args.splice(resumeIndex, 1);

  const unknownOption = args.find((arg) => arg.startsWith("--"));
  if (unknownOption) {
    throw new Error(
      `Unknown research option '${unknownOption}'. Use \`causalsmith study <slug>\` for the substrate builder.`,
    );
  }

  // `--clear-gate` is a resume-only action (it clears a flag on an EXISTING run's
  // state). Reject it on a cold start rather than silently ignoring it.
  if (clearGates.length > 0 && !resume) {
    throw new Error("--clear-gate requires --resume (it clears a flag on an existing run's state).");
  }

  if (reopenMode) {
    const [qid, spec, extra] = args;
    if (!qid || !spec || extra !== undefined) {
      throw new Error("Usage: causalsmith research --reopen <qid> <spec>");
    }
    return {
      qid, specialization: spec, resume, dryRun, auto: false,
      reopenMode: true,
    } as CliArgs;
  }

  if (dischargeGateMode) {
    const [qid, spec, node, extra] = args;
    if (!qid || !spec || !node || extra !== undefined) {
      throw new Error("Usage: causalsmith research --discharge-gate <qid> <spec> <node_id> [--lean-name <Name>]");
    }
    return {
      qid, specialization: spec, resume, dryRun, auto,
      dischargeGateMode: true, dischargeGateNode: node, dischargeLeanName: leanName, fromStage,
    } as CliArgs;
  }

  if (downgradeTierMode) {
    const [qid, spec, extra] = args;
    if (!qid || !spec || extra !== undefined) {
      throw new Error(
        "Usage: causalsmith research --downgrade-tier <incremental|subfield|field|flagship> <qid> <spec> [--auto] [--stop-after <stage>] [--dry-run]",
      );
    }
    // Always a resume operation (it rewrites an existing run's floor and re-passes D0.5).
    return {
      qid, specialization: spec, resume: true, dryRun, auto,
      downgradeTierMode: true, downgradeTier, stopAfter, fromStage,
    } as CliArgs;
  }

  if (angleActionMode) {
    const [qid, spec, extra] = args;
    if (!qid || !spec || extra !== undefined) {
      throw new Error(
        "Usage: causalsmith research --angle-action <continue|switch|retry|give-up> <qid> <spec> [--extra-revisions N] [--angle-directive <text|->] [--auto]",
      );
    }
    return {
      qid,
      specialization: spec,
      resume: true,
      dryRun,
      auto,
      angleActionMode: true,
      angleAction,
      angleDirective,
      angleDirectiveNote,
      extraRevisions,
      stopAfter,
    } as CliArgs;
  }

  // Phase 3: --from-question is the entrypoint form; reject combinations.
  if (fromQuestionOqId) {
    if (proposeTopic) {
      throw new Error("--from-question is mutually exclusive with --propose");
    }
    if (upgradeParent) {
      throw new Error("--from-question is mutually exclusive with --upgrade / --upgrade-axis");
    }
  }

  const [qid, specialization, extra] = args;
  if (!qid || !specialization || extra !== undefined) {
    throw new Error(
      "Usage: causalsmith research [--resume] [--auto] [--propose <topic>] [--proposer <codex|claude>] [--novelty <incremental|subfield|field|flagship>] [--upgrade <parent_qid>_<parent_spec> --upgrade-axis <axis>] [--from-question <oq_id>] [--stop-after <stage>] [--from-stage <stage>] [--clear-gate <flag>] <qid> <specialization> [--dry-run]\n" +
        "  or: causalsmith research --reopen <qid> <spec> [--dry-run]   (pull a banked entry back to its working dir)\n" +
        "  or: causalsmith research --discharge-gate <qid> <spec> <node_id> [--from-stage <stage>] [--auto] [--dry-run]   (reopen, ungate, re-verify F2.5→F5, re-bank)\n" +
        "  or: causalsmith research --downgrade-tier <incremental|subfield|field|flagship> <qid> <spec> [--auto] [--stop-after <stage>] [--dry-run]   (accept an achieved lower tier: lower the novelty floor and re-pass D0.5)\n" +
        "  or: causalsmith research --angle-action <continue|switch|retry|give-up> <qid> <spec> [--extra-revisions N] [--angle-directive <text|->] [--auto]",
    );
  }

  const upgradeFrom: UpgradeFrom | undefined =
    upgradeParent && upgradeAxis
      ? {
          parent_qid: upgradeParent.parent_qid,
          parent_spec: upgradeParent.parent_spec,
          // Placeholder; `loadParentEntry` snaps this to the resolved tier
          // (accepted | downgraded) in stageNeg1_2.
          parent_tier: "accepted",
          upgrade_axis: upgradeAxis,
        }
      : undefined;

  return {
    qid,
    specialization,
    resume,
    dryRun,
    auto,
    proposeTopic,
    noveltyTarget,
    upgradeFrom,
    proposerOverride,
    fromQuestionOqId,
    stopAfter,
    fromStage,
    clearGates: clearGates.length > 0 ? clearGates : undefined,
  };
}

// Test-only alias.
export const parseArgsForTest = parseArgs;

/**
 * Absolute `file://` URL of tsx's ESM loader, for `node --import <spec>` when spawning a
 * `bin/*.ts` child at a cwd where the bare `tsx/esm` specifier would not resolve.
 *
 * `createRequire(import.meta.url)` resolves from `tools/src/`, so it finds
 * `tools/node_modules/tsx` via the package's own export map (no hardcoded dist path)
 * regardless of the child's cwd.
 */
export function tsxEsmSpecifier(): string {
  return pathToFileURL(createRequire(import.meta.url).resolve("tsx/esm")).href;
}

/**
 * Stages that perform NO work: F3/F3.5/F4 are logged pass-throughs whose real execution moved
 * inside the combined F2.5 proof-review loop (see `formalization/dispatcher.ts`).
 */
const PASS_THROUGH_STAGES: readonly StageHaltId[] = ["F3", "F3.5", "F4"];

/**
 * Stage `--discharge-gate` re-enters the pipeline at. Defaults to **F2.5**, matching
 * the documented live-run discharge convention: `gate.ts --ungate` reopens every
 * consumer to `unreviewed`, so the F2.5 delta / added-premise review must re-run to
 * confirm each consumer is now honestly UNCONDITIONAL. Flows F2.5 → F3 → F3.5 → F4 → F5.
 *
 * A `--from-stage` naming a pass-through stage is REFUSED. `gate.ts --ungate` edits only the
 * plan/graph (the hypothesis is re-scaffolded into the `.lean` by F2, never hand-written), so
 * entering at F3/F3.5/F4 drops the hypothesis from the metadata, runs no review, no re-scaffold
 * and no build, and then lets F5 re-bank the entry as `accepted` — publishing a theorem whose
 * Lean is still conditional as though it were unconditional. This previously read as a supported
 * shortcut ("F4 to skip straight to equivalence review") and was valid input.
 */
export function dischargeStartStage(fromStage: StageHaltId | undefined): StageHaltId {
  if (fromStage && PASS_THROUGH_STAGES.includes(fromStage)) {
    throw new Error(
      `discharge-gate: --from-stage ${fromStage} is a pass-through stage — it performs NO verification ` +
        `(F3/F3.5/F4 execute inside the F2.5 proof-review loop). Entering there would re-bank the ` +
        `ungated entry as accepted without re-reviewing, re-scaffolding or rebuilding it. ` +
        `Use --from-stage F2.5 (the default), which re-runs the delta review over the reopened consumers.`,
    );
  }
  return fromStage ?? "F2.5";
}

/** `--reopen <qid> <spec>`: pull a banked entry back to its working dir, clear
 *  `banked`, and stamp `reopened_from` so the normal toolchain can operate on it. */
async function runReopen(repoRoot: string, parsed: CliArgs): Promise<void> {
  const { reopenEntry } = await import("../bin/bank_entry.js");
  const spec = parsed.specialization!;
  const res = await reopenEntry({ repoRoot, qid: parsed.qid, spec, dryRun: parsed.dryRun });
  const rel = path.relative(repoRoot, res.workingDir);
  console.log(
    parsed.dryRun
      ? `[dry-run] would reopen ${parsed.qid}/${spec} (tier ${res.priorTier}) -> ${rel}`
      : `reopened ${parsed.qid}/${spec} (was ${res.priorTier}) -> ${rel}`,
  );
}

/**
 * `--discharge-gate <qid> <spec> <node_id>`: reopen a banked entry, ungate the
 * node (now that its substrate is built), re-verify through F4→F5, and re-bank.
 *
 * Fused, resumable, idempotent: each step is a no-op if already done, so a
 * re-invocation after a reviewer reject just re-runs the tail. When the re-verify
 * does not reach stage 5 (reject), the entry is LEFT reopened at the working dir
 * for manual iteration — no auto-rollback, no re-bank.
 */
async function runDischargeGate(repoRoot: string, parsed: CliArgs): Promise<void> {
  const { reopenEntry, bankEntry } = await import("../bin/bank_entry.js");
  const { formalizationDir } = await import("./paths.js");
  const spec = parsed.specialization!;
  const node = parsed.dischargeGateNode!;
  const workingDir = formalizationDir(repoRoot, parsed.qid);

  // Step 1 — reopen (idempotent: skip when the entry is already at the working dir).
  if (existsSync(workingDir)) {
    console.log(`discharge-gate: working dir present; skipping reopen (idempotent).`);
  } else {
    const res = await reopenEntry({ repoRoot, qid: parsed.qid, spec, dryRun: parsed.dryRun });
    console.log(`discharge-gate: reopened ${parsed.qid}/${spec} (was ${res.priorTier}).`);
  }

  const startId = dischargeStartStage(parsed.fromStage);

  if (parsed.dryRun) {
    console.log(
      `[dry-run] would ungate ${node}, re-verify from ${startId}→F5, and re-bank ${parsed.qid}/${spec}.`,
    );
    return;
  }

  // Step 2 — ungate the node via the existing atomic op (idempotent: no-ops on an
  // already-discharged node). The child runs at `repoRoot` so `gate.ts`'s own
  // `findCausalSmithRoot` lands on the package, but `tsx` is installed under `tools/`, not at
  // `repoRoot` — so a bare `--import tsx/esm` specifier is resolved against the wrong
  // directory and dies `ERR_MODULE_NOT_FOUND`. Resolve it here, from `tools/src/`.
  const gateScript = fileURLToPath(new URL("../bin/gate.ts", import.meta.url));
  execFileSync(
    process.execPath,
    [
      "--import", tsxEsmSpecifier(), gateScript, parsed.qid, spec, node, "--ungate",
      ...(parsed.dischargeLeanName ? ["--lean-name", parsed.dischargeLeanName] : []),
    ],
    { cwd: repoRoot, stdio: "inherit" },
  );
  console.log(`discharge-gate: ungated ${node}.`);

  // Step 3 — re-verify: resume from `startId` (default F2.5, flowing to F5). The
  // ungate reopened every consumer to `unreviewed`, so F2.5's delta / added-premise
  // review re-runs and confirms each is now honestly UNCONDITIONAL. The equivalence /
  // laundering backstop runs INSIDE that loop (F3/F3.5/F4 are pass-throughs), which is why
  // `dischargeStartStage` refuses an entry stage that would skip it. No pre-promotion check —
  // the reviewers are the gate.
  const finalState = await runPipeline(
    { repoRoot, qid: parsed.qid, specialization: spec, resume: true, dryRun: false, auto: parsed.auto },
    undefined,
    { startStage: toInternalStopAfter(startId) },
  );

  // Reviewer reject (or any halt before stage 5): leave the entry reopened for iteration.
  if (String(finalState.stage_completed) !== "5") {
    console.log(
      `discharge-gate: re-verify did not reach F5 (stopped at ${formatStageLabel(finalState.stage_completed)}). ` +
        `Entry left reopened at ${path.relative(repoRoot, workingDir)} — fix the Lean and re-run --discharge-gate ` +
        `(or --resume --from-stage ${startId}).`,
    );
    return;
  }

  // Step 4 — re-bank, recording the discharge (revision bump + discharged_gates).
  await bankEntry({
    repoRoot,
    qid: parsed.qid,
    spec,
    tier: "accepted",
    dischargedGates: [node],
    reason: `Gate ${node} discharged (substrate built); re-verified F4→F5 and re-banked.`,
  });
  console.log(`discharge-gate: ${parsed.qid}/${spec} re-banked — gate ${node} discharged.`);
}

/**
 * `--downgrade-tier <tier> <qid> <spec>`: accept an achieved lower tier. Lowers the
 * run's persisted novelty floor to `<tier>` and re-passes D0.5 at the new floor, so a
 * sound-but-below-target note (the field advance proved unreachable) can proceed instead
 * of dead-ending at the D0.5 below-floor halt.
 *
 * Guarded both ways: `<tier>` must be STRICTLY BELOW the current floor (it only lowers),
 * and `<= the reviewer-assessed tier` from the last D0.5 review (you cannot claim a floor
 * the result did not actually meet). Records a `command` decision-log entry for audit.
 * Honors `--auto` (continue into F) / `--stop-after`; without `--auto` it halts at the
 * D0.5 go/no-go for a human commit-to-F.
 */
async function runDowngradeTier(repoRoot: string, parsed: CliArgs): Promise<void> {
  const { loadState, saveState } = await import("./state.js");
  const { appendEntry } = await import("./decision_log.js");
  const { formalizationDir, resolveInDir } = await import("./paths.js");
  const spec = parsed.specialization!;
  const target = parsed.downgradeTier!;

  const state = await loadState(repoRoot, parsed.qid, spec);
  const currentFloor = state.proposed_from?.novelty_target ?? "field";

  // Guard 1 — it is a DOWNGRADE: strictly below the current floor.
  if (REVIEWER_TIER_RANK[target] >= REVIEWER_TIER_RANK[currentFloor]) {
    throw new Error(
      `--downgrade-tier: '${target}' is not below the current novelty floor '${currentFloor}'. ` +
        `This command only LOWERS the floor.`,
    );
  }

  // Read the achieved tier from the last D0.5 general review (evidence the note meets the new floor).
  const reviewsDir = resolveInDir(formalizationDir(repoRoot, parsed.qid), "reviews", [
    `${parsed.qid}_${spec}_reviews`,
  ]);
  const reviewFile = path.join(reviewsDir, "review_general.json");
  let achievedTier: string | undefined;
  if (existsSync(reviewFile)) {
    try {
      achievedTier = (JSON.parse(readFileSync(reviewFile, "utf8")) as { tier?: string }).tier;
    } catch {
      /* unparseable review — treat as unknown below */
    }
  }
  if (achievedTier === undefined) {
    throw new Error(
      `--downgrade-tier: no D0.5 review at ${path.relative(repoRoot, reviewFile)} — run D0.5 first so the achieved tier is known.`,
    );
  }
  // Guard 2 — the achieved tier must actually MEET the requested floor.
  if ((REVIEWER_TIER_RANK[achievedTier] ?? -1) < REVIEWER_TIER_RANK[target]) {
    throw new Error(
      `--downgrade-tier: achieved tier '${achievedTier}' does not meet the requested floor '${target}'. ` +
        `Downgrade to '${achievedTier}' or lower.`,
    );
  }

  if (parsed.dryRun) {
    console.log(
      `[dry-run] would downgrade ${parsed.qid}/${spec} novelty floor ${currentFloor} -> ${target} ` +
        `(D0.5 achieved ${achievedTier}), re-pass D0.5, and ${parsed.auto ? "continue into F" : "halt at the D0.5 go/no-go"}.`,
    );
    return;
  }

  // 1. Rewrite the persisted floor so a later bare --resume recovers the downgraded target.
  if (state.proposed_from) {
    state.proposed_from.novelty_target = target;
    await saveState(repoRoot, parsed.qid, spec, state);
  }

  // 2. Audit the downgrade in the orchestrator decision log.
  appendEntry(repoRoot, parsed.qid, {
    type: "command",
    from: "main",
    phase: "D",
    stage: "D0.5",
    cmd: "downgrade-tier",
    target,
    note: `Downgraded novelty floor ${currentFloor} -> ${target} (D0.5 achieved tier=${achievedTier}); re-passing D0.5 at the new floor.`,
  });
  console.log(
    `downgrade-tier: ${parsed.qid}/${spec} novelty floor ${currentFloor} -> ${target} (achieved ${achievedTier}). Re-passing D0.5…`,
  );

  // 3. Re-run D0.5 at the new floor. Pass noveltyTarget so ctx wins over state; start at D0.5.
  //    Honor --auto (continue into F); without it (or with an explicit --stop-after) halt at go/no-go.
  const startStage = toInternalStopAfter("D0.5");
  const stopAfterStage = parsed.stopAfter
    ? toInternalStopAfter(parsed.stopAfter)
    : parsed.auto
      ? undefined
      : toInternalStopAfter("D0.5");
  const finalState = await runPipeline(
    {
      repoRoot,
      qid: parsed.qid,
      specialization: spec,
      resume: true,
      dryRun: false,
      auto: parsed.auto,
      noveltyTarget: target,
    },
    undefined,
    { startStage, stopAfterStage },
  );
  console.log(
    `downgrade-tier: ${parsed.qid}/${spec} finished at stage ${formatStageLabel(finalState.stage_completed)}.`,
  );
}

interface StudyArgs {
  slug: string;
  resume: boolean;
  dryRun: boolean;
}

function parseStudyArgs(argv: string[]): StudyArgs {
  const args = [...argv];
  const resumeIndex = args.indexOf("--resume");
  const resume = resumeIndex !== -1;
  if (resume) args.splice(resumeIndex, 1);
  const dryRunIndex = args.indexOf("--dry-run");
  const dryRun = dryRunIndex !== -1;
  if (dryRun) args.splice(dryRunIndex, 1);
  const [slug, extra] = args;
  if (!slug || extra || slug.startsWith("-")) {
    throw new Error("Usage: causalsmith study <slug> [--resume] [--dry-run]");
  }
  return { slug, resume, dryRun };
}

/** Test-only access to the `causalsmith study` parser. */
export function parseStudyArgsForTest(argv: string[]): StudyArgs {
  return parseStudyArgs(argv);
}

/** Run the reusable-substrate builder behind `causalsmith study`. */
export async function runStudyCli(argv: string[]): Promise<void> {
  applyWorkerEnv();
  const parsed = parseStudyArgs(argv);
  const repoRoot = findCausalSmithRoot(process.cwd());
  const { runSubstratePipeline } = await import("./substrate/pipeline.js");
  const { startSharedLeanLsp } = await import("./shared/lean_lsp_server.js");
  const leanProject = leanProjectPathFor(repoRoot);

  // Fail fast before a cold lean-lsp stage parks on a from-scratch build.
  if (!parsed.dryRun) await warmUpLeanOrThrow(leanProject);

  // Pay the lean-lsp cold start once and share it across the entire study run.
  let shared: Awaited<ReturnType<typeof startSharedLeanLsp>> | null = null;
  const ownsSharedLeanLsp = !process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL?.trim();
  if (ownsSharedLeanLsp && !parsed.dryRun) {
    try {
      shared = await startSharedLeanLsp(repoRoot);
      process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL = shared.url;
    } catch {
      shared = null;
    }
  }
  try {
    const finalState = await runSubstratePipeline({
      repoRoot, slug: parsed.slug, resume: parsed.resume, dryRun: parsed.dryRun,
    });
    console.log(`CausalSmith study ${parsed.slug} finished in phase ${finalState.phase}.`);
  } finally {
    if (ownsSharedLeanLsp && shared) {
      try {
        await shared.stop();
      } catch {
        /* best-effort teardown */
      }
      delete process.env.CAUSALSMITH_SHARED_LEAN_LSP_URL;
    }
  }
}

/** Run the theorem-research pipeline behind `causalsmith research`. */
export async function runCli(argv: string[]): Promise<void> {
  // Inject worker-required env from the central local config (git-bash path for
  // the headless `claude` CLI on Windows; MCP_TIMEOUT) before any worker spawns.
  applyWorkerEnv();
  const parsed = parseArgs(argv);

  // The live `causalsmith research` pipeline owns `doc/research/active/<qid>/`.
  // Bare insight ids belong to retired study runs under `doc/study/runs/`;
  // never let a current research command revive that writer path by accident.
  if (!parsed.reopenMode && isInsightStyleQid(parsed.qid)) {
    throw new Error(
      `Research qid '${parsed.qid}' is an insight-style legacy id. ` +
        "Use a research-prefixed qid (eid_, pid_, stat_, panel_, exp_, scm_, q_, or q<digits>_); " +
        "doc/study/runs is reserved for retired study-run compatibility.",
    );
  }
  const repoRoot = findCausalSmithRoot(process.cwd());

  if (parsed.reopenMode) {
    await runReopen(repoRoot, parsed);
    return;
  }

  if (parsed.dischargeGateMode) {
    await runDischargeGate(repoRoot, parsed);
    return;
  }

  if (parsed.downgradeTierMode) {
    await runDowngradeTier(repoRoot, parsed);
    return;
  }

  if (parsed.angleActionMode) {
    const { applyProposalAngleAction } = await import("./discovery/proposal_angle_checkpoint.js");
    const directive = parsed.angleDirective === "-"
      ? readFileSync(0, "utf8").trim()
      : parsed.angleDirective;
    const result = await applyProposalAngleAction({
      repoRoot,
      qid: parsed.qid,
      specialization: parsed.specialization!,
      action: parsed.angleAction!,
      extraRevisions: parsed.extraRevisions,
      directive,
      directiveNote: parsed.angleDirectiveNote,
    });
    console.log(
      `angle-action: ${result.action} angle=${result.angle} v${result.version}` +
        `${result.nextAngle === undefined ? "" : ` -> angle=${result.nextAngle}`}` +
        `${result.reviseCap === undefined ? "" : ` revise-cap=${result.reviseCap}`}` +
        ` directive=${result.directivePersisted ? "persisted" : "none"}.`,
    );
    if (!result.resume) return;
  }

  // --stop-after takes precedence over a pre-set CAUSALSMITH_STOP_AFTER env var.
  // CLI values are passed through runPipeline options. Env-var values still
  // feed the legacy pipeline check, so normalize them back to internal stages.
  const stopAfterStage = parsed.stopAfter ? toInternalStopAfter(parsed.stopAfter) : undefined;
  // --from-stage → runPipeline `startStage` (resume-entry override). Only honored
  // on --resume; a cold start always begins from the pipeline's own first stage.
  const startStage = parsed.angleActionMode
    ? toInternalStopAfter("D-1.2")
    : parsed.resume && parsed.fromStage
      ? toInternalStopAfter(parsed.fromStage)
      : undefined;
  if (parsed.stopAfter) {
    // The pipeline loop also consults the env var directly; a stale value
    // (e.g. exported in a wrapper script) would otherwise still fire even
    // though the flag was given. Flag wins — drop the env var.
    delete process.env.CAUSALSMITH_STOP_AFTER;
  } else if (process.env.CAUSALSMITH_STOP_AFTER) {
    process.env.CAUSALSMITH_STOP_AFTER = toInternalStopAfter(
      parseStopAfterToken(process.env.CAUSALSMITH_STOP_AFTER),
    );
  }

  // Phase 3: cold-start --from-question must atomically claim the OpenQuestion
  // (status: open → in_progress) under the graph write lock BEFORE the pipeline
  // begins. On --resume this is a no-op (the OQ is already in_progress and the
  // qid is the checkout key). See spec §15.4 point 2 (double-consumption).
  if (parsed.fromQuestionOqId && !parsed.resume) {
    const { claimOpenQuestionForRun } = await import("./shared/claim_open_question.js");
    await claimOpenQuestionForRun({
      repoRoot,
      oq_id: parsed.fromQuestionOqId,
    });
  }

  const finalState = await runPipeline(
    {
      repoRoot,
      qid: parsed.qid,
      specialization: parsed.specialization!,
      resume: parsed.resume,
      dryRun: parsed.dryRun,
      auto: parsed.auto,
      proposeTopic: parsed.proposeTopic,
      noveltyTarget: parsed.noveltyTarget,
      upgradeFrom: parsed.upgradeFrom,
      proposerOverride: parsed.proposerOverride,
      fromQuestionOqId: parsed.fromQuestionOqId,
    },
    undefined,
    { stopAfterStage, startStage, clearGates: parsed.clearGates },
  );
  console.log(
    `CausalSmith research ${parsed.dryRun ? "dry-run " : ""}${finalState.auto_mode ? "[AUTO] " : ""}finished at stage ${formatStageLabel(finalState.stage_completed)}.`,
  );
}
