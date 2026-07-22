// Orchestrator helper: reset the D-1/D-0.5 proposal cursor so a bumped-cap
// `--resume` continues a CONVERGED-but-cap-exhausted angle instead of banking.
//
// Why this exists: when the proposal loop exhausts NEG1_REVISE_CAP / the pivot
// budget it parks the cursor on the LAST (dead) angle and writes
// `proposed_from.final_verdict = "NO-PASS"`. A naive `--resume` then re-enters
// that dead cursor and re-NO-PASSes. The good draft is archived
// (`proposal_angle<N>_rejected.tex`). There was no sanctioned way to point the
// cursor back at the converged angle short of hand-editing `state.json`, which
// the orchestrator rules forbid. This is that sanctioned, schema-valid writer:
// it re-seats the cursor, clears the NO-PASS verdict, un-exhausts the angle, and
// restores that angle's archived draft as the active `proposal.tex`. Pair it
// with a raised `CAUSALSMITH_NEG1_REVISE_CAP` on the `--resume` to give the angle
// more revise rounds.
import { rename, access, readFile, readdir, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { loadState, saveState } from "../state.js";
import { proposalTexPath } from "../paths.js";
import { NEG1_PIVOT_BUDGET } from "./stages/neg1_2.js";
import { readRepairedModelJson } from "./core/core_io.js";

export type ProposalMode = "cold-start" | "revise" | "pivot" | "kernel-replace" | "draft-rebuild";

export interface ResetProposalCursorOptions {
  /** Angle to re-seat the cursor on. Default 0 (the first, usually best-developed angle). */
  angle?: number;
  /** Version to resume from. Default: the highest version seen for `angle` in
   *  `iterations` (the producer increments on entry, so this continues the angle). */
  version?: number;
  /** Cursor mode on re-entry. Default "revise" (continue the angle's revise loop). */
  mode?: ProposalMode;
  /** Restore the angle's archived draft to the active proposal path. Default true. */
  restoreArchived?: boolean;
  /** Discard every active D-1.2/D-0.5 artifact and cursor field for this angle,
   *  while preserving the completed D-1.1 gaps harvest. The next plain
   *  `--resume` starts a genuinely fresh D-1.2 v1 draft. */
  freshAngle?: boolean;
}

export interface ResetProposalCursorResult {
  angle: number;
  version: number;
  mode: ProposalMode;
  /** The proposal path restored from archive, or null if no archive was found. */
  restored: string | null;
  /** The proto_core.json path restored from archive (single-artifact mode), or null. */
  restoredProtoCore: string | null;
  /** The verdict that was cleared (e.g. "NO-PASS"), or null if already clear. */
  clearedVerdict: string | null;
  exhausted_angles: number[];
  freshAngle: boolean;
  /** True when this reset consumed a parked angle checkpoint that was blocking --resume. */
  clearedAngleCheckpoint: boolean;
}

const fileExists = (p: string): Promise<boolean> => access(p).then(() => true, () => false);

/** Highest version already USED for `angle` — the value the producer will increment from.
 *
 *  `iterations` rows are written by the REVIEWER, so a draft that was authored but never
 *  reviewed leaves no row. Reading those rows alone therefore yielded the last REVIEWED
 *  version, and the producer's `current_version + 1` would then author over a version
 *  that already exists on disk (silently replacing it). The live cursor knows what was
 *  authored, so fold it in whenever it refers to this same angle. */
export function resolveResumeVersion(args: {
  angle: number;
  iterations: Array<{ angle: number; version: number }>;
  cursorAngle: number;
  cursorVersion?: number;
}): number {
  const versions = args.iterations.filter((it) => it.angle === args.angle).map((it) => it.version);
  if (args.cursorAngle === args.angle && typeof args.cursorVersion === "number") {
    versions.push(args.cursorVersion);
  }
  return versions.length > 0 ? Math.max(...versions) : 0;
}

/** Names in `dir` matching `pattern`. A MISSING directory yields nothing; any other
 *  failure throws, so a reset cannot report success having listed nothing. Separated from
 *  deletion so callers can resolve every listing BEFORE destroying anything. */
async function listMatching(dir: string, pattern: RegExp): Promise<string[]> {
  const entries = await readdir(dir).catch((err: NodeJS.ErrnoException) => {
    if (err?.code === "ENOENT") return [] as string[];
    throw new Error(
      `reset: cannot list ${dir} to clear stale artifacts (${err?.code ?? "unknown"}: ${err?.message ?? err}). ` +
        `Refusing to report a fresh reset that removed nothing.`,
    );
  });
  return entries.filter((name) => pattern.test(name));
}

async function removeMatching(dir: string, pattern: RegExp): Promise<void> {
  // A MISSING directory is legitimate — there is nothing to remove. Any other failure
  // (permissions, I/O) is not: swallowing it into an empty listing meant the reset deleted
  // nothing and still reported success, leaving stale artifacts behind a "fresh" reset.
  const entries = await readdir(dir).catch((err: NodeJS.ErrnoException) => {
    if (err?.code === "ENOENT") return [] as string[];
    throw new Error(
      `reset: cannot list ${dir} to clear stale artifacts (${err?.code ?? "unknown"}: ${err?.message ?? err}). ` +
        `Refusing to report a fresh reset that removed nothing.`,
    );
  });
  await Promise.all(entries.filter((name) => pattern.test(name)).map((name) => rm(path.join(dir, name), { force: true })));
}

async function removeAngleReviewRows(reviewsJsonl: string, angle: number): Promise<void> {
  if (!(await fileExists(reviewsJsonl))) return;
  const lines = (await readFile(reviewsJsonl, "utf8")).split(/\r?\n/).filter(Boolean);
  let unparseable = 0;
  const kept = lines.filter((line) => {
    try {
      const row = JSON.parse(line) as { stage?: string; report_summary?: string; angle?: number };
      if (row.stage !== "stage_neg1") return true;
      // Prefer a STRUCTURED angle field; fall back to the free-text summary only when
      // absent. Matching solely on `report_summary` couples row removal to a prose
      // format — a wording change silently retains rows that --fresh-angle promised to
      // clear, leaving a "fresh" angle carrying its predecessor's review history.
      if (typeof row.angle === "number") return row.angle !== angle;
      return !row.report_summary?.includes(`angle=${angle} `);
    } catch {
      unparseable += 1;
      return true; // conservative: never drop a row we could not read
    }
  });
  if (unparseable > 0) {
    console.warn(
      `[reset_proposal_cursor] ${unparseable} unparseable row(s) in ${reviewsJsonl} were RETAINED; ` +
        `angle ${angle} history may not be fully cleared.`,
    );
  }
  if (kept.length === 0) {
    await rm(reviewsJsonl, { force: true });
  } else {
    await writeFile(reviewsJsonl, `${kept.join("\n")}\n`, "utf8");
  }
}

export async function resetProposalCursor(
  repoRoot: string,
  qid: string,
  specialization: string,
  options: ResetProposalCursorOptions = {},
): Promise<ResetProposalCursorResult> {
  const state = await loadState(repoRoot, qid, specialization);
  const pf = state.proposed_from;
  if (!pf) {
    throw new Error(
      `[reset_proposal_cursor] ${qid}/${specialization} has no proposed_from — not a --propose run; there is no proposal cursor to reset.`,
    );
  }

  // Validate the angle BEFORE writing anything. `--angle 99` used to be accepted
  // (Number.isInteger passes), written to state, and then silently skip the driving
  // loop `while (current_angle_index < NEG1_PIVOT_BUDGET)` — the run exited the
  // proposal phase with no diagnostic. `--angle -1` passed the same way and blew up on
  // the NEXT loadState, far from the cause.
  if (options.angle !== undefined) {
    if (!Number.isInteger(options.angle) || options.angle < 0 || options.angle >= NEG1_PIVOT_BUDGET) {
      throw new Error(
        `[reset_proposal_cursor] --angle ${options.angle} is out of range: must be an integer in ` +
          `[0, ${NEG1_PIVOT_BUDGET}) (NEG1_PIVOT_BUDGET). Nothing was written.`,
      );
    }
  } else if ((pf.current_angle_index ?? 0) !== 0) {
    // Defaulting to 0 while the run is parked on another angle silently re-seats the
    // cursor somewhere the operator did not ask for.
    console.warn(
      `[reset_proposal_cursor] no --angle given; defaulting to 0 while the run is parked on angle ` +
        `${pf.current_angle_index}. Pass --angle explicitly if that is not what you meant.`,
    );
  }
  const angle = options.angle ?? 0;
  const freshAngle = options.freshAngle ?? false;
  const mode: ProposalMode = freshAngle ? "cold-start" : (options.mode ?? "revise");
  // `iterations` rows are pushed by the REVIEWER, so a draft that was authored but not
  // yet reviewed contributes no row. Deriving the version from reviewed rows alone
  // therefore returned the last REVIEWED version, and the producer (which does
  // `current_version + 1`) would author over a version that already exists on disk.
  // The live cursor is the authority on "what was authored"; fold it in when it refers
  // to this angle.
  const version = freshAngle
    ? 0
    : options.version ??
      resolveResumeVersion({
        angle,
        iterations: pf.iterations ?? [],
        cursorAngle: pf.current_angle_index ?? 0,
        cursorVersion: pf.current_version,
      });

  const clearedVerdict = pf.final_verdict;
  // Clear the angle checkpoint on EVERY reset, not only `--fresh-angle`.
  //
  // `resolveResumeGates` refuses any `--resume` while `angle_checkpoint` is set. Clearing
  // it only in the fresh-angle branch meant the default documented recovery — the one this
  // file's own header prescribes ("re-seat the cursor … pair it with a raised
  // CAUSALSMITH_NEG1_REVISE_CAP on the --resume") — re-seated the cursor and then left the
  // run just as blocked, pointing the operator at a different tool. Re-seating the cursor
  // IS the resolution of the checkpoint that parked it, so consume it here.
  const clearedAngleCheckpoint = pf.angle_checkpoint !== undefined;
  pf.angle_checkpoint = undefined;
  pf.current_angle_index = angle;
  pf.current_version = version;
  pf.current_mode = mode;
  pf.exhausted_angles = (pf.exhausted_angles ?? []).filter((a) => a !== angle);
  pf.final_verdict = freshAngle ? "pending" : null;
  // The parked cursor carries the DEAD angle's producer verdict: last_draft_status
  // "needs-pivot" makes stageNeg0_5 treat the angle as dead, and a stale
  // last_draft_handoff makes the loop review that dead draft instead of re-driving
  // the producer. Reset both so the revise loop re-drives the producer against the
  // restored core (stageNeg0_5.ts §"Resume-aware producer-first guard").
  pf.last_draft_status = "completed";
  pf.last_draft_handoff = undefined;

  if (freshAngle) {
    // Return to the durable D-1.1 boundary. `state.gaps` and gaps.json are
    // intentionally untouched; a plain --resume therefore begins at D-1.2.
    state.stage_completed = "-1.1";
    // Never REGRANT pivot budget. `pivot_budget_used = angle` meant that resetting
    // angle 0 after angles 1..N had already been burned silently reset the counter to
    // 0, handing the run a fresh pivot budget it had already spent.
    const priorBudgetUsed = pf.pivot_budget_used ?? 0;
    pf.pivot_budget_used = Math.max(priorBudgetUsed, angle);
    if (priorBudgetUsed > angle) {
      console.warn(
        `[reset_proposal_cursor] keeping pivot_budget_used=${priorBudgetUsed} (not lowering it to ${angle}): ` +
          `angles beyond ${angle} were already burned and that budget is not refundable.`,
      );
    }
    pf.iterations = (pf.iterations ?? []).filter((it) => it.angle !== angle);
    pf.last_draft_status = undefined;
    pf.last_reviewer_verdict = "";
    pf.accepted_scope_caveats = undefined;
    pf.seed_list = [];
    pf.seed_details = [];
    pf.literature_map = undefined;
    pf.novelty_justification = "";
    pf.kernel_replace_used_angles = (pf.kernel_replace_used_angles ?? []).filter((a) => a !== angle);
    pf.draft_rebuild_used_angles = (pf.draft_rebuild_used_angles ?? []).filter((a) => a !== angle);
    if (pf.revision_cap_by_angle) {
      delete pf.revision_cap_by_angle[String(angle)];
      if (Object.keys(pf.revision_cap_by_angle).length === 0) pf.revision_cap_by_angle = undefined;
    }
    state.flags.stage_neg1_fallback = undefined;

    const proposalTex = proposalTexPath(repoRoot, qid, specialization);
    const discoveryDir = path.dirname(proposalTex);
    const runDir = path.dirname(discoveryDir);
    // LIST BEFORE DELETING. These ran as one Promise.all, so a listing failure surfaced
    // only AFTER sibling deletes had already removed proto_core.json and the escalation
    // log — a reset that destroyed artifacts and then threw, leaving the cursor unsaved
    // and pointing at files that no longer exist. Teaching `removeMatching` to fail loudly
    // (rather than silently listing nothing) made that window reachable, so resolve every
    // listing first and only then delete.
    const angleArchives = new RegExp(`^(?:proposal|proto_core)_angle${angle}_(?:rejected|archive)`);
    const angleReviews = new RegExp(`^angle${angle}_v\\d+\\.json$`);
    const reviewsDir = path.join(runDir, "reviews");
    const [archiveNames, reviewNames] = await Promise.all([
      listMatching(discoveryDir, angleArchives),
      listMatching(reviewsDir, angleReviews),
    ]);
    await Promise.all([
      rm(path.join(discoveryDir, "proto_core.json"), { force: true }),
      rm(path.join(discoveryDir, "proposal_output_template.json"), { force: true }),
      rm(path.join(discoveryDir, "dneg1_escalation_log.jsonl"), { force: true }),
      ...archiveNames.map((n) => rm(path.join(discoveryDir, n), { force: true })),
      ...reviewNames.map((n) => rm(path.join(reviewsDir, n), { force: true })),
      removeAngleReviewRows(path.join(reviewsDir, "reviews.jsonl"), angle),
    ]);
    pf.archived_proposals = (pf.archived_proposals ?? []).filter(
      (p) => !new RegExp(`(?:proposal|proto_core)_angle${angle}_`).test(path.basename(p)),
    );
  }

  let restored: string | null = null;
  let restoredProtoCore: string | null = null;
  if (!freshAngle && (options.restoreArchived ?? true)) {
    const proposalTex = proposalTexPath(repoRoot, qid, specialization);
    const dir = path.dirname(proposalTex);
    const archive = path.join(dir, `proposal_angle${angle}_rejected.tex`);
    if (await fileExists(archive)) {
      // Restore CONSUMES the archive (see the paired proto_core restore below, which
      // now does the same). Consuming is the intended semantics — the restored content
      // is live in proposal.tex, so there is nothing left to restore — but it is only
      // SAFE if both artifacts behave identically. Previously the .tex was renamed
      // while proto_core.json was copied, so a second invocation restored the core
      // again over a .tex it could no longer restore: a run-1 .tex beside a run-2 core.
      await rename(archive, proposalTex);
      restored = proposalTex;
      pf.proposal_path = proposalTex;
      // Compare by basename: the recorded path may differ from the reconstructed one
      // by separator or normalization, and exact string equality then leaks a stale
      // entry that later looks like a live archive.
      pf.archived_proposals = (pf.archived_proposals ?? []).filter(
        (p) => path.basename(p) !== path.basename(archive),
      );
    }
    // Single-artifact mode (stage -1.2): the load-bearing substance lives in
    // proto_core.json, not the .tex skeleton. Restore the angle's archived core
    // over whatever dead needs-pivot record the pivot left behind.
    const protoCore = path.join(dir, "proto_core.json");
    const protoArchive = path.join(dir, `proto_core_angle${angle}_rejected.json`);
    if (await fileExists(protoArchive)) {
      // CONSUME, matching the .tex restore above. This was a copy, which made the two
      // restores asymmetric: on a second invocation the .tex reported "(no archive)"
      // and stayed as-is while the core was restored again from its surviving archive,
      // silently pairing a run-1 proposal with a run-2 core.
      await rename(protoArchive, protoCore);
      restoredProtoCore = protoCore;
      pf.archived_proposals = (pf.archived_proposals ?? []).filter(
        (p) => path.basename(p) !== path.basename(protoArchive),
      );
    }

    // A needs-pivot cold start may have emitted its ranked seed slate only in
    // the diagnostic proto core. Older pipeline code returned before harvesting
    // it, leaving the parked state with seed_list=[]. Rehydrate those ideation
    // fields while the sanctioned cursor reset already owns the state mutation,
    // so the resumed pivot receives the actual alternatives instead of burning
    // another budget on an empty prompt.
    if (await fileExists(protoCore)) {
      try {
        // Needs-pivot diagnostic cores are agent-raw (never canonicalized at a
        // persist boundary) — read through the three-layer escape defense.
        const core = (await readRepairedModelJson(protoCore)) as Record<string, unknown>;
        if ((!Array.isArray(pf.seed_list) || pf.seed_list.length === 0) && Array.isArray(core.seeds)) {
          pf.seed_list = core.seeds.filter((seed): seed is string => typeof seed === "string");
        }
        if ((!Array.isArray(pf.seed_details) || pf.seed_details.length === 0) && Array.isArray(core.seed_details)) {
          pf.seed_details = core.seed_details.filter(
            (detail): detail is Record<string, unknown> => typeof detail === "object" && detail !== null,
          );
        }
        if (!pf.literature_map && typeof core.literature_map === "string") {
          pf.literature_map = core.literature_map;
        }
        if (!pf.novelty_justification && typeof core.novelty_justification === "string") {
          pf.novelty_justification = core.novelty_justification;
        }
      } catch (err) {
        // The block's whole purpose (see above) is to stop the resumed pivot from
        // "burning another budget on an empty prompt". Swallowing a malformed
        // proto_core silently leaves seed_list=[] — i.e. exactly that failure.
        console.warn(
          `[reset_proposal_cursor] could not rehydrate ideation metadata from ${protoCore} ` +
            `(${err instanceof Error ? err.message : String(err)}); the resumed pivot may run with an EMPTY ` +
            `seed slate and burn a budget on it. Inspect that file before resuming.`,
        );
      }
    }
  }

  await saveState(repoRoot, qid, specialization, state);
  return {
    angle,
    version,
    mode,
    restored,
    restoredProtoCore,
    clearedVerdict,
    exhausted_angles: pf.exhausted_angles,
    freshAngle,
    clearedAngleCheckpoint,
  };
}
