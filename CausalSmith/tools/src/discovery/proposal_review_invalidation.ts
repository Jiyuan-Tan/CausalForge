/**
 * Sanctioned reviewer-only rewind for D-0.5 plumbing failures.
 *
 * This is intentionally narrower than resetProposalCursor: it preserves the
 * authored proposal/core and producer handoff, invalidates only the current
 * angle/version review, and reopens D-0.5. It must never be used to obtain a
 * second opinion on a valid review.
 */
import { access, rename } from "node:fs/promises";
import path from "node:path";
import { appendPipelineLog } from "../log.js";
import { reviewsDir } from "../paths.js";
import { loadState, saveState } from "../state.js";

export interface InvalidateProposalReviewResult {
  angle: number;
  version: number;
  removedIterations: number;
  archivedReview: string;
}

const fileExists = (file: string): Promise<boolean> => access(file).then(() => true, () => false);

async function firstFreeArchive(file: string): Promise<string> {
  const base = `${file}.invalidated`;
  if (!(await fileExists(base))) return base;
  for (let n = 1; n < 1000; n++) {
    const candidate = `${base}.${n}`;
    if (!(await fileExists(candidate))) return candidate;
  }
  throw new Error(`invalidate-proposal-review: no free archive name beside ${file}`);
}

export async function invalidateCurrentProposalReview(
  repoRoot: string,
  qid: string,
  specialization: string,
  reason: string,
): Promise<InvalidateProposalReviewResult> {
  if (reason.trim().length === 0) {
    throw new Error("invalidate-proposal-review requires a non-empty plumbing-failure reason");
  }
  const state = await loadState(repoRoot, qid, specialization);
  const pf = state.proposed_from;
  if (!pf) throw new Error("invalidate-proposal-review requires an existing --propose run");
  const checkpoint = pf.angle_checkpoint;
  if (!checkpoint) {
    throw new Error("invalidate-proposal-review requires a pending D-0.5 angle checkpoint");
  }
  const angle = checkpoint.angle;
  const version = checkpoint.version;
  if ((pf.current_angle_index ?? 0) !== angle || (pf.current_version ?? 0) !== version) {
    throw new Error(
      `invalidate-proposal-review cursor mismatch: checkpoint angle ${angle} v${version}, ` +
        `cursor angle ${pf.current_angle_index ?? 0} v${pf.current_version ?? 0}`,
    );
  }
  if (pf.last_draft_status !== "completed" || !pf.last_draft_handoff) {
    throw new Error(
      "invalidate-proposal-review refuses to reopen without a completed producer handoff; " +
        "this helper may re-run only the reviewer, never the author",
    );
  }
  if (state.stage_completed !== "-1.2") {
    throw new Error(
      `invalidate-proposal-review requires the run parked at D-0.5 (stage_completed=-1.2); ` +
        `found ${state.stage_completed}`,
    );
  }

  const reviewFile = path.join(reviewsDir(repoRoot, qid, specialization), `angle${angle}_v${version}.json`);
  if (!(await fileExists(reviewFile))) {
    throw new Error(
      `invalidate-proposal-review cannot find the receipt to archive at ${reviewFile}; nothing was changed`,
    );
  }
  const archivedReview = await firstFreeArchive(reviewFile);
  await rename(reviewFile, archivedReview);

  const before = pf.iterations ?? [];
  const after = before.filter((it) => !(it.angle === angle && it.version === version));
  const removedIterations = before.length - after.length;
  if (removedIterations === 0) {
    // Restore the receipt before refusing so validation failures are non-destructive.
    await rename(archivedReview, reviewFile);
    throw new Error(
      `invalidate-proposal-review found no state iteration for angle ${angle} v${version}; nothing was changed`,
    );
  }

  pf.iterations = after;
  pf.angle_checkpoint = undefined;
  pf.final_verdict = "pending";
  pf.last_reviewer_verdict = "";
  pf.accepted_scope_caveats = undefined;
  // Preserve current_mode, current_version, last_draft_status, and
  // last_draft_handoff: D-0.5 will review this exact authored artifact again.

  try {
    await saveState(repoRoot, qid, specialization, state);
  } catch (err) {
    await rename(archivedReview, reviewFile);
    throw err;
  }
  await appendPipelineLog(
    { repoRoot, qid, specialization },
    {
      stage: "-0.5",
      status: "review-invalidated",
      duration_ms: 0,
      message:
        `Invalidated D-0.5 angle ${angle} v${version} review for a plumbing failure: ${reason}. ` +
        `Archived receipt at ${archivedReview}; preserved the authored proposal for reviewer-only re-entry.`,
    },
  );
  return { angle, version, removedIterations, archivedReview };
}
