// Stage -1.2 (proposal producer) orchestrator directive channel — mirrors D0's
// escalation-log directive (`stage0_working.ts` `EscalationLogEntry`/
// `appendEscalationLog`/`formatEscalationContext`). A standalone, durable,
// orchestrator-injectable steer for the proposal author: no applied change, just
// a concrete direction (e.g. a literature-grounded reframe, or a recurring
// drift the reviewer keeps flagging) fed into every subsequent draft.
//
// Unlike D0's `round` (a solve counter), D-1.2's counter is `proposed_from.
// current_version` (the draft version). The JSONL retains the complete audit
// history, but prompt assembly replays only the current angle's directives so
// abandoned-angle steers do not bloat or contradict a later pivot. Directives
// within an angle remain live until an explicit lifecycle mechanism can prove
// them discharged; do not infer discharge merely from a newer draft version.
import { existsSync } from "node:fs";
import { appendFile, readFile } from "node:fs/promises";
import { artifactPath } from "../paths.js";
import type { PipelineContext } from "../types.js";

/** One orchestrator directive to the next D-1.2 draft. No `changed` concept
 *  (unlike D0) — Stage -1.2 has no def/statement/assumption to "apply a
 *  correction" to; it is always a standalone steer. */
export interface Neg1EscalationLogEntry {
  /** Target proposal angle. Legacy rows predate this field and are conservatively
   * segmented by monotone version resets or rejected as ambiguous. */
  angle?: number;
  version: number;
  note?: string;
  directive: string;
  /** Durable angle boundary that is not an author obligation. */
  provenance_only?: boolean;
}

export function neg1EscalationLogPath(ctx: PipelineContext): string {
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", "dneg1_escalation_log.jsonl", [
    `${ctx.qid}_dneg1_escalation_log.jsonl`,
  ]);
}

export async function appendNeg1EscalationLog(
  ctx: PipelineContext,
  entry: Neg1EscalationLogEntry,
): Promise<void> {
  await appendFile(neg1EscalationLogPath(ctx), JSON.stringify(entry) + "\n", "utf8");
}

export async function readNeg1EscalationLog(ctx: PipelineContext): Promise<Neg1EscalationLogEntry[]> {
  const p = neg1EscalationLogPath(ctx);
  if (!existsSync(p)) return [];
  const txt = await readFile(p, "utf8");
  const entries: Neg1EscalationLogEntry[] = [];
  txt.split("\n").forEach((l, i) => {
    if (l.trim().length === 0) return;
    try {
      entries.push(JSON.parse(l) as Neg1EscalationLogEntry);
    } catch (err) {
      // why: one corrupt JSONL row should not poison all future D-1.2 drafts.
      console.warn(
        `[D-1.2] skipping malformed escalation log line ${i + 1} at ${p}: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  });
  return entries;
}

/** Format the current angle's live directives as agent-prompt context. Legacy
 *  rows use conservative version/switch segmentation and fail closed when that
 *  cannot reach the current angle unambiguously. Empty string when there is
 *  nothing to report. */
export function formatNeg1EscalationContext(
  log: Neg1EscalationLogEntry[],
  currentAngle = 0,
): string {
  // Backfill pre-provenance rows deterministically. Draft versions are
  // monotone within an angle and reset on ordinary pivots. An angle-action
  // switch row itself targets the next angle before state resets, so it starts
  // the new segment and suppresses exactly the following version-drop split.
  let legacyAngle = 0;
  let previousLegacyVersion: number | undefined;
  let suppressNextDrop = false;
  let sawLegacy = false;
  let hasExplicitCurrentBoundary = false;
  const angleLog = log.filter((entry) => {
    if (entry.angle !== undefined) {
      if (
        entry.angle === currentAngle &&
        entry.provenance_only === true &&
        entry.note?.startsWith("angle-action:switch") === true
      ) hasExplicitCurrentBoundary = true;
      return entry.angle === currentAngle && entry.provenance_only !== true;
    }
    sawLegacy = true;
    const isSwitch = entry.note?.startsWith("angle-action:switch") === true;
    if (isSwitch) {
      legacyAngle++;
      suppressNextDrop = true;
    } else if (
      previousLegacyVersion !== undefined &&
      entry.version < previousLegacyVersion
    ) {
      if (suppressNextDrop) suppressNextDrop = false;
      else legacyAngle++;
    } else if (suppressNextDrop) {
      suppressNextDrop = false;
    }
    previousLegacyVersion = entry.version;
    return legacyAngle === currentAngle;
  });
  if (sawLegacy && currentAngle > legacyAngle && !hasExplicitCurrentBoundary) {
    throw new Error(
      `D-1.2 directive log predates angle provenance and cannot be safely mapped to current angle ${currentAngle}; ` +
      `the observable legacy version history reaches only angle ${legacyAngle}. Backfill explicit angle fields before resuming.`,
    );
  }
  if (angleLog.length === 0) return "";
  const lines = angleLog
    .map((e) => `  [v${e.version}] DIRECTIVE: ${e.directive}${e.note ? ` — ${e.note}` : ""}`);
  return [
    "=== ORCHESTRATOR ESCALATION LOG (current angle — act on every DIRECTIVE) ===",
    ...lines,
  ].join("\n");
}
