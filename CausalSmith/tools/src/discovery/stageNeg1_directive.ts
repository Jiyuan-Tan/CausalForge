// Stage -1.2 (proposal producer) orchestrator directive channel — mirrors D0's
// escalation-log directive (`stage0_working.ts` `EscalationLogEntry`/
// `appendEscalationLog`/`formatEscalationContext`). A standalone, cumulative,
// orchestrator-injectable steer for the proposal author: no applied change, just
// a concrete direction (e.g. a literature-grounded reframe, or a recurring
// drift the reviewer keeps flagging) fed into every subsequent draft.
//
// Unlike D0's `round` (a solve counter), D-1.2's counter is `proposed_from.
// current_version` (the draft version). The log is replayed in FULL on every
// call — like D0, directives accumulate rather than being one-shot or requiring
// an explicit clear.
import { existsSync } from "node:fs";
import { appendFile, readFile } from "node:fs/promises";
import { artifactPath } from "../paths.js";
import type { PipelineContext } from "../types.js";

/** One orchestrator directive to the next D-1.2 draft. No `changed` concept
 *  (unlike D0) — Stage -1.2 has no def/statement/assumption to "apply a
 *  correction" to; it is always a standalone steer. */
export interface Neg1EscalationLogEntry {
  version: number;
  note?: string;
  directive: string;
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

/** Format the escalation log as agent-prompt context, most recent last. Empty
 *  string when there is nothing to report — mirrors `formatEscalationContext`. */
export function formatNeg1EscalationContext(log: Neg1EscalationLogEntry[]): string {
  if (log.length === 0) return "";
  const lines = log.map((e) => `  [v${e.version}] DIRECTIVE: ${e.directive}${e.note ? ` — ${e.note}` : ""}`);
  return [
    "=== ORCHESTRATOR ESCALATION LOG (directives since the last draft — build on these, act on every DIRECTIVE) ===",
    ...lines,
  ].join("\n");
}
