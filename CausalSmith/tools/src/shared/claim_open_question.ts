/**
 * Phase 3 — atomic OpenQuestion claim performed by `/causalsmith --from-question
 * <oq_id>` on cold start (BEFORE the pipeline begins).
 *
 * Contract:
 *   - Wrapped in `withGraphWriteLock` so two concurrent claims cannot both
 *     succeed (spec §15.4 point 2: prevent double-consumption).
 *   - Only `status: "open"` → `status: "in_progress"` is a legal transition
 *     here. Any other observed status (including `in_progress` from a stuck
 *     prior run) fails fast and instructs the operator to clear it manually.
 *   - Rebuilds `index.json` so subsequent reads see the new status without
 *     loading the in-memory fallback.
 */
import path from "node:path";
import { existsSync, readFileSync } from "node:fs";
import { readFile, rename, writeFile } from "node:fs/promises";
import { buildIndex, loadAllNodes, writeIndexAtomic } from "./graph.js";
import { withGraphWriteLock } from "./graph_lock.js";
import type { OpenQuestion } from "./kb_types.js";

export interface ClaimOpenQuestionInput {
  repoRoot: string;
  oq_id: string;
  /** Defaults to `<repoRoot>/doc/study`. */
  graphRoot?: string;
}

export interface ClaimOpenQuestionResult {
  oq_id: string;
  method_id: string | null;
  lineage_parent_kind: "research" | "study" | null;
}

export class OpenQuestionClaimError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "OpenQuestionClaimError";
  }
}

export async function claimOpenQuestionForRun(
  input: ClaimOpenQuestionInput,
): Promise<ClaimOpenQuestionResult> {
  const graphRoot = input.graphRoot ?? path.join(input.repoRoot, "doc", "study");
  const oqPath = path.join(graphRoot, "nodes", "open_question", `${input.oq_id}.json`);

  return withGraphWriteLock(graphRoot, async () => {
    if (!existsSync(oqPath)) {
      throw new OpenQuestionClaimError(`OpenQuestion ${input.oq_id} not found at ${oqPath}`);
    }
    const oq = JSON.parse(await readFile(oqPath, "utf8")) as OpenQuestion;
    const status = stringifyStatus(oq.status);
    if (status !== "open") {
      throw new OpenQuestionClaimError(
        `OpenQuestion ${input.oq_id} is ${status}; cannot claim. Only "open" → "in_progress" is allowed. ` +
          `If a previous run is stuck, edit the node JSON manually to reset status to "open".`,
      );
    }
    const next = { ...oq, status: "in_progress" as const };
    const tmp = `${oqPath}.new`;
    await writeFile(tmp, JSON.stringify(next, null, 2) + "\n", "utf8");
    await rename(tmp, oqPath);

    // Rebuild index so readers see the new status.
    const nodes = await loadAllNodes(graphRoot);
    await writeIndexAtomic(graphRoot, buildIndex(nodes));

    const lineageBag = (oq as unknown as { lineage?: { parent_kind?: "research" | "study" } }).lineage;
    return {
      oq_id: input.oq_id,
      method_id: oq.seed_method_id ?? null,
      lineage_parent_kind: lineageBag?.parent_kind ?? null,
    };
  }).catch((err: unknown) => {
    if (err instanceof OpenQuestionClaimError) throw err;
    const code = (err as { code?: string })?.code;
    if (code === "ELOCKED" || code === "EEXIST") {
      throw new OpenQuestionClaimError(
        `Could not acquire the graph write lock to claim ${input.oq_id}. ` +
          `Another writer is holding it; wait or stop the other run.`,
      );
    }
    throw err;
  });
}

function stringifyStatus(status: OpenQuestion["status"]): string {
  if (typeof status === "string") return status;
  if (status && typeof status === "object" && "closed_by" in status) {
    return `closed_by:${(status as { closed_by: string }).closed_by}`;
  }
  return String(status);
}

// Re-export for tests/CLI callers that just need to read the file.
export function _readOpenQuestionStatus(graphRoot: string, oq_id: string): string {
  const p = path.join(graphRoot, "nodes", "open_question", `${oq_id}.json`);
  const raw = readFileSync(p, "utf8");
  const j = JSON.parse(raw) as { status: unknown };
  return stringifyStatus(j.status as OpenQuestion["status"]);
}
