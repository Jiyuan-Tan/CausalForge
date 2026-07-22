/**
 * Mint an OpenQuestion node for a failed theorem entry from a causalsmith run.
 *
 * Stage 0.5 gate: refuses to mint when the theorem failed at or before
 * Stage 0.5 (math review). OQs carry the contract "valid math claim,
 * currently unproved" — banking a math-rejected theorem would silently
 * degrade every downstream consumer (close_open_question, the `suggests`
 * edge, human researchers picking problems). Such failures still live in
 * the per-run fail bank, so no information is lost. Result kind is
 * `"skipped"` with reason `"stage_below_0_5"` in that case.
 *
 * Invariant: idempotent on (qid, spec, theorem_local_id). The OQ id is
 * deterministic: `oq_failed_<qid>_<spec>_<theorem_local_id>`. On second
 * call with identical inputs the existing file is preserved and result kind
 * is `"existed"`. On second call with conflicting `minted_from`,
 * `OpenQuestionConflict` is thrown.
 *
 * The write is done under the graph lock (shared with close_open_question)
 * so concurrent banks of different runs cannot race on graph state.
 *
 * Lifecycle: minted OQs start as `status: "open"`. A future run that proves
 * one must first call `claim_open_question` (transition to `in_progress`)
 * before `close_open_question` will close it.
 */
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { STAGE_ORDER } from "../constants.js";
import type { OpenQuestion } from "./kb_types.js";
import { withGraphWriteLock } from "./graph_lock.js";

export interface TheoremForMint {
  theorem_local_id: string;
  origin_theorem_id: string;
  statement: string;
  status: "pending" | "in_progress" | "completed" | "stuck" | "failed";
  stage_completed: string | null;
  lean_file_relpath: string | null;
  failure_reason?: string;
}

export interface MintInput {
  qid: string;
  spec: string;
  theorem: TheoremForMint;
  graphRoot: string;
}

export type MintResult =
  | { kind: "created"; oq_id: string; oq_path: string }
  | { kind: "existed"; oq_id: string; oq_path: string }
  | { kind: "skipped"; reason: "stage_below_0_5"; required_stage: "1" };

export class OpenQuestionConflict extends Error {
  constructor(
    public readonly oq_id: string,
    public readonly oq_path: string,
    public readonly existingMintedFrom: unknown,
    public readonly proposedMintedFrom: unknown,
  ) {
    super(
      `OpenQuestion ${oq_id} already exists at ${oq_path} with a different minted_from block. ` +
        `Inspect and reconcile manually.`,
    );
    this.name = "OpenQuestionConflict";
  }
}

const STAGE_0_5_INDEX = STAGE_ORDER.indexOf("0.5" as (typeof STAGE_ORDER)[number]);

function stagePastReview(stage: string | null): boolean {
  if (stage === null) return false;
  const idx = STAGE_ORDER.indexOf(stage as (typeof STAGE_ORDER)[number]);
  if (idx < 0) return false; // unknown stage → fail closed (do not mint)
  return idx > STAGE_0_5_INDEX;
}

/**
 * Derive a human-readable title from the theorem statement. Falls back to a
 * mechanical run-keyed label when the statement is empty / unusable so that
 * the title field is never blank.
 */
function deriveTitle(input: MintInput): string {
  const firstLine = input.theorem.statement.split("\n")[0]?.trim() ?? "";
  if (firstLine.length === 0) {
    return `Unproved: ${input.theorem.theorem_local_id} of ${input.qid} (${input.spec})`;
  }
  const MAX = 80;
  const truncated =
    firstLine.length > MAX
      ? firstLine.slice(0, MAX - 1).trimEnd() + "…"
      : firstLine;
  return `Unproved: ${truncated}`;
}

function mintedFromFor(input: MintInput): NonNullable<OpenQuestion["minted_from"]> {
  const out: NonNullable<OpenQuestion["minted_from"]> = {
    qid: input.qid,
    spec: input.spec,
    theorem_local_id: input.theorem.theorem_local_id,
  };
  if (input.theorem.lean_file_relpath) out.lean_file_relpath = input.theorem.lean_file_relpath;
  if (input.theorem.failure_reason) out.failure_reason = input.theorem.failure_reason;
  return out;
}

/**
 * Structural deep equality for plain JSON objects + primitives. Key-order
 * independent (so a hand-edited or jq-rewritten minted_from block does not
 * falsely trigger OpenQuestionConflict).
 */
function deepEqual(a: unknown, b: unknown): boolean {
  if (a === b) return true;
  if (a === null || b === null) return false;
  if (typeof a !== typeof b) return false;
  if (typeof a !== "object") return false;
  if (Array.isArray(a) !== Array.isArray(b)) return false;
  if (Array.isArray(a) && Array.isArray(b)) {
    if (a.length !== b.length) return false;
    return a.every((v, i) => deepEqual(v, b[i]));
  }
  const aObj = a as Record<string, unknown>;
  const bObj = b as Record<string, unknown>;
  const aKeys = Object.keys(aObj);
  const bKeys = Object.keys(bObj);
  if (aKeys.length !== bKeys.length) return false;
  return aKeys.every((k) => Object.prototype.hasOwnProperty.call(bObj, k) && deepEqual(aObj[k], bObj[k]));
}

export async function mintFailedTheoremOpenQuestion(
  input: MintInput,
): Promise<MintResult> {
  if (input.theorem.status !== "failed") {
    throw new Error(
      `mintFailedTheoremOpenQuestion: theorem.status is "${input.theorem.status}" but must be "failed"`,
    );
  }
  if (!stagePastReview(input.theorem.stage_completed)) {
    return { kind: "skipped", reason: "stage_below_0_5", required_stage: "1" };
  }
  const oq_id = `oq_failed_${input.qid}_${input.spec}_${input.theorem.theorem_local_id}`;
  const oq_path = path.join(input.graphRoot, "nodes", "open_question", `${oq_id}.json`);
  const proposed = mintedFromFor(input);

  return withGraphWriteLock(input.graphRoot, async () => {
    if (existsSync(oq_path)) {
      const existing = JSON.parse(await readFile(oq_path, "utf8")) as OpenQuestion;
      if (deepEqual(existing.minted_from, proposed)) {
        return { kind: "existed", oq_id, oq_path };
      }
      throw new OpenQuestionConflict(oq_id, oq_path, existing.minted_from, proposed);
    }
    const node: OpenQuestion = {
      schema_version: 2,
      open_question_id: oq_id,
      title: deriveTitle(input),
      body:
        `causalsmith run \`${input.qid}_${input.spec}\` terminated with the following ` +
        `theorem still unproved (cleared Stage 0.5 math review; failed downstream).\n\n` +
        `**theorem_local_id:** ${input.theorem.theorem_local_id}\n` +
        `**origin_theorem_id:** ${input.theorem.origin_theorem_id}\n` +
        `**stage_at_failure:** ${input.theorem.stage_completed ?? "(none)"}\n` +
        (input.theorem.failure_reason
          ? `**failure_reason:** ${input.theorem.failure_reason}\n`
          : "") +
        (input.theorem.lean_file_relpath
          ? `**lean_file:** ${input.theorem.lean_file_relpath}\n`
          : "") +
        `\n**Statement:**\n\n${input.theorem.statement}`,
      status: "open",
      minted_from: proposed,
    };
    // why: fresh graph roots may not have nodes/open_question yet.
    await mkdir(path.dirname(oq_path), { recursive: true });
    await writeFile(oq_path, JSON.stringify(node, null, 2) + "\n", "utf8");
    return { kind: "created", oq_id, oq_path };
  });
}
