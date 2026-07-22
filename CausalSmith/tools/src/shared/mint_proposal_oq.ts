/**
 * Mint an OpenQuestion node from an Open-ended Question in a D-1.2 proposal
 * whose §8 has no Conjecture (proposer chose a constructive / design /
 * computation question as the kernel slot — peer to Conjecture).
 *
 * Fires at Stage 0 short-circuit time, BEFORE any math derivation runs:
 * Stage 0.0 parses §8, finds zero Conjectures + ≥1 Open-ended Questions, banks
 * each OEQ via this minter, and the orchestrator skips F-phase.
 *
 * Distinct from `mintFailedTheoremOpenQuestion` (post-F5, theorem-derived):
 * here the run never reaches math review, so there is no Stage 0.5 gate.
 * The proposal cleared D-0.5 ACCEPT, which is the upstream quality bar.
 *
 * Invariant: idempotent on (qid, spec, oeq_local_label). The OQ id is
 * deterministic: `oq_proposal_<qid>_<spec>_<oeq_local_label>`. On second call
 * with identical inputs the existing file is preserved and result kind is
 * `"existed"`. On conflict, `OpenQuestionConflict` is thrown.
 *
 * Lifecycle: minted OQs start as `status: "open"`. A future causalsmith run
 * launched with `--from-question <oq_id>` can claim then close them.
 */
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import type { OpenQuestion } from "./kb_types.js";
import { withGraphWriteLock } from "./graph_lock.js";
import { OpenQuestionConflict } from "./mint_failed_theorem_oq.js";

// ---------------------------------------------------------------------------
// Open-ended Question proposal-grammar concept (type moved here 2026-07-20 when
// the per-conjecture D0 parse path — conjecture_parser.ts — was retired; this
// module is its only remaining consumer).
// ---------------------------------------------------------------------------

export interface ParsedOpenEndedQuestion {
  /** 1-indexed position from "Open-ended Question N" in the bracketed argument. */
  index: number;
  /** Slug from `\label{oeq:<slug>}`. */
  label: string;
  /** Optional title after "Open-ended Question N:" — empty string if absent. */
  title: string;
  /** Verbatim body (statement + Handle + Why it matters), trimmed. */
  body: string;
  /** Handle text extracted from `\textbf{Handle:}` clause; empty string if absent. */
  handle: string;
  /** Why-it-matters text extracted from `\textbf{Why it matters:}` clause; empty string if absent. */
  why_it_matters: string;
  beginLine: number;
}

export interface ProposalOqMintInput {
  qid: string;
  spec: string;
  oeq: ParsedOpenEndedQuestion;
  /** Absolute path of the proposal .tex this OEQ was parsed from. */
  proposal_path: string;
  /** Idea-map graph root (e.g. `<repoRoot>/doc/study`). */
  graphRoot: string;
}

export type ProposalOqMintResult =
  | { kind: "created"; oq_id: string; oq_path: string }
  | { kind: "existed"; oq_id: string; oq_path: string };

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
  return aKeys.every(
    (k) => Object.prototype.hasOwnProperty.call(bObj, k) && deepEqual(aObj[k], bObj[k]),
  );
}

function deriveTitle(input: ProposalOqMintInput): string {
  const t = input.oeq.title.trim();
  if (t.length > 0) return `Open: ${t}`;
  return `Open: ${input.oeq.label} (${input.qid}/${input.spec})`;
}

function buildBody(input: ProposalOqMintInput): string {
  const lines: string[] = [
    `causalsmith run \`${input.qid}_${input.spec}\` proposed this Open-ended Question ` +
      `in §8 of its D-1.2 proposal. The proposal cleared D-0.5 ACCEPT with no Conjecture ` +
      `to derive (the OEQ IS the kernel slot, peer to Conjecture), so the F-phase was ` +
      `skipped and the OEQ was banked here for future causalsmith dispatch via ` +
      `\`--from-question <oq_id>\`.`,
    "",
    `**oeq_local_label:** ${input.oeq.label}`,
    `**proposal_path:** ${input.proposal_path}`,
    `**title:** ${input.oeq.title || "(untitled)"}`,
  ];
  if (input.oeq.handle.length > 0) {
    lines.push(`**Handle:** ${input.oeq.handle}`);
  }
  if (input.oeq.why_it_matters.length > 0) {
    lines.push(`**Why it matters:** ${input.oeq.why_it_matters}`);
  }
  lines.push("", "**Verbatim §8 body:**", "", input.oeq.body);
  return lines.join("\n");
}

function mintedFromFor(
  input: ProposalOqMintInput,
): NonNullable<OpenQuestion["minted_from"]> {
  return {
    qid: input.qid,
    spec: input.spec,
    origin: "proposal_open_ended_question",
    oq_local_label: input.oeq.label,
    proposal_path: input.proposal_path,
  };
}

export async function mintProposalOpenEndedQuestion(
  input: ProposalOqMintInput,
): Promise<ProposalOqMintResult> {
  const oq_id = `oq_proposal_${input.qid}_${input.spec}_${input.oeq.label}`;
  const oq_path = path.join(
    input.graphRoot,
    "nodes",
    "open_question",
    `${oq_id}.json`,
  );
  const proposed = mintedFromFor(input);

  return withGraphWriteLock(input.graphRoot, async () => {
    if (existsSync(oq_path)) {
      const existing = JSON.parse(await readFile(oq_path, "utf8")) as OpenQuestion;
      if (deepEqual(existing.minted_from, proposed)) {
        return { kind: "existed", oq_id, oq_path };
      }
      throw new OpenQuestionConflict(
        oq_id,
        oq_path,
        existing.minted_from,
        proposed,
      );
    }
    const node: OpenQuestion = {
      schema_version: 2,
      open_question_id: oq_id,
      title: deriveTitle(input),
      body: buildBody(input),
      status: "open",
      minted_from: proposed,
    };
    // why: fresh graph roots may not have nodes/open_question yet.
    await mkdir(path.dirname(oq_path), { recursive: true });
    await writeFile(oq_path, JSON.stringify(node, null, 2) + "\n", "utf8");
    return { kind: "created", oq_id, oq_path };
  });
}
