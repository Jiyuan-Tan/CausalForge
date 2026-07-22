/**
 * Phase 4 — Codex-driven next-action proposer.
 *
 * Single ~5-10k-token codex call invoked at two hook sites:
 *   - after research Stage 5 closes an OpenQuestion (`runPostStage5CloseHook`)
 *   - after study S2 commits a graph plan (`stageS2.run`)
 *
 * Inputs are pre-filtered server-side so the codex prompt sees only what is
 * actionable:
 *   - OpenQuestions with `status: "open"` scoped to the just-finished run's
 *     Method family (when a `method_id` is supplied).
 *   - StudyTargets with `status: "pending"`.
 *   - The 5 most-recently-banked theorems.
 *   - The registered-sources index.
 *
 * The codex output (JSON list of options) is validated:
 *   - JSON shape conforms to ProposedOption.
 *   - Every `cited_ids` entry resolves to a real node in the loaded graph.
 *   - Any `study_learn` option whose topic is not covered by an entry in
 *     `registeredSources()` is downgraded to a `register_source` option
 *     (spec §R8 mitigation).
 *
 * On any failure (codex throws, JSON malformed, schema mismatch, or all
 * options rejected by validation), the proposer returns a minimal fallback
 * template. The caller logs `fallback === true` but never blocks completion.
 *
 * The Stop option is always appended.
 */

import path from "node:path";
import { readFile } from "node:fs/promises";
import {
  loadGraph,
  registeredSources,
  nodeTypeOf,
  type Graph,
} from "./graph.js";
import type {
  BankedTheorem,
  OpenQuestion,
  StudyTarget,
  StudyTargetDraft,
} from "./kb_types.js";
import { runCodex as defaultRunCodex } from "./codex.js";

export type ProposedOptionKind =
  | "research_oq"
  | "study_paper"
  | "study_learn"
  | "register_source"
  | "stop";

export interface ProposedOption {
  kind: ProposedOptionKind;
  title: string;
  why: string;
  cited_ids: string[];
  command: string;
  study_target_draft?: StudyTargetDraft;
}

export interface ProposeResult {
  options: ProposedOption[];
  fallback: boolean;
  reason?: string;
}

export interface RunSummary {
  loop: "research" | "study";
  run_id: string;
  /** Plain-English summary of what just completed. */
  text: string;
  /** Optional method id used to scope OQ filtering. */
  method_id?: string | null;
}

/** Allow tests to inject a stub codex without spawning the real CLI. */
export type CodexRunner = (input: {
  prompt: string;
  cwd: string;
}) => Promise<{ stdout: string; stderr: string }>;

export interface ProposeNextOptions {
  /** Absolute path to `<package>/doc/study`. */
  graphRoot: string;
  /** Absolute path passed to the codex runner as cwd. */
  cwd?: string;
  /** Override the codex dispatcher (for tests). */
  runCodex?: CodexRunner;
  /** Override the prompt template used to call codex. */
  promptTemplate?: string;
}

const STOP_OPTION: ProposedOption = {
  kind: "stop",
  title: "Stop",
  why: "Human pacing: take a break, review the just-completed run, or change direction.",
  cited_ids: [],
  command: "# Stop — do not launch a follow-up run.",
};

const FALLBACK_OPTION: ProposedOption = {
  kind: "stop",
  title: "No automatic suggestions",
  why: "propose_next had no validated options (codex failed or all cited ids unresolved). Inspect the just-completed run manually.",
  cited_ids: [],
  command: "# No automatic suggestions available; review the run output and decide manually.",
};

const DEFAULT_PROMPT_TEMPLATE = `You are the CausalSmith next-action proposer.

A run in the {{LOOP}} loop just finished:

{{RUN_SUMMARY}}

Available actionable graph slices:

## Open OpenQuestions (status=open){{METHOD_FILTER_NOTE}}
{{OPEN_QUESTIONS}}

## Pending StudyTargets (status=pending)
{{PENDING_STUDY_TARGETS}}

## Most-recently-banked theorems (up to 5)
{{RECENT_BANKED}}

## Registered sources
{{REGISTERED_SOURCES}}

## Instructions

Propose 1 to 3 ranked next actions for the operator. Every option MUST cite specific node ids by name in its \`why\` field (these ids will be verified against the loaded graph). For each option supply:

- kind: one of "research_oq" | "study_paper" | "study_learn" | "register_source"
- title: a one-line label
- why: 1-3 sentences explaining the choice, citing node ids verbatim
- cited_ids: a JSON array of every node id referenced in \`why\`
- command: a copy-pastable shell command (verbatim)
- study_target_draft: required for kind in {study_paper, study_learn, register_source}; omit for research_oq

Emit ONLY a JSON object of the form:

{
  "options": [ ...ProposedOption ]
}

Do NOT wrap the JSON in prose; do NOT include the Stop option (the renderer appends it).
`;

export async function proposeNext(
  summary: RunSummary,
  opts: ProposeNextOptions,
): Promise<ProposeResult> {
  const runCodex = opts.runCodex ?? defaultRunCodex;
  const cwd = opts.cwd ?? path.dirname(opts.graphRoot);
  let graph: Graph;
  try {
    graph = await loadGraph(opts.graphRoot);
  } catch (err) {
    return fallback(`loadGraph failed: ${(err as Error).message}`);
  }

  const inputs = buildFilteredInputs(graph, summary);
  const prompt = renderPrompt(summary, inputs, opts.promptTemplate);

  let raw: string;
  try {
    const res = await runCodex({ prompt, cwd });
    raw = res.stdout;
  } catch (err) {
    return fallback(`codex error: ${(err as Error).message}`);
  }

  let parsed: unknown;
  try {
    parsed = JSON.parse(extractJson(raw));
  } catch (err) {
    return fallback(`JSON parse error: ${(err as Error).message}`);
  }

  const optionsRaw = (parsed as { options?: unknown }).options;
  if (!Array.isArray(optionsRaw)) return fallback("missing options array");

  const validated: ProposedOption[] = [];
  for (const candidate of optionsRaw) {
    const opt = coerceOption(candidate);
    if (!opt) continue;
    if (opt.kind === "stop") continue; // never accept stop from codex
    if (!citedIdsResolve(graph, opt.cited_ids)) continue;
    const adjusted = downgradeUncoveredLearn(opt, inputs.sources);
    validated.push(adjusted);
    if (validated.length >= 3) break;
  }

  if (validated.length === 0) {
    return fallback("no candidate options passed validation");
  }
  return { options: [...validated, STOP_OPTION], fallback: false };
}

// ---------------------------------------------------------------------------
// Filtering / rendering helpers
// ---------------------------------------------------------------------------

interface FilteredInputs {
  openQuestions: OpenQuestion[];
  pendingTargets: StudyTarget[];
  recentBanked: BankedTheorem[];
  sources: ReturnType<typeof registeredSources>;
}

function buildFilteredInputs(graph: Graph, summary: RunSummary): FilteredInputs {
  const openQuestions: OpenQuestion[] = [];
  const pendingTargets: StudyTarget[] = [];
  const banked: BankedTheorem[] = [];
  for (const node of graph.nodes.values()) {
    const t = nodeTypeOf(node);
    if (t === "open_question") {
      const q = node as OpenQuestion;
      if (q.status === "open") {
        if (summary.method_id && q.seed_method_id !== summary.method_id) {
          // Allow OQs without a seed_method_id (broad questions) when filtering
          // by method, otherwise scope strictly.
          if (q.seed_method_id !== undefined) continue;
        }
        openQuestions.push(q);
      }
    } else if (t === "study_target") {
      const st = node as StudyTarget;
      if (st.status === "pending") pendingTargets.push(st);
    } else if (t === "banked_theorem") {
      banked.push(node as BankedTheorem);
    }
  }
  // Recent banked: lexicographic by id is a stand-in for chronological ordering
  // in the absence of a created_at field; keep it stable and bounded at 5.
  banked.sort((a, b) => b.bt_id.localeCompare(a.bt_id));
  return {
    openQuestions: openQuestions.sort((a, b) => a.open_question_id.localeCompare(b.open_question_id)),
    pendingTargets: pendingTargets.sort((a, b) => a.study_target_id.localeCompare(b.study_target_id)),
    recentBanked: banked.slice(0, 5),
    sources: registeredSources(graph),
  };
}

function renderPrompt(
  summary: RunSummary,
  inputs: FilteredInputs,
  template: string | undefined,
): string {
  const t = template ?? DEFAULT_PROMPT_TEMPLATE;
  const methodNote = summary.method_id ? ` scoped to method=${summary.method_id}` : "";
  const renderOq = (q: OpenQuestion) =>
    `- ${q.open_question_id}: ${q.title} (seed_method=${q.seed_method_id ?? "—"})`;
  const renderSt = (st: StudyTarget) =>
    `- ${st.study_target_id}: ${st.title}${st.suggested_keywords?.length ? ` [keywords: ${st.suggested_keywords.join(", ")}]` : ""}`;
  const renderBt = (b: BankedTheorem) =>
    `- ${b.bt_id} (qid=${b.qid}, spec=${b.spec})`;
  const renderSources = (s: FilteredInputs["sources"]) => {
    const lines: string[] = [];
    if (s.papers.length) lines.push(`papers: ${s.papers.map((p) => p.paper_id).join(", ")}`);
    if (s.textbooks.length) lines.push(`textbooks: ${s.textbooks.map((b) => b.book_id).join(", ")}`);
    if (s.lecture_notes.length) lines.push(`lecture_notes: ${s.lecture_notes.map((n) => n.note_meta_id).join(", ")}`);
    return lines.length > 0 ? lines.join("\n") : "(none registered)";
  };
  return t
    .replaceAll("{{LOOP}}", summary.loop)
    .replaceAll("{{RUN_SUMMARY}}", summary.text)
    .replaceAll("{{METHOD_FILTER_NOTE}}", methodNote)
    .replaceAll(
      "{{OPEN_QUESTIONS}}",
      inputs.openQuestions.length > 0
        ? inputs.openQuestions.map(renderOq).join("\n")
        : "(none open)",
    )
    .replaceAll(
      "{{PENDING_STUDY_TARGETS}}",
      inputs.pendingTargets.length > 0
        ? inputs.pendingTargets.map(renderSt).join("\n")
        : "(none pending)",
    )
    .replaceAll(
      "{{RECENT_BANKED}}",
      inputs.recentBanked.length > 0
        ? inputs.recentBanked.map(renderBt).join("\n")
        : "(none banked yet)",
    )
    .replaceAll("{{REGISTERED_SOURCES}}", renderSources(inputs.sources));
}

function extractJson(raw: string): string {
  // codex sometimes wraps JSON in a ```json fence. Strip leading prose and
  // trailing prose so JSON.parse can handle the common cases.
  const trimmed = raw.trim();
  const fenceMatch = /```(?:json)?\s*([\s\S]*?)\s*```/.exec(trimmed);
  if (fenceMatch) return fenceMatch[1];
  const firstBrace = trimmed.indexOf("{");
  const lastBrace = trimmed.lastIndexOf("}");
  if (firstBrace === -1 || lastBrace === -1 || lastBrace <= firstBrace) return trimmed;
  return trimmed.slice(firstBrace, lastBrace + 1);
}

function coerceOption(raw: unknown): ProposedOption | null {
  if (!raw || typeof raw !== "object") return null;
  const r = raw as Record<string, unknown>;
  const kind = r.kind;
  if (
    kind !== "research_oq" &&
    kind !== "study_paper" &&
    kind !== "study_learn" &&
    kind !== "register_source" &&
    kind !== "stop"
  ) return null;
  if (typeof r.title !== "string" || typeof r.why !== "string" || typeof r.command !== "string") {
    return null;
  }
  if (!Array.isArray(r.cited_ids) || r.cited_ids.length === 0 || !r.cited_ids.every((x) => typeof x === "string")) return null;
  const cited = r.cited_ids; // why: every proposed option must carry at least one well-formed evidence id, not a filtered-empty contract.
  const out: ProposedOption = {
    kind,
    title: r.title,
    why: r.why,
    cited_ids: cited,
    command: r.command,
  };
  if (kind === "study_paper" || kind === "study_learn" || kind === "register_source") {
    if (!isStudyTargetDraft(r.study_target_draft)) return null;
    out.study_target_draft = r.study_target_draft;
  } else if (r.study_target_draft && typeof r.study_target_draft === "object") {
    if (!isStudyTargetDraft(r.study_target_draft)) return null;
    out.study_target_draft = r.study_target_draft;
  }
  return out;
}

function isStringArray(v: unknown): v is string[] {
  return Array.isArray(v) && v.every((x) => typeof x === "string");
}

function isStudyTargetDraft(v: unknown): v is StudyTargetDraft {
  if (!v || typeof v !== "object") return false;
  const d = v as Record<string, unknown>;
  if (typeof d.title !== "string" || typeof d.rationale !== "string" || typeof d.from_qid !== "string") {
    return false;
  }
  if (d.from_run_state !== undefined && typeof d.from_run_state !== "string") return false;
  if (d.gap_description !== undefined && typeof d.gap_description !== "string") return false;
  if (d.suggested_source !== undefined && typeof d.suggested_source !== "string") return false;
  if (d.suggested_keywords !== undefined && !isStringArray(d.suggested_keywords)) return false;
  // why: study/register actions commit this draft later, so reject malformed payloads here.
  return true;
}

function citedIdsResolve(graph: Graph, ids: string[]): boolean {
  for (const id of ids) {
    if (!graph.nodes.has(id)) return false;
  }
  return true;
}

function downgradeUncoveredLearn(
  opt: ProposedOption,
  sources: FilteredInputs["sources"],
): ProposedOption {
  if (opt.kind !== "study_learn") return opt;
  const draft = opt.study_target_draft;
  if (!draft) return opt;
  const ref = draft.suggested_source ?? "";
  if (ref && sourceCovered(ref, sources)) return opt;
  // Downgrade: replace with a register_source option pointing the user at
  // register_book.ts (spec §R8 mitigation).
  return {
    kind: "register_source",
    title: `Register a source first`,
    why: `${opt.why} — no registered source covers this topic; register one via tools/bin/register_book.ts before launching --learn.`,
    cited_ids: opt.cited_ids,
    command: `npx tsx tools/bin/register_book.ts <book_id> <pdf_path>  # then: ${opt.command}`,
    study_target_draft: draft,
  };
}

function sourceCovered(ref: string, sources: FilteredInputs["sources"]): boolean {
  // Heuristic: a ref is "covered" if its leading identifier matches a known
  // paper id, textbook book_id, or lecture-note meta id.
  const head = ref.split(":")[0];
  if (sources.papers.some((p) => p.paper_id === head)) return true;
  if (sources.textbooks.some((b) => b.book_id === head)) return true;
  if (sources.lecture_notes.some((n) => n.note_meta_id === head)) return true;
  return false;
}

function fallback(reason: string): ProposeResult {
  return {
    options: [{ ...FALLBACK_OPTION, why: `${FALLBACK_OPTION.why} Reason: ${reason}` }],
    fallback: true,
    reason,
  };
}

/** Exported helpers reused by tests (and writer glue). */
export const __internals = {
  buildFilteredInputs,
  renderPrompt,
  coerceOption,
  citedIdsResolve,
  downgradeUncoveredLearn,
  STOP_OPTION,
  FALLBACK_OPTION,
};

export async function readPromptFile(absPath: string): Promise<string> {
  return readFile(absPath, "utf8");
}
