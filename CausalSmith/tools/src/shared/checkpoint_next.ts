/**
 * Phase 4 — pure Markdown renderer for CHECKPOINT_NEXT.md.
 *
 * No filesystem, no codex. Given a CheckpointNextInput, returns the full
 * Markdown body that the writer module persists to
 * `<run_dir>/CHECKPOINT_NEXT.md`.
 *
 * Conventions (spec §6.2):
 *   - Header always includes `Loop: <loop>, lineage depth: <depth>` and an
 *     optional `origin:` field.
 *   - When `lineage_depth > 3` a banner block is prepended just under the
 *     header advising the operator to consider stopping (spec §R6).
 *   - "What just finished" carries the supplied paragraph verbatim.
 *   - Each ProposedOption renders as `### Option N — <title>`, a `Why:` line,
 *     and a fenced bash block with the verbatim command. When the option has
 *     a `study_target_draft`, the JSON serialisation is embedded as an
 *     adjacent fenced json block so the retired study CLI's `--target-from` can parse it.
 *   - The Stop option (always the last entry) is rendered the same way.
 */

import type { ProposedOption } from "./propose_next.js";

export interface CheckpointNextInput {
  run_id: string;
  loop: "research" | "study";
  what_just_finished: string;
  options: ProposedOption[];
  lineage_depth: number;
  lineage_origin?: string;
  /** When true, prefix the file with a `> ⚠️ fallback` block. */
  fallback?: boolean;
}

const LINEAGE_BANNER_THRESHOLD = 3;

export function renderCheckpointNext(input: CheckpointNextInput): string {
  const lines: string[] = [];
  lines.push(`# Next-action checkpoint for ${input.run_id}`);
  const headerSegments = [`Loop: ${input.loop}`, `lineage depth: ${input.lineage_depth}`];
  if (input.lineage_origin) headerSegments.push(`origin: ${input.lineage_origin}`);
  lines.push("");
  lines.push(headerSegments.join(", "));
  lines.push("");

  if (input.lineage_depth > LINEAGE_BANNER_THRESHOLD) {
    lines.push("> **Consider stopping or changing direction.**");
    lines.push(`>`);
    lines.push(
      `> This run sits at lineage depth ${input.lineage_depth}; the spec (§R6) recommends a hard reset past depth ${LINEAGE_BANNER_THRESHOLD} to avoid drift.`,
    );
    lines.push("");
  }

  if (input.fallback) {
    lines.push("> ⚠️ propose_next fell back to the no-suggestions template (codex failed or no validated options).");
    lines.push("");
  }

  lines.push("## What just finished");
  lines.push("");
  lines.push(input.what_just_finished.trim());
  lines.push("");
  lines.push("## Proposed next actions");
  lines.push("");

  let n = 0;
  for (const opt of input.options) {
    n += 1;
    lines.push(`### Option ${n} — ${opt.title}`);
    lines.push("");
    lines.push(`Why: ${opt.why}`);
    lines.push("");
    lines.push(`Command:`);
    lines.push("```bash");
    lines.push(opt.command);
    lines.push("```");
    if (opt.study_target_draft) {
      lines.push("");
      lines.push(`Draft StudyTarget JSON:`);
      lines.push("```json");
      lines.push(JSON.stringify(opt.study_target_draft, null, 2));
      lines.push("```");
    }
    lines.push("");
  }

  return lines.join("\n");
}

// ---------------------------------------------------------------------------
// Reverse parser for --target-from consumption.
// ---------------------------------------------------------------------------

export interface ParsedOption {
  option_n: number;
  title: string;
  command: string;
  study_target_draft?: unknown;
}

/**
 * Extract the Nth option's command + embedded JSON draft from a
 * CHECKPOINT_NEXT.md body. Used by the retired study CLI's `--target-from`.
 *
 * Throws when the option does not exist or when an Option 2/3 lacks an
 * embedded JSON payload.
 */
export function parseCheckpointNext(markdown: string, optionN: number): ParsedOption {
  const sections = splitSections(markdown);
  if (optionN < 1 || optionN > sections.length) {
    throw new Error(
      `CHECKPOINT_NEXT has ${sections.length} option(s); --target-from asked for Option ${optionN}.`,
    );
  }
  const section = sections[optionN - 1];
  const title = section.title;
  const command = extractFencedBlock(section.body, "bash");
  if (!command) {
    throw new Error(`Option ${optionN} (${title}) has no Command fenced bash block.`);
  }
  const jsonRaw = extractFencedBlock(section.body, "json");
  const draft = jsonRaw ? JSON.parse(jsonRaw) : undefined;
  return { option_n: optionN, title, command, study_target_draft: draft };
}

interface Section { title: string; body: string }

function splitSections(md: string): Section[] {
  const out: Section[] = [];
  const re = /^###\s+Option\s+(\d+)\s+—\s+(.+)$/gm;
  const matches: Array<{ idx: number; n: number; title: string }> = [];
  let m: RegExpExecArray | null;
  while ((m = re.exec(md)) !== null) {
    matches.push({ idx: m.index + m[0].length, n: Number(m[1]), title: m[2].trim() });
  }
  for (let i = 0; i < matches.length; i++) {
    const start = matches[i].idx;
    const end = i + 1 < matches.length ? md.lastIndexOf("\n", matches[i + 1].idx - 1) : md.length;
    out.push({ title: matches[i].title, body: md.slice(start, end) });
  }
  return out;
}

function extractFencedBlock(body: string, lang: string): string | null {
  const re = new RegExp("```" + lang + "\\s*\\n([\\s\\S]*?)```", "m");
  const m = re.exec(body);
  return m ? m[1].replace(/\n$/, "") : null;
}
