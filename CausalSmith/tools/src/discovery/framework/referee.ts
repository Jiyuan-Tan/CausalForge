// Shared referee harness (spec §Stage kernel): one implementation of
// "render output template → dispatch reviewer → parse stdout JSON → strip
// template scaffolding → extract verdict". Divergence between hand-rolled
// copies of this pipeline produced real incidents (stale template prefill,
// silent parse-failure→phantom-REVISE). Two contracts:
//   - stdout mode (default; D-0.5, D0.5.G): the reviewer emits the verdict
//     JSON on stdout.
//   - `verdictFile` mode (D0.5 panel): the reviewer's stdout carries only the
//     {status,...} wrapper and the verdict JSON is written to the given path.
// Stage-specific validation (source receipts, Zod verdict schemas, fail-closed
// artifact checks) stays in the caller.
import { existsSync } from "node:fs";
import path from "node:path";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { templatePath } from "../../paths.js";
import type { PipelineContext, Stage } from "../../types.js";
import { parseStageOutput, type StageDeps } from "../../pipeline_support.js";
import type { CodexRunInput } from "../../shared/codex.js";
import { dispatchAgent, parseAgentJson } from "../../framework/agent_dispatch.js";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairLatexStringsDeep,
} from "../core/latex_serialization.js";

/** Apply the post-parse LaTeX repair to a parsed verdict and report any surviving
 * decoded control character as a parse error (the referee failure convention). */
function repairAndCheckVerdict(json: Record<string, unknown>, source: string): string | null {
  repairLatexStringsDeep(json);
  try {
    assertNoDecodedControlChars(json, source);
    return null;
  } catch (err) {
    return err instanceof Error ? err.message : String(err);
  }
}

/** Drop keys starting with "_" recursively. Reviewer output templates use
 *  `_emit_rules` / `_prototype` / `_doc` scaffolding the agent is told to
 *  strip; this guards the downstream JSON if it forgets. */
export function stripTemplateScaffolding(value: unknown): unknown {
  if (Array.isArray(value)) return value.map(stripTemplateScaffolding);
  if (value && typeof value === "object") {
    const out: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(value as Record<string, unknown>)) {
      if (k.startsWith("_")) continue;
      out[k] = stripTemplateScaffolding(v);
    }
    return out;
  }
  return value;
}

/** Render a reviewer's stdout-JSON template into the qid folder, applying the
 *  caller's prefill mutation. Re-rendered per attempt so the template always
 *  matches the artifact under review. */
export async function renderRefereeTemplate(args: {
  ctx: PipelineContext;
  templateName: string;
  targetPath: string;
  prefill: (tmpl: Record<string, unknown>) => void;
}): Promise<void> {
  const src = await readFile(templatePath(args.ctx.repoRoot, args.templateName), "utf8");
  const tmpl = JSON.parse(src) as Record<string, unknown>;
  args.prefill(tmpl);
  await mkdir(path.dirname(args.targetPath), { recursive: true });
  await writeFile(args.targetPath, `${JSON.stringify(tmpl, null, 2)}\n`, "utf8");
}

/** `verdictFile` mode only: the mechanical failure class, so a caller can keep
 *  its own stage-specific error message per class. */
export type RefereeFailure =
  | { kind: "stdout-parse" }
  | { kind: "not-completed"; status: string }
  | { kind: "missing-file"; path: string };

export interface RefereeResult {
  raw: string;
  json: Record<string, unknown>;
  /** Uppercased `verdict` field, or null when absent/unparseable. */
  verdict: string | null;
  /** Non-null ⇒ the review DID NOT HAPPEN mechanically (parse failure or a
   *  caller-supplied validation error). A parse failure must never masquerade
   *  as a review verdict — callers halt without consuming a revise round. */
  parseError: string | null;
  /** Non-null only in `verdictFile` mode, alongside `parseError`. */
  failure: RefereeFailure | null;
}

/** Dispatch a referee and parse its verdict. `validate` (optional) runs over
 *  the parsed+stripped JSON and returns an error string to fail the review
 *  mechanically (e.g. missing source receipts). */
export async function runReferee(args: {
  ctx: PipelineContext;
  deps: StageDeps;
  stage: Stage;
  label: string;
  prompt: string;
  promptSources: string[];
  model: string;
  reasoningEffort: CodexRunInput["reasoningEffort"];
  inactivityTimeoutMs?: number;
  /** Forwarded to dispatchAgent/runCodex (e.g. a cold referee disables the Lean LSP). */
  leanLsp?: boolean;
  /** When set, stdout is parsed as the {status,...} stage wrapper and the verdict
   *  JSON is read from this path instead of stdout. The caller owns removing any
   *  stale file before the call, so existence proves a fresh write. A malformed
   *  verdict FILE throws (it is caller-diagnosable data corruption, not a verdict). */
  verdictFile?: string;
  validate?: (json: Record<string, unknown>) => string | null;
}): Promise<RefereeResult> {
  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: args.stage,
    label: args.label,
    prompt: args.prompt,
    promptSources: args.promptSources,
    model: args.model,
    reasoningEffort: args.reasoningEffort,
    inactivityTimeoutMs: args.inactivityTimeoutMs,
    ...(args.leanLsp !== undefined ? { leanLsp: args.leanLsp } : {}),
  });
  if (args.verdictFile !== undefined) {
    const parsed = parseStageOutput(out.stdout);
    if (parsed.status === "parse_failed") {
      return {
        raw: out.stdout, json: {}, verdict: null,
        parseError: "stage output did not parse (parse_failed)",
        failure: { kind: "stdout-parse" },
      };
    }
    if (parsed.status !== "completed") {
      return {
        raw: out.stdout, json: {}, verdict: null,
        parseError: `referee did not complete (status='${parsed.status ?? "missing"}')`,
        failure: { kind: "not-completed", status: parsed.status ?? "missing" },
      };
    }
    if (!existsSync(args.verdictFile)) {
      return {
        raw: out.stdout, json: {}, verdict: null,
        parseError: `referee completed without writing ${args.verdictFile}`,
        failure: { kind: "missing-file", path: args.verdictFile },
      };
    }
    // Model-written verdict JSON quotes TeX statements — repair under-escaped
    // backslashes at the raw-byte boundary before parsing.
    const fileJson = JSON.parse(normalizeRawModelJson(await readFile(args.verdictFile, "utf8"))) as Record<string, unknown>;
    const json = stripTemplateScaffolding(fileJson) as Record<string, unknown>;
    const controlError = repairAndCheckVerdict(json, `referee verdict file ${args.verdictFile}`);
    const validationError = args.validate ? args.validate(json) : null;
    const verdict = typeof json.verdict === "string" ? json.verdict.toUpperCase() : null;
    return { raw: out.stdout, json, verdict, parseError: controlError ?? validationError, failure: null };
  }
  const parsed = parseAgentJson(out.stdout);
  if (!parsed.json) {
    return { raw: out.stdout, json: {}, verdict: null, parseError: parsed.parseError, failure: null };
  }
  const json = stripTemplateScaffolding(parsed.json) as Record<string, unknown>;
  const controlError = repairAndCheckVerdict(json, "referee stdout verdict");
  const validationError = args.validate ? args.validate(json) : null;
  const verdict = typeof json.verdict === "string" ? json.verdict.toUpperCase() : null;
  return { raw: out.stdout, json, verdict, parseError: controlError ?? validationError, failure: null };
}
