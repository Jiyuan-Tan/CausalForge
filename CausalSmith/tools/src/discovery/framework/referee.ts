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
import { appendPipelineLog } from "../../log.js";
import { templatePath } from "../../paths.js";
import type { PipelineContext, Stage } from "../../types.js";
import { parseStageOutput, type StageDeps } from "../../pipeline_support.js";
import type { CodexRunInput } from "../../shared/codex.js";
import { ClaudeRunError } from "../../workers/claude.js";
import { dispatchAgent, dispatchClaudeAgent, parseAgentJson } from "../../framework/agent_dispatch.js";
import {
  assertNoDecodedControlChars,
  containsLikelyDecodedTexNewlines,
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
  provenance: {
    requested_runner: "codex" | "claude";
    actual_runner: "codex" | "claude";
    model: string;
    fallback_kind: string | null;
    quorum: number;
  };
}

const CODEX_COLD_REFEREE_PREAMBLE = [
  "You are a non-interactive cold referee in an automated pipeline.",
  "The prompt is the world: do not use filesystem, shell, web, MCP, or subagent tools.",
  "Judge only the note and definitions in this prompt. Do not seek repository rubrics or run artifacts.",
  "Emit only the single JSON object requested by the prompt, with no commentary before or after it.",
].join("\n");

/** Classify only verified service/quota unavailability. Configuration errors,
 * timeouts and ambiguous failures fail closed and do not swap judges. */
export function claudeUnavailableKind(err: unknown): string | null {
  const message = err instanceof Error ? err.message : String(err);
  const stdout = err instanceof ClaudeRunError ? err.stdout : "";
  const stderr = err instanceof ClaudeRunError ? err.stderr : "";
  const diagnostic = `${message}\n${stdout}\n${stderr}`;
  const events = stdout.split(/\r?\n/).flatMap((line) => {
    try { return [JSON.parse(line) as Record<string, unknown>]; } catch { return []; }
  });
  const hasSubstantiveResponse = events.some((event) =>
    (event.type === "assistant" && event.is_api_error_message !== true) ||
    (event.type === "result" && event.is_error !== true && event.api_error_status === undefined),
  );
  // Never discard a substantive response merely because CLI teardown failed.
  if (hasSubstantiveResponse) return null;
  const apiStatuses = events
    .map((event) => typeof event.api_error_status === "number" ? event.api_error_status : null)
    .filter((status): status is number => status !== null);
  if (apiStatuses.includes(429) || events.some((event) => event.type === "rate_limit_event") ||
      /api_error_status[^\n]*429|rate_limit_event|hit your session limit|usage limit reached|rate[ -]?limit(?:ed| exceeded)?|quota (?:exceeded|exhausted)/i.test(diagnostic)) {
    return "rate-limit";
  }
  if (apiStatuses.some((status) => status === 502 || status === 503) ||
      /api_error_status[^\n]*50[23]|service unavailable|temporarily unavailable|overloaded_error/i.test(diagnostic)) {
    return "service-unavailable";
  }
  if (/\bENOENT\b|command not found|executable not found|spawn claude[^\n]*not found/i.test(diagnostic)) {
    return "runner-unavailable";
  }
  return null;
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
  /** Which agent runner judges. Defaults to `codex`. `claude` routes through
   *  `dispatchClaudeAgent` with NO filesystem tools — denying disk access is what keeps a
   *  rubric-free referee rubric-free (it cannot go read the flagship rubric off disk) and
   *  what stops run artifacts (prior reviews, state) from steering a cold verdict.
   *  Parsing, LaTeX repair and `validate` are shared, so the verdict contract is
   *  identical either way. See `webSearch` for the one tool a referee may opt into. */
  runner?: "codex" | "claude";
  /** Grant (or deny) hosted web search. A referee grading novelty against published work
   *  needs it: what a named comparator actually states is not in the note and cannot be
   *  inferred from it. Filesystem access is NOT the alternative — it would reintroduce the
   *  steering the no-disk call prevents. The web reaches the SOURCE, not the run.
   *
   *  Leave UNSET to keep each runner's own default, which differ and deliberately so:
   *  the claude path is forced hermetic (a zero-tool call), while codex keeps its
   *  default-on hosted `web_search`. Set it explicitly to pin the intent either way. */
  webSearch?: boolean;
  model: string;
  /** Optional, explicit availability fallback for a configured Claude referee.
   *  It fires only when runClaude throws ClaudeRunError (process failure,
   *  timeout, quota/unavailability), never when Claude returned a malformed or
   *  schema-invalid verdict. The swap is recorded in pipeline.jsonl. */
  claudeUnavailableFallback?: {
    runner: "codex";
    model: string;
    reasoningEffort?: CodexRunInput["reasoningEffort"];
  };
  /** Codex-only; ignored when `runner === "claude"` (the claude CLI has no effort knob). */
  reasoningEffort?: CodexRunInput["reasoningEffort"];
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
  let out: { stdout: string; stderr: string } | undefined;
  const requestedRunner = args.runner ?? "codex";
  let actualRunner: "codex" | "claude" = requestedRunner;
  let actualModel = args.model;
  let fallbackKind: string | null = null;
  let quorum = 1;
  if (args.runner === "claude") {
    try {
      if (!args.deps.runClaude) {
        throw new Error("claude executable not found: no claude runner is configured on deps");
      }
      const stdout = await dispatchClaudeAgent({
        ctx: args.ctx,
        deps: { runClaude: args.deps.runClaude },
        stage: args.stage,
        label: args.label,
        promptSources: args.promptSources,
        input: {
          prompt: args.prompt,
          cwd: args.ctx.repoRoot,
          model: args.model,
          // Filesystem/subagent tools stay denied regardless of `webSearch`: the grant is
          // "reach the literature", not "reach the run". `buildClaudePreamble` adapts on
          // its own — with web on, the preamble advertises exactly WebFetch/WebSearch
          // instead of asserting the zero-tool "the prompt is the world".
          allowedTools: [],
          allowSubagents: false,
          webSearch: args.webSearch === true,
          leanLsp: false,
          ...(args.inactivityTimeoutMs !== undefined ? { inactivityTimeoutMs: args.inactivityTimeoutMs } : {}),
        },
      });
      out = { stdout, stderr: "" };
    } catch (err) {
      const fallback = args.claudeUnavailableFallback;
      const unavailableKind = claudeUnavailableKind(err);
      if (fallback === undefined || unavailableKind === null) throw err;
      actualRunner = "codex";
      actualModel = fallback.model;
      fallbackKind = unavailableKind;
      await appendPipelineLog(args.ctx, {
        stage: args.stage,
        status: "dispatch-fallback",
        duration_ms: 0,
        model: fallback.model,
        message:
          `${args.label}: Claude unavailable [${unavailableKind}] (${err instanceof Error ? err.message : String(err)}); ` +
          `falling back to one Codex cold review ${fallback.model}/${fallback.reasoningEffort ?? "high"}`,
      });
      out = await dispatchAgent({
        ctx: args.ctx,
        deps: args.deps,
        stage: args.stage,
        label: `${args.label} (Codex availability fallback)`,
        prompt: `${CODEX_COLD_REFEREE_PREAMBLE}\n\n${args.prompt}`,
        promptSources: args.promptSources,
        model: fallback.model,
        reasoningEffort: fallback.reasoningEffort,
        inactivityTimeoutMs: args.inactivityTimeoutMs,
        leanLsp: false,
        multiAgent: false,
        // Inherit the grant: a stage whose verdict needs the literature must not lose
        // the web merely because the Claude process was unavailable. Codex's search is
        // hosted/server-side, so `read-only` does not block it.
        webSearch: args.webSearch === true,
        sandboxMode: "read-only",
        ignoreUserConfig: true,
      });
    }
  } else {
    out = await dispatchAgent({
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
      // Forwarded ONLY when the caller set it. Codex's hosted `web_search` is default-ON,
      // and D-0.5 (whose prompt instructs citation verification) relies on that default —
      // mapping unset to `false` here would silently take the web away from it.
      ...(args.webSearch !== undefined ? { webSearch: args.webSearch } : {}),
    });
  }
  if (!out) throw new Error(`${args.label}: fallback quorum produced no referee output`);
  if (args.verdictFile !== undefined) {
    const parsed = parseStageOutput(out.stdout);
    if (parsed.status === "parse_failed") {
      return {
        raw: out.stdout, json: {}, verdict: null,
        parseError: "stage output did not parse (parse_failed)",
        failure: { kind: "stdout-parse" }, provenance: { requested_runner: requestedRunner, actual_runner: actualRunner, model: actualModel, fallback_kind: fallbackKind, quorum },
      };
    }
    if (parsed.status !== "completed") {
      return {
        raw: out.stdout, json: {}, verdict: null,
        parseError: `referee did not complete (status='${parsed.status ?? "missing"}')`,
        failure: { kind: "not-completed", status: parsed.status ?? "missing" }, provenance: { requested_runner: requestedRunner, actual_runner: actualRunner, model: actualModel, fallback_kind: fallbackKind, quorum },
      };
    }
    if (!existsSync(args.verdictFile)) {
      return {
        raw: out.stdout, json: {}, verdict: null,
        parseError: `referee completed without writing ${args.verdictFile}`,
        failure: { kind: "missing-file", path: args.verdictFile }, provenance: { requested_runner: requestedRunner, actual_runner: actualRunner, model: actualModel, fallback_kind: fallbackKind, quorum },
      };
    }
    // Model-written verdict JSON quotes TeX statements — repair under-escaped
    // backslashes at the raw-byte boundary before parsing.
    const fileJson = JSON.parse(normalizeRawModelJson(await readFile(args.verdictFile, "utf8"))) as Record<string, unknown>;
    const json = stripTemplateScaffolding(fileJson) as Record<string, unknown>;
    const controlError = repairAndCheckVerdict(json, `referee verdict file ${args.verdictFile}`);
    const validationError = args.validate ? args.validate(json) : null;
    const verdict = typeof json.verdict === "string" ? json.verdict.toUpperCase() : null;
    return { raw: out.stdout, json, verdict, parseError: controlError ?? validationError, failure: null, provenance: { requested_runner: requestedRunner, actual_runner: actualRunner, model: actualModel, fallback_kind: fallbackKind, quorum } };
  }
  // Stdout-mode referees can quote TeX in their JSON just as verdict-file
  // referees do.  Preserve `out.stdout` as the raw receipt, but normalize a
  // separate copy at the raw-byte boundary before JSON.parse.  In particular,
  // model output such as `\(d/\epsilon\)` otherwise fails on the invalid `\(`
  // escape before the post-parse LaTeX repair can run.
  let parsed = parseAgentJson(normalizeRawModelJson(out.stdout));
  if (!parsed.json) {
    // The normalizer assumes a pure JSON document: narration around the JSON
    // with an ODD number of `"` characters flips its in-string tracker for the
    // rest of the stream and corrupts the real (correctly escaped) JSON. Fall
    // back to the untouched stdout before discarding a paid review round — but
    // FAIL CLOSED if the un-normalized parse shows the `\n`-family decode
    // signature (`\neq` → newline+"eq"): that is silent TeX corruption only the
    // raw-byte normalizer could have prevented, and a discarded round is
    // cheaper than a persisted corrupted verdict.
    const fallback = parseAgentJson(out.stdout);
    if (fallback.json && !containsLikelyDecodedTexNewlines(fallback.json)) parsed = fallback;
  }
  if (!parsed.json) {
    return { raw: out.stdout, json: {}, verdict: null, parseError: parsed.parseError, failure: null, provenance: { requested_runner: requestedRunner, actual_runner: actualRunner, model: actualModel, fallback_kind: fallbackKind, quorum } };
  }
  const json = stripTemplateScaffolding(parsed.json) as Record<string, unknown>;
  const controlError = repairAndCheckVerdict(json, "referee stdout verdict");
  const validationError = args.validate ? args.validate(json) : null;
  const verdict = typeof json.verdict === "string" ? json.verdict.toUpperCase() : null;
  return { raw: out.stdout, json, verdict, parseError: controlError ?? validationError, failure: null, provenance: { requested_runner: requestedRunner, actual_runner: actualRunner, model: actualModel, fallback_kind: fallbackKind, quorum } };
}
