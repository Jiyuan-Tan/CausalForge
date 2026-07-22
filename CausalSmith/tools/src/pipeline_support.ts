import { appendFile, mkdir, readdir, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import {
  REUSE_LIST_BY_CLUSTER,
  CLUSTER_SUBSTRATE_ROOTS,
  formatStageLabel,
  type ClusterKey,
} from "./constants.js";
import {
  extractJsonObject,
  interventionSchema,
  reviewResultSchema,
  stageOutputSchema,
  substrateGateSchema,
  type Intervention,
  type ReviewResult,
  type SubstrateGate,
} from "./judgment.js";
import { appendReviewLog } from "./log.js";
import type { ReviewLogEntry } from "./log.js";
import {
  assumptionTablePath,
  crosswalkFullJsonPath,
  crosswalkFullMdPath,
  crosswalkJsonPath,
  crosswalkMdPath,
  formalizationDir,
  ensurePaperTmpDir,
  gapsJsonPath,
  leanTheoremDir,
  logsDir,
  mdPath,
  planPath,
  promptPath,
  citedDependenciesPath,
  PAPER_TMP_DIR,
  proposalOutputJsonPath,
  proposalReviewOutputJsonPath,
  proposalTexPath,
  sorriesPath,
  substrateDebtPath,
  templatePath,
  texPath,
} from "./paths.js";
import type { PipelineContext, Stage, StateJson } from "./types.js";
import { runClaude } from "./workers/claude.js";
import { runCodex } from "./shared/codex.js";
import { updateLedgerFile } from "./shared/ledger_update.js";
import { createLeanLspClient, type LeanLspClient } from "./workers/leanLsp.js";
export { getLastClaudeDiagnostic } from "./workers/claude.js";

export interface StageDeps {
  runCodex: typeof runCodex;
  runClaude: typeof runClaude;
  lean: LeanLspClient;
}

/** Central per-run agent-call transcript (chronological, ALL stages in one file):
 *  `doc/research/_agent_logs/<qid>_<spec>.log`. The cross-stage view used by the debug
 *  workflow (diff what a stage EMITTED against what the next stage RECEIVED). Every codex/claude
 *  dispatch (D-1…D0.5 and all F stages, since they all run through these deps) appends here, so the
 *  reasoning behind every stage is inspectable and an expensive call is never lost — the raw lands
 *  here before any caller parses it. */
function centralAgentLogPath(ctx: PipelineContext): string {
  return path.join(ctx.repoRoot, "doc/research/_agent_logs", `${ctx.qid}_${ctx.specialization}.log`);
}

/** Slugify a label into a safe, compact filename component (lowercase, `[^a-z0-9]`→`-`). */
function slugifyLabel(s: string, max: number): string {
  const slug = s.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "").slice(0, max);
  return slug || "misc";
}

/** Per-STAGE transcript file, co-located with the run under `<qid>/logs/stages/`:
 *  `<stageId>__<sub-stage>.log`. The `stageId` (e.g. `F3`, `D0.5`, from `formatStageLabel`) groups
 *  by pipeline stage; the sub-stage slug (first prompt line) separates the DISTINCT calls made under
 *  one coarse handler stage — e.g. the F2.5–F4 review loop's faithfulness reviewer vs. filler vs.
 *  intervention each get their own file, with successive rounds appended chronologically. This is
 *  the discoverable per-qid mirror of the central transcript (same entries, split by stage).
 *  Leading underscore matches the run-log convention (`_reviewer_calls.log`) so the `_*.log`
 *  .gitignore rule keeps these transient transcripts out of commits. */
function perStageLogPath(ctx: PipelineContext, stageId: string, promptHint: string): string {
  const name = `_${slugifyLabel(stageId, 12)}__${slugifyLabel(promptHint, 48)}.log`;
  return path.join(logsDir(ctx.repoRoot, ctx.qid), "stages", name);
}

async function logAgentCall(
  ctx: PipelineContext,
  stageId: string,
  agent: string,
  prompt: string,
  model: string,
  effort: string,
  ms: number,
  output: string,
): Promise<void> {
  // First non-empty prompt line is the stage/prompt header (e.g. "=== UNIFIED FAITHFULNESS REVIEWER ===").
  const stageHint = (prompt.split("\n").find((l) => l.trim().length > 0) ?? "").trim().slice(0, 110);
  // Log the FULL assembled input prompt (base prompt + sources + graph context) alongside the output,
  // so a wrong/empty base prompt or a mis-assembled source block is directly inspectable — not inferred
  // from the model's behaviour. (An empty base prompt is the failure that motivated this.)
  const entry =
    `\n===== ${agent} model=${model} effort=${effort} dur=${(ms / 1000).toFixed(0)}s :: ${stageHint} =====\n` +
    `----- INPUT (${prompt.length} chars) -----\n${prompt}\n` +
    `----- OUTPUT -----\n${output}\n`;
  // Same entry to BOTH sinks: the central chronological transcript (all stages, one file) and the
  // per-stage split under the run's `logs/stages/` (grouped + discoverable). Best-effort; never throws.
  const central = centralAgentLogPath(ctx);
  const perStage = perStageLogPath(ctx, stageId, stageHint);
  await mkdir(path.dirname(central), { recursive: true }).catch(() => {});
  await mkdir(path.dirname(perStage), { recursive: true }).catch(() => {});
  await Promise.all([
    appendFile(central, entry).catch(() => {}),
    appendFile(perStage, entry).catch(() => {}),
  ]);
}

export function defaultDeps(ctx: PipelineContext, currentStage?: Stage, state?: StateJson): StageDeps {
  // Stage label for the per-stage log filename. `liveStageHandler` builds a fresh StageDeps per
  // stage iteration and passes the stage it is running, so every call routes to that stage's file.
  let stageId = "misc";
  if (currentStage !== undefined) {
    try {
      stageId = formatStageLabel(currentStage);
    } catch {
      stageId = String(currentStage);
    }
  }
  // Every source-producing formalization agent is told where scratch belongs.
  // F2 itself stays at the package root because it is the source-emission
  // stage and legacy scaffold prompts still use root-relative production
  // paths. F2.5 onward additionally receives the paper-local cwd, so a
  // relative `Main.lean` cannot pollute the CausalSmith package root.
  const formalizationScratch = state && currentStage !== undefined && Number(currentStage) >= 2;
  const paperTmp =
    formalizationScratch
      ? ensurePaperTmpDir(ctx.repoRoot, state.lean_subdir)
      : undefined;
  // F2.5–F4 must stay in the paper-local scratch directory, but F5 is the
  // repository API-catalogue updater and is explicitly required to edit
  // doc/API.md. Running F5 from tmp makes Codex's workspace-write sandbox
  // reject that production path and leaves an otherwise clean run stuck at
  // CKPT 2.
  const usePaperTmpAsCwd =
    currentStage !== undefined && Number(currentStage) >= 2.5 && Number(currentStage) < 5;
  const scratchInstruction = paperTmp
    ? [
        "",
        "Scratch-work boundary:",
        `- Your cwd is this paper's disposable workspace: ${paperTmp}`,
        "- Put every intermediate Lean probe, check file, generated test, and temporary script here (including Main.lean).",
        `- Do not create scratch files at the CausalSmith package root (${ctx.repoRoot}).`,
        "- This tmp/ directory is excluded from the paper's build/review inventory. Write intended paper source only to the explicit production paths named in the task.",
      ].join("\n")
    : "";
  return {
    // Wrap both agents so EVERY stage's call is transcribed (raw output logged on return, before
    // any caller parses it). Logging never throws into the call path (best-effort append).
    runCodex: async (input) => {
      const t0 = Date.now();
      try {
        const out = await runCodex({
          ...input,
          prompt: input.prompt + scratchInstruction,
          cwd: usePaperTmpAsCwd ? paperTmp! : input.cwd,
          leanProjectPath: usePaperTmpAsCwd ? ctx.repoRoot : input.leanProjectPath,
        });
        await logAgentCall(ctx, stageId, "codex", input.prompt, input.model ?? "?", input.reasoningEffort ?? "?", Date.now() - t0, out.stdout);
        return out;
      } catch (err) {
        // "Not lost": a crashed/timed-out call still gets a log entry (with any
        // partial stdout the error carries) before the throw propagates.
        const partial = (err as { stdout?: string })?.stdout ?? "";
        await logAgentCall(ctx, stageId, "codex", input.prompt, input.model ?? "?", input.reasoningEffort ?? "?", Date.now() - t0, `[CALL THREW: ${err instanceof Error ? err.message : String(err)}]\n${partial}`);
        throw err;
      }
    },
    runClaude: async (input) => {
      const t0 = Date.now();
      try {
        const out = await runClaude({
          ...input,
          prompt: input.prompt + scratchInstruction,
          cwd: usePaperTmpAsCwd ? paperTmp! : input.cwd,
        });
        await logAgentCall(ctx, stageId, "claude", input.prompt, input.model, "-", Date.now() - t0, out);
        return out;
      } catch (err) {
        const partial = (err as { stdout?: string })?.stdout ?? "";
        await logAgentCall(ctx, stageId, "claude", input.prompt, input.model, "-", Date.now() - t0, `[CALL THREW: ${err instanceof Error ? err.message : String(err)}]\n${partial}`);
        throw err;
      }
    },
    lean: createLeanLspClient({ repoRoot: ctx.repoRoot }),
  };
}

export async function readPrompt(ctx: PipelineContext, name: string): Promise<string> {
  return readFile(promptPath(ctx.repoRoot, name), "utf8");
}

function escapeLatexUnderscores(value: string): string {
  return value.replace(/_/g, "\\_");
}

export async function ensureSkeleton(args: {
  ctx: PipelineContext;
  templateName: string;
  target: string;
}): Promise<{ created: boolean; templateFile: string }> {
  const templateFile = templatePath(args.ctx.repoRoot, args.templateName);
  if (existsSync(args.target)) return { created: false, templateFile };
  const raw = await readFile(templateFile, "utf8");
  const rendered = raw
    .split("__QID__")
    .join(escapeLatexUnderscores(args.ctx.qid))
    .split("__SPECIALIZATION__")
    .join(escapeLatexUnderscores(args.ctx.specialization));
  await mkdir(path.dirname(args.target), { recursive: true });
  await writeFile(args.target, rendered, "utf8");
  return { created: true, templateFile };
}

export async function readIfExists(file: string): Promise<string> {
  if (!existsSync(file)) return "";
  return readFile(file, "utf8");
}

/** Fail-loud read for a stage-REQUIRED artifact (framework/store.ts semantics: a
 *  missing required input is a fault, never an empty prompt section). Use
 *  readIfExists only for genuinely optional inputs. */
export async function readRequired(file: string, requiredBy: string): Promise<string> {
  if (!existsSync(file)) {
    throw new Error(`${requiredBy}: required input missing at ${file} — refusing to degrade the prompt/gate`);
  }
  return readFile(file, "utf8");
}

/**
 * Delete a rendered per-qid stdout-JSON output template after its stage has
 * successfully consumed the agent's output. These templates (the D-1.2 producer,
 * D-0.5 proposal-review, and F-phase 0.5 derivation-review output templates) are
 * write-once scratch: the pipeline renders one next to the proposal so the agent
 * has a stable named path to read its output schema from, but nothing downstream
 * reads them back — the real result lives in `state.json` / `*.tex` /
 * `*_reviews.jsonl`. They are re-rendered on every stage invocation, so deletion
 * is always safe. Callers invoke this ONLY on the success path; a failure path
 * deliberately leaves the file so the exact template the agent saw survives for
 * debugging. Best-effort: a missing file or unlink error is swallowed.
 */
export async function cleanupRenderedTemplate(targetPath: string): Promise<void> {
  try {
    await rm(targetPath, { force: true });
  } catch {
    // best-effort: leave the scratch file in place if removal fails.
  }
}

// Stage 0 skeleton section headers (mirrors templates/stage0_skeleton.tex).
export function artifactPaths(ctx: PipelineContext, state: StateJson) {
  return {
    tex: texPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    proposalTex: proposalTexPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    proposalOutputJson: proposalOutputJsonPath(
      ctx.repoRoot,
      ctx.qid,
      ctx.specialization,
    ),
    proposalReviewOutputJson: proposalReviewOutputJsonPath(
      ctx.repoRoot,
      ctx.qid,
      ctx.specialization,
    ),
    gapsJson: gapsJsonPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    md: mdPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    plan: planPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    formalizationDir: formalizationDir(ctx.repoRoot, ctx.qid),
    leanDir: leanTheoremDir(ctx.repoRoot, state.lean_subdir),
    sorries: sorriesPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    assumptionTable: assumptionTablePath(ctx.repoRoot, ctx.qid, ctx.specialization),
    crosswalkJson: crosswalkJsonPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    crosswalkMd: crosswalkMdPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    crosswalkFullJson: crosswalkFullJsonPath(ctx.repoRoot, ctx.qid, ctx.specialization),
    crosswalkFullMd: crosswalkFullMdPath(ctx.repoRoot, ctx.qid, ctx.specialization),
  };
}

export function correctionBlock(
  prior: ReviewResult | null,
  attempt: number,
  opts: { manifestContract?: boolean } = {},
): string {
  if (!prior || prior.status === "pass" || prior.status === "accept") return "";
  const rows = prior.perItemFindings
    .map((item) => `- ${item.label} | ${item.verdict} | ${item.one_line}`)
    .join("\n");
  const manifestReminder = opts.manifestContract
    ? [
        "",
        "MANIFEST INVARIANT: your JSON output MUST still enumerate every covered theorem in `theorems[]` (one entry per theorem_local_id present in the artifact body). Only patch the per-item issues above; do NOT drop entries from the manifest — omitted entries that still appear in the body will trigger a handler warning, and entries absent from both manifest and body are auto-marked `stuck`.",
      ].join("\n")
    : "";
  return [
    `=== CORRECTION (round ${attempt}, prior review classification: ${prior.classification}) ===`,
    `Previous attempt received status ${prior.status}. Address ONLY the items below. Do not regress on items that previously passed.`,
    "",
    "Per-item findings:",
    rows || "(none)",
    "",
    "Verbatim critique:",
    prior.verbatim_critique,
    manifestReminder,
    "=== END CORRECTION ===",
    "",
  ].join("\n");
}

// Body-scan helpers for the producer-side safety net: when a paper-scoped stage
// returns a JSON `theorems[]` manifest that omits an entry but the artifact body
// still covers it, repair the manifest instead of falsely marking the entry
// `stuck`. Used by Stage 0/1/2 handlers in pipeline_stages.ts.
export function bodyMentionsTheoremId(body: string, id: string): boolean {
  if (!id || !body) return false;
  const escaped = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return new RegExp(`\\b${escaped}\\b`, "i").test(body);
}

// Stage 2 convention (stage2_scaffold.txt:11): theorem decl is `<id>_thm` or
// `<id>_<suffix>`. Returns the recovered decl name if a matching decl exists.
export function findLeanDeclByLocalId(leanSource: string, id: string): string | null {
  if (!id || !leanSource) return null;
  const escaped = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const uncommented = stripLeanComments(leanSource);
  // why: strip comments so a commented-out `-- theorem t1_thm` is not matched; keep the match
  // unanchored so a real decl found anywhere in the (uncommented) body still repairs the manifest.
  const m = uncommented.match(
    new RegExp(`(?:theorem|lemma|def)\\s+(${escaped}(?:_\\w+)?)\\b`),
  );
  return m ? m[1] : null;
}

function stripLeanComments(source: string): string {
  let out = "";
  let blockDepth = 0;
  for (let i = 0; i < source.length; i++) {
    const ch = source[i];
    const next = source[i + 1];
    if (blockDepth > 0) {
      if (ch === "/" && next === "-") {
        blockDepth++;
        out += "  ";
        i++;
      } else if (ch === "-" && next === "/") {
        blockDepth--;
        out += "  ";
        i++;
      } else {
        out += ch === "\n" ? "\n" : " ";
      }
      continue;
    }
    if (ch === "-" && next === "-") {
      // why: commented-out declarations must not satisfy local-id recovery.
      while (i < source.length && source[i] !== "\n") {
        out += " ";
        i++;
      }
      if (i < source.length) out += "\n";
      continue;
    }
    if (ch === "/" && next === "-") {
      blockDepth = 1;
      out += "  ";
      i++;
      continue;
    }
    out += ch;
  }
  return out;
}

// Defense-in-depth: drop keys starting with "_" recursively. Review-output
// templates (templates/*_review_output_template.json) use `_emit_rules`,
// `_prototype`, `_doc`, `_accept_form`, `_revise_reject_form` as scaffolding
// the reviewer agent is told to strip. If it forgets, this prevents the
// scaffolding from tripping reviewResultSchema validation.
function stripReviewTemplateKeys(value: unknown): unknown {
  if (Array.isArray(value)) return value.map(stripReviewTemplateKeys);
  if (value && typeof value === "object") {
    const out: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(value as Record<string, unknown>)) {
      if (k.startsWith("_")) continue;
      out[k] = stripReviewTemplateKeys(v);
    }
    return out;
  }
  return value;
}

export function parseReview(stdout: string): ReviewResult {
  try {
    return reviewResultSchema.parse(stripReviewTemplateKeys(extractJsonObject(stdout)));
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    console.warn(
      `[causalsmith] parseReview fallback: ${reason}. stdout-tail=${stdout.trim().slice(-300)}`,
    );
    // Synthesize a reject so the boundary routes to runIntervention instead of
    // crashing. The raw model output is preserved in verbatim_critique so the
    // appendReview log keeps the reviewer's actual text for triage.
    return {
      status: "reject",
      classification: "parse_failure",
      perItemFindings: [],
      verbatim_critique: stdout.trim().slice(0, 4000),
    } as ReviewResult;
  }
}

export function parseStageOutput(stdout: string) {
  try {
    return stageOutputSchema.parse(extractJsonObject(stdout));
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    console.warn(
      `[causalsmith] parseStageOutput fallback: ${reason}. stdout-tail=${stdout.trim().slice(-300)}`,
    );
    // why: malformed worker stdout is a hard parse result; never fabricate completion.
    return { status: "parse_failed", message: stdout.trim().slice(0, 500), artifacts: [] };
  }
}

export function parseIntervention(stdout: string): Intervention {
  return interventionSchema.parse(extractJsonObject(stdout));
}

/**
 * Deterministic intervention synthesis used when the LLM judge returns
 * un-parseable output even after retries (Bug B follow-up). Reads the
 * latest review verdict and picks a sensible (route, action_kind) pair so
 * the pipeline can checkpoint cleanly instead of dropping a content-free
 * PARSE_FAILED message. The synthesized intervention is conservative:
 * everything routes to `user` (we never auto-loop on a missing judge),
 * but the action_kind reflects what the review actually says so the user
 * sees a meaningful checkpoint reason.
 */
export function synthesizeInterventionFromReviews(
  reviews: ReviewResult[],
  boundary: string,
): { route: Intervention["route"]; reason: string; action_kind: Intervention["action_kind"]; proposed_action?: string } {
  const last = reviews[reviews.length - 1];
  if (!last) {
    return {
      route: "user",
      reason: `No reviews available at boundary ${boundary}; cannot synthesize a route.`,
      action_kind: "user_required",
    };
  }
  if (last.status === "pass" || last.status === "accept") {
    return {
      route: "user",
      reason: `Latest review at ${boundary} is ${last.status}; checkpoint pending user decision because the LLM judge could not be reached.`,
      action_kind: "user_required",
    };
  }
  // status === "reject" or "revise"
  // Deterministic escalation: when the Stage 0.5 reviewer marked a finding as
  // non-repairable-by-re-solve (needs a proposal restructure / new math), route
  // to the proposer (stage_neg1) directly — no LLM judge needed. applyInterventionRoute
  // performs the D-1.2 rewind in propose-mode, or sets stage_neg1_fallback + checkpoints.
  const lastEsc = last as {
    escalate_to_proposer?: boolean;
    escalate_reason?: string;
    verbatim_critique?: string;
    perItemFindings?: Array<{ one_line?: string }>;
  };
  if (lastEsc.escalate_to_proposer) {
    // Build a usable redraft brief even when the reviewer omitted escalate_reason
    // (we deliberately do NOT hard-fail on the omission — see the proposal_drift
    // enum lesson): fall back to the critique, then the findings, then generic.
    const reason =
      lastEsc.escalate_reason?.trim() ||
      lastEsc.verbatim_critique?.trim().slice(0, 300) ||
      (Array.isArray(lastEsc.perItemFindings)
        ? lastEsc.perItemFindings.map((f) => f.one_line).filter(Boolean).join("; ").slice(0, 300)
        : "") ||
      "reclassify/redraft the proposal";
    return {
      route: "stage_neg1",
      reason: `Stage 0.5 flagged a finding not fixable by a D0 re-solve: ${reason}. Routed stage_neg1 (D-1.2 redraft); falls back to a user checkpoint if not in propose-mode.`,
      action_kind: "redraft_proposal",
      proposed_action: reason,
    };
  }
  const cls = (last.classification ?? "mixed") as string;
  const findings = (last as { perItemFindings?: Array<{ verdict?: string; one_line?: string }> })
    .perItemFindings ?? [];
  const tierFlag = findings.find((f) =>
    /below.*flagship|tier.*letter|tier.*subfield|tier.*field|orchestrator-enforced/i.test(
      f.one_line ?? "",
    ),
  );
  const noveltyHits = findings.filter((f) => f.verdict === "novelty").length;
  const correctnessHits = findings.filter((f) => f.verdict === "correctness").length;
  if (tierFlag || noveltyHits > 0) {
    return {
      route: "user",
      reason: `Latest review at ${boundary} is ${last.status} with ${noveltyHits} novelty finding(s) (${tierFlag?.one_line ?? cls}); LLM judge unreachable. Synthesized route=user pending human triage — the deterministic synth does not pre-judge whether a local revise, re-derive, lower-tier accept, or pivot is the right action; surfacing the raw review findings to the user is the safe default.`,
      action_kind: "user_required",
    };
  }
  if (correctnessHits > 0 && noveltyHits === 0) {
    return {
      route: "user",
      reason: `Latest review at ${boundary} is ${last.status} on correctness only (${correctnessHits} finding(s)); LLM judge unreachable so cannot autonomously decide between re-derive and theorem-split. Synthesized route=user.`,
      action_kind: "user_required",
    };
  }
  return {
    route: "user",
    reason: `Latest review at ${boundary} is ${last.status}/${cls}; LLM judge unreachable so synthesized route=user pending human triage.`,
    action_kind: "user_required",
  };
}

export async function appendReview(
  ctx: PipelineContext,
  stage: string,
  attempt: number,
  review: ReviewResult,
): Promise<void> {
  const acceptTier =
    review.status === "accept" && "tier_at_derivation" in review ? review.tier_at_derivation : undefined;
  const acceptTierMissing = review.status === "accept" && acceptTier === undefined;
  const kernelStatus =
    review.status === "accept" && "kernel_status" in review ? review.kernel_status : undefined;
  const kernelSuffix =
    kernelStatus === "refuted_with_positive_result" ? " [refuted-with-positive-result]" : "";
  const entry: Omit<Extract<ReviewLogEntry, { kind: "review" }>, "timestamp"> = {
    kind: "review",
    stage,
    attempt,
    status: review.status,
    classification:
      review.status === "reject" || review.status === "revise" ? review.classification : undefined,
    report_summary:
      review.status === "pass"
        ? review.notes
        : review.status === "accept"
          ? `tier=${acceptTierMissing ? "unset [AUDIT-CORE missing tier_at_derivation]" : acceptTier}${kernelSuffix} | ${review.notes ?? ""}` // AUDIT-CORE
          : review.perItemFindings.map((item) => `${item.label}:${item.verdict}`).join(", "),
    review,
  };
  await appendReviewLog(ctx, entry);
  await persistReviewBoundaryJson(ctx, stage, attempt, review);
}

/**
 * Persist per-attempt review JSON to `<qid>_<spec>_reviews/<boundary>_attempt<N>.json`.
 * Mirrors `persistReviewJson` for Stage -0.5 so derivation/NL/Lean review
 * history is greppable as standalone files instead of buried inside
 * reviews.jsonl. Best-effort: errors are logged but never block the pipeline.
 */
async function persistReviewBoundaryJson(
  ctx: PipelineContext,
  boundary: string,
  attempt: number,
  review: ReviewResult,
): Promise<void> {
  try {
    const dir = path.join(
      formalizationDir(ctx.repoRoot, ctx.qid),
      `${ctx.qid}_${ctx.specialization}_reviews`,
    );
    await mkdir(dir, { recursive: true });
    // Sanitize boundary for filesystem (e.g. "stage_0.5_to_0").
    const safe = boundary.replace(/[^A-Za-z0-9._-]/g, "_");
    const file = path.join(dir, `${safe}_attempt${attempt}.json`);
    await writeFile(file, `${JSON.stringify(review, null, 2)}\n`, "utf8");
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    console.warn(
      `[causalsmith] persistReviewBoundaryJson failed for ${boundary} attempt ${attempt}: ${reason}`,
    );
  }
}

export async function writeAssumptionTableIfPresent(
  ctx: PipelineContext,
  output: unknown,
): Promise<string | undefined> {
  if (typeof output === "object" && output !== null && "assumption_table_markdown" in output) {
    const table = (output as { assumption_table_markdown?: unknown }).assumption_table_markdown;
    if (typeof table === "string" && table.trim()) {
      const file = assumptionTablePath(ctx.repoRoot, ctx.qid, ctx.specialization);
      await mkdir(path.dirname(file), { recursive: true });
      await writeFile(file, `${table.trim()}\n`, "utf8");
      return file;
    }
  }
  const parsed = stageOutputSchema.safeParse(output);
  const table = parsed.success ? parsed.data.assumption_table_markdown : undefined;
  if (!table?.trim()) return undefined;
  const file = assumptionTablePath(ctx.repoRoot, ctx.qid, ctx.specialization);
  await mkdir(path.dirname(file), { recursive: true });
  await writeFile(file, `${table.trim()}\n`, "utf8");
  return file;
}

const SUBSTRATE_DEBT_HEADER = `# Substrate debt ledger

Assumed-but-should-be-proven named hypotheses surfaced by Stage 4 (equivalence
review): each is a TRUE standard mathematical fact a banked theorem currently
ASSUMES because the discharging Mathlib/Causalean substrate does not exist yet
(the \`_of_<gate>\` convention). These are honest, trackable debt — NOT
laundering (a gate never weakens a claim or makes it vacuous). This ledger is
the build queue for missing infrastructure.

Each row is appended automatically; edit the **Status** column by hand
(\`open\` → \`resolved (<qid>/<spec>, <date>)\`) once the gate is discharged.

| Gate | Run (qid/spec) | Assumed statement | Classical fact | Missing infra | Status |
|------|----------------|-------------------|----------------|---------------|--------|
`;

/** Escape a cell for a single-line Markdown table (no pipes / newlines). */
function mdCell(s: string): string {
  return s.replace(/\r?\n/g, " ").replace(/\|/g, "\\|").trim();
}

/** Collect + validate the `substrate_gates` a Stage-4 review reported. */
export function collectSubstrateGates(review: ReviewResult): SubstrateGate[] {
  const raw = (review as { substrate_gates?: unknown }).substrate_gates;
  if (!Array.isArray(raw)) return [];
  const gates: SubstrateGate[] = [];
  for (const g of raw) {
    const parsed = substrateGateSchema.safeParse(g);
    if (parsed.success) gates.push(parsed.data);
  }
  return gates;
}

const CITED_DEPENDENCIES_HEADER = `# Cited dependencies registry

Borrowed results a banked theorem ASSUMES but does NOT discharge at run time
(\`gate_class:"cited"\`): each is formalized as a Lean \`def … : Prop\`, taken as a
hypothesis (like citing a theorem in a paper), and MATCHED against an external
source by the F4 convergence reviewer, which also writes these rows. Unlike
SUBSTRATE_DEBT.md these are NOT owed a build — they may graduate to a real lemma
in a future run.

A \`cited-mismatch\` or \`cited-underspecified\` verdict BLOCKS banking: F4 persists
it to \`state.cited_checks\` and escalates, and \`bankEntry\` re-checks that field so
the block survives outside the review loop (a row is written here only once the
match gate PASSES, so this registry never lists a failing def).

| Cited def | Run (qid/spec) | Assumed statement | Source | Locator | Check status |
|-----------|----------------|-------------------|--------|---------|--------------|
`;

/** A row written to the cited-dependencies registry (subset of {@link SubstrateGate}). */
type CitedRowInput = Pick<
  SubstrateGate,
  "name" | "statement" | "classical_fact" | "source" | "check_status"
>;

/** "Source" cell: the named classical fact + its cite id / url, when present. */
function citedSourceCell(g: CitedRowInput): string {
  const parts = [g.classical_fact, g.source?.cite_id, g.source?.url].filter(Boolean) as string[];
  return parts.join(" · ");
}

/** Replace the row whose line starts with `marker`, else append `row` (ends with \\n). */
function upsertRow(body: string, marker: string, row: string): string {
  const lines = body.split("\n");
  const idx = lines.findIndex((l) => l.startsWith(marker));
  if (idx >= 0) {
    lines[idx] = row.replace(/\n$/, "");
    return lines.join("\n");
  }
  return body + row;
}

/**
 * Append/update cited-dependency rows in the global {@link citedDependenciesPath}
 * registry. Upserts on (cited def name, run) so an F1-time `pending` row is later
 * overwritten with the F2.5 match verdict. Returns the path when anything changed.
 */
async function writeCitedRows(
  ctx: Pick<PipelineContext, "repoRoot">,
  tag: string,
  gates: CitedRowInput[],
): Promise<string | undefined> {
  if (gates.length === 0) return undefined;
  const file = citedDependenciesPath(ctx.repoRoot);
  // Locked + atomic: this ledger is global, so an unsynchronized read-modify-write lets a
  // concurrent qid's rows be erased by whichever run writes last.
  return updateLedgerFile(file, CITED_DEPENDENCIES_HEADER, (before) => {
    let body = before;
    for (const g of gates) {
      const marker = `| \`${mdCell(g.name)}\` | ${tag} |`;
      const row =
        `| \`${mdCell(g.name)}\` | ${tag} | ${mdCell(g.statement)} | ` +
        `${mdCell(citedSourceCell(g))} | ${mdCell(g.source?.locator ?? "")} | ` +
        `${mdCell(g.check_status ?? "pending")} |\n`;
      body = upsertRow(body, marker, row);
    }
    return body;
  });
}

/**
 * Append substrate gates to the global {@link substrateDebtPath} ledger (`gated`) or the
 * cited-dependencies registry (`cited`), deduped by gate name and skipping rows already present for
 * this `qid/spec` so re-runs do not duplicate. Returns the path when a row was written.
 *
 * Callers hold the convergence reviewer's already-parsed `substrateGates`; use
 * {@link collectSubstrateGates} first if you only have a raw `ReviewResult`.
 *
 * Writing a row is DISCLOSURE, not registration: a `gated` row is an entry in the build queue that
 * the ORCHESTRATOR must still register with `bin/gate.ts` (the only sanctioned writer of plan/graph
 * gate keys). `bankEntry`'s `auditSubstrateGates` check is what refuses to bank `accepted` while a
 * disclosed gate is still unregistered.
 */
export async function recordSubstrateGateList(
  ctx: Pick<PipelineContext, "repoRoot" | "qid" | "specialization">,
  gates: SubstrateGate[],
): Promise<string | undefined> {
  const byName = new Map<string, SubstrateGate>();
  for (const gate of gates) {
    if (!byName.has(gate.name)) byName.set(gate.name, gate);
  }
  if (byName.size === 0) return undefined;
  const tag = `${ctx.qid}/${ctx.specialization}`;
  // Route by discharge fate: "cited" → cited-dependencies registry; everything
  // else (incl. absent gate_class, back-compat) → substrate-debt build queue.
  const gated: SubstrateGate[] = [];
  const cited: SubstrateGate[] = [];
  for (const gate of byName.values()) (gate.gate_class === "cited" ? cited : gated).push(gate);

  let wrote: string | undefined;
  if (gated.length > 0) {
    // Locked + atomic — see writeCitedRows.
    wrote = await updateLedgerFile(substrateDebtPath(ctx.repoRoot), SUBSTRATE_DEBT_HEADER, (existing) => {
      let body = existing;
      for (const gate of gated) {
        // Dedup on (gate name, run): one row per gate per run.
        const marker = `| \`${mdCell(gate.name)}\` | ${tag} |`;
        if (body.includes(marker)) continue;
        body +=
          `| \`${mdCell(gate.name)}\` | ${tag} | ${mdCell(gate.statement)} | ` +
          `${mdCell(gate.classical_fact)} | ${mdCell(gate.missing_infra)} | open |\n`;
      }
      return body;
    });
  }
  const citedFile = await writeCitedRows(ctx, tag, cited);
  return wrote ?? citedFile;
}

export interface GateNodeDebt {
  name: string;
  statement: string;
  classical_fact: string;
  missing_infra: string;
  /** Discharge fate (absent ⇒ "gated"). "cited" → cited-dependencies registry. */
  gate_class?: "gated" | "cited";
  /** For cited nodes: the citation matched against (locator etc.). */
  source?: { cite_id: string; locator: string; url?: string };
}

/**
 * Append F1-authored `gate:true` plan nodes to the right ledger: `gated` nodes to
 * the global substrate-debt build queue, `cited` nodes to the cited-dependencies
 * registry (status `pending` until F2.5 stamps a match verdict). Dedupe matches
 * {@link recordSubstrateGates}: one row per gate name per run.
 */
export async function recordGateNodes(
  ctx: PipelineContext,
  gates: GateNodeDebt[],
): Promise<string | undefined> {
  if (gates.length === 0) return undefined;
  const tag = `${ctx.qid}/${ctx.specialization}`;
  const gated = gates.filter((g) => g.gate_class !== "cited");
  const cited = gates.filter((g) => g.gate_class === "cited");

  let wrote: string | undefined;
  if (gated.length > 0) {
    // Locked + atomic (updateLedgerFile), same as recordSubstrateGateList: this ledger is
    // GLOBAL, so a raw read-modify-write here raced a concurrent run's F4 gate write and the
    // last writer silently erased the other's rows.
    wrote = await updateLedgerFile(substrateDebtPath(ctx.repoRoot), SUBSTRATE_DEBT_HEADER, (existing) => {
      let body = existing;
      for (const gate of gated) {
        const marker = `| \`${mdCell(gate.name)}\` | ${tag} |`;
        if (body.includes(marker)) continue;
        body +=
          `| \`${mdCell(gate.name)}\` | ${tag} | ${mdCell(gate.statement)} | ` +
          `${mdCell(gate.classical_fact)} | ${mdCell(gate.missing_infra)} | open |\n`;
      }
      return body;
    });
  }
  const citedFile = await writeCitedRows(ctx, tag, cited);
  return wrote ?? citedFile;
}

export async function listLeanFiles(dir: string): Promise<string[]> {
  const out: string[] = [];
  async function walk(current: string) {
    const entries = await readdir(current, { withFileTypes: true }).catch(() => []);
    for (const entry of entries) {
      const full = path.join(current, entry.name);
      // The paper's disposable agent workspace (`<leanDir>/tmp`) is NOT part of the
      // formalization: scratch probes there must never feed the bank-soundness scan,
      // the @node coverage/duplicate gates, or the F2 revise inventory.
      if (entry.isDirectory() && entry.name !== PAPER_TMP_DIR) await walk(full);
      if (entry.isFile() && entry.name.endsWith(".lean")) out.push(full);
    }
  }
  await walk(dir);
  return out;
}

/**
 * Cluster derived from `state.lean_subdir` (`CausalSmith/{Panel,ExactID,PartialID,Stat}/...`).
 * Returns null if the subdir is not under one of the canonical clusters
 * — caller then injects the union of all reuse lists.
 */
export function clusterFromLeanSubdir(leanSubdir: string): ClusterKey | null {
  const parts = leanSubdir.split(/[\\/]/).filter(Boolean);
  // Expected shape: ["CausalSmith", "<Cluster>", "<QName>"...]
  const segment = parts[1]?.toLowerCase();
  if (segment === "panel") return "panel";
  if (segment === "exactid") return "exactid";
  if (segment === "partialid") return "partialid";
  if (segment === "stat") return "stat";
  if (segment === "experimentation") return "experimentation";
  if (segment === "scm") return "scm";
  return null;
}

function reuseListBlock(cluster: ClusterKey | null): string {
  if (cluster) {
    const list = REUSE_LIST_BY_CLUSTER[cluster];
    return `Reuse list (${cluster}): ${list.join(", ")}`;
  }
  // Unknown cluster: emit all cluster-labelled reuse lists so the model can pick.
  return (
    "Reuse list (cluster unknown — pick by lean_subdir):\n" +
    (Object.keys(REUSE_LIST_BY_CLUSTER) as ClusterKey[])
      .map((c) => `  ${c}: ${REUSE_LIST_BY_CLUSTER[c].join(", ")}`)
      .join("\n")
  );
}

// The working directory for every worker is the CausalSmith package root; the
// Causalean source is a SIBLING package at `../Causalean/…`. So `Causalean/…` substrate
// paths below are NOT under cwd — a `Glob`/`ls` of `Causalean/Stat/…` returns empty
// (wrong base) and must never be read as proof of absence. `lean_local_search` /
// `lean_leansearch` are LSP-indexed and cwd-independent — they see Causalean through
// the dependency — so use them to confirm presence/absence; for raw file reads use
// `../Causalean/…`.
const SUBSTRATE_PATH_BASE_NOTE =
  "Path base: cwd is the CausalSmith package root; Causalean is a sibling at `../Causalean/…`. " +
  "An empty `Causalean/…` Glob/ls means WRONG BASE, not absence — confirm via `lean_local_search`/`lean_leansearch` (cwd-independent) or re-check under `../Causalean/…`.";

// Shared definition of a "bookkeeping premise" (a.k.a. regularity side-condition).
// Referenced verbatim by F1, F2, the F1.5/F2.5 gates, the Stage-3 failure
// classifier, and the local-patch dispatch so the bookkeeping-vs-content line is
// drawn ONCE and never drifts. The whole point: a regularity side-condition is
// honest scope, NOT content — so adding one must NOT be treated as illegitimate
// assumption-strengthening — while a content assumption dressed as regularity is
// still forbidden (that is the assume-the-conclusion laundering the gate exists to
// stop). Conservative by construction.
export const BOOKKEEPING_PREMISE_NOTE = [
  "BOOKKEEPING PREMISE (regularity side-condition) — definition and policy.",
  "",
  "A hypothesis is BOOKKEEPING iff it is a measurability / integrability /",
  "finiteness / summability / a.e.-definedness / σ-finiteness side-condition whose",
  "ONLY role is to make an object well-defined or to let a Mathlib lemma fire",
  "(`integral_add`, `integral_sub`, `MeasureTheory.integrable_*`, `Measurable.*`,",
  "etc.). It carries no quantitative content: it states nothing about a rate, a",
  "bound, a separation, an identity, or the value of the estimand.",
  "",
  "Bookkeeping premises are LEGITIMATE to add to a lemma OR a theorem signature —",
  "they are honest scope, not assumption-strengthening. Do NOT flag/reject them as",
  "stronger-in-Lean. Two tiers:",
  "  • FREE bookkeeping — follows from hypotheses already present (e.g. a bounded",
  "    measurable function on a probability/finite measure is integrable). PREFER",
  "    TO DERIVE it inline rather than assume it; assuming a derivable side-condition",
  "    is wasteful but never wrong.",
  "  • GENUINE-SCOPE bookkeeping — not derivable from current hypotheses (e.g. an",
  "    unbounded integrand whose integrability is a real restriction). Admissible as",
  "    an added premise.",
  "",
  "NOT bookkeeping (still forbidden as a smuggled premise) — a hypothesis that:",
  "  (a) substitutes for a quantitative step the proof is supposed to perform, or",
  "  (b) encodes the conclusion, a rate, a bound, or a separation, or",
  "  (c) could make the statement VACUOUS (a premise no law in the class satisfies).",
  "",
  "WEAK-OVERLAP CARVE-OUT — integrability/finiteness of an UNBOUNDED inverse-weight",
  "or estimator score under a weak-overlap / tail assumption is NOT free bookkeeping:",
  "it is tied to (and should be DERIVED from) the tail/overlap assumption (PolyTail,",
  "etc.), and for a CONVERSE the explicitly-constructed laws must be CHECKED to",
  "satisfy it — never blanket-assumed, or the converse risks vacuity.",
  "",
  "PREMISE-THREADING (a helper inheriting a premise its caller already has) — adding a",
  "hypothesis to a NON-T-BLOCK helper's signature is a LOCAL, T-block-preserving fix",
  "(handle in place; never a rewind/escalation) EVEN IF the hypothesis is",
  "content-bearing (a rate / tail / overlap / separation / identification condition),",
  "PROVIDED the consuming declaration (the T-block or decl that calls the helper)",
  "ALREADY carries that hypothesis. You are only PROPAGATING an existing assumption",
  "down to the helper, not strengthening the theorem — the T-block's assumption set is",
  "UNCHANGED. Thread it into the helper signature and pass it at every call site. This",
  "counts as content-strengthening (forbidden / structural) ONLY when the premise must",
  "be added to a T-BLOCK itself, or when NO caller in scope already supplies it.",
  "",
  "REFLECT-BACK RULE — whenever a bookkeeping premise is added at the Lean level, it",
  "MUST also be written into the NL note (the .md assumption table / P-entry) as an",
  "explicit regularity assumption, so the Lean signature and the note stay",
  "consistent and the drift-watch does not re-flag it as extra-in-Lean.",
].join("\n");

/** Wrap {@link BOOKKEEPING_PREMISE_NOTE} as a delimited prompt block. Injected by
 *  the F1, F2, F1.5, F2.5, Stage-3 classifier, and local-patch builders so all of
 *  them share one definition of the bookkeeping-vs-content line. */
export function bookkeepingPolicyBlock(): string {
  return [
    "=== BOOKKEEPING PREMISE POLICY (shared — applies to every hypothesis you add or judge) ===",
    BOOKKEEPING_PREMISE_NOTE,
    "=== END BOOKKEEPING PREMISE POLICY ===",
  ].join("\n");
}

function substrateRootBlock(cluster: ClusterKey | null): string {
  if (cluster) {
    return `Cluster substrate root: ${CLUSTER_SUBSTRATE_ROOTS[cluster].join(", ")}\n${SUBSTRATE_PATH_BASE_NOTE}`;
  }
  return (
    "Cluster substrate root (cluster unknown):\n" +
    (Object.keys(CLUSTER_SUBSTRATE_ROOTS) as ClusterKey[])
      .map((c) => `  ${c}: ${CLUSTER_SUBSTRATE_ROOTS[c].join(", ")}`)
      .join("\n") +
    `\n${SUBSTRATE_PATH_BASE_NOTE}`
  );
}

/**
 * Paper-scoped theorem manifest. The stage0_common preamble tells the solver
 * that state.theorems[] is "rendered in the brief" — this is the block that
 * actually renders it (empty string on single-theorem runs).
 */
function paperManifestBlock(state: StateJson): string {
  if (!state.theorems || state.theorems.length === 0) return "";
  const rows = state.theorems.map(
    (t) =>
      `- ${t.theorem_local_id} [${t.status}]: ${t.statement.replace(/\s+/g, " ").slice(0, 400)}`,
  );
  return [
    "=== PAPER-SCOPED THEOREM MANIFEST (state.theorems) ===",
    "This run is a paper-scoped batch: the §8 solve targets must cover every",
    "non-failed theorem below (conjecture labels match theorem_local_id).",
    ...rows,
    "=== END PAPER-SCOPED THEOREM MANIFEST ===",
  ].join("\n");
}

export function baseBrief(ctx: PipelineContext, state: StateJson): string {
  const paths = artifactPaths(ctx, state);
  const cluster = clusterFromLeanSubdir(state.lean_subdir);
  return [
    `Repository: ${ctx.repoRoot}`,
    `QID: ${ctx.qid}`,
    `Specialization: ${ctx.specialization}`,
    `Cluster: ${cluster ?? "unknown"}`,
    `Lean target subdirectory: ${state.lean_subdir}`,
    substrateRootBlock(cluster),
    "Substrate-survey rule: BEFORE drafting or scaffolding, audit the cluster substrate root(s) above with `lean_local_search` / `lean_leansearch` for the primitives you need. Default: reuse existing Causalean structures (e.g. `POManskiIVSystem`, `Backdoor`, etc.) when they fit the artifact's abstraction level. Exception: if the Causalean analogue is at a different abstraction (e.g. Causalean has the measure-theoretic version but the artifact is purely algebraic over generic types), it is FINE to scaffold over Mathlib only — record this in the file plan as `bypass-justified` with a one-line reason per surveyed module. Stage 2.5 reads that record and only flags un-justified bypass.",
    `TeX artifact: ${paths.tex}`,
    `NL artifact: ${paths.md}`,
    `Lean artifact directory: ${paths.leanDir}`,
    `Assumption table artifact: ${paths.assumptionTable}`,
    paperManifestBlock(state),
    reuseListBlock(cluster),
    `Design decisions: ${JSON.stringify(state.design_decisions, null, 2)}`,
    `Added assumptions: ${JSON.stringify(state.added_assumptions, null, 2)}`,
  ].join("\n");
}

/**
 * A LEAN brief for DISCOVERY stages (D-1, D0). Discovery is mathematics, not
 * formalization — so this carries NO Lean/Causalean substrate context (no
 * substrate-survey rule, no reuse lists, no Lean artifact paths). The model is
 * free to reason about the math; substrate concerns enter only at the F-stages.
 */
export function discoveryBrief(ctx: PipelineContext, state: StateJson): string {
  const cluster = clusterFromLeanSubdir(state.lean_subdir);
  const topic = state.proposed_from?.topic;
  return [
    `Repository: ${ctx.repoRoot}`,
    `QID: ${ctx.qid}`,
    `Specialization: ${ctx.specialization}`,
    `Cluster: ${cluster ?? "unknown"}`,
    topic ? `Topic: ${topic}` : "",
    `Design decisions: ${JSON.stringify(state.design_decisions, null, 2)}`,
    `Added assumptions: ${JSON.stringify(state.added_assumptions, null, 2)}`,
  ]
    .filter((l) => l.length > 0)
    .join("\n");
}
