// Stage 0.5 (core review) — the math+decision panel over the typed core.
//
// D0.5.1 (math) and D0.5.2 (decision) review the CORE node by node and emit a
// node-addressable verdict; the cold general referee runs separately after this
// panel passes. The structural gate has already verified well-formedness, so the
// panel focuses on the math/decision rubric. Verdicts are combined worst-of, and
// a finding citing a nonexistent node is rejected mechanically (D0_CORE_REDESIGN.md §6).
// Prompts are derived from stage0_5_{math_review,review}.txt + a core-review adapter (§11).
import { existsSync } from "node:fs";
import { mkdir, rm } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../../constants.js";
import { runReferee } from "../framework/referee.js";
import { reviewsDir } from "../../paths.js";
import { baseBrief, readPrompt, type StageDeps } from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { coreJsonPath } from "./d0_core.js";
import { TARGET_FLOOR_LABEL } from "./d0_5_general.js";
import { type Core } from "../core/schema.js";
import { loadPaperView, logPaperView } from "../core/paper_view.js";
import {
  type D0CitedCheck,
  ReviewVerdictSchema,
  combineVerdicts,
  unresolvedFindingNodes,
  type ReviewVerdict,
  REVIEW_VERDICTS,
} from "../core/review.js";
import {
  resolveCitedTarget,
  type CitedMatchTarget,
  type ResolvableCitation,
} from "../../formalization/citation_fetch.js";

// The core panel is the NODE-ADDRESSABLE math/decision review (concise
// {referee,verdict,findings} via stage0_5_core_adapter.txt). The holistic
// "general" judgment — proved-vs-claimed + the publishability TIER — is a
// SEPARATE cold referee (stage0_5_general.ts::runGeneralReview, run after this
// panel passes in runStage0_5Typed), so it is intentionally NOT a panel role:
// that avoids reusing the cold-referee prompt here and then stripping its tier.
const REFEREES: { role: "math" | "general" | "decision"; prompt: string }[] = [
  { role: "math", prompt: "stage0_5_math_review.txt" },
  { role: "decision", prompt: "stage0_5_review.txt" },
];

function reviewVerdictPath(ctx: PipelineContext, role: string): string {
  // Panel verdicts live in the run's reviews/ subfolder; the `decision` referee's
  // file is named `review_rubric.json` (it applies the decision/novelty rubric).
  // Written then read back within the same stage invocation, so no cross-run legacy
  // resolution is needed (the dir is mkdir'd by the caller before writing).
  const fileRole = role === "decision" ? "rubric" : role;
  return path.join(reviewsDir(ctx.repoRoot, ctx.qid, ctx.specialization), `review_${fileRole}.json`);
}

interface D0CitedTarget {
  nodeId: string;
  statement: string;
  citationLabel: string;
  source: ResolvableCitation;
  target: CitedMatchTarget;
}

async function resolveD0CitedTargets(
  core: Core,
  resolver: (source: ResolvableCitation) => Promise<CitedMatchTarget>,
): Promise<D0CitedTarget[]> {
  const bib = new Map(core.bibliography.map((b) => [b.key, b.citation ?? b.key] as const));
  return Promise.all(core.statements.filter((s) => s.status === "cited").map(async (s) => {
    const source: ResolvableCitation = {
      id: s.source!.cite,
      locator: s.source!.locator,
      // Migration fallback: old D0 instructions put the exact transcription in
      // proof_tex. Prefer the new source field, but do not discard an existing
      // lawful attestation merely because the core predates this schema field.
      verbatim_statement: s.source!.verbatim_statement ?? s.proof_tex?.trim() ?? undefined,
      arxiv: s.source!.arxiv,
      doi: s.source!.doi,
      url: s.source!.url,
    };
    return {
      nodeId: s.id,
      statement: s.statement,
      citationLabel: bib.get(s.source!.cite) ?? s.source!.cite,
      source,
      target: await resolver(source),
    };
  }));
}

function citedReviewBlock(role: "math" | "general" | "decision", cited: D0CitedTarget[]): string {
  if (cited.length === 0) return "";
  if (role !== "math") {
    return [
      "=== CITED-NODE ROLE BOUNDARY ===",
      "The math referee owns exact source matching. At your decision role, judge only whether each",
      "borrowed fact is legitimate external substrate (not the note's novel kernel relabelled as cited,",
      "and not impermissibly headline-load-bearing). Emit NO cited_checks rows.",
    ].join("\n");
  }
  return [
    "=== CITED SOURCE-OF-RECORD AUDIT — MATH REFEREE OWNS THIS ===",
    "Emit EXACTLY one cited_checks row for every target below. Compare quantifiers, hypotheses,",
    "model/class restrictions, constants, and conclusion. Agent recollection is never verification.",
    "Statuses: fetched source match => cited-verified; supplied verbatim match => cited-verified-attested;",
    "wrong claim => cited-mismatch; missing distinguishing hypothesis/class => cited-underspecified;",
    "unavailable source => cited-source-unverifiable (external-verification checkpoint, NOT math failure).",
    ...cited.flatMap((c) => [
      "",
      `### ${c.nodeId}`,
      `D-core claim: ${c.statement}`,
      `Source: ${c.citationLabel} @ ${c.source.locator}`,
      c.target.mode === "unverifiable"
        ? `SOURCE UNAVAILABLE: ${c.target.detail}. You MUST emit cited-source-unverifiable; do not verify from memory.`
        : `SOURCE OF RECORD (${c.target.mode}, ${c.target.detail}):\n${c.target.text.slice(0, 6000)}`,
    ]),
  ].join("\n");
}

async function reviewWithReferee(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  core: Core;
  paperTex: string;
  citedTargets: D0CitedTarget[];
  referee: { role: "math" | "general" | "decision"; prompt: string };
}): Promise<ReviewVerdict> {
  const { ctx, referee } = args;
  const outPath = reviewVerdictPath(ctx, referee.role);
  await mkdir(path.dirname(outPath), { recursive: true });
  // why: referee verdict paths are stable, so remove stale files before this round writes.
  await rm(outPath, { force: true });

  // The decision referee owns the novelty/positioning + tier-aware judgment, so it
  // must KNOW the run's novelty target (and the floor tier it must clear) to calibrate its
  // pass/revise/fail — flag below-floor as a novelty `revise`. (The math referee
  // judges correctness only and ignores tiering, so it is not told the floor; the
  // authoritative tier call is the separate cold referee in runStage0_5Typed.)
  const target = ctx.noveltyTarget ?? "field";
  const noveltyLine =
    referee.role === "decision"
      ? `novelty_target: ${target}  (floor tier this note must clear: ${TARGET_FLOOR_LABEL[target]}). Flag a note below this floor as a novelty \`revise\`/\`fail\`; tiering otherwise informs your verdict text.`
      : "";

  const prompt = [
    await readPrompt(ctx, referee.prompt),
    "",
    await readPrompt(ctx, "stage0_5_core_adapter.txt"),
    "",
    baseBrief(ctx, args.state),
    ...(noveltyLine ? ["", noveltyLine] : []),
    "",
    citedReviewBlock(referee.role, args.citedTargets),
    "",
    "=== FULL CURRENT PAPER UNDER REVIEW ===",
    "This TeX is rendered in memory from the exact typed core below for this referee call; it cannot be a stale disk render.",
    args.paperTex,
    "",
    "=== CORE UNDER REVIEW ===",
    JSON.stringify(args.core, null, 2),
    "",
    `VERDICT_OUTPUT_PATH: ${outPath}`,
    'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<verdict.json>"]}.',
  ].join("\n");

  // Referee harness in `verdictFile` mode: dispatch + wrapper parse + fresh-write
  // check; the Zod verdict validation and role-tag check below stay stage-specific.
  const result = await runReferee({
    ctx,
    deps: args.deps,
    stage: "0.5",
    label: `D0.5 panel referee ${referee.role}`,
    prompt,
    promptSources: [`referee:${referee.role}`, "core+paper (inline)"],
    model: MODEL_PLAN.mechanicalTier.model,
    reasoningEffort: MODEL_PLAN.mechanicalTier.effort,
    inactivityTimeoutMs: 25 * 60 * 1000,
    verdictFile: outPath,
  });
  if (result.failure?.kind === "stdout-parse") {
    // AUDIT-A: fail closed on unparseable stage output; why: Stage 0.5 must not advance on garbage.
    throw new Error(`Stage 0.5: referee ${referee.role} output did not parse (parse_failed) - refusing to advance on unparseable output`);
  }
  if (result.failure?.kind === "not-completed") {
    // why: a failed/non-completed referee must not reuse a prior verdict file.
    throw new Error(`Stage 0.5 referee ${referee.role} did not complete (status='${result.failure.status}')`);
  }
  if (result.failure?.kind === "missing-file") {
    // why: after deleting the old file, existence proves this referee wrote a fresh verdict.
    throw new Error(`Stage 0.5 referee ${referee.role} completed without writing ${outPath}`);
  }
  const verdict = ReviewVerdictSchema.parse(result.json);
  if (verdict.referee !== referee.role) {
    throw new Error(
      `Stage 0.5 referee ${referee.role} emitted a verdict tagged '${verdict.referee}'`,
    );
  }
  return verdict;
}

export interface Stage0_5CoreResult {
  overall: (typeof REVIEW_VERDICTS)[number];
  verdicts: ReviewVerdict[];
  cited_checks: D0CitedCheck[];
  /** Unavailable is neither pass nor revise: typed D0.5 checkpoints to main/user. */
  citation_verification_required: D0CitedCheck[];
}

export async function runStage0_5Core(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  /** Test seam; production uses the same resolver as F2.5/F4. */
  citedResolver?: (source: ResolvableCitation) => Promise<CitedMatchTarget>;
}): Promise<Stage0_5CoreResult> {
  const corePath = coreJsonPath(args.ctx);
  if (!existsSync(corePath)) {
    throw new Error(`Stage 0.5 requires a core at ${corePath}`);
  }
  // Every reviewer assembles the paper through loadPaperView — see core/paper_view.ts.
  // Reading writeup.tex here would review a pre-D0.R or pre-proposal render even while
  // core.json is current; and reading core.json raw would miss this round's provisional
  // proofs. The shared assembler removes both split-brains for every consumer at once.
  const view = await loadPaperView(args.ctx, { corePath });
  logPaperView(view, "D0.5");
  const core = view.core;
  const paperTex = view.tex;
  const citedTargets = await resolveD0CitedTargets(core, args.citedResolver ?? resolveCitedTarget);

  const verdicts = await Promise.all(
    REFEREES.map((referee) =>
      reviewWithReferee({
        ctx: args.ctx,
        state: args.state,
        deps: args.deps,
        core,
        paperTex,
        citedTargets,
        referee,
      }),
    ),
  );

  const bad = unresolvedFindingNodes(core, verdicts);
  if (bad.length > 0) {
    throw new Error(
      `Stage 0.5 referee cited nonexistent core node(s): ${[...new Set(bad)].join(", ")}`,
    );
  }

  const math = verdicts.find((v) => v.referee === "math")!;
  const nonMathRows = verdicts.filter((v) => v.referee !== "math").flatMap((v) => v.cited_checks);
  if (nonMathRows.length > 0) {
    throw new Error("Stage 0.5: only the math referee may emit cited_checks");
  }
  const expected = new Map(citedTargets.map((c) => [c.nodeId, c] as const));
  const seen = new Set<string>();
  for (const check of math.cited_checks) {
    const target = expected.get(check.node_id);
    if (!target) throw new Error(`Stage 0.5 math referee emitted cited check for non-cited node ${check.node_id}`);
    if (seen.has(check.node_id)) throw new Error(`Stage 0.5 math referee emitted duplicate cited check for ${check.node_id}`);
    seen.add(check.node_id);
    const allowed = target.target.mode === "fetched"
      ? new Set(["cited-verified", "cited-mismatch", "cited-underspecified", "cited-source-unverifiable"])
      : target.target.mode === "attested"
        ? new Set(["cited-verified-attested", "cited-mismatch", "cited-underspecified", "cited-source-unverifiable"])
        : new Set(["cited-source-unverifiable"]);
    if (!allowed.has(check.check_status)) {
      throw new Error(
        `Stage 0.5 cited check ${check.node_id}=${check.check_status} is invalid for resolver mode ${target.target.mode}`,
      );
    }
  }
  const missing = [...expected.keys()].filter((id) => !seen.has(id));
  if (missing.length > 0) {
    throw new Error(`Stage 0.5 math referee omitted cited check(s): ${missing.join(", ")}`);
  }
  const citedBad = math.cited_checks.filter(
    (c) => c.check_status === "cited-mismatch" || c.check_status === "cited-underspecified",
  );
  for (const check of citedBad) {
    if (!math.findings.some((f) => f.node_id === check.node_id && f.code === check.check_status)) {
      math.findings.push({
        node_id: check.node_id,
        code: check.check_status,
        one_line: check.note,
      });
    }
  }
  const citationVerificationRequired = math.cited_checks.filter(
    (c) => c.check_status === "cited-source-unverifiable",
  );
  const combined = combineVerdicts(verdicts);
  const overall = citedBad.length > 0 && combined === "pass" ? "revise" : combined;
  return {
    overall,
    verdicts,
    cited_checks: math.cited_checks,
    citation_verification_required: citationVerificationRequired,
  };
}
