// D0.5.G — the COLD general referee (rubric-free, fresh eyes).
//
// Runs only after D0.5.2 (the rubric reviewer) reaches ACCEPT and a novelty
// target is set. Anti-Goodhart: the rubric became the producer's optimization
// target (and the statement_correction route literally rewrites the headline
// until the rubric is satisfied), so rubric-compliance stopped measuring
// quality. This referee is given ONLY the paper + plain tier definitions — never
// the flagship rubric — so it reproduces the "paste into a fresh model, does it
// actually clear the bar?" check the user does by hand.
//
// Outcome (handled by the caller in stage0_5.ts):
//   tier ≥ floor          → ACCEPT stands.
//   tier < floor, salvageable → ACCEPT downgraded to REVISE; the D0.5 boundary
//                               re-runs runStage0 (re-derive at D0) carrying the
//                               critique + flagged targets.
//   tier < floor, NOT salvageable → ACCEPT downgraded to REJECT + `halt_reason`,
//                               which runReviewBoundary short-circuits to a clean
//                               checkpoint (pipeline halts for the user).
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../../constants.js";
import { runReferee } from "../framework/referee.js";
import type { ReviewResult } from "../../judgment.js";
import { formalizationDir, resolveInDir } from "../../paths.js";
import {
  baseBrief,
  readIfExists,
  readPrompt,
  type StageDeps,
} from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import type { NoveltyTarget } from "../../novelty.js";
import { loadPaperView, logPaperView } from "../core/paper_view.js";

/** Resolve the note this referee reviews — FAIL-CLOSED.
 *
 *  This read used to be `readIfExists(paths.tex)`, which returns "" for a missing
 *  file. The consequence was not a missing-input error but a fabricated
 *  mathematical verdict: empty note → referee returns an unparseable/low tier →
 *  `parseGeneralReview` fail-safes to "incremental" → the pipeline reports "BELOW
 *  NOVELTY FLOOR". The orchestrator then spends D-1.2/D0 rounds fixing mathematics
 *  that was never the problem. A referee must never be asked to judge nothing. */
export async function resolveNoteText(args: {
  noteText?: string;
  /** Assembles the canonical paper view. Injected so this stays a pure decision function. */
  loadView: () => Promise<string>;
}): Promise<string> {
  if (args.noteText !== undefined) {
    if (args.noteText.trim().length === 0) {
      throw new Error("D0.5.G received an empty note override — refusing to run a novelty judgment on no content.");
    }
    return args.noteText;
  }
  const text = await args.loadView();
  if (text.trim().length === 0) {
    throw new Error(
      "D0.5.G cannot review: the assembled paper is empty (0 non-whitespace chars). This is a render/plumbing " +
        "failure, NOT a novelty verdict.",
    );
  }
  return text;
}

export type GeneralTier = "flagship" | "field" | "subfield" | "incremental";

export interface GeneralReviewResult {
  tier: GeneralTier;
  salvageable: boolean;
  /**
   * When `salvageable`, a concrete bounded fix on the SAME object the D0 re-solve
   * should implement (a better/adaptive estimator, deriving an assumed condition
   * from primitive rates, tightening a bound). Threaded into the revise critique so
   * the re-derivation attacks the named upgrade instead of reproducing the same note.
   */
  improvement_directive?: string;
  flagged_conjecture_labels: string[];
  critique: string;
  /**
   * Flagship-upside: true when the note CLEARS its floor (accepted) but is below
   * flagship with a concrete bounded path up. Drives up to 2 bonus D0.R rounds
   * AFTER an accept — never loses the accepted result. Independent of `salvageable`.
   */
  flagship_potential?: boolean;
  /** When `flagship_potential`, the one bounded step to attempt for flagship. */
  flagship_directive?: string;
  /** Raw codex stdout, for logging. */
  raw: string;
}

/**
 * novelty_target → the plain floor-tier name shown to the cold referee. The target
 * IS the floor tier now (identity over the tier ladder); the two legacy spellings
 * are mapped for back-compat with pre-unification state read straight off disk.
 */
export const TARGET_FLOOR_LABEL: Record<string, GeneralTier> = {
  incremental: "incremental",
  subfield: "subfield",
  field: "field",
  flagship: "flagship",
  "relative-to-repo": "incremental",
  "relative-to-literature": "subfield",
};

const VALID_TIERS = new Set<GeneralTier>(["flagship", "field", "subfield", "incremental"]);

/**
 * Run the cold general referee over the stitched note. No Lean (a discovery-note
 * referee does not touch the scaffold), so lean-lsp is disabled for speed.
 */
export async function runGeneralReview(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  attempt?: number;
  /** Override the note text reviewed (default: the run's canonical stitched .tex).
   *  Lets the cold referee score a CANDIDATE note (e.g. a D0.R round output) without
   *  touching the run artifact — also what the D0.5 ⇄ D0.R loop needs. */
  noteText?: string;
}): Promise<GeneralReviewResult> {
  const target = args.ctx.noveltyTarget ?? "field";
  const floor = TARGET_FLOOR_LABEL[target];
  // Assemble through the SHARED paper view, not writeup.tex.
  //
  // This referee used to read writeup.tex from disk while the D0.5 core panel
  // reviewed an overlaid in-memory render. When a round banks provisional proofs,
  // writeup.tex still shows the stale/absent proof text for exactly those nodes —
  // so the two halves of one review stage judged different papers, and the cold
  // referee (whose whole job is "judge what is PROVED here") systematically
  // under-tiered. An explicit `noteText` override still wins, for the D0.5 ⇄ D0.R
  // loop which scores a candidate note without touching run artifacts.
  const noteText = await resolveNoteText({
    noteText: args.noteText,
    loadView: async () => {
      const view = await loadPaperView(args.ctx);
      logPaperView(view, "D0.5.G");
      return view.tex;
    },
  });
  const prompt = [
    await readPrompt(args.ctx, "stage0_5_general_review.txt"),
    "",
    baseBrief(args.ctx, args.state),
    "",
    `novelty_target: ${target}  (floor tier you must clear: ${floor})`,
    "",
    `TeX (the full stitched note — judge what is PROVED here):\n${noteText}`,
    "",
    "RETURN ONLY the JSON described above.",
  ].join("\n");
  const plan = MODEL_PLAN.stage0_5_general;
  // Referee harness (stdout mode): dispatch + parse + scaffolding-strip. An
  // unparseable stdout throws here exactly as the old inline extractJsonObject
  // did — a mechanical failure, never a tier verdict.
  const result = await runReferee({
    ctx: args.ctx,
    deps: args.deps,
    stage: "0.5",
    label: "D0.5.G general referee",
    prompt,
    promptSources: ["prompts/D0.5/stage0_5_general_review.txt", "stitched note (inline)"],
    model: plan.model,
    reasoningEffort: plan.effort,
    leanLsp: false,
  });
  if (result.parseError !== null) {
    throw new Error(result.parseError);
  }
  const gen = normalizeGeneralReview(result.json, result.raw);
  // Persist the cold-referee review to the reviews folder, mirroring how the
  // D0.5 boundary attempts are saved. Unlike the boundary verdict (only emitted
  // when the tier falls below the floor), this captures the D0.5.G review on
  // EVERY run — including a pass — so the tier/critique is greppable history.
  await persistGeneralReviewJson(args.ctx, args.attempt ?? 1, gen, floor);
  return gen;
}

/**
 * Persist the D0.5.G cold-referee (general) review to `reviews/review_general.json`
 * — the latest attempt, alongside the panel verdicts `review_math.json` /
 * `review_rubric.json` (the full per-attempt history lives in `reviews/reviews.jsonl`).
 * The `attempt` and `stage` fields are kept inside the record. Best-effort: errors
 * are logged but never block the pipeline.
 */
async function persistGeneralReviewJson(
  ctx: PipelineContext,
  attempt: number,
  gen: GeneralReviewResult,
  floor: GeneralTier,
): Promise<void> {
  try {
    const dir = resolveInDir(formalizationDir(ctx.repoRoot, ctx.qid), "reviews", [
      `${ctx.qid}_${ctx.specialization}_reviews`,
    ]);
    await mkdir(dir, { recursive: true });
    const file = path.join(dir, "review_general.json");
    const record = {
      stage: "0.5.G",
      attempt,
      novelty_target: ctx.noveltyTarget,
      floor,
      meets_floor: tierRank(gen.tier) >= tierRank(floor),
      tier: gen.tier,
      salvageable: gen.salvageable,
      improvement_directive: gen.improvement_directive ?? null,
      flagship_potential: gen.flagship_potential ?? false,
      flagship_directive: gen.flagship_directive ?? null,
      flagged_conjecture_labels: gen.flagged_conjecture_labels,
      critique: gen.critique,
      raw: gen.raw,
    };
    await writeFile(file, `${JSON.stringify(record, null, 2)}\n`, "utf8");
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    console.warn(
      `[causalsmith] persistGeneralReviewJson failed for attempt ${attempt}: ${reason}`,
    );
  }
}

/** Order tiers low→high so the saved record can flag whether the floor was met. */
export function tierRank(tier: GeneralTier): number {
  return ["incremental", "subfield", "field", "flagship"].indexOf(tier);
}

/** Normalize the harness-parsed referee JSON into the typed review result. The
 *  parse itself now lives in `runReferee`; every fail-safe below (unknown tier →
 *  incremental, prefix-stripped labels, critique default) is stage semantics. */
function normalizeGeneralReview(obj: Record<string, unknown>, raw: string): GeneralReviewResult {
  const tierRaw = typeof obj.tier === "string" ? obj.tier.trim().toLowerCase() : "";
  // Fail SAFE: an unparseable / unknown tier is treated as below any non-trivial
  // floor (incremental) rather than silently passing the gate.
  const tier: GeneralTier = VALID_TIERS.has(tierRaw as GeneralTier)
    ? (tierRaw as GeneralTier)
    : "incremental";
  // Normalize to the BARE SLUG the prompt contract specifies
  // (stage0_5_general_review.txt: "bare slugs (strip the `conj:`/`thm:` prefix)"), so a
  // referee that emits the prefixed form anyway still yields the contract shape — these
  // labels also flow into `perItemFindings[].label`, which downstream reads as a slug.
  //
  // The bug this looked like was real but lived elsewhere: a bare slug matched no core id
  // (which carries the prefix), so `required_core_targets` was always empty and D0's
  // exact-target enforcement never armed, degrading each below-floor reroute into a
  // WHOLE-PAPER re-solve. The fix is in `partitionReviewTargets`, which now resolves a
  // bare slug to its unique core id — not in changing what the referee emits.
  const labels = Array.isArray(obj.flagged_conjecture_labels)
    ? obj.flagged_conjecture_labels
        .map((s) => (typeof s === "string" ? s.replace(/^(?:conj|oeq|thm|lem|prop):/i, "").trim() : ""))
        .filter(Boolean)
    : [];
  const critique =
    typeof obj.critique === "string" && obj.critique.trim().length > 0
      ? obj.critique.trim()
      : "General referee returned no usable critique; treating the note as below the novelty floor.";
  const improvement_directive =
    typeof obj.improvement_directive === "string" && obj.improvement_directive.trim().length > 0
      ? obj.improvement_directive.trim()
      : undefined;
  const flagship_directive =
    typeof obj.flagship_directive === "string" && obj.flagship_directive.trim().length > 0
      ? obj.flagship_directive.trim()
      : undefined;
  return {
    tier,
    salvageable: obj.salvageable === true,
    improvement_directive,
    flagged_conjecture_labels: labels,
    critique,
    flagship_potential: obj.flagship_potential === true && !!flagship_directive,
    flagship_directive,
    raw,
  };
}

/**
 * Transcribe a below-floor general verdict into the {@link ReviewResult} the
 * D0.5 boundary already knows how to route. Salvageable → `revise` (the boundary
 * re-runs runStage0); not salvageable → `reject` carrying a `halt_reason` that
 * runReviewBoundary short-circuits to a clean checkpoint. A deterministic
 * transcription of referee findings into a revise/reject verdict, same pattern
 * used elsewhere for other typed panel outputs.
 */
export function buildGeneralTierVerdict(
  gen: GeneralReviewResult,
  target: NoveltyTarget,
  // The caller decides reroute-vs-halt: `canReroute` = the referee marked it
  // salvageable AND gave a concrete directive AND the reroute cap is not yet hit.
  // `capExhausted` lets the halt path explain WHY a salvageable note still stops.
  canReroute: boolean,
  capExhausted = false,
): ReviewResult {
  const floor = TARGET_FLOOR_LABEL[target];
  const header = `[D0.5.G cold referee] delivered tier=${gen.tier} below novelty_target=${target} (floor=${floor}). `;
  const directiveLine = gen.improvement_directive
    ? `\n\nDIRECTED IMPROVEMENT (re-derive the SAME object implementing this, do not reproduce the prior note): ${gen.improvement_directive}`
    : "";
  const verbatim_critique = header + gen.critique + (canReroute ? directiveLine : "");
  if (canReroute) {
    return {
      status: "revise",
      classification: "novelty",
      // kernel_substituted = a weaker object than headlined was delivered and a
      // re-derivation (carrying the named directive) has a path to the stronger one
      // on the SAME object — solver shortfall, not a structurally-below kernel.
      proposal_promise_gap: "kernel_substituted",
      perItemFindings: [
        {
          label: gen.flagged_conjecture_labels[0] ?? "headline",
          verdict: "novelty",
          one_line: `Delivered tier ${gen.tier} < floor ${floor}; directed reroute: ${gen.improvement_directive ?? "re-derive to lift"}`,
        },
      ],
      verbatim_critique,
      flagged_conjecture_labels: gen.flagged_conjecture_labels,
    } as ReviewResult;
  }
  // Halt: either genuinely unsalvageable (dead object / open-ended new idea), or the
  // directed-reroute budget is exhausted (the bounded fixes were tried and did not
  // lift it). Deterministic halt (no judge, no pivot) — hand to the operator.
  const haltCritique =
    verbatim_critique +
    (capExhausted
      ? `\n\nDirected re-attempts exhausted: the named bounded improvements were tried and did not lift the tier. Lifting now needs new math (directed solve) or a re-anchored proposal — halting for the operator.`
      : "");
  return {
    status: "reject",
    classification: "novelty",
    proposal_promise_gap: "tier_genuinely_below",
    perItemFindings: [
      {
        label: "headline",
        verdict: "novelty",
        one_line: capExhausted
          ? `Delivered tier ${gen.tier} < floor ${floor}; directed re-attempts exhausted, halting.`
          : `Delivered tier ${gen.tier} < floor ${floor}; not salvageable within scope.`,
      },
    ],
    verbatim_critique: haltCritique,
    // Read by runReviewBoundary BEFORE the reject fast-path → deterministic halt.
    halt_reason: haltCritique,
  } as ReviewResult;
}
