// D0.5.G — the COLD general referee (rubric-free, fresh eyes).
//
// Anti-Goodhart: the rubric became the producer's optimization
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
//
// TWO CALL ROLES (see runStage0_5Typed). The AUTHORITATIVE call is the one on the
// round the core panel passes — it decides the accept, exactly as above. A second
// TRIAGE call is dispatched CONCURRENTLY with the panel on the first round of a D0.5
// invocation, so that the non-pass exits (math `fail`, the convergence backstops, D0.R
// self-escalation, cap exhaustion) carry a tier at all: every one of them routes back
// to a D0 re-solve, the priciest step in the pipeline, and used to do so blind to
// whether the note could ever clear the floor. `decideTriageKill` below is the ONLY
// authority a triage read has to end a run early, and it is deliberately narrow.
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { D0_5_TRIAGE_MARKER, MODEL_PLAN } from "../../constants.js";
import { runReferee } from "../framework/referee.js";
import type { ReviewResult } from "../../judgment.js";
import { formalizationDir, resolveInDir } from "../../paths.js";
import {
  discoveryBrief,
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

/** Stdout contract for the D0.5.G cold referee.  Raw-byte LaTeX repair is performed by
 * the shared referee harness first; every field that DETERMINES ROUTING (`tier`,
 * `salvageable`, `critique`, `flagship_potential`, and the flagged labels) stays
 * required and strictly typed, so escape recovery cannot turn a structurally malformed
 * response into an accepted review.
 *
 * Two deviations are deliberately tolerated, because a validation failure here THROWS
 * and discards a completed (paid) cold-referee call, and `normalizeGeneralReview` below
 * already absorbs both while failing SAFE — an unusable tier becomes `incremental`,
 * i.e. below any non-trivial floor, never an accept:
 *   - unknown extra keys (a stray `"reasoning": "…"` is routine LLM output, not a
 *     structural fault), and
 *   - an absent `improvement_directive` / `flagship_directive`, which are already
 *     OPTIONAL on `GeneralReviewResult` — requiring them here was a schema/interface
 *     mismatch that failed a referee for correctly omitting a directive it had no
 *     reason to emit.
 * `tier` is lower-cased first for the same reason: the normalizer does it, so a
 * capitalized `"Field"` should not cost the whole call. */
export const generalReviewPayloadSchema = z.object({
  tier: z.preprocess(
    (v) => (typeof v === "string" ? v.trim().toLowerCase() : v),
    z.enum(["flagship", "field", "subfield", "incremental"]),
  ),
  salvageable: z.boolean(),
  improvement_directive: z.string().optional(),
  flagged_conjecture_labels: z.array(z.string()),
  critique: z.string().min(1),
  flagship_potential: z.boolean(),
  flagship_directive: z.string().optional(),
});

export function generalReviewPayloadValidationError(obj: Record<string, unknown>): string | null {
  const parsed = generalReviewPayloadSchema.safeParse(obj);
  if (parsed.success) return null;
  return `D0.5.G general-referee response failed strict schema validation: ${parsed.error.message}`;
}

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
    discoveryBrief(args.ctx, args.state),
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
    validate: generalReviewPayloadValidationError,
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
 *
 * READERS: this file EXISTING no longer means D0.5 passed — the triage call writes it on
 * non-passing rounds too. `meets_floor` is the pass signal.
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

/**
 * May a TRIAGE tier read (taken concurrently with the core panel, BEFORE D0.R has
 * repaired anything) end the run on its own?
 *
 * Only when the referee places the note below the floor AND reports no bounded fix.
 * That combination is a judgment about the KERNEL, and a directed in-place math repair
 * does not change the kernel — so spending the rest of the revise cap, and then a D0
 * re-solve, on it is pure waste.
 *
 * A `salvageable` below-floor read deliberately does NOT kill. Two reasons: it names a
 * bounded upgrade the loop may yet deliver, and the triage referee is reading a draft
 * whose flagged proofs are still under repair while its prompt asks it to judge what is
 * PROVED — so it under-tiers. This referee class already over-rejects on complete work
 * (internal/memory/feedback_topics_gate_over_rejects.md: 7 consecutive field candidates
 * down-tiered to subfield); handing it a mid-repair draft compounds that. Everything it
 * says short of "no bounded fix exists" is therefore advisory, and the floor call stays
 * with the authoritative read on the passing round.
 */
export function decideTriageKill(
  gen: Pick<GeneralReviewResult, "tier" | "salvageable">,
  target: NoveltyTarget,
): boolean {
  return tierRank(gen.tier) < tierRank(TARGET_FLOOR_LABEL[target]) && !gen.salvageable;
}

/**
 * One-line provenance of a triage tier read, appended to every non-pass D0.5 checkpoint
 * message. Those halts all hand the run back for a D0 re-solve; without this the operator
 * pays for that re-solve with no signal about whether the note can clear the floor.
 *
 * WORDING IS LOAD-BEARING. Both the machine classifier and the human/agent orchestrator
 * decide a D0.5 halt by reading its message, so this note must not be mistakable for the
 * halt's own verdict. It therefore avoids every token those readers key on: no `PASS`, no
 * `BELOW NOVELTY FLOOR`, and no `tier=X ≥ floor=Y` — that last one is verbatim the PASS
 * signal in internal/memory/feedback_d05_verify_verdict_body.md, and emitting it on a
 * cap-exhausted halt made a non-pass satisfy the documented pass check.
 * `checkpoint_playbook` additionally cuts the message at D0_5_TRIAGE_MARKER, which requires
 * this string to OPEN with that marker.
 */
export function formatTriageTier(gen: GeneralReviewResult, target: NoveltyTarget): string {
  const floor = TARGET_FLOOR_LABEL[target];
  const meets = tierRank(gen.tier) >= tierRank(floor);
  return (
    `${D0_5_TRIAGE_MARKER} — advisory context only, NOT the verdict for this halt (a cold read of ` +
    `this invocation's first-round draft, taken while the panel was still reviewing). ` +
    `Graded tier '${gen.tier}' against target '${target}' (floor '${floor}'): ` +
    `${meets ? "meets the bar" : "under the bar"}; ` +
    `${gen.salvageable ? "salvageable" : "no bounded fix in scope"}. ${gen.critique}` +
    (meets
      ? ""
      : ` A re-solve that does not lift the tier will stop here again` +
        (gen.improvement_directive ? `; the referee's bounded upgrade: ${gen.improvement_directive}` : "") +
        `.`)
  );
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
