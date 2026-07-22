import { z } from "zod";

/**
 * Per-theorem verdict entry inside a Stage 0.5 paper-scoped review.
 * Returned inside the `theorems_review` field of a ReviewResult when the
 * note covers multiple theorems from `state.theorems`.
 */
export interface TheoremReviewEntry {
  theorem_local_id: string;
  verdict: string; // "pass" | "accept" | "fail" | "reject" — open string for forward compat
  findings?: unknown[];
}

/**
 * A named Lean hypothesis that ASSUMES a true, standard mathematical fact the
 * theorem ought eventually to prove, deferred only because the discharging
 * Mathlib/Causalean substrate does not exist yet (e.g. `PinskerBound`, pending the
 * Scheffé / f-divergence layer). Reported by Stage 4 EVEN ON A PASSING review
 * and aggregated into the global `SUBSTRATE_DEBT.md` ledger so we know what
 * infrastructure to build.
 *
 * This is categorically distinct from a reject-class-A missing assumption: a
 * genuine gate must NOT weaken the claim, smuggle the conclusion, or make the
 * theorem vacuous — it is honest, trackable debt, not laundering.
 */
export interface SubstrateGate {
  /** Lean hypothesis identifier / binder (e.g. `h : PinskerBound P₀ P₁`). */
  name: string;
  /** The assumed proposition (informal or Lean rendering). */
  statement: string;
  /** The standard theorem this encodes (e.g. "Pinsker's inequality"). */
  classical_fact: string;
  /** The substrate layer whose absence forces the assumption. */
  missing_infra: string;
  /**
   * Discharge fate on the discharge-this-run axis (absent ⇒ "gated", back-compat):
   *  - "gated": WILL be discharged this run (parallelism gate); recorded in
   *    SUBSTRATE_DEBT.md until its proof lands. Verified by that proof.
   *  - "cited": NOT discharged this run — a deferred assumption matched against
   *    `source`; recorded in CITED_DEPENDENCIES.md; may be built in a future run.
   */
  gate_class?: "gated" | "cited";
  /** For `gate_class:"cited"`: the citation this assumption is matched against. */
  source?: { cite_id: string; locator: string; url?: string };
  /**
   * For `gate_class:"cited"`: the F2.5 source-match verdict.
   *  - `cited-verified`: Lean def matches the FETCHED source at the locator.
   *  - `cited-verified-attested`: matches the attested `verbatim_statement` (no fetch).
   *  - `cited-mismatch`: def does NOT match — HARD-BLOCKS banking.
   *  - `cited-underspecified`: def is not self-contained — a distinguishing
   *    hypothesis/class the cited statement relies on is referenced only by name
   *    (a free abstract variable or an undefined named class) instead of being
   *    encoded — HARD-BLOCKS banking.
   *  - `cited-source-unverifiable`: neither fetch nor verbatim statement — invalid
   *    for new runs; migration-only carve-out (flag, do not block).
   */
  check_status?:
    | "cited-verified"
    | "cited-verified-attested"
    | "cited-mismatch"
    | "cited-underspecified"
    | "cited-source-unverifiable";
}

export type ReviewResult =
  | { status: "pass"; notes?: string; assumption_table_markdown?: string; theorems_review?: TheoremReviewEntry[]; substrate_gates?: SubstrateGate[]; derived_obj_ids?: string[] }
  | {
      status: "accept";
      notes?: string;
      dimension_findings: Record<string, { verdict: string; notes: string }>;
      tier_at_derivation?: "flagship" | "field" | "subfield" | "incremental";
      /**
       * Whether Stage 0 proved the kernel as proposed (`as_proposed`), or
       * refuted the kernel while proving an independently flagship-grade
       * positive result (`refuted_with_positive_result`). The second value is
       * a Stage 0.5 refutation-as-flagship outcome — see flagship rubric path
       * (d) in `stage0_5_review.txt`. Defaults to `as_proposed` when omitted.
       */
      kernel_status?: "as_proposed" | "refuted_with_positive_result";
      journal_recommendations: Array<{
        journal: string;
        tier: string;
        fit_reasoning: string;
      }>;
      assumption_table_markdown?: string;
      theorems_review?: TheoremReviewEntry[];
    }
  | {
      status: "revise" | "reject";
      classification: string;
      dimension_findings?: Record<string, { verdict: string; notes: string }>;
      perItemFindings: Array<{
        label: string;
        verdict: string;
        one_line: string;
        /**
         * Stage 2.5 only (fix-locus early triage). Where the ROOT of this
         * finding lives, hence who can fix it:
         *  - `lean-scaffold` — the .md/.tex are correct; only the Lean encoding
         *    is wrong (keyword, missing import, a hypothesis present in the .md
         *    but not transcribed, an untied local def). F2-fixable.
         *  - `nl-plan` — the F1 NL formalization plan (.md) itself is unfaithful
         *    / vacuous / incomplete vs the .tex. Only F1 can fix it.
         *  - `math-source` — the .tex math itself is wrong. Only F0 can fix it.
         * Consumed by `fixLocusRouteFromReview` to escalate upstream WITHOUT
         * spinning the F2 revise loop. Absent ⇒ treated as `lean-scaffold`.
         */
        fix_locus?: "lean-scaffold" | "nl-plan" | "math-source";
      }>;
      verbatim_critique: string;
      /**
       * Stage 0.5 only: when the derived kernel falls short of the proposal's
       * flagship promise, identify WHICH gap shape it is. Separates H1
       * (solver shortfall — the proposal was flagship-shaped but Stage 0
       * substituted a weaker derivable claim) from H2 (the proposal itself
       * was overrated at -0.5 and the derivation faithfully delivered it).
       *
       * - `kernel_substituted` — Stage 0 derived a different (weaker) object
       *   than the proposal headlined (e.g. row-span identity in place of
       *   distributional sharpness).
       * - `assumption_omitted` — flagship object derived only after silently
       *   dropping a load-bearing assumption (e.g. rank-invariance dropped,
       *   sharpness claim no longer applies to the advertised model).
       * - `direction_only` — proposal promised an iff / equivalence frontier;
       *   Stage 0 proved only one direction (typically soundness) without
       *   the converse.
       * - `constructive_object_missing` — proposal promised an enumeration,
       *   algorithm, or explicit threshold; Stage 0 only proved existence
       *   or used generic duality without producing the constructive object.
       * - `tier_genuinely_below` — the derived kernel exactly matches the
       *   proposal AND that kernel is honestly subfield/field; the -0.5
       *   reviewer overrated novelty. No solver-shortfall claim.
       *
       * Optional and only used by the Stage 0.5 boundary (other boundaries
       * leave it omitted). Downstream consumers (bank_entry.ts) read this
       * to auto-classify the reusability of the run.
       */
      proposal_promise_gap?:
        | "kernel_substituted"
        | "assumption_omitted"
        | "direction_only"
        | "constructive_object_missing"
        | "tier_genuinely_below"
        | "proposal_drift";
      assumption_table_markdown?: string;
      theorems_review?: TheoremReviewEntry[];
      /**
       * Stage 0.5 only (per-conjecture split, layer 5). When the reviewer can
       * isolate the failure to one or more specific conjectures (by `\label{conj:<slug>}`),
       * listing them here routes the rewind to those Stage 0.k sub-stages only
       * rather than a full Stage 0 rerun. Empty/absent → fall back to the
       * existing full-Stage-0 rewind path. Consumed by `propagateTheoremReview`
       * and `intervention_routing.ts::stage_0_k`.
       */
      flagged_conjecture_labels?: string[];
      /**
       * Stage 0.5 only (D0 revise router). True when the review has findings in
       * the shared setup sections §1–§8 (abstract / introduction & motivating
       * conjectures / related-work positioning / formal setup / assumptions /
       * estimand / target) or in a supporting theorem — i.e. content the
       * per-conjecture (§9–§15) revise cannot reach. Routes a Stage 0.0 setup
       * revise pass. Independent of `flagged_conjecture_labels`: a review may
       * set both (setup AND a specific conjecture need repair), either, or
       * neither (structural finding ⇒ escalate). Consumed by `runStage0`.
       */
      setup_revision_needed?: boolean;
      /**
       * Stage 0.5 only (D0 triage → escalation). True when a finding is NOT
       * fixable by a D0 re-solve (0.0 / 0.k revise) because it needs a proposal
       * restructure or genuinely new math: reclassify a supporting theorem as a
       * conjecture so it can headline §9, prove a result the proposal assumed,
       * or change the kernel. Routes the D0.5 boundary to `stage_neg1` (D-1.2
       * proposer redraft) instead of spinning the revise loop. `escalate_reason`
       * carries the one-line instruction for the proposer.
       */
      escalate_to_proposer?: boolean;
      escalate_reason?: string;
      /**
       * Stage 2.5 only (fix-locus early triage → F1/F0). Set when the blocking
       * root of a `revise` lives UPSTREAM of F2: `stage_1` (the F1 NL plan is
       * wrong) or `stage_0` (the F0 math source is wrong). Computed
       * deterministically from per-finding `fix_locus` tags by
       * `fixLocusRouteFromReview`. Honored by `runReviewBoundary`, which breaks
       * the F2 revise loop immediately and rewinds there rather than spinning
       * up to the cap. Absent ⇒ all blocking findings are `lean-scaffold`
       * (F2-fixable) and the loop proceeds normally.
       */
      escalate_route?: "stage_0" | "stage_1";
      escalate_locus_reason?: string;
      /**
       * Stage 4 only (PRIMITIVE-vs-DERIVED audit → graph). obj_ids the reviewer
       * classified as DERIVED (proven from primitives, not an assumed primitive).
       * Written back to the formalization graph as `node.review.status = "derived"`.
       */
      derived_obj_ids?: string[];
    };

export interface Intervention {
  route: "user" | "stage_0" | "stage_1" | "stage_2" | "stage_3_local" | "stage_4d" | "stage_neg1";
  reason: string;
  proposed_action?: string;
  cite?: string;
  /**
   * Auto-approved Bucket A assumption authored by the Opus intervention judge.
   * Present only when the judge has elected to resolve a bucket-A
   * assumption-strengthening rather than escalate to the user. Must be paired
   * with `route: "stage_0"`. The orchestrator appends this to
   * `state.added_assumptions` with `user_approved: true` so that
   * `bucketAApprovedBlock` surfaces it verbatim to the rewound Stage 0.
   */
  proposed_assumption?: {
    label: string;
    statement: string;
    source?: string;
  };
  /**
   * What kind of action the route asks for. Load-bearing for the
   * theorem-split loop guard: when the judge proposes a Bucket-A grant whose
   * classification is `regime_defining`, it MUST set
   * `action_kind: "theorem_split"` and the orchestrator increments
   * `state.flags.theorem_splits`. Other values are informational.
   */
  action_kind?:
    | "theorem_split"
    | "statement_correction"
    | "re_derive"
    | "patch"
    | "local_patch"
    | "split_collapsed"
    | "loop_guard"
    | "user_required"
    | "redraft_proposal";
  /**
   * Corrected, standard-form restatement of an OVER-PRECISE headline object,
   * emitted with `action_kind: "statement_correction"`. Unlike a
   * `theorem_split` (which demotes the original claim to a conjecture and proves
   * a conditional-on-Q version), a statement correction asserts that the draft
   * over-stated the SAME focal object — e.g. claimed pointwise extremum
   * ATTAINMENT / exactness where the standard true statement is the closure /
   * inf-sup / a.e. form — and the corrected form holds UNCONDITIONALLY (no new
   * assumption). The router stores `statement` on
   * `state.flags.statement_correction_directive` for the rewound proposer.
   */
  proposed_restatement?: {
    statement: string;
    rationale?: string;
  };
  /**
   * Per-assumption scope-reduction classification surfaced when the judge
   * proposes (or evaluates) a Bucket A grant. `regime_defining` is the
   * dangerous category: the assumption defines the regime the conjecture
   * promised to characterize, so granting silently collapses the headline
   * theorem unless paired with a theorem-split.
   */
  assumption_classifications?: Array<{
    label: string;
    classification: "latent" | "caveat" | "regime_defining";
    one_line: string;
  }>;
}

/**
 * Zod schema for the optional `theorems_review` field added in paper-scoped
 * Stage 0.5. Each entry records a per-theorem verdict so the orchestrator can
 * propagate failures to `state.theorems[k]` before the rewind decision.
 */
const theoremsReviewSchema = z
  .array(
    z.object({
      theorem_local_id: z.string(),
      verdict: z.string(),
      findings: z.array(z.unknown()).optional(),
    }),
  )
  .optional();

/** Zod schema for one {@link SubstrateGate} entry (Stage 4 substrate-debt report). */
export const substrateGateSchema = z.object({
  name: z.string(),
  statement: z.string(),
  classical_fact: z.string(),
  missing_infra: z.string(),
  gate_class: z.enum(["gated", "cited"]).optional(),
  source: z
    .object({ cite_id: z.string(), locator: z.string(), url: z.string().optional() })
    .optional(),
  check_status: z
    .enum([
      "cited-verified",
      "cited-verified-attested",
      "cited-mismatch",
      "cited-underspecified",
      "cited-source-unverifiable",
    ])
    .optional(),
});

export const reviewResultSchema = z.union([
  z.object({
    status: z.literal("pass"),
    notes: z.string().optional(),
    assumption_table_markdown: z.string().optional(),
    theorems_review: theoremsReviewSchema,
    substrate_gates: z.array(substrateGateSchema).optional(),
  }).passthrough(),
  z.object({
    status: z.literal("accept"),
    notes: z.string().optional(),
    dimension_findings: z.record(z.object({ verdict: z.string(), notes: z.string() })),
    tier_at_derivation: z
      .enum(["flagship", "field", "subfield", "incremental"])
      .optional(),
    kernel_status: z
      .enum(["as_proposed", "refuted_with_positive_result"])
      .optional(),
    journal_recommendations: z
      .array(
        z.object({
          journal: z.string(),
          tier: z.string(),
          fit_reasoning: z.string(),
        }),
      )
      .max(3),
    assumption_table_markdown: z.string().optional(),
    theorems_review: theoremsReviewSchema,
  }).passthrough(),
  // Stage 1.5 / 2.5 / 4 simple-ACCEPT form (synonym of "pass"). Lighter
  // boundaries that don't carry novelty/journal dimensions emit ACCEPT
  // without `dimension_findings` / `journal_recommendations`. Listed AFTER
  // the heavy ACCEPT variant so a Stage 0.5 / -0.5 payload with the heavy
  // fields binds to the strict variant first; this fallback fires only for
  // payloads that lack them. The boundary loop treats "accept" identically
  // to "pass".
  z.object({
    status: z.literal("accept"),
    notes: z.string().optional(),
    classification: z.string().optional(),
    assumption_table_markdown: z.string().optional(),
    theorems_review: theoremsReviewSchema,
  }).passthrough(),
  z.object({
    status: z.union([z.literal("revise"), z.literal("reject")]),
    classification: z.string(),
    dimension_findings: z
      .record(z.object({ verdict: z.string(), notes: z.string() }))
      .optional(),
    perItemFindings: z.array(
      z.object({
        label: z.string(),
        verdict: z.string(),
        one_line: z.string(),
        fix_locus: z.enum(["lean-scaffold", "nl-plan", "math-source"]).optional(),
      }),
    ),
    verbatim_critique: z.string(),
    proposal_promise_gap: z
      .enum([
        "kernel_substituted",
        "assumption_omitted",
        "direction_only",
        "constructive_object_missing",
        "tier_genuinely_below",
        "proposal_drift",
      ])
      .optional(),
    assumption_table_markdown: z.string().optional(),
    theorems_review: theoremsReviewSchema,
    flagged_conjecture_labels: z.array(z.string()).optional(),
    setup_revision_needed: z.boolean().optional(),
    escalate_to_proposer: z.boolean().optional(),
    escalate_reason: z.string().optional(),
    escalate_route: z.enum(["stage_0", "stage_1"]).optional(),
    escalate_locus_reason: z.string().optional(),
  }).passthrough(),
]) as unknown as z.ZodType<ReviewResult>;

export const interventionSchema: z.ZodType<Intervention> = z
  .object({
    route: z.enum(["user", "stage_0", "stage_1", "stage_2", "stage_3_local", "stage_4d", "stage_neg1"]),
    reason: z.string(),
    proposed_action: z.string().optional(),
    cite: z.string().optional(),
    proposed_assumption: z
      .object({
        label: z.string().min(1),
        statement: z.string().min(1),
        source: z.string().optional(),
      })
      .optional(),
    action_kind: z
      .enum([
        "theorem_split",
        "statement_correction",
        "re_derive",
        "patch",
        "local_patch",
        "split_collapsed",
        "loop_guard",
        "user_required",
        "redraft_proposal",
      ])
      .optional(),
    proposed_restatement: z
      .object({
        statement: z.string().min(1),
        rationale: z.string().optional(),
      })
      .optional(),
    assumption_classifications: z
      .array(
        z.object({
          label: z.string().min(1),
          classification: z.enum(["latent", "caveat", "regime_defining"]),
          one_line: z.string().min(1),
        }),
      )
      .optional(),
  })
  .superRefine((value, ctx) => {
    if (value.route !== "user" && !value.proposed_action?.trim()) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["proposed_action"],
        message: "proposed_action is required when route is not user",
      });
    }
    if (value.proposed_assumption && value.route !== "stage_0") {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["proposed_assumption"],
        message: "proposed_assumption is only valid with route=stage_0 (auto Bucket A path)",
      });
    }
    // Loop-guard contract: any Bucket-A grant whose classification is
    // regime_defining MUST be paired with action_kind=theorem_split so that
    // the orchestrator can increment state.flags.theorem_splits. Otherwise the
    // judge is asking us to silently strengthen the headline theorem.
    const hasRegimeDefining = (value.assumption_classifications ?? []).some(
      (c) => c.classification === "regime_defining",
    );
    if (hasRegimeDefining && value.proposed_assumption && value.action_kind !== "theorem_split") {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["action_kind"],
        message:
          "regime_defining grant must be paired with action_kind=theorem_split (or escalate via route=user)",
      });
    }
    // Statement-correction contract: a corrected restatement is NOT an
    // assumption grant. It must carry the corrected statement, rewind to
    // stage_0, and must NOT smuggle in a proposed_assumption (that would be a
    // covert strengthening — use theorem_split / re_derive for that).
    if (value.action_kind === "statement_correction") {
      if (!value.proposed_restatement?.statement?.trim()) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["proposed_restatement"],
          message: "action_kind=statement_correction requires proposed_restatement.statement",
        });
      }
      if (value.route !== "stage_0") {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["route"],
          message: "action_kind=statement_correction requires route=stage_0",
        });
      }
      if (value.proposed_assumption) {
        ctx.addIssue({
          code: z.ZodIssueCode.custom,
          path: ["proposed_assumption"],
          message:
            "statement_correction must not carry a proposed_assumption — a correction restates the same object unconditionally; if a new hypothesis is needed use theorem_split",
        });
      }
    }
    if (value.proposed_restatement && value.action_kind !== "statement_correction") {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["proposed_restatement"],
        message: "proposed_restatement is only valid with action_kind=statement_correction",
      });
    }
  });

export const stageOutputSchema = z
  .object({
    status: z.string().optional(),
    message: z.string().optional(),
    artifacts: z.array(z.string()).optional(),
    missing_items: z
      .array(
        z.object({
          kind: z.string(),
          name_suggestion: z.string(),
          purpose: z.string(),
          why_substantial: z.string(),
          nl_artifact_reference: z.string().optional(),
          suggested_location: z.string().optional(),
        }),
      )
      .optional(),
    assumption_table_markdown: z.string().optional(),
    /** Paper-scoped manifest: per-theorem lean declaration names. */
    theorems: z
      .array(
        z.object({
          theorem_local_id: z.string(),
          lean_decl_name: z.string().optional(),
        }),
      )
      .optional(),
  })
  .passthrough();

/**
 * Extract the first valid JSON object from `text`.
 *
 * Walks brace depth (respecting strings + escapes) to find each candidate
 * balanced `{...}` slice, then attempts `JSON.parse` on it. Returns the first
 * slice that parses successfully. This handles three real-world layouts:
 *
 *   (a) Pure JSON output (the common case).
 *   (b) Prose-then-JSON ("Reading the .md confirms…\n{\"route\":...}").
 *   (c) Prose containing accidental balanced braces in code-spans
 *       (e.g. a backticked Lean set ``{Z=z_l}`` or a ``{x | P x}`` builder)
 *       FOLLOWED by the real JSON body. Without try-and-retry, the legacy
 *       extractor latched onto the first balanced pair from the prose and
 *       failed `JSON.parse` at position 1 (unquoted key), masking a perfectly
 *       valid JSON object further down. This was the recurring
 *       "model output did not contain a JSON object" /
 *       "Expected property name or '}' in JSON at position 1" failure.
 *
 * Falls back to a first-`{` / last-`}` slice only if no balanced parse
 * succeeds, which preserves behavior for outputs with stray closing braces.
 */
export function extractJsonObject(text: string): unknown {
  let firstParseError: unknown = null;

  const fences = Array.from(text.matchAll(/```([^\n`]*)\n?([\s\S]*?)```/g));
  const jsonFences = fences.filter((m) => m[1].trim().toLowerCase().startsWith("json"));
  const otherFences = fences.filter((m) => !m[1].trim().toLowerCase().startsWith("json"));
  // why: scan the raw text in DOCUMENT ORDER FIRST, so the FIRST valid JSON object wins — a real bare
  // object (e.g. `{"route":"stage_2"}`) must NOT be overridden by a later ```json example/diagnostic
  // the model appended. Accidental prose braces (`{x | P x}`) fail JSON.parse and are skipped, so the
  // real object further down is still found. Fenced contents are only a fallback when the document-order
  // scan finds nothing parseable (e.g. JSON that is only well-formed once the fence is stripped).
  const candidates = [text, ...jsonFences.map((m) => m[2]), ...otherFences.map((m) => m[2])];

  for (const candidate of candidates) {
    let cursor = 0;
    // Every top-level balanced object this candidate yields. Collected rather than
    // returned-on-first so that an ambiguous output (narration object + real payload)
    // is VISIBLE in the transcript instead of silently resolving to whichever came
    // first in document order.
    const parsed: unknown[] = [];
    // Try every balanced `{...}` starting at successive `{` positions; accept
    // the first one that JSON.parse can read. This survives prose with
    // accidentally balanced curly-brace runs before the real JSON.
    while (true) {
      const start = candidate.indexOf("{", cursor);
      if (start === -1) break;
      const balancedEnd = findBalancedObjectEnd(candidate, start);
      if (balancedEnd === -1) {
        // This object never closes — the output is TRUNCATED (a watchdog kill mid-write
        // is the usual cause). Every `{` after this point is therefore nested inside it,
        // so continuing the scan can only return a fragment of the payload we failed to
        // read: `{"a":1,"b":{"c":2}` used to yield `{"c":2}`. Stop scanning this
        // candidate so truncation surfaces as a parse failure instead of a plausible
        // wrong object.
        if (firstParseError === null) {
          firstParseError = new Error(
            `model output contains an unterminated JSON object at offset ${start} (truncated response)`,
          );
        }
        break;
      }
      const slice = candidate.slice(start, balancedEnd + 1);
      try {
        parsed.push(JSON.parse(slice));
        // Skip PAST this object, not one character into it.
        //
        // `cursor = start + 1` was the load-bearing defect: on a top-level parse
        // failure the walk re-entered the object it had just rejected and returned
        // one of its NESTED sub-objects. A payload with one bad LaTeX escape
        // (`"\sum"` is not a valid JSON escape) silently degraded to an inner
        // fragment like `{"cite_id":"C1"}` — which then validated, because
        // `stageOutputSchema` is all-optional plus passthrough. Advancing past the
        // object makes a failed payload stay failed.
        cursor = balancedEnd + 1;
      } catch (err) {
        if (firstParseError === null) firstParseError = err;
        cursor = balancedEnd + 1;
      }
    }
    if (parsed.length > 0) {
      if (parsed.length > 1) {
        // Behavior-preserving (first wins), but no longer silent. A model that
        // narrates before emitting — or echoes the prompt's own
        // `{"status":"completed",...}` example line — produces exactly this, and the
        // echoed template would otherwise be accepted as a genuine completion.
        console.error(
          `[extractJsonObject] AMBIGUOUS output: ${parsed.length} top-level JSON objects found; ` +
            `using the first. Keys per object: ` +
            parsed.map((o) => `{${Object.keys(o as object).slice(0, 6).join(",")}}`).join(" | "),
        );
      }
      return parsed[0];
    }
    // Legacy fallback: first `{` to last `}`. Rarely useful when balanced
    // parsing already failed, but kept for parity with the prior behavior on
    // malformed outputs that nonetheless contain a coarsely-recoverable body.
    const firstStart = candidate.indexOf("{");
    const lastEnd = candidate.lastIndexOf("}");
    if (firstStart !== -1 && lastEnd > firstStart) {
      try {
        return JSON.parse(candidate.slice(firstStart, lastEnd + 1));
      } catch (err) {
        if (firstParseError === null) firstParseError = err;
      }
    }
  }
  if (firstParseError) throw firstParseError;
  throw new Error("model output did not contain a JSON object");
}

function findBalancedObjectEnd(text: string, start: number): number {
  let depth = 0;
  let inString = false;
  let escape = false;
  for (let i = start; i < text.length; i++) {
    const ch = text[i];
    if (inString) {
      if (escape) {
        escape = false;
      } else if (ch === "\\") {
        escape = true;
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }
    if (ch === '"') {
      inString = true;
      continue;
    }
    if (ch === "{") {
      depth++;
    } else if (ch === "}") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}
