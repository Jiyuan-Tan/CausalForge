/**
 * Typed graph schema for the CausalSmith study substrate.
 *
 * Source of truth: spec §4.1 (node fields), §4.2 (edges), §4.3 (IDs).
 *
 * Every node carries `schema_version: 2`. The bump from 1 → 2 introduced
 * the `Theorem` node, the `decomposes_into` edge kind, and tier-1 fields
 * on `Insight` (`background`, `theorems`, `extensions`, `verification_status`).
 * Existing v1 graphs must be passed through `tools/bin/migrate_v1_to_v2.ts`
 * before they will load.
 */

export const SCHEMA_VERSION = 2 as const;

/** Edge kinds enumerated in spec §4.2. */
export type EdgeKind =
  | "cites"
  | "extends"
  | "introduces"
  | "instantiates"
  | "relies_on"
  | "relaxes"
  | "discusses"
  | "suggests"
  | "closes"
  | "decomposes_into";

export type NodeTypeName =
  | "paper"
  | "insight"
  | "method"
  | "assumption"
  | "note"
  | "open_question"
  | "study_target"
  | "banked_theorem"
  | "theorem"
  | "next_study_recommendation";

/** Optional structural lineage shared by several node types. */
export interface NodeLineage {
  parent_run_id?: string;
  parent_kind?: "research" | "study";
}

// ---------------------------------------------------------------------------
// Paper (spec §4.1)
// ---------------------------------------------------------------------------

/** Stage 5b item 1 — annotated citation entry. */
export interface AnnotatedCite {
  paper_id: string;
  /** Free-text: which Insight / phenomenon / theorem this cite supports. */
  used_for: string;
  /** Free-text: why the citation is load-bearing (1-2 sentences). */
  rationale: string;
}

export interface Paper {
  schema_version: 2;
  paper_id: string;
  title: string;
  arxiv_id?: string;
  doi?: string;
  year: number;
  citations?: number;
  source: "seed" | "extension";
  added_by?: string;
  /** Optional supersession pointer. */
  supersedes?: string;
  // Outbound edges
  /** Paper -> Paper. Stage 5b: each entry may be either a plain paper_id
   * string OR an AnnotatedCite. The graph index accessor handles both shapes. */
  cites?: Array<string | AnnotatedCite>;
  introduces?: string[]; // Paper -> Insight
}

// ---------------------------------------------------------------------------
// Insight (spec §4.1)
// ---------------------------------------------------------------------------

/**
 * Verification status of an Insight, denormalized from the statuses of the
 * Theorems it `decomposes_into`. Recomputed by Stage S5.
 *
 * Derivation rule:
 *   - all theorems formalization_verified → "all_verified"
 *   - all theorems formalization_failed or substrate_blocked → "all_failed"
 *   - mix of verified and not-yet-verified → "partially_verified"
 *   - no theorems verified yet (initial state) → "unverified"
 */
export type InsightVerificationStatus =
  | "unverified"
  | "partially_verified"
  | "all_verified"
  | "all_failed";

export interface Insight {
  schema_version: 2;
  insight_id: string;
  title: string;
  summary: string;
  /** Three-part framing for the Insight; populated at S2 commit time. */
  background: {
    why_matters: string;
    prior_approach: string;
    gap: string;
  };
  /** Optional final-paragraph synthesis describing how the Insight closes the gap. */
  closing_synthesis?: string;
  /** Theorem ids this Insight decomposes into. */
  theorems: string[];
  /** OpenQuestion ids this Insight suggests as natural extensions. */
  extensions: string[];
  /** Denormalized verification status. See InsightVerificationStatus docs. */
  verification_status: InsightVerificationStatus;
  /** Stage 5b item 2 — agent-proposed connections to other Insights/Methods. */
  connections?: Array<{ kind: string; target_id: string; rationale: string }>;
  /** Stage 5b item 7 — minimal worked example exhibiting the Insight. */
  minimal_example?: { setup: string; computation: string; observation: string };
  introduced_by?: string; // Paper id; mirror of Paper.introduces
  supersedes?: string;
  // Outbound edges
  extends?: string[]; // Insight -> Insight
  instantiates?: string[]; // Insight -> Method
  relies_on?: string[]; // Insight -> Assumption
  relaxes?: string[]; // Insight -> Assumption
}

// ---------------------------------------------------------------------------
// Method (spec §4.1)
// ---------------------------------------------------------------------------

export interface Method {
  schema_version: 2;
  method_id: string;
  /** Canonical short name used by findMethodByName. */
  name: string;
  description: string;
  supersedes?: string;
}

// ---------------------------------------------------------------------------
// Assumption (spec §4.1)
// ---------------------------------------------------------------------------

export interface Assumption {
  schema_version: 2;
  assumption_id: string;
  /** Canonical short name used by findAssumptionByName. */
  name: string;
  description: string;
  supersedes?: string;
}

// ---------------------------------------------------------------------------
// Note (spec §4.1)
// ---------------------------------------------------------------------------

export type NoteKind =
  | "area_survey"
  | "lean_pattern"
  | "estimator_taxonomy"
  | "open_problem"
  | "scratch";

export interface Note {
  schema_version: 2;
  note_id: string;
  kind: NoteKind;
  title: string;
  body: string;
  /** Source refs, e.g. `[autoid:...]` markers. */
  source_refs?: string[];
  supersedes?: string;
  lineage?: NodeLineage;
  // Outbound edges
  discusses?: string[]; // Note -> Method | Assumption | Insight | Paper

  // ---------------------------------------------------------------------------
  // Substrate-handoff fields (populated only on Notes minted by --from-substrate)
  // ---------------------------------------------------------------------------
  /**
   * The verbatim `missing_concept` string from the substrate_request that
   * triggered this learn run. Lets `substrate_provide` and `--retry-blocked`
   * find the Note by concept without parsing the body. Set at
   * `--from-substrate` dispatch time in the retired study-pipeline CLI.
   */
  substrate_concept?: string;
  /** Tier copied from the source substrate_request. */
  substrate_tier?: "mathlib_reexport" | "mathlib_adjacent" | "genuinely_new";
  /** Theorem ids whose substrate_requests this Note fulfills. */
  fulfills_substrate_for?: string[];
  /**
   * Marker stamped by `tools/bin/substrate_provide.ts` once a human (or a
   * future auto-builder) has actually written the corresponding Lean
   * substrate. `--retry-blocked` reads this to decide which
   * `substrate_blocked` Theorems are ready to re-dispatch.
   */
  substrate_provided?: {
    /** Path to the Lean file that contains the new substrate, relative to the Causalean repo root. */
    lean_path: string;
    provided_at: string; // ISO8601
    /** Optional human-supplied note about how the substrate was verified (e.g. `lake build` clean, signed off). */
    verified?: boolean;
    note?: string;
  } | null;
}

// ---------------------------------------------------------------------------
// OpenQuestion (spec §4.1)
// ---------------------------------------------------------------------------

export type OpenQuestionStatus =
  | "open"
  | "in_progress"
  | { closed_by: string } // BankedTheorem id
  | "abandoned";

export interface OpenQuestion {
  schema_version: 2;
  open_question_id: string;
  title: string;
  body: string;
  status: OpenQuestionStatus;
  /** Method this question seeds from (scalar — not an outbound edge array). */
  seed_method_id?: string;
  supersedes?: string;
  lineage?: NodeLineage;
  /**
   * Provenance pointer back to the causalsmith run that minted this OQ.
   *
   * Two origin paths:
   *   - `origin: "failed_theorem"` — auto-minted from a failed `theorems[]`
   *     entry at bank time; `theorem_local_id` identifies the failed theorem.
   *   - `origin: "proposal_open_ended_question"` — auto-minted at Stage 0
   *     short-circuit time when the D-1.2 proposal carried only Open-ended
   *     Question(s) in §8 with no Conjecture to derive; `oq_local_label` is
   *     the `oeq:<slug>` label from the proposal LaTeX.
   *
   * `origin` is optional for backward compatibility with OQs minted before the
   * field was introduced; treat absent `origin` as `"failed_theorem"` when
   * `theorem_local_id` is present.
   *
   * Absent on hand-authored OQs.
   */
  minted_from?: {
    qid: string;
    spec: string;
    origin?: "failed_theorem" | "proposal_open_ended_question";
    /** Present iff origin = "failed_theorem". */
    theorem_local_id?: string;
    /** Present iff origin = "proposal_open_ended_question"; the `oeq:<slug>` label slug. */
    oq_local_label?: string;
    lean_file_relpath?: string;
    failure_reason?: string;
    /** Path of the proposal .tex (proposal_open_ended_question only). */
    proposal_path?: string;
  };
  // Outbound edges
  suggests?: string[]; // OpenQuestion -> Insight | Note (reverse: who suggested it)
}

// ---------------------------------------------------------------------------
// StudyTarget (spec §4.1, with created_at per R4 mitigation)
// ---------------------------------------------------------------------------

export type StudyTargetStatus =
  | "pending"
  | "in_progress"
  | "promoted"
  | "rejected"
  | "abandoned"
  | "dismissed"
  | { acted_on: string };

export interface StudyTarget {
  schema_version: 2;
  study_target_id: string;
  title: string;
  rationale: string;
  status: StudyTargetStatus;
  /** ISO timestamp; flag old pending targets in Phase 4. */
  created_at: string;
  supersedes?: string;
  lineage?: NodeLineage;
  // Phase 4 additions (all optional, backward compatible).
  /** qid of the research run that proposed this target via CHECKPOINT_NEXT. */
  from_qid?: string;
  /** Compact summary of the originating run's state when proposed. */
  from_run_state?: string;
  /** Plain-text gap description used to bias source/paper selection. */
  gap_description?: string;
  /** Keywords used by the directed Stage S-1 to bias paper/source ranking. */
  suggested_keywords?: string[];
  /** Optional registered-source ref (resolved by resolveSource). */
  suggested_source?: string;
}

/** Draft shape used by propose_next / checkpoint_next.md Option 2/3 payloads.
 * Missing `study_target_id` (minted at commit time) and `created_at`
 * (stamped at commit time). */
export interface StudyTargetDraft {
  title: string;
  rationale: string;
  from_qid: string;
  from_run_state?: string;
  gap_description?: string;
  suggested_keywords?: string[];
  suggested_source?: string;
  lineage?: NodeLineage;
}

// ---------------------------------------------------------------------------
// BankedTheorem (spec §4.1, §4.3)
// ---------------------------------------------------------------------------

export interface BankedTheorem {
  schema_version: 2;
  /** `<qid>_<spec>` per spec §4.3. */
  bt_id: string;
  qid: string;
  spec: string;
  /** Method ids; populated by Phase 2 canonicalization (Phase 1 leaves empty). */
  instantiates: string[];
  /** Assumption ids; populated by Phase 2 canonicalization (Phase 1 leaves empty). */
  uses: string[];
  /** Optional OpenQuestion id (Phase 1 leaves undefined). */
  derived_from?: string;
  /** Outbound edge for closing an OpenQuestion (Phase 1 leaves undefined). */
  closes?: string[];
  lineage?: NodeLineage;
}

// ---------------------------------------------------------------------------
// Theorem (spec §4.1 — added in schema v2)
// ---------------------------------------------------------------------------

/**
 * Verification status of a Theorem. Default `"unverified"` at S2 commit.
 * Flipped by S5 reconcile when a BankedTheorem mints (`"formalization_verified"`)
 * or a failure-Note is recorded (`"formalization_failed"` or
 * `"substrate_blocked"`).
 */
export type TheoremVerificationStatus =
  | "unverified"
  | "formalization_verified"
  | "formalization_failed"
  | "substrate_blocked";

/** Stage 5a item 3 — substrate gap surfaced by Pass B. */
export interface SubstrateRequest {
  missing_concept: string;
  location_in_proof: string;
  /** Theorem ids whose proofs are blocked by this gap (within-Insight only). */
  blocks: string[];
  tier: "mathlib_reexport" | "mathlib_adjacent" | "genuinely_new";
}

/** Stage 5a item 4 — pre-formalization forecast emitted by Pass B. */
export interface FormalizationForecast {
  /** 0..1 */
  confidence: number;
  /** Free-text predictions of where formalization will struggle. */
  expected_failure_points: string[];
  rationale: string;
}

/** Stage 5a — S5-filled record of what actually happened during dispatch. */
export interface FormalizationActual {
  succeeded: boolean;
  /** Empty when succeeded === true. */
  actual_failure_points: string[];
  /** Brief: what causalsmith stderr / failure-Note body said. */
  rationale: string;
}

/** Stage 5a — diff between forecast and actual. Only emitted on mismatch. */
export interface ForecastMiss {
  confidence_calibration:
    | "over_confident"
    | "under_confident"
    | "well_calibrated";
  predicted_but_didnt_happen: string[];
  happened_but_unpredicted: string[];
}

export interface Theorem {
  schema_version: 2;
  theorem_id: string;
  parent_insight_id: string;
  setup: string;
  statement: string;
  /** Null when the parent Insight was produced in --skim mode. */
  proof_sketch: string | null;
  /** Null when the parent Insight was produced in --skim mode. */
  proof_punchline: string | null;
  /** Theorem ids this theorem cites; constrained to siblings within the same Insight. */
  cites_theorems: string[];
  prerequisites: string[];
  candidate_specializations: string[];
  /** BankedTheorem ids that instantiate this Theorem; filled by S5 (Stage 4). */
  banked_by: string[];
  verification_status: TheoremVerificationStatus;
  /** Stage 5a item 3 — substrate gaps surfaced by Pass B (or S5 classifier). */
  substrate_requests?: SubstrateRequest[];
  /** Stage 5a item 4 — pre-formalization forecast emitted by Pass B. */
  formalization_forecast?: FormalizationForecast;
  /** Stage 5a — record of what actually happened during dispatch. Append-only. */
  formalization_actual?: FormalizationActual;
  /** Stage 5a — forecast-vs-actual diff. Only emitted on mismatch. Append-only. */
  forecast_miss?: ForecastMiss;
  lineage?: NodeLineage;
}

// ---------------------------------------------------------------------------
// NextStudyRecommendation (Stage 5b item 5)
// ---------------------------------------------------------------------------

export interface NextStudyRecommendation {
  schema_version: 2;
  next_study_id: string;
  paper_ref?: string;
  rationale: string;
  expected_value: "high" | "medium" | "low";
  source_run_id: string;
  source_insight_id?: string;
  /** ISO timestamp set when consumed by the retired `--extend` flow or similar. */
  consumed_at?: string;
}

// ---------------------------------------------------------------------------
// Discriminated union
// ---------------------------------------------------------------------------

export type StudyNode =
  | Paper
  | Insight
  | Method
  | Assumption
  | Note
  | OpenQuestion
  | StudyTarget
  | BankedTheorem
  | Theorem
  | NextStudyRecommendation;

/**
 * Mapping from a node's discriminating id-field name to its NodeTypeName.
 * Inspect this rather than chaining if/else.
 */
const ID_FIELD_TO_TYPE: ReadonlyArray<[string, NodeTypeName]> = [
  ["paper_id", "paper"],
  ["insight_id", "insight"],
  ["method_id", "method"],
  ["assumption_id", "assumption"],
  ["note_id", "note"],
  ["open_question_id", "open_question"],
  ["study_target_id", "study_target"],
  ["bt_id", "banked_theorem"],
  ["theorem_id", "theorem"],
  ["next_study_id", "next_study_recommendation"],
];

export function nodeTypeOf(n: StudyNode): NodeTypeName {
  const bag = n as unknown as Record<string, unknown>;
  for (const [field, type] of ID_FIELD_TO_TYPE) {
    if (bag[field] !== undefined) return type;
  }
  throw new Error(
    `nodeTypeOf: unrecognized node shape (no known id field) — keys=${Object.keys(bag).join(",")}`,
  );
}

export function nodeIdOf(n: StudyNode): string {
  const bag = n as unknown as Record<string, unknown>;
  for (const [field] of ID_FIELD_TO_TYPE) {
    const v = bag[field];
    if (typeof v === "string") return v;
  }
  throw new Error(`nodeIdOf: no id field on node — keys=${Object.keys(bag).join(",")}`);
}

export function nodePath(type: NodeTypeName, id: string, studyDir: string): string {
  // Inline path.join to avoid a dependency from a pure types module; callers
  // already import `node:path` if they need OS-specific joins.
  return `${studyDir}/nodes/${type}/${id}.json`;
}

/**
 * Outbound edge accessor table: for a given node type, the list of
 * (field-name, edge-kind) pairs that should be projected forward.
 * Used by `shared/graph.ts#buildIndex` to derive the adjacency.
 */
export const OUTBOUND_EDGES: Record<NodeTypeName, ReadonlyArray<{ field: string; kind: EdgeKind }>> = {
  paper: [
    { field: "cites", kind: "cites" },
    { field: "introduces", kind: "introduces" },
  ],
  insight: [
    { field: "extends", kind: "extends" },
    { field: "instantiates", kind: "instantiates" },
    { field: "relies_on", kind: "relies_on" },
    { field: "relaxes", kind: "relaxes" },
    { field: "theorems", kind: "decomposes_into" },
    { field: "extensions", kind: "suggests" },
  ],
  method: [],
  assumption: [],
  note: [{ field: "discusses", kind: "discusses" }],
  open_question: [{ field: "suggests", kind: "suggests" }],
  study_target: [],
  banked_theorem: [
    { field: "instantiates", kind: "instantiates" },
    { field: "uses", kind: "relies_on" },
    { field: "closes", kind: "closes" },
  ],
  theorem: [
    { field: "cites_theorems", kind: "decomposes_into" },
    { field: "banked_by", kind: "instantiates" },
  ],
  next_study_recommendation: [],
};

/**
 * A single structured reviewer finding (relocated from study/checkpoint.ts so the
 * causalsmith formalization layer can depend on it without the study pipeline).
 */
export interface Finding {
  field:
    | "setup"
    | "statement"
    | "proof_sketch"
    | "proof_punchline"
    | "cites_theorems"
    | "closing_synthesis"
    | "summary"
    | "background"
    | "method_mentions"
    | "assumption_mentions";
  code: string;
  one_line: string;
}
