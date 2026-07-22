import { MODELS } from "./models.js";

export const STAGE_ORDER = [
  "-1.1",
  "-1.2",
  "-0.5",
  "0",
  "0.5",
  "1",
  "1.5",
  "2",
  "2.5",
  "3",
  "3.5",
  "4",
  "5",
] as const;

export const MODEL_PLAN = {
  // D-1.1 literature scout: search/read and gap synthesis on the kernel tier.
  // Env: CAUSALEAN_MODEL_CODEX_KERNEL.
  stageNeg1_1_litReview: { runner: "codex", model: MODELS.codexKernel, effort: "high" },
  // Stage -1.2 draft is the only producer with a runtime-switchable runner
  // (--proposer claude|codex). Both candidates are listed; `default` picks one
  // when --proposer is absent. See workers/draftAdapter.ts.
  stageNeg1_2_draft: {
    default: "codex",
    codex: { runner: "codex", model: MODELS.codexKernel, effort: "high" },
    claude: { runner: "claude", model: MODELS.claudeMain },
  },
  // D-0.5 proposal review. On the mechanical tier (gpt-5.6-terra) per operator call;
  // was codexKernel. Kept at `high` effort. Env: CAUSALEAN_MODEL_CODEX_MECH.
  stageNeg0_5_review: { runner: "codex", model: MODELS.codexMechanical, effort: "high" },
  // Shared "mechanical / clerical" codex tier (default gpt-5.6-terra, env CAUSALEAN_MODEL_CODEX_MECH).
  // NOT a stage — three consumers each pass `MODEL_PLAN.mechanicalTier.model`:
  // stage_neg1_2_proto_core (proposal typed-core author), stage0_5_core (the D0-solve loop's
  // per-round review), stage0_R_core (its directed revise). The HARD D0 derivation is
  // `stage0_solve` on the kernel tier, not this. (Formerly `stage0_0`, named after the removed
  // legacy D0.0 setup pass — see doc/API.md §4.0.)
  mechanicalTier: { runner: "codex", model: MODELS.codexMechanical, effort: "high" },
  // Typed D0-SOLVE (runStage0Solve) does the HARD derivation in one stage. It must
  // run at the kernel-math tier; on gpt-5.4 it missed a standard step (clip =
  // 1-Lipschitz projection ⟹ compare ê_q to the TRUE-clipped e_q, not to ê) that
  // gpt-5.5 cleared, and punted a derivable upper bound to an open obligation.
  stage0_solve: { runner: "codex", model: MODELS.codexKernel, effort: "xhigh" },
  // Stage 0.5 is SPLIT into two referees that fill disjoint regions of ONE
  // ReviewResult — no TS stitch:
  //   D0.5.1 `stage0_5_math` — the correctness leg, runs FIRST. A clean-context
  //     referee that RE-DERIVES the note's load-bearing steps from definitions
  //     and diffs its term list against the note's (reproduce, don't
  //     check-along). Isolated from the tiering / novelty / JSON overhead that
  //     diluted the old monolith (a rubric-free web model caught a dropped
  //     first-order term the medium monolith missed). Emits a lean correctness
  //     verdict; does NOT decide accept/revise/reject. Runs at `high` (dialed
  //     from xhigh for cost; the focused reproduce-don't-check protocol caught
  //     the load-bearing omissions at `high` in live validation).
  //   D0.5.2 `stage0_5`      — structure + novelty + tier + journal + routing,
  //     runs SECOND. ADOPTS D0.5.1's injected correctness verdict and makes the
  //     single final accept/revise/reject decision. `high` suffices — it no
  //     longer re-derives math.
  stage0_5: { runner: "codex", model: MODELS.codexKernel, effort: "high" },
  stage0_5_math: { runner: "codex", model: MODELS.codexKernel, effort: "high" },
  // D0.5.G — the COLD general referee. Runs THIRD, only after D0.5.2 reaches
  // ACCEPT and a novelty target is set. Rubric-free by design (anti-Goodhart):
  // it is given only the paper + plain tier definitions, NOT the flagship rubric
  // the producer optimizes against, so it reproduces the "paste into a fresh
  // model, does it actually clear the bar?" check. Emits an independent tier +
  // salvageability; below-floor → re-derive (salvageable) or halt (not). `high`.
  stage0_5_general: { runner: "codex", model: MODELS.codexKernel, effort: "high" },
  stage1: { runner: "claude", model: MODELS.claudeMain },
  // F1.5 review (via REVIEW_MODEL_PLAN["1.5"]): plan DEPTH + REUSE + statement-vs-math
  // fidelity audit. On the mechanical tier (gpt-5.6-terra) per operator call; was
  // codexKernel/medium — effort bumped medium→high to offset the cheaper model.
  // Env: CAUSALEAN_MODEL_CODEX_MECH.
  stage1_5: { runner: "codex", model: MODELS.codexMechanical, effort: "high" },
  stage2: { runner: "codex", model: MODELS.codexKernel, effort: "high" },
  // Compatibility plan for the isolated `review_codex.ts` helper. The live unified
  // F2.5/F4 path is `proof_reviewer.ts::runUnit`, which uses codexKernel with
  // per-target high/medium effort; do not infer its runtime routing from this entry.
  stage2_5: { runner: "codex", model: MODELS.codexMechanical, effort: "medium" },
  // Stages 3/3.5/4 are no-op pass-throughs (the proof-review loop in the F2.5
  // slot owns their work, including statement reconciliation); their old per-stage model configs were removed
  // with the retired split-stage system. No LLM call runs at those slots.
  // F5 (API.md / doc-generation pass): clerical → mechanical tier (gpt-5.6-terra).
  stage5: { runner: "codex", model: MODELS.codexMechanical, effort: "medium" },
} as const;

/**
 * Display/CLI-facing stage IDs with D (discovery) / F (formalization) prefixes.
 * Includes umbrella stages AND first-class substage halt points (F3.group/fill,
 * F4.codex/claude/d — not yet wired). The active typed D0 has no substages (the
 * legacy D0.0/k/M per-conjecture split was removed, see doc/API.md §4.0). Used by
 * `--stop-after`, log strings, and
 * cross-pipeline coordination. The internal `Stage` literal in STAGE_ORDER
 * stays in bare-number form so on-disk state JSON keys remain stable; this
 * type is purely the display/wire surface.
 */
export const STAGE_HALT_IDS = [
  "D-1.1",
  "D-1.2",
  "D-0.5",
  "D0",
  "D0.5",
  "F1",
  "F1.5",
  "F2",
  "F2.5",
  "F3",
  "F3.group",
  "F3.fill",
  "F3.5",
  "F4",
  "F4.codex",
  "F4.claude",
  "F4.d",
  "F5",
] as const;

export type StageHaltId = (typeof STAGE_HALT_IDS)[number];

/**
 * Maps the internal `Stage` (bare-number) → new umbrella `StageHaltId`.
 * One-to-one for umbrella stages; substages don't appear here (they're not
 * in STAGE_ORDER).
 */
export const STAGE_TO_HALT_ID: Record<
  (typeof STAGE_ORDER)[number],
  StageHaltId
> = {
  "-1.1": "D-1.1",
  "-1.2": "D-1.2",
  "-0.5": "D-0.5",
  "0": "D0",
  "0.5": "D0.5",
  "1": "F1",
  "1.5": "F1.5",
  "2": "F2",
  "2.5": "F2.5",
  "3": "F3",
  "3.5": "F3.5",
  "4": "F4",
  "5": "F5",
};

/**
 * Translation map: new umbrella StageHaltId → internal Stage. Used at the
 * CLI / dispatch boundary to bridge the new prefixed surface to the
 * existing pipeline halt mechanism. Substage halt IDs (F3.group/fill,
 * F4.codex/claude/d) are intentionally absent: substage halts are not yet
 * wired into runPipeline (Phase 3 work).
 */
export const STAGE_HALT_ID_TO_INTERNAL: Partial<
  Record<StageHaltId, (typeof STAGE_ORDER)[number]>
> = {
  "D-1.1": "-1.1",
  "D-1.2": "-1.2",
  "D-0.5": "-0.5",
  D0: "0",
  "D0.5": "0.5",
  F1: "1",
  "F1.5": "1.5",
  F2: "2",
  "F2.5": "2.5",
  F3: "3",
  "F3.5": "3.5",
  F4: "4",
  F5: "5",
};

/**
 * Deprecated → canonical mapping for the CLI compat layer.
 *
 * Accepts the old bare-number forms (`"3"`, `"-0.5"`, `"0"`) AND legacy
 * substage spellings (e.g. `"3.group"`, `"3.fill"`, `"4d"`, `"4.codex"`,
 * `"4.claude"`). CLI callers should look
 * up `--stop-after` values here BEFORE validating against STAGE_HALT_IDS;
 * if the input matches a key here, emit a stderr deprecation warning and
 * use the mapped value.
 */
export const LEGACY_STAGE_ALIASES: Record<string, StageHaltId> = {
  "-1.1": "D-1.1",
  "-1.2": "D-1.2",
  "-0.5": "D-0.5",
  "0": "D0",
  "0.5": "D0.5",
  "1": "F1",
  "1.5": "F1.5",
  "2": "F2",
  "2.5": "F2.5",
  "3": "F3",
  "3.group": "F3.group",
  "3.fill": "F3.fill",
  "3.5": "F3.5",
  "4": "F4",
  "4.codex": "F4.codex",
  "4.claude": "F4.claude",
  "4.d": "F4.d",
  "4d": "F4.d",
  "5": "F5",
};

/**
 * Format an internal Stage (and optional substage marker) as the new
 * display ID. Use this in log strings instead of interpolating raw stage
 * literals. For substage logging, pass the substage suffix exactly as it
 * appears in STAGE_HALT_IDS (e.g. `"group"` for F3.group, `"d"` for F4.d).
 *
 * Examples:
 *   formatStageLabel("3")           → "F3"
 *   formatStageLabel("3", "group")  → "F3.group"
 *   formatStageLabel("4", "d")      → "F4.d"
 *   formatStageLabel("-0.5")        → "D-0.5"
 */
export function formatStageLabel(
  stage: (typeof STAGE_ORDER)[number],
  substage?: string,
): StageHaltId {
  const base = STAGE_TO_HALT_ID[stage];
  if (substage === undefined) return base;
  const composed = `${base}.${substage}` as StageHaltId;
  if (!(STAGE_HALT_IDS as readonly string[]).includes(composed)) {
    throw new Error(
      `formatStageLabel: ${stage} + substage="${substage}" → ${composed} is not in STAGE_HALT_IDS`,
    );
  }
  return composed;
}

/**
 * Resolve a user-supplied stage token (e.g. from `--stop-after`) into a
 * canonical StageHaltId. Returns `null` if the token is not recognized.
 *
 * The returned `deprecated` flag is true when the input matched
 * LEGACY_STAGE_ALIASES (not STAGE_HALT_IDS directly) — callers should emit
 * a deprecation warning in that case.
 */
export function resolveStageHaltId(
  token: string,
): { id: StageHaltId; deprecated: boolean } | null {
  if ((STAGE_HALT_IDS as readonly string[]).includes(token)) {
    return { id: token as StageHaltId, deprecated: false };
  }
  const mapped = LEGACY_STAGE_ALIASES[token];
  if (mapped !== undefined) {
    return { id: mapped, deprecated: true };
  }
  return null;
}

/**
 * Cluster-keyed reuse hints. Each list names Causalean / CausalSmith primitives
 * the scaffolder should prefer over re-deriving from scratch. The brief
 * injects exactly one list (selected by `state.lean_subdir`'s cluster), or
 * the union when the cluster cannot be determined.
 *
 *   panel     — panel-method substrate in CausalSmith/Panel + Causalean/Panel
 *   exactid   — point-identification estimators in Causalean/PO/ID/Exact
 *   partialid — bounds / sensitivity primitives in Causalean/PO/ID/Partial
 *   stat      — estimation-and-inference substrate in Causalean/Stat + Causalean/Estimation
 *               (minimax / efficiency / empirical-process / concentration / GMM)
 *
 * Wildcards (`*`) signal "see this module's API.md section for the full list."
 */
export const REUSE_LIST_BY_CLUSTER = {
  panel: [
    "Cells",
    "ip",
    "tildeX",
    "H_twfe",
    "Q_XX",
    "thetaHat",
    "RankCondition",
    "IIDBernoulli",
    "SwitchOn",
    "DistributedLag",
    "CleanHistoryTWFE",
    "SaturatedHistory",
    "theorem2_1_general_projection*",
  ],
  exactid: [
    // Causalean/PO/ID/Exact/
    "Identifiable",
    "Overlap",
    "Adjustment",
    "Backdoor.*",
    "Frontdoor.*",
    "ATE.*",
    "DID.*",
    "DTR.*",
    "LATE.*",
    // Theorem-local assumption bundles + Causalean/SCM/ID/GraphicalThms/
    "*.Assumptions",
    "GraphicalThms.*",
    // Causalean/PO/ + Causalean/SCM/Do/ + Causalean/Graph/
    "PO.*",
    "SCM.Do.*",
    "Graph.SWIG.*",
    "SWIGGraph",
  ],
  partialid: [
    // Causalean/PO/ID/Partial/
    "POManskiIVSystem",
    "Manski.Setup.*",
    "Manski.NonAsp.*",
    "manski_bounds_ATE",
    "lowerBound1",
    "upperBound1",
    "lowerBound0",
    "upperBound0",
    "ciSup_lowerBound1_le_integral_Y1",
    "integral_Y1_le_ciInf_upperBound1",
    "Manski.MTR.*",
    "Manski.MTS.*",
    "Manski.MIV.*",
    "Manski.Combined.*",
    "BalkePearl.*",
    "Lee.*",
    "Proxy.*",
    "PartialID.Basic.*",
    // PO substrate Manski/Lee/Proxy build on
    "POSystem",
    "POVar",
    "PO.*",
  ],
  stat: [
    // Causalean/Stat/ — asymptotic & finite-sample inference machinery
    "Minimax.*",
    "CLT.*",
    "Concentration.*",
    "EmpiricalProcess.*",
    "Bootstrap.*",
    "GMM.*",
    "UStatistic.*",
    "MEstimation.*",
    "Quantile.*",
    "Orthogonality.*",
    "SampleSplit.*",
    "Inference.*",
    // Causalean/Estimation/ — causal-estimand estimation and inference theory
    "Efficiency.*",
    "StructureAgnostic.*",
    "OrthogonalMoments.*",
    "OSL.*",
    "NPIV.*",
    "GaussMarkov.*",
    "CATE.*",
    "ATE.*",
    "ATT.*",
  ],
  experimentation: [
    // Causalean/Experimentation/DesignBased/ — paper-agnostic randomization-inference substrate
    "FiniteDesign",
    "htTotal",
    "htMean",
    "htEffect",
    "E_htTotal",
    "E_htMean",
    "E_htEffect",
    "var_htMean_le",
    "Exposure.*",
    "PotentialOutcome.*",
    "chebyshev",
    "EdgeVarianceBound.*",
    "Var_prod_linear_comb",
    "E_compound_tower",
    "Var_compound_eq_tower",
    // CLT / coverage machinery (IndepSummandsCLT, GaussianCDF, Stein dependency-graph CLT)
    "IndepSummandsCLT.*",
    "GaussianCDF.*",
    "SteinMethod.*",
    "DepGraphCLT.*",
    "LocalDependenceCLT.*",
  ],
  scm: [
    // Causalean/SCM/ID/ — recursive Tian–Shpitser ID, backdoor, frontdoor, c-factorization
    "id_sound.*",
    "idAlgorithm.*",
    "backdoor.*",
    "frontdoor.*",
    "c_component_factorization",
    // Causalean/SCM/Do/ — do/σ-calculus rules + fixing
    "do_rule1",
    "do_rule2.*",
    "do_rule3",
    "SCM.Do.*",
    // Causalean/Graph/ — d-separation, SWIG, c-components, Markov equivalence
    "dSep.*",
    "cComponentSet.*",
    "markovEquiv.*",
    // Part-A substrate (graphical partial-ID + assumptions)
    "CanonicalModel.*",
    "SelectionDiagram.*",
    "SharpnessCertificate.*",
    "Monotonicity.*",
  ],
} as const;

export type ClusterKey = keyof typeof REUSE_LIST_BY_CLUSTER;

/** Substrate-root pointers for the `baseBrief` "Cluster substrate root" line. */
export const CLUSTER_SUBSTRATE_ROOTS: Record<ClusterKey, string[]> = {
  panel: [
    "Causalean/Panel/",
    "Causalean/PO/",
    "CausalSmith/Panel/Regression/",
  ],
  exactid: [
    "Causalean/PO/ID/Exact/",
    "Causalean/SCM/ID/",
    "Causalean/SCM/ID/GraphicalThms/",
    "Causalean/PO/",
    "Causalean/SCM/Do/",
    "Causalean/Graph/SWIG.lean",
  ],
  partialid: [
    "Causalean/PO/ID/Partial/",
    "Causalean/PO/ID/Partial/Manski/",
    "Causalean/PO/",
    "Causalean/SCM/",
  ],
  stat: [
    "Causalean/Stat/",
    "Causalean/Estimation/",
    "Causalean/Estimation/Efficiency/",
    "Causalean/Estimation/StructureAgnostic/",
    "Causalean/PO/",
  ],
  experimentation: [
    "Causalean/Experimentation/DesignBased/",
    "Causalean/Experimentation/",
    "Causalean/PO/",
  ],
  scm: [
    "Causalean/Graph/",
    "Causalean/SCM/Do/",
    "Causalean/SCM/ID/",
    "Causalean/SCM/Model/",
    "Causalean/SCM/PartialID/",
    "Causalean/PO/ID/Partial/",
  ],
};

/**
 * Is `file` inside the substrate of `cluster`? A null/undefined cluster means "unfiltered".
 *
 * Cluster substrates OVERLAP deliberately — `Causalean/PO/` is a root of panel, exactid,
 * partialid, stat AND experimentation — so cluster membership is a per-cluster PREDICATE, never
 * a one-file-one-cluster labelling. Every retrieval tier must filter through this single
 * definition: when the semantic tier used a longest-root-wins label instead, each equal-length
 * tie went to whichever cluster is declared first here, silently hiding the shared PO substrate
 * from all the others.
 *
 * A root ending in `.lean` names one FILE and matches exactly; any other root is a directory
 * prefix and matches itself or anything beneath it.
 */
export function inClusterSubstrate(file: string, cluster: ClusterKey | null | undefined): boolean {
  if (!cluster) return true;
  return CLUSTER_SUBSTRATE_ROOTS[cluster].some((r) => {
    const rr = r.replace(/\/+$/, "");
    if (rr.endsWith(".lean")) return file === rr;
    return file === rr || file.startsWith(rr + "/");
  });
}

/**
 * @deprecated Use `REUSE_LIST_BY_CLUSTER[cluster]` instead. Kept as the
 * panel-cluster value so any unported caller continues to compile, but the
 * brief no longer injects it directly.
 */
export const REUSE_LIST = REUSE_LIST_BY_CLUSTER.panel;
