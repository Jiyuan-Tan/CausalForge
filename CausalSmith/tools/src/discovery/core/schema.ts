// Typed schema for the D0 "core" — the machine-checkable logical skeleton of a
// theorem note (see CausalSmith/doc/research/D0_CORE_REDESIGN.md §3).
//
// `proto_core` (the D-1 subset) and `core` (the D0 extension) share this one
// schema; the difference is enforced by the structural gate (gate.ts), not by a
// separate shape. This file is the only shared-fate artifact between D-1 and D0:
// every stage binds to it, so changing a producer never re-tests a consumer as
// long as the file still validates.
import { z } from "zod";

// SUGGESTED assumption-kind tags (NOT a closed enum — `assumption.kind` is a
// free-form optional string, since the space of real assumption kinds is open).
// These are example labels an author may reuse for skimmability; any other tag is
// equally valid. Nothing consumes `kind` mechanically.
export const SUGGESTED_ASSUMPTION_KINDS = [
  "causal-structural", // consistency, (conditional) ignorability/exchangeability, SUTVA
  "support", // positivity, overlap, boundedness
  "tail-rate", // overlap decay / margin
  "smoothness", // Hölder / boundary extrapolation
  "empirical-process", // Lindeberg / concentration
  "regularity", // measurability / integrability
  "exclusion", // IV exclusion / mean-independence
  "monotonicity", // LATE monotonicity / MTR
  "shape-restriction", // MTR / MTS / MIV
  "sensitivity", // bounded log-odds / marginal sensitivity Λ
  "rank", // rank / identification / Panel basis conditions
] as const;

// `openendedquestion` is the first-class OPEN/CONSTRUCT-question kind: it poses a
// question + a HANDLE (technique + target object), and the SOLVER derives the
// construction and proves the property — the answer is NOT pre-committed (max
// solver freedom). `conjecture` is DEPRECATED (a conjecture pre-commits a
// candidate answer, which suppresses the solver); it is kept in the enum only so
// legacy/typed consumers do not break, and the D-1.2 author must never emit one —
// pose an `oeq:` instead.
export const STATEMENT_KINDS = [
  "theorem",
  "lemma",
  "proposition",
  "openendedquestion",
  "conjecture",
] as const;

const idRe = (prefix: string) => new RegExp(`^${prefix}:[a-z0-9-]+$`);

/** One typed symbol, defined once. `refs` lists OTHER symbols this symbol's
 * `def` references — used by the gate's defined-before-use check (G1). */
export const SymbolSchema = z.object({
  name: z.string(),
  type: z.string(),
  space: z.string().optional(),
  sig: z.string().optional(),
  def: z.string().optional(),
  role: z.string().optional(),
  ref: z.string().optional(), // e.g. a def id, for a class symbol
  refs: z.array(z.string()).optional(),
});

export const StandardTagSchema = z.object({ name: z.string(), cite: z.string() });
export const NovelTagSchema = z.object({ flag: z.literal(true), justification: z.string() });
/** ORCHESTRATOR-ONLY sanction (a solver may NEVER emit this — see stage0_solve.txt). Marks an
 * assumption as a MAINTAINED (disclosed, high-level) condition the note is stated CONDITIONAL on
 * and does NOT derive — the legitimate slot for "proved under condition A, where verifying A is
 * itself the open object" (cf. a DML nuisance-rate condition). Set by `bin/d0_maintain.ts`. Gated:
 * `open_object` is the OEQ it surfaces; `separate_object` justifies that A constrains a SEPARATE
 * object (a functional property / an estimator-/nuisance-side rate) and NOT the target estimand's
 * own asymptotics at the conclusion scale — the D0.5 math referee re-checks this and flags
 * `maintained_is_crux` (BLOCKING) if it fails. A `maintained`-dependent headline is CONDITIONAL and
 * tier-capped one notch (never flagship). */
export const MaintainedTagSchema = z.object({
  flag: z.literal(true),
  reason: z.string(),
  open_object: z.string(),
  separate_object: z.string(),
  sanctioned_by: z.literal("orchestrator"),
});

/** An assumption is ONE pure condition. No derived consequences, no where-used
 * pointers (those are `used_by` edges), no disclaimers, no omnibus. */
export const AssumptionSchema = z
  .object({
    id: z.string().regex(idRe("ass")),
    kind: z.string().optional(), // free-form tag (open set); see SUGGESTED_ASSUMPTION_KINDS
    condition: z.string(),
    free_symbols: z.array(z.string()).default([]),
    constants: z.array(z.string()).optional(),
    standard: StandardTagSchema.optional(),
    novel: NovelTagSchema.optional(),
    maintained: MaintainedTagSchema.optional(),
    used_by: z.array(z.string()).optional(),
  })
  .refine((a) => (a.standard ? 1 : 0) + (a.novel ? 1 : 0) + (a.maintained ? 1 : 0) === 1, {
    message: "assumption must carry exactly one of {standard, novel, maintained} (G6)",
  });

/** A definition is EITHER a class (carved by member-properties) OR a
 * proof-internal construction (inputs + construction) — never both. A class is
 * never carved by a witness; class membership of a construction is always a
 * `statement`, never an assumption. (This is what makes A6 unrepresentable.) */
export const DefinitionSchema = z
  .object({
    id: z.string().regex(idRe("def")),
    name: z.string(),
    // REQUIRED on EVERY definition — the explicit defining expression, so the
    // notation is never opaque (e.g. `P_{κ,β,n}`):
    //   • CLASS → a set-builder `{x : φ(x)}` that spells out ALL index parameters
    //     (notably the triangular-array `n`); φ is a predicate over the
    //     member-property assumptions, NEVER the image of a witness construction.
    //   • CONSTRUCTED OBJECT → the explicit formula / algorithm.
    construction: z.string().min(1),
    // Present ⟺ this definition is a CLASS, carved by these member-property ids.
    // This is the A6 firewall anchor: a class is carved ONLY by member-properties;
    // the gate (G5) additionally checks neither the member-property list NOR the
    // set-builder `construction` references a witness construction.
    by_member_properties: z.array(z.string()).optional(),
    // Constructed-object metadata: the free inputs the construction consumes.
    inputs: z.array(z.string()).optional(),
  })
  .refine((d) => !(d.by_member_properties !== undefined && d.inputs !== undefined), {
    message:
      "a class (by_member_properties) declares no construction `inputs`; a constructed object declares no `by_member_properties` (G5/G7)",
  });

/** The external source a `cited` statement is borrowed from: a `cite` bibkey
 * (must resolve in the core `bibliography`) and the exact `locator` (e.g.
 * "Theorem 3.1"). This is the structured provenance that lets F1 mint a `cite:`
 * node and the F2.5 match check verify the Lean def against the real statement —
 * instead of the result being laundered as `status:"proved"` with the citation
 * buried in `proof_tex`. */
export const CitedSourceSchema = z.object({
  cite: z.string(), // bibkey into `bibliography`
  locator: z.string(), // e.g. "Theorem 3.1", "Lemma 4.2", "§5.2"
  // Exact source-of-record when the source can be transcribed lawfully. This is
  // preferred over agent recollection and is copied unchanged into F1's cite:
  // entry. Legacy cores may still carry the transcription in `proof_tex`; D0.5
  // treats that as an attested fallback and D0.R can migrate it here.
  verbatim_statement: z.string().min(1).optional(),
  // Stable source handles. arXiv is directly fetchable by the shared resolver;
  // DOI/URL may still require main/user attestation when access is unavailable.
  arxiv: z.string().min(1).optional(),
  doi: z.string().min(1).optional(),
  url: z.string().url().optional(),
  attestation: z.object({
    by: z.enum(["d0-agent", "main", "user"]),
    note: z.string().min(1),
    at: z.string().datetime().optional(),
  }).optional(),
});

export const StatementSchema = z
  .object({
    // `oeq:` is the open/construct-question id (the kind the author actually emits);
    // `conj:` is retained as DEPRECATED so any pre-existing conjecture node still
    // validates, but the D-1.2 author must pose an `oeq:` instead (see STATEMENT_KINDS).
    id: z.string().regex(/^(thm|lem|prop|oeq|conj):[a-z0-9-]+$/),
    kind: z.enum(STATEMENT_KINDS),
    statement: z.string(),
    depends_on: z.array(z.string()).default([]),
    route: z.string().optional(), // proof strategy — D0-CORE fills (statement + strategy)
    // JSON-producing agents commonly spell an inapplicable optional field as
    // `null`.  For cited leaves the citation is the justification, so normalize
    // that representation to the canonical absence used by the rest of the
    // pipeline.  Non-null, non-string values remain validation errors.
    proof_tex: z.preprocess((value) => value === null ? undefined : value, z.string().optional()), // D0-PROVE fills; absent at CORE time
    // `cited` = a result the note INVOKES rather than DERIVES (a published theorem
    // we use for completeness). Its justification IS the citation, so it is NOT
    // `proved` by us — marking such a result `proved` (with the citation as its
    // proof_tex) is laundering. A `cited` statement MUST carry `source` and is a
    // LEAF: it may reference `def:`/`ass:` for notation but must not `depends_on`
    // other `lem:`/`thm:`/`prop:` (cite the theorem, never reconstruct its proof —
    // G-cited). F1 maps `cited` → `gate_class:"cited"` BY DEFAULT, except a cited
    // node load-bearing on a headline, which F1 re-routes to reuse/crux/gated
    // (a headline may not rest on a never-built citation — anti-laundering).
    status: z.enum(["to-prove", "proved", "cited"]),
    source: CitedSourceSchema.optional(), // REQUIRED ⟺ status === "cited"
    // Results in OTHER CausalSmith papers that this node NAMES but does not depend
    // on — the declared channel for provenance. The D0.5 rubric asks each theorem to
    // position itself against prior in-repository work; a node answers that by
    // RE-PROVING the generic step in this core and crediting the source. That is the
    // opposite of laundering (nothing is borrowed), but the credit line reads as a
    // citation to a regex, so declaring it here makes the distinction data instead of
    // something a prose scan has to infer. Format `<qid>/<node-id>`. This is NOT
    // `source` — `source` is a published paper a `cited` LEAF invokes in place of a
    // proof; `external_refs` is a sibling run's node mentioned by a node we PROVE.
    // Optional, NOT `.default([])`: defaulting would make the key required on every
    // node type and stamp an empty array onto every node of every existing core.
    external_refs: z.array(z.string().regex(/^[a-z0-9_]+\/(thm|lem|prop|oeq|conj|def|ass):[a-z0-9-]+$/)).optional(),
    // Prose fields (motivation only — never load-bearing math; the formal claim is
    // `statement`). Optional in the schema so a D0 core validates without them; the
    // PROPOSAL gate (GP3) requires them on every statement at D-1. Rendered
    // deterministically into the .tex — no separate prose agent.
    justification: z.string().optional(), // one-line: why this claim / why it matters
    gap: z.string().optional(), // closest prior art (bibkeys) + why this differs
    consumer: z.string().optional(), // one concrete downstream consumer
  })
  .refine((s) => (s.status === "cited") === (s.source !== undefined), {
    message: "a `cited` statement must carry `source` (bibkey + locator), and only a cited statement may (G-cited)",
  })
  .refine(
    // A `proved` statement with no proof is a hollow result: it renders as established
    // with nothing behind it and passes discharge checks that only read `status`.
    // `solvedStatus` even warns about this case and returns "proved" anyway, so the
    // schema is the only place that can actually stop it. Verified against all 93 real
    // cores before enforcing: zero violations.
    (s) => s.status !== "proved" || (s.proof_tex ?? "").trim().length > 0,
    {
      message:
        "a `proved` statement must carry a non-empty proof_tex — a proved node with no proof " +
        "renders as an established result with nothing establishing it (use `to-prove`, or " +
        "`cited` with a `source` if the justification is a citation)",
    },
  )
  .refine(
    // `oeq:`/`conj:` belong here too: a cited result resting on an OPEN question is
    // strictly worse than one resting on a proved lemma, yet the original pattern
    // omitted them, so `cited` + `depends_on:["oeq:open"]` validated and the node
    // counted as settled while its support was unresolved.
    (s) => s.status !== "cited" || !s.depends_on.some((d) => /^(lem|thm|prop|oeq|conj):/.test(d)),
    {
      message:
        "a `cited` statement is a LEAF: cite the theorem, do not reconstruct its proof — it must not depends_on other lem:/thm:/prop:/oeq:/conj: nodes (G-cited-leaf)",
    },
  )
  .refine(
    // The id PREFIX and the `kind` were validated independently, so `{id:"thm:headline",
    // kind:"lemma"}` was accepted. That is not cosmetic: reachability keys on `kind`, not
    // on the prefix. Non-lemma nodes are roots (stage0_working.ts:369) and unreachable
    // `kind:"lemma"` nodes are PRUNED (stage0_working.ts:398), so a headline mislabelled
    // as a lemma is silently deleted from the core; the re-derive frontier keys on `kind`
    // the same way (stage0_solve.ts:746).
    //
    // Deliberately NARROW rather than a prefix↔kind bijection. A bijection would outlaw a
    // legitimate pattern: `thm:` with kind `conjecture`, a conjectured headline posed at
    // D-1. (An earlier version of this comment also cited `thm:` with kind `remark`; that
    // was wrong — `remark` is not in STATEMENT_KINDS at all and belongs to the
    // presentation schema, so such a node never reaches this refinement.)
    // Only ONE direction is destructive: a headline-shaped id carrying kind `lemma` is
    // not a root, so once it is unreferenced the orphan pruner DELETES it outright. Every
    // other mismatch merely mis-roots a node, which is recoverable.
    // `conj:` is included: the exemption below is about a conjecture being PROMOTED to
    // theorem/proposition once proved, which is legitimate. Carrying kind `lemma` is not
    // that — the orphan pruner keys on `kind` and would delete a conj: headline exactly as
    // it would a thm: one.
    (s) => !/^(thm|prop|oeq|conj):/.test(s.id) || s.kind !== "lemma",
    {
      message:
        "a thm:/prop:/oeq:/conj: node must not have kind `lemma` — orphan-pruning keys on `kind` and " +
        "DELETES unreferenced lemmas (stage0_working.ts:398), so a headline mislabelled this way is " +
        "silently removed from the core. Give it its real kind, or use a lem: id.",
    },
  );

export const BibEntrySchema = z.object({ key: z.string(), citation: z.string().optional() });

/** SC6's auditable mapping from published comparator claims to proposal nodes.
 * Both top-level spellings remain supported because early proto producers used
 * `comparator_promises`; new prompts emit `comparator_promise_table`. */
export const ComparatorPromiseSchema = z.object({
  comparator_bibkey: z.string().min(1),
  comparator_claim: z.string().min(1),
  matched_by: z.string().min(1),
  match_kind: z.enum([
    "strict_tightening",
    "iff_frontier",
    "equivalence",
    "non_representability",
    "downgraded_to_informed_by",
    "dropped_from_abstract",
  ]),
});

/** The project-level justification (replaces a free-prose intro): the literature
 * GAP, the NICHE that gap opens, and how this project FILLS it. */
export const ProjectJustificationSchema = z.object({
  gap: z.string(), // what the literature is missing
  niche: z.string(), // the specific opportunity that gap opens
  fill: z.string(), // how this project fills the niche
});

export const CoreSchema = z.object({
  qid: z.string(),
  specialization: z.string().optional(),
  cluster: z.enum(["panel", "exactid", "partialid", "stat", "experimentation", "scm"]).optional(),
  symbols: z.array(SymbolSchema),
  assumptions: z.array(AssumptionSchema),
  definitions: z.array(DefinitionSchema).default([]),
  statements: z.array(StatementSchema),
  sampling_model: z.record(z.any()).optional(),
  // The §7 identifying functional, first-class and parallel to the §8
  // target_estimand: ExactID identifying formula, PartialID bounding functional,
  // Panel regression formula, (Stat) the estimator+rate pair, or — for a
  // structure-identification proposal — the recovery map (the functional of P
  // returning the structural target). Added by the non-Stat sanity-check — in
  // the Stat-only schema it had been absorbed into a `def:estimator`
  // construction, which is awkward for an ID/bound formula.
  estimand_functional: z.string().optional(),
  // The §8 causal target. Usually an effect estimand; for a structure-
  // identification proposal it is instead the structural / mechanism parameter
  // to be recovered (DAG / edge set / coefficient matrix), stated with the
  // indeterminacy under which it is identified (exact, sign·permutation, MEC).
  target_estimand: z.string(),
  bibliography: z.array(BibEntrySchema).default([]),
  comparator_promise_table: z.array(ComparatorPromiseSchema).optional(),
  comparator_promises: z.array(ComparatorPromiseSchema).optional(),
  // Top-level prose (motivation/narrative). Optional so a D0 core validates without
  // them; the PROPOSAL gate (GP3) requires tldr/project_justification/related_work at
  // D-1, and D0-CORE may fill project_justification/related_work/interpretation for its
  // rendered note. All rendered deterministically — no separate prose/render agent.
  tldr: z.string().optional(), // a one-paragraph summary of the whole proposal
  project_justification: ProjectJustificationSchema.optional(), // gap → niche → fill
  related_work: z.string().optional(),
  interpretation: z.string().optional(),
  // Optional non-contribution diagnostic retained from the accepted proposal.
  // This is deliberately prose, not a StatementSchema node: it may document an
  // internal limitation/counterexample without promoting it to a numbered
  // theorem, novelty claim, or closed open question.
  technical_internal_limitation: z.string().optional(),
  honest_scope: z.string().optional(),
})
  // Statement ids must be UNIQUE. Every consumer collapses them through a Map or Set
  // keyed by id (the structural gate, the apply's `stmtById`/`originalStatements`), so a
  // duplicate silently resolves to ONE record — usually the last — while a sibling code
  // path may edit the other. Two same-id records with different claims therefore let a
  // bundle mutate one copy and render the other, with no error anywhere.
  .refine(
    (c) => new Set(c.statements.map((s) => s.id)).size === c.statements.length,
    (c) => {
      // NB: `!seen.add(id)` is always false — Set.add returns the Set — which is exactly
      // the always-false-predicate class this audit was hunting. Use an explicit has/add.
      const seen = new Set<string>();
      const dupes = new Set<string>();
      for (const s of c.statements) {
        if (seen.has(s.id)) dupes.add(s.id);
        else seen.add(s.id);
      }
      return { message: `duplicate statement id(s): ${[...dupes].join(", ")} — every consumer keys nodes by id, so a duplicate silently resolves to one record` };
    },
  );

export type CoreSymbol = z.infer<typeof SymbolSchema>;
export type CitedSource = z.infer<typeof CitedSourceSchema>;
export type CoreAssumption = z.infer<typeof AssumptionSchema>;
export type CoreDefinition = z.infer<typeof DefinitionSchema>;
export type CoreStatement = z.infer<typeof StatementSchema>;
export type Core = z.infer<typeof CoreSchema>;

/** The set of all addressable core node ids (assumptions ∪ definitions ∪ statements).
 * Shared by the gate's dep checks, RENDER's \coreref resolution, and the review's
 * finding-node resolution. */
export function coreNodeIds(core: Core): Set<string> {
  return new Set<string>([
    ...core.assumptions.map((a) => a.id),
    ...core.definitions.map((d) => d.id),
    ...core.statements.map((s) => s.id),
  ]);
}
