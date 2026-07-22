// Typed schema for the F1 "formalization plan" — the machine-checkable map from
// every typed-core node to the Lean object that realizes it. F1 authors it, the
// plan_gate validates one-to-one coverage, F2 implements it and syncs deviations
// back. See CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md §4.
//
// The plan binds to the core's node ids (assumptions ∪ definitions ∪ statements),
// NOT the prose .tex — so F1/F2 never re-extract structure. Changing F1's
// authoring never re-tests F2 as long as the file still validates against this.
import { z } from "zod";

/** Where a node's Lean realization comes from. */
export const DispositionSchema = z.enum(["reuse", "define-local"]);

/** The Lean form a core node maps to. `variable` never appears here — symbols
 * are covered by `env` (S-blocks), not by `nodes`.
 *
 * Every assumption atom maps to ONE named `def … : Prop` (`assumption`). Whether
 * it is used *inline* (a statement lists it in `hyps`) or *bundled* (a class lists
 * it in `members`) — or both, e.g. a shared `ass:consistency` that is a field of
 * two classes — is captured by those cross-references, not by the atom's kind. */
export const LeanKindSchema = z.enum([
  "assumption", // assumption atom → named `def … : Prop` (referenced by hyps/fields)
  "structure", // class definition (by_member_properties) → structure / typeclass
  "def", // construction definition (inputs) → def / noncomputable def
  "theorem", // statement (T-block)
  "lemma", // statement (L-block)
]);

/** Delivery is orthogonal to mathematical provenance. An undelivered object remains
 * in the typed core/plan for an honest audit trail, but is not emitted as a Lean
 * declaration or claimed as a proved paper result. The plan gate restricts this
 * escape hatch to secondary theorems and cited nodes. */
export const DeliveryRoleSchema = z.enum(["headline", "headline-support", "secondary"]);
export const DeliveryStatusSchema = z.enum(["deliver", "undelivered"]);

/** One environment binding (S-block): binds a subset of symbols + the sampling
 * model to a chosen Causalean world. Derived from `core.symbols` + `sampling_model`
 * + `cluster`; has no dedicated core node. This is where substrate reuse concentrates. */
export const EnvEntrySchema = z.object({
  id: z.string().regex(/^S[0-9]+$/), // S-block local id
  world: z.string(), // free-form: po-system | scm | panel-dgp | measure-space | ...
  binds_symbols: z.array(z.string()).default([]),
  binds_sampling_model: z.boolean().default(false),
  disposition: DispositionSchema,
  reuse: z.string().nullable().default(null), // decl/typeclass to instantiate, or null
  modules: z.array(z.string()).default([]),
  notes: z.string().optional(),
});

/** One node entry: the Lean decision for a single core node id. */
export const NodeEntrySchema = z.object({
  lean_kind: LeanKindSchema,
  lean_name: z.string(),
  disposition: DispositionSchema,
  reuse: z.string().nullable().default(null),
  modules: z.array(z.string()).default([]),
  // Set true only when a `define-local` node needs Defer-tier substrate; drives
  // the derived feasibility verdict (§4.3).
  defer_tier: z.boolean().default(false),
  // Set true ONLY for a Defer node tagged `substrate-gate` (a classical, named,
  // off-the-shelf fact assumed visibly as debt). A gate is emitted like an
  // assumption — `def … : Prop` threaded as a `_of_gate` hypothesis into its
  // consumers (never a sorry-lemma / axiom) — classified `kind:"gate"` in the
  // graph. Mutually exclusive with a crux Defer (which must be BUILT). Default
  // false; opt-in. The discharge fate of a gate is refined by `gate_class`.
  gate: z.boolean().default(false),
  // For a gate node (`gate:true`), its discharge fate on the discharge-this-run axis:
  //  - "gated" (default when absent): the gate WILL be discharged this run — it is
  //    scaffolded as an assumed gate only to parallelize proof-fill, its own proof
  //    is its verification, and it is recorded in SUBSTRATE_DEBT.md until discharged.
  //    This is the existing substrate-gate behavior (the `substrate_build_required`
  //    channel), unchanged — so pre-split plans (no `gate_class`) keep working.
  //  - "cited": the gate will NOT be discharged this run — a deferred assumption
  //    that is formalized + assumed + MATCHED against `source` (a cite: entry), may
  //    be built in a future run, and is recorded in CITED_DEPENDENCIES.md. Its only
  //    verification is the F2.5 source-match (it is never proven this run).
  gate_class: z.enum(["gated", "cited"]).optional(),
  // The id of the `cite:` entry (in the plan's `citations`) this node is matched
  // against. REQUIRED for `gate_class:"cited"` (a never-proven assumption needs
  // something exact to check against); optional provenance for "gated".
  source: z.string().optional(),
  // structure only: the member-atom ids, in field order (== core by_member_properties).
  members: z.array(z.string()).optional(),
  // statement only: the file the decl is emitted to, and the node ids it takes as
  // hypotheses (assumption atoms used inline, and/or class structures it bundles).
  target_file: z.string().optional(),
  hyps: z.array(z.string()).optional(),
  // statement only, paper-scoped runs: the `theorem_local_id` (t1, t2 …) this
  // statement realizes, so the F1 `theorems[]` manifest and F2's `T<id>.lean`
  // naming reconcile against `state.theorems[]`. Absent on legacy single-theorem runs.
  local_id: z.string().optional(),
  delivery_role: DeliveryRoleSchema.optional(),
  delivery_status: DeliveryStatusSchema.default("deliver"),
  delivery_reason: z.string().min(1).optional(),
  notes: z.string().optional(),
});

/** One external citation a `cited` node is matched against — a first-class graph
 * dependency, id `cite:<slug>`. The `cited` node's Lean `def … : Prop` must
 * faithfully encode the lemma at `locator`; F2.5 verifies it against the fetched
 * source (preferred), or against `verbatim_statement` when no fetchable handle
 * (arxiv | doi | url) resolves. */
export const CitationSchema = z.object({
  id: z.string().regex(/^cite:/),
  title: z.string(),
  authors: z.string(),
  year: z.number().int(),
  arxiv: z.string().optional(),
  doi: z.string().optional(),
  url: z.string().optional(),
  locator: z.string(), // e.g. "Theorem 3.1", "Lemma 4.2", "§5.2"
  // REQUIRED when no fetchable handle (arxiv | doi | url) resolves; else advisory.
  verbatim_statement: z.string().optional(),
  // Provenance for an attested transcription, especially when main/user supplied
  // a lawfully obtained page because automated retrieval was unavailable.
  attestation: z.object({
    by: z.enum(["d0-agent", "main", "user"]),
    note: z.string().min(1),
    at: z.string().datetime().optional(),
  }).optional(),
});

export const FeasibilitySchema = z.enum(["formalizable-now", "needs-new-infrastructure"]);

export const PlanSchema = z.object({
  qid: z.string(),
  specialization: z.string().optional(),
  cluster: z.enum(["panel", "exactid", "partialid", "stat", "experimentation", "scm"]).optional(),
  /** Target Lean subdirectory for emitted files, e.g. `CausalSmith/Stat/Foo`. */
  lean_subdir: z.string().optional(),
  env: z.array(EnvEntrySchema).default([]),
  nodes: z.record(z.string(), NodeEntrySchema),
  /** External citations (`cite:<slug>` entries) referenced by `cited` nodes via
   * their `source` field. Empty on runs with no cited dependencies. */
  citations: z.array(CitationSchema).default([]),
  /** Derived from the plan (§4.3); stored for convenience and gate-checked. */
  feasibility: FeasibilitySchema.optional(),
});

export type Disposition = z.infer<typeof DispositionSchema>;
export type LeanKind = z.infer<typeof LeanKindSchema>;
export type DeliveryRole = z.infer<typeof DeliveryRoleSchema>;
export type DeliveryStatus = z.infer<typeof DeliveryStatusSchema>;
export type Citation = z.infer<typeof CitationSchema>;
export type EnvEntry = z.infer<typeof EnvEntrySchema>;
type ParsedNodeEntry = z.infer<typeof NodeEntrySchema>;
type ParsedPlan = z.infer<typeof PlanSchema>;
export type NodeEntry = Omit<ParsedNodeEntry, "gate" | "delivery_status"> & {
  gate?: boolean;
  /** Optional in hand-built/legacy Plan values; PlanSchema materializes `deliver`. */
  delivery_status?: z.infer<typeof DeliveryStatusSchema>;
};
export type Plan = Omit<ParsedPlan, "nodes"> & { nodes: Record<string, NodeEntry> };

/** Feasibility is a pure function of the plan: any `define-local` node flagged
 * Defer-tier ⇒ needs-new-infrastructure; otherwise formalizable-now. */
export function deriveFeasibility(plan: Plan): z.infer<typeof FeasibilitySchema> {
  const needsInfra = Object.values(plan.nodes).some(
    (n) => n.delivery_status !== "undelivered" && n.disposition === "define-local" && n.defer_tier,
  );
  return needsInfra ? "needs-new-infrastructure" : "formalizable-now";
}
