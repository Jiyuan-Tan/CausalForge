// Solve-unit payload shapes: the interfaces a D0 solve unit may emit, and the zod
// schemas that validate them at the file boundary.
//
// Split out of `stage0_solve.ts` (2181 lines) so the payload contract is readable on
// its own. These are pure declarations — no I/O, no policy. The policy that decides
// WHO may emit each of these lives in `ownership.ts`.

import { z } from "zod";
import {
  AssumptionSchema,
  BibEntrySchema,
  DefinitionSchema,
  ProjectJustificationSchema,
  StatementSchema,
  SymbolSchema,
  type CoreStatement,
} from "../core/schema.js";
import type { RawCoreEdit } from "../stages/d0_apply.js";

export interface ProposedStatementChange {
  id: string;
  current: string;
  proposed: string;
  reason: string;
  /** "narrow" = the claim is genuinely too strong (allowed, for review);
   *  any other value is treated as a weaken-to-ease-the-proof attempt and rejected. */
  direction: string;
}

/** A solver-proposed correction to a CONSTRUCTED-OBJECT definition (a formula —
 *  envelope, rate functional, exponent — that the proof shows is mis-specified).
 *  Flagged, never silently applied; class definitions (by_member_properties) are
 *  NOT changeable here (that is an assumption/scope move, and gerrymandering a def
 *  to the proof's own objects is laundering). */
export interface ProposedDefinitionChange {
  id: string;
  current: string;
  proposed: string;
  reason: string;
  /** "correct" = the construction formula was wrong (too small / mis-specified) and
   *  the proposed one is its true value; any other value is treated as gerrymandering
   *  a definition to ease the proof and is rejected. */
  direction: string;
}

/** A GENUINE OPEN GAP the solver isolated but cannot close from the frozen primitives,
 *  and for which no honest narrowing exists — a research-level obstruction that needs a
 *  NEW DIRECTION (a different proof strategy, a paper to adapt, a reframing) from the
 *  orchestrator. Distinct from a `proposed_statement_change` (the claim is fine, just
 *  too strong → narrow) and from an unfinished round (ran out of steam → just re-solve).
 *  The orchestrator answers via the escalation-log `directive`, then re-solves. */
export interface OpenObligation {
  node_id: string;
  what_is_open: string; // the precise sub-claim / construction that is not closed
  obstruction: string; // why it does not close from the current primitives
  attempted: string; // what route(s) were tried, so guidance does not repeat them
  /** The STRONGEST partial result the solver could establish for this node (e.g. a
   *  weaker-but-proved sub-bound). Preserved across rounds so the next solve EXTENDS it
   *  instead of restarting — and the orchestrator's guidance improves upon a concrete
   *  partial, reducing back-and-forth. Empty if nothing partial was reachable. */
  partial_result?: string;
}

/** A NEW ASSUMPTION the solver genuinely needs and is allowed to PROPOSE (not
 *  silently bake in). Surfaced at the checkpoint for orchestrator/user APPROVAL —
 *  never auto-applied. A faithful refinement (the math intent already lives in this
 *  setting; a standard named condition) is approvable; one that ASSUMES THE CRUX
 *  (the node's own hard claim dressed as a hypothesis) is rejected. Distinct from a
 *  PROOF INTERMEDIATE (an oracle/true counterpart, coupling, truncation introduced
 *  inside a proof), which needs NO approval and is NOT reported here. */
export interface ProposedAssumption {
  id: string; // ass:<slug>
  condition: string; // the single new condition
  reason: string; // why the proof genuinely needs it
  standard_or_novel: string; // "standard: <name/cite>" or "novel: <justification>"
  not_crux: string; // why this is NOT the node's own hard claim restated as a hypothesis
}

export interface SolveUnitOutput {
  /** `argues_proposed`: this proof argues the PROPOSED statement text emitted for the
   *  same id in this round's bundle (not the current frozen text). Apply uses it to
   *  promote the proof in the same adjudication when the proposal lands verbatim. */
  proofs: Array<{ id: string; proof_tex: string; argues_proposed?: boolean }>;
  resolved_oeqs: Array<{ source_id: string; theorem: CoreStatement }>;
  added_lemmas: CoreStatement[];
  proposed_statement_changes: ProposedStatementChange[];
  proposed_definition_changes: ProposedDefinitionChange[];
  proposed_assumptions: ProposedAssumption[];
  proposed_core_edits: RawCoreEdit[];
  open_obligations: OpenObligation[];
  prose_updates?: ProseUpdates;
}


const ProseUpdatesSchema = z.object({
  tldr: z.string().min(1).optional(),
  project_justification: ProjectJustificationSchema.partial().optional(),
  related_work: z.string().min(1).optional(),
  interpretation: z.string().min(1).optional(),
  technical_internal_limitation: z.string().min(1).optional(),
  honest_scope: z.string().min(1).optional(),
  statement_notes: z.array(z.object({
    id: z.string(),
    justification: z.string().min(1).optional(),
    gap: z.string().min(1).optional(),
    consumer: z.string().min(1).optional(),
  })).default([]),
});
export type ProseUpdates = z.infer<typeof ProseUpdatesSchema>;

const ProposedStatementChangeSchema = z.object({
  id: z.string(),
  current: z.string(),
  proposed: z.string(),
  reason: z.string(),
  direction: z.string(),
});

const ProposedDefinitionChangeSchema = z.object({
  id: z.string(),
  current: z.string(),
  proposed: z.string(),
  reason: z.string(),
  direction: z.string(),
});

const ProposedAssumptionSchema = z.object({
  id: z.string(),
  condition: z.string(),
  reason: z.string(),
  standard_or_novel: z.string(),
  not_crux: z.string(),
});

// A statement replacement carries dependency/metadata only. Reusing StatementSchema
// directly made a proved node require its entire proof merely so apply could discard it;
// large LaTeX proofs cannot be transcribed byte-for-byte reliably. Validate every other
// StatementSchema invariant against a synthetic carried proof, then remove that sentinel.
// `z.never()` rejects an authored proof before it can become part of the typed payload.
const StatementReplacementSchema = z
  .object({ proof_tex: z.never().optional() })
  .passthrough()
  .transform((statement) => ({ ...statement, proof_tex: "<carried by apply>" }))
  .pipe(StatementSchema)
  .transform(({ proof_tex: _carriedProof, ...statement }) => statement);

const ProposedCoreEditSchema = z.discriminatedUnion("kind", [
  z.object({
    kind: z.literal("assumption-replace"), id: z.string().regex(/^ass:[a-z0-9-]+$/),
    proposed: AssumptionSchema, reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("assumption-delete"), id: z.string().regex(/^ass:[a-z0-9-]+$/),
    reason: z.string(), direction: z.literal("delete-obsolete"),
  }),
  z.object({
    kind: z.literal("statement-replace"), id: z.string().regex(/^(?:thm|lem|prop|conj|oeq):[a-z0-9-]+$/),
    proposed: StatementReplacementSchema, reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("statement-delete"), id: z.string().regex(/^(?:thm|lem|prop|conj|oeq):[a-z0-9-]+$/),
    replacement_id: z.string().regex(/^(?:thm|lem|prop|conj|oeq):[a-z0-9-]+$/).optional(),
    reason: z.string(), direction: z.literal("delete-obsolete"),
  }),
  z.object({
    kind: z.literal("definition-add"), id: z.string().regex(/^def:[a-z0-9-]+$/),
    proposed: DefinitionSchema, reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("definition-replace"), id: z.string().regex(/^def:[a-z0-9-]+$/),
    proposed: DefinitionSchema, reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("definition-delete"), id: z.string().regex(/^def:[a-z0-9-]+$/),
    reason: z.string(), direction: z.literal("delete-obsolete"),
  }),
  z.object({
    kind: z.literal("bibliography-replace"), key: z.string(), proposed: BibEntrySchema,
    reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("symbol-add"), name: z.string(), proposed: SymbolSchema,
    reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("symbol-replace"), name: z.string(), proposed: SymbolSchema,
    reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("symbol-delete"), name: z.string(),
    reason: z.string(), direction: z.literal("delete-obsolete"),
  }),
  z.object({
    kind: z.literal("rebuild-reverse-dependencies"), id: z.literal("metadata:reverse-dependencies"),
    reason: z.string(), direction: z.literal("correct"),
  }),
]);

const OpenObligationSchema = z.object({
  node_id: z.string(),
  what_is_open: z.string(),
  obstruction: z.string(),
  attempted: z.string(),
  partial_result: z.string().optional(),
});

/** STRICT on purpose. Every array below is `.default([])`, so on a non-strict object a
 *  misspelled or camelCased top-level key (`proposedCoreEdits`, `open_obligation`) was
 *  stripped as unknown and the real key silently defaulted to empty — a round in which
 *  the solver proposed a narrowing and isolated an obligation parsed cleanly as "solved
 *  nothing, proposed nothing", and the orchestrator dispatched another blind solve.
 *  `.strict()` turns that silent drop into a loud parse failure, which the caller
 *  already fails closed on. The prompt specifies these keys exactly, so an unknown
 *  top-level key IS the bug, never a harmless extra. */
export const SolveUnitOutputSchema = z.strictObject({
  proofs: z.array(z.object({ id: z.string(), proof_tex: z.string(), argues_proposed: z.boolean().optional() })).default([]),
  resolved_oeqs: z.array(z.object({
    source_id: z.string().regex(/^oeq:[a-z0-9-]+$/),
    theorem: StatementSchema.refine(
      (s) => s.id.startsWith("thm:") && s.kind === "theorem" && s.status === "proved" && (s.proof_tex ?? "").trim().length > 0,
      { message: "a resolved OEQ must be replaced by one proved thm: node with nonempty proof_tex" },
    ),
  })).default([]),
  added_lemmas: z.array(StatementSchema).default([]),
  proposed_statement_changes: z.array(ProposedStatementChangeSchema).default([]),
  proposed_definition_changes: z.array(ProposedDefinitionChangeSchema).default([]),
  proposed_assumptions: z.array(ProposedAssumptionSchema).default([]),
  proposed_core_edits: z.array(ProposedCoreEditSchema).default([]),
  open_obligations: z.array(OpenObligationSchema).default([]),
  prose_updates: ProseUpdatesSchema.optional(),
});
