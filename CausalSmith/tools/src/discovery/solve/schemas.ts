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
  ComparatorPromiseSchema,
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
  /** Revision stamp of the displayed statement view. Optional for legacy output. */
  based_on_revision?: string;
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
  /** Revision stamp of the displayed constructed-definition view. */
  based_on_revision?: string;
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
  /** Symbol-table names the `condition` uses. Optional so an older payload still parses,
   *  but it is what carries a symbol into the invalidation scope of every statement that
   *  reaches that symbol only through this assumption — `d0_apply` used to stub `[]`. */
  free_symbols?: string[];
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
  // Sampling-model entries are prose metadata too.  Keep this a partial map so a
  // directive can correct one scoped description (most often `design`) without
  // making the model reproduce, and potentially drift, every sibling entry.
  sampling_model: z.record(z.string().min(1)).optional(),
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
  based_on_revision: z.string().regex(/^rev:[a-f0-9]{64}$/).optional(),
  proposed: z.string(),
  reason: z.string(),
  direction: z.string(),
});

const ProposedDefinitionChangeSchema = z.object({
  id: z.string(),
  current: z.string(),
  based_on_revision: z.string().regex(/^rev:[a-f0-9]{64}$/).optional(),
  proposed: z.string(),
  reason: z.string(),
  direction: z.string(),
});

const ProposedAssumptionSchema = z.object({
  id: z.string().regex(/^ass:[a-z0-9-]+$/),
  condition: z.string(),
  reason: z.string(),
  standard_or_novel: z.string(),
  not_crux: z.string(),
  free_symbols: z.array(z.string()).optional(),
});

// A statement replacement carries dependency/metadata only. Reusing StatementSchema
// directly made a proved node require its entire proof merely so apply could discard it;
// large LaTeX proofs cannot be transcribed byte-for-byte reliably. Validate every other
// StatementSchema invariant against a synthetic carried proof, then remove that sentinel.
// `z.never()` rejects an authored proof before it can become part of the typed payload.
const StatementReplacementSchema = z
  .object({
    proof_tex: z.never().optional(),
    // An OEQ replacement may synchronize the strongest proved partial result with
    // its revised scope.  This is adjudication context, not a proof and not part of
    // CoreStatement; apply continues to carry the authoritative partial from the
    // working record.  Preserve it across the schema boundary instead of letting
    // StatementSchema's ordinary unknown-key stripping silently erase it.
    partial_result: z.string().optional(),
  })
  .passthrough()
  .transform((payload, ctx) => {
    const { partial_result: partialResult, ...statementPayload } = payload;
    const parsed = StatementSchema.safeParse({
      ...statementPayload,
      proof_tex: "<carried by apply>",
    });
    if (!parsed.success) {
      for (const issue of parsed.error.issues) ctx.addIssue(issue);
      return z.NEVER;
    }
    const { proof_tex: _carriedProof, ...statement } = parsed.data;
    return {
      ...statement,
      ...(partialResult !== undefined ? { partial_result: partialResult } : {}),
    };
  });

export const ProposedCoreEditSchema = z.discriminatedUnion("kind", [
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
    /** Phase 2 (reference-by-revision-hash): the `revision` stamp of the node
     *  view this edit was authored against, as shown in the dispatch context /
     *  review packet. When present, the apply matches it against the revisions
     *  of its legal views instead of running the byte-echo view-selection; an
     *  unknown hash skips fail-safe. Absent on old artifacts → echo fallback. */
    based_on_revision: z.string().regex(/^rev:[a-f0-9]{64}$/).optional(),
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
    based_on_revision: z.string().regex(/^rev:[a-f0-9]{64}$/).optional(),
  }),
  z.object({
    kind: z.literal("definition-delete"), id: z.string().regex(/^def:[a-z0-9-]+$/),
    reason: z.string(), direction: z.literal("delete-obsolete"),
  }),
  z.object({
    kind: z.literal("bibliography-replace"), key: z.string(), proposed: BibEntrySchema,
    reason: z.string(), direction: z.literal("correct"),
  }),
  // The ONLY channel that can edit `target_estimand`. It exists because a referee can
  // legitimately object to the estimand line itself — typically an unqualified causal
  // equality ("θ_P(t₀) = ∫μ_P(t₀,x)p_X(x)dx = E[Y(t₀)]") that in truth holds only under
  // the run's identification proposition. With no channel, such a finding is unfixable:
  // the repair stage cannot touch the field, so the run can neither pass review nor
  // address what review objected to, and every in-core workaround (relocating the causal
  // claim into class membership) is laundering, because E[Y(t₀)] then stops being a
  // functional of the observed law.
  //
  // `current` is a MANDATORY byte-for-byte echo of the estimand being replaced. This is
  // what keeps the field's anti-drift guarantee: the estimand is the anchor of what the
  // run committed to deliver, so an edit must prove it saw the text it is overwriting and
  // can never be applied blind to a core the author never read. Qualifying the causal
  // equality is a correction; quietly swapping the deliverable is not, and the echo plus
  // the logged `from`/`to` diff is what lets review tell them apart.
  z.object({
    kind: z.literal("target-estimand-replace"),
    id: z.literal("metadata:target-estimand"),
    current: z.string(),
    proposed: z.string(),
    reason: z.string(), direction: z.literal("correct"),
  }),
  // Same contract for the §7 identifying/minimax functional. These two fields fail
  // together: a repair that removes a parameter from the law class leaves the headline
  // functional still advertising it, which is the SAME unfaithfulness the referee
  // objected to, merely relocated one line over. `current` echoes byte-for-byte, with
  // `""` echoing an absent field. With this, every top-level Core field is writable
  // through exactly one reviewed channel — formal fields here, framing prose through
  // `prose_updates` — and none is frozen with no way to correct it.
  z.object({
    kind: z.literal("estimand-functional-replace"),
    id: z.literal("metadata:estimand-functional"),
    current: z.string(),
    proposed: z.string(),
    reason: z.string(), direction: z.literal("correct"),
  }),
  z.object({
    kind: z.literal("comparator-promise-table-replace"),
    id: z.literal("metadata:comparator-promise-table"),
    proposed: z.array(ComparatorPromiseSchema),
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
  what_is_open: z.string().trim().min(1),
  obstruction: z.string().trim().min(1),
  attempted: z.string().trim().min(1),
  // Empty is the prompt's canonical "no partial result reached" value.
  partial_result: z.string().trim().optional(),
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
  proofs: z.array(z.object({
    id: z.string(),
    proof_tex: z.string().refine((proof) => proof.trim().length > 0, {
      message: "proof_tex must contain a substantive proof",
    }),
    argues_proposed: z.boolean().optional(),
  })).default([]),
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
}).superRefine((output, ctx) => {
  for (const change of output.proposed_definition_changes) {
    const paired = output.proposed_core_edits.filter(
      (edit): edit is Extract<(typeof output.proposed_core_edits)[number], { kind: "definition-replace" }> =>
        edit.kind === "definition-replace" && edit.id === change.id,
    );
    if (paired.length !== 1) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["proposed_definition_changes"],
        message:
          `${change.id} formula correction requires exactly one paired definition-replace ` +
          `with complete post-image metadata; found ${paired.length}`,
      });
      continue;
    }
    if (paired[0].proposed.construction !== change.proposed || paired[0].proposed.free_symbols === undefined) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["proposed_core_edits"],
        message:
          `${change.id} paired definition-replace must match the proposed formula and declare free_symbols`,
      });
    }
  }

  for (const change of output.proposed_statement_changes) {
    const paired = output.proposed_core_edits.filter(
      (edit): edit is Extract<(typeof output.proposed_core_edits)[number], { kind: "statement-replace" }> =>
        edit.kind === "statement-replace" && edit.id === change.id,
    );
    if (paired.length !== 1) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["proposed_statement_changes"],
        message:
          `${change.id} claim correction requires exactly one paired statement-replace ` +
          `whose metadata describes the post-change claim; found ${paired.length}`,
      });
      continue;
    }
    if (paired[0].proposed.statement !== change.proposed || paired[0].proposed.free_symbols === undefined) {
      ctx.addIssue({
        code: z.ZodIssueCode.custom,
        path: ["proposed_core_edits"],
        message:
          `${change.id} paired statement-replace must match the proposed claim and declare free_symbols`,
      });
    }
  }
});
