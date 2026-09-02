// Orchestrator-authored PROOF-IRRELEVANT core edits.
//
// The D0 single-writer rule ("only the solver writes core bytes") exists so no
// claim, construction, condition, dependency, free-symbol declaration, status or
// source is ever authored outside the proof-tracked solve/merge/apply path. It
// does not need to cover positioning prose (a statement's justification / gap /
// consumer) — yet routing that through `d0_directive` costs a full
// solver round whose only output is a transcription of the directive.
//
// This channel lets the orchestrator land exactly that class of edit through the
// SAME apply path a worker bundle takes (schema, structural gate, atomic
// transaction, proof preservation/invalidation, escalation-log entry), with no
// model call, no stage rewind, and no round-output clearing (core.json is simply
// re-rendered). Every proof-relevant field is locked against the current
// authoritative catalog; anything else is refused and pointed at `d0_directive`.
import { readFile } from "node:fs/promises";
import type { PipelineContext } from "../../types.js";
import { CoreSchema, type Core, type CoreStatement } from "../core/schema.js";
import { normalizeRawModelJson } from "../core/latex_serialization.js";
import { assembleCore } from "../core/assemble.js";
import { coreRevision } from "../core/revision.js";
import { ProposedCoreEditSchema } from "../solve/schemas.js";
import { healCoreEditDirections } from "../solve/dispatch.js";
import { authoritativeStatementCatalog } from "../solve/oeq_source.js";
import { emptyProposals, readRoundProposals } from "../solve/proposals.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import { loadWorkingState, snapshotMember, type EscalationLogEntry } from "./d0_working.js";
import { applyProposedChanges, type RawCoreEdit } from "./d0_apply.js";

/** Kinds the orchestrator may author directly. Everything else is solver-owned. */
export const AUTHORABLE_EDIT_KINDS = new Set<RawCoreEdit["kind"]>(["statement-replace"]);
// NOT authorable: symbol edits (every symbol field enters the symbol-basis fingerprint
// that reopens dependents), bibliography (the citation string decides which paper a
// cited leaf indexes), the comparator table (match_kind/matched_by is adjudicated
// mathematical positioning), and everything structural. All go through `d0_directive`.

/** Statement fields the orchestrator may change: positioning prose only. */
const STATEMENT_PROSE_FIELDS = ["justification", "gap", "consumer"] as const;

const sameSet = (a: readonly string[] | undefined, b: readonly string[] | undefined): boolean => {
  if (a === undefined || b === undefined) return a === b;
  const sa = new Set(a);
  const sb = new Set(b);
  return sa.size === sb.size && [...sa].every((x) => sb.has(x));
};
const sameJson = (a: unknown, b: unknown): boolean => JSON.stringify(a ?? null) === JSON.stringify(b ?? null);

export type ProseField = (typeof STATEMENT_PROSE_FIELDS)[number];

/** Validate the orchestrator's items and compose the exact bundle apply will see, plus
 * the prose fields actually supplied per node (the payload is a full-node echo, so apply
 * cannot tell a supplied value from an echoed one). Pure: throws on the first refusal. */
export function composeAuthoredMetadataEdits(
  rawEdits: unknown,
  catalog: {
    /** Current ASSEMBLED view (proto + working proofs): the bytes apply's echo checks compare against. */
    statements: Map<string, CoreStatement>;
    /** The proto/working CARRIER node (frozen proto statement or agent-authored record
     * node). Non-prose fields are seeded from here, never from the assembled render,
     * whose edges may be re-wired (e.g. an answered question mapped to its theorem). */
    carrierStatements: Map<string, CoreStatement>;
    /** Proof-relevant snapshot of a node (`snapshotMember`), serialized; must not move. */
    snapshot: (node: CoreStatement) => string;
    /** Ids whose working record is `partial` (reopened / shelved debt). */
    partialIds: ReadonlySet<string>;
  },
): { edits: RawCoreEdit[]; suppliedProse: Record<string, ProseField[]> } {
  if (!Array.isArray(rawEdits)) throw new Error("d0_author_edits: --file must contain a JSON array of core edits");
  const carrier = { proposed_core_edits: structuredClone(rawEdits) };
  healCoreEditDirections(carrier);
  const out: RawCoreEdit[] = [];
  const suppliedProse: Record<string, ProseField[]> = {};
  carrier.proposed_core_edits.forEach((item, index) => {
    // Kind gate first, so a solver-owned kind is refused with the right pointer
    // even when its payload would not parse.
    const kind = (item as { kind?: unknown } | null)?.kind;
    if (typeof kind === "string" && !AUTHORABLE_EDIT_KINDS.has(kind as RawCoreEdit["kind"])) {
      const target = (item as { id?: unknown; name?: unknown; key?: unknown });
      const why = kind.startsWith("symbol-")
        ? "every symbol field enters the symbol-basis fingerprint, so the edit would reopen dependent proofs"
        : kind === "bibliography-replace"
          ? "the citation string decides which paper a cited leaf indexes"
          : kind === "comparator-promise-table-replace"
            ? "comparator match_kind/matched_by is adjudicated mathematical positioning"
            : "it can change a claim, construction, condition, dependency, or estimand";
      throw new Error(
        `d0_author_edits: '${kind}' on ${String(target.id ?? target.name ?? target.key ?? "?")} is solver-owned (${why}). ` +
          "Issue a `d0_directive` and let the solver author and re-prove it.",
      );
    }
    const parsed = ProposedCoreEditSchema.safeParse(item);
    if (!parsed.success) {
      throw new Error(`d0_author_edits: edit #${index + 1} is not a valid core edit: ${parsed.error.issues.map((i) => `${i.path.join(".")}: ${i.message}`).join("; ")}`);
    }
    const edit = parsed.data as RawCoreEdit;
    if (edit.kind === "statement-replace") {
      const carrier = catalog.carrierStatements.get(edit.id);
      const current = catalog.statements.get(edit.id) ?? carrier;
      if (carrier === undefined || current === undefined) throw new Error(`d0_author_edits: ${edit.id} is not in the authoritative statement catalog`);
      // A cited leaf owes the byte-faithful revalidation receipt and apply's cited
      // shortcut would settle it; a partial record is reopened debt. Neither is prose-only.
      if (current.status === "cited" || carrier.status === "cited") {
        throw new Error(`d0_author_edits: ${edit.id} is a cited leaf; its metadata travels with the citation receipt — use d0_directive`);
      }
      if (catalog.partialIds.has(edit.id)) {
        throw new Error(`d0_author_edits: ${edit.id} has a partial (reopened) working record; settle it through a solve round first`);
      }
      const proposed = edit.proposed as Partial<CoreStatement> & { partial_result?: string };
      if (proposed.partial_result !== undefined) {
        throw new Error(`d0_author_edits: ${edit.id}: partial_result is adjudication content, not metadata — use d0_directive`);
      }
      // Locked fields are checked against the carrier (what the proto/working store holds);
      // `status` may echo either the carrier or the assembled (solved) view, and
      // `depends_on` may echo either the carrier's or the render's re-wired edges.
      const locked: Array<[string, boolean]> = [
        ["statement", proposed.statement === carrier.statement],
        ["kind", proposed.kind === carrier.kind],
        ["status", proposed.status === current.status || proposed.status === carrier.status],
        ["depends_on", sameSet(proposed.depends_on ?? [], carrier.depends_on) || sameSet(proposed.depends_on ?? [], current.depends_on)],
        ["free_symbols", sameSet(proposed.free_symbols, carrier.free_symbols)],
        ["source", sameJson(proposed.source, carrier.source)],
        ["route", (proposed.route ?? undefined) === (carrier.route ?? undefined)],
        ["external_refs", sameSet(proposed.external_refs, carrier.external_refs)],
      ];
      const violated = locked.filter(([, ok]) => !ok).map(([field]) => field);
      if (violated.length > 0) {
        throw new Error(
          `d0_author_edits: ${edit.id}: field(s) ${violated.join(", ")} differ from the current node; this channel ` +
            `may change only ${STATEMENT_PROSE_FIELDS.join("/")}. A claim, dependency, declaration, status or source change goes through d0_directive.`,
        );
      }
      // Compose from the CARRIER (so the proto diff is genuinely prose-only) with the
      // assembled status (what apply's echo compares), overlaying only supplied prose.
      const { proof_tex: _proof, ...base } = carrier;
      const composed: Record<string, unknown> = { ...base, status: current.status };
      const supplied: ProseField[] = [];
      for (const field of STATEMENT_PROSE_FIELDS) {
        if (proposed[field] !== undefined) {
          composed[field] = proposed[field];
          supplied.push(field);
        }
      }
      if (supplied.length === 0) throw new Error(`d0_author_edits: ${edit.id}: no prose field supplied — nothing to author`);
      if (suppliedProse[edit.id] !== undefined) throw new Error(`d0_author_edits: ${edit.id} appears twice in one bundle`);
      suppliedProse[edit.id] = supplied;
      // Belt and braces: the proof-relevant snapshot the working record was proved
      // against must be byte-identical after the edit.
      if (catalog.snapshot(composed as unknown as CoreStatement) !== catalog.snapshot(carrier)) {
        throw new Error(`d0_author_edits: ${edit.id}: the edit would change the node's proof-relevant snapshot; use d0_directive`);
      }
      out.push({ ...edit, proposed: composed as Extract<RawCoreEdit, { kind: "statement-replace" }>["proposed"] });
      return;
    }
    throw new Error(`d0_author_edits: unsupported edit kind '${edit.kind}'`);
  });
  if (out.length === 0) throw new Error("d0_author_edits: no edits supplied");
  return { edits: out, suppliedProse };
}

/** Land orchestrator-authored metadata edits through the ordinary apply path.
 * Returns the applied (or, under `checkOnly`, validated) change list. */
export async function authorMetadataEdits(args: {
  ctx: PipelineContext;
  edits: unknown;
  note: string;
  checkOnly?: boolean;
}): Promise<EscalationLogEntry["changed"]> {
  const { ctx, edits, note, checkOnly = false } = args;
  if (!note.trim()) throw new Error("d0_author_edits: --note is required (why this metadata is being corrected)");
  const protoPath = protoCoreJsonPath(ctx);
  const proto = CoreSchema.parse(JSON.parse(normalizeRawModelJson(await readFile(protoPath, "utf8")))) as Core;
  const working = await loadWorkingState(ctx);
  if (working === null) {
    throw new Error("d0_author_edits: no D0 working state yet — before the first solve round, correct the proto through the D-1 author path");
  }
  const pending = await readRoundProposals(ctx, working);
  const pendingCount = pending.statements.length + pending.definitions.length + pending.assumptions.length +
    pending.coreEdits.length + pending.proofs.length + (pending.citationRevalidations?.length ?? 0);
  if (pendingCount > 0) {
    throw new Error(
      `d0_author_edits: ${pendingCount} solver proposal(s) are pending adjudication; apply or discard them with ` +
        "d0_apply_change first so orchestrator-authored bytes never mix with a solver bundle",
    );
  }
  if ((working.required_core_edit_mandates?.length ?? 0) > 0) {
    throw new Error("d0_author_edits: exact core-edit mandates are pending; resolve or cancel them first");
  }
  const assembled = CoreSchema.parse(assembleCore(proto, working));
  // Carrier = proto statement or agent record node; assembled = the solved/re-wired render.
  const carrierStatements = authoritativeStatementCatalog(proto.statements, working);
  const statements = new Map(assembled.statements.map((statement) => [statement.id, statement] as const));
  const { edits: composed, suppliedProse } = composeAuthoredMetadataEdits(edits, {
    statements,
    carrierStatements,
    snapshot: (node) => JSON.stringify(snapshotMember(proto, node)),
    partialIds: new Set(Object.entries(working.solved).filter(([, record]) => record.partial === true).map(([id]) => id)),
  });

  // Thread the bundle in memory: a preview or a failure touches no file, and a
  // concurrent round can never find authored items in the durable cursor.
  const proposalsOverride = {
    ...emptyProposals(),
    basis_revision: coreRevision(assembled),
    coreEdits: composed,
    citationRevalidations: [],
  };
  const fullNote = `orchestrator-authored metadata edit: ${note.trim()}`;
  const preview = await applyProposedChanges({
    ctx, ids: null, note: fullNote, checkOnly: true, authoredMetadataOnly: true, proposalsOverride, authoredProseFields: suppliedProse,
  });
  if (preview.length !== composed.length) {
    throw new Error(`d0_author_edits: apply would land ${preview.length} of ${composed.length} edit(s); nothing was mutated`);
  }
  if (checkOnly) return preview;
  return applyProposedChanges({
    ctx, ids: null, note: fullNote, checkOnly: false, authoredMetadataOnly: true, proposalsOverride, authoredProseFields: suppliedProse,
  });
}
