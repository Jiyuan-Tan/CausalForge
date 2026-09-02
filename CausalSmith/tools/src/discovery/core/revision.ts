// Phase 2 of the 2026-07-30 migration: reference-by-revision-hash.
//
// The echo contract required a solver's `statement-replace` to byte-echo "the
// node it saw" — but WHICH view that is depended on bundle composition (frozen
// vs carried × claim-paired vs metadata-only × settled working overlay), and
// every new view was a fresh opportunity to break the enumeration. A revision
// hash pins the view instead: every surface that shows a node to the solver
// (dispatch targets, the frozen-core context block, the review packet's
// rendered core) stamps it with `revision`, the solver cites that value in
// `based_on_revision`, and the apply matches it against the revisions of its
// legal views — one comparison, no view-selection logic.
//
// ONE function computes the hash everywhere (writer and reader, same process,
// same serialization), so canonicalization drift is unrepresentable — the
// lesson of mandate hash v3. The hash covers EXACTLY the fields the echo
// checks compared — id, kind, statement, status — and nothing more. Fields the
// pipeline derives or the edit itself modifies are deliberately excluded
// (audit P23F1): `depends_on` is auto-wired by assembly, so the packet's wired
// view and the apply's bare-proto reconstruction would hash differently and
// every wiring-touched node would fail-safe forever; proof bytes never change
// which CLAIM the solver saw; `source` moves under attestation without the
// claim moving. The three legal views remain distinguishable through `status`
// (pre-bundle open vs settled overlay) and `statement` (post-claim).
import { createHash } from "node:crypto";
import { CoreSchema, DefinitionSchema, type Core, type CoreDefinition, type CoreStatement } from "./schema.js";

export const REVISION_PREFIX = "rev:";
export const REVISION_PATTERN = /^rev:[a-f0-9]{64}$/;

/** Exact revision of a validated assembled core. Used to ensure a surfaced
 * proposal is applied to the same durable round state that was adjudicated. */
export function coreRevision(core: Core): string {
  return REVISION_PREFIX + createHash("sha256").update(JSON.stringify(CoreSchema.parse(core))).digest("hex");
}

/** The revision of one statement view. Pure and total: any object carrying the
 *  statement fields hashes, whether it came from the packet render, a dispatch
 *  target, or an apply-side reconstruction of a legal view. */
export function statementRevision(view: {
  id: string;
  kind?: string;
  statement?: string;
  status?: string;
}): string {
  const payload = JSON.stringify({
    id: view.id,
    kind: view.kind ?? null,
    statement: view.statement ?? null,
    status: view.status ?? null,
  });
  return REVISION_PREFIX + createHash("sha256").update(payload).digest("hex");
}

/** A statement as shown to the solver / adjudicator, with its revision stamp. */
export function stampRevision<T extends Parameters<typeof statementRevision>[0]>(
  view: T,
): T & { revision: string } {
  return { ...view, revision: statementRevision(view) };
}

/** Revision of the complete semantic definition view used by a construction
 * correction and its exact typed post-image.  The construction-only channel
 * still changes only `construction`, but the shared revision prevents its
 * paired whole-node replacement from overwriting intervening metadata. */
type DefinitionRevisionView = Pick<CoreDefinition, "id" | "construction"> &
  Partial<Omit<CoreDefinition, "id" | "construction">>;

export function definitionRevision(view: DefinitionRevisionView, frozenBasis?: Core): string {
  const payload = JSON.stringify({
    definition: DefinitionSchema.parse(view),
    frozen_core: frozenBasis === undefined ? null : CoreSchema.parse(frozenBasis),
  });
  return REVISION_PREFIX + createHash("sha256").update(payload).digest("hex");
}

export function stampDefinitionRevision<T extends DefinitionRevisionView>(
  view: T,
  frozenBasis?: Core,
): T & { revision: string } {
  return { ...view, revision: definitionRevision(view, frozenBasis) };
}

/** Stamp every statement of a core COPY for an outward-facing rendering (the
 *  review packet). The stored core.json field shapes never change (migration
 *  scope guard) — this is applied only to the serialized view. */
export function stampCoreStatements<C extends { statements: CoreStatement[] }>(
  core: C,
): Omit<C, "statements"> & { statements: Array<CoreStatement & { revision: string }> } {
  return {
    ...core,
    statements: core.statements.map((s) => stampRevision(s)),
  };
}
