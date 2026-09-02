// Apply D0-SOLVE proposed changes to the frozen proto + record an escalation entry.
//
// Shared by the CLI (`bin/d0_apply_change.ts`, human-driven) and the automated D0
// revise loop (`runStage0SolveLoop`). Applying a change edits the FROZEN PROTO (the
// spec the next solve reads), appends an escalation-log entry (so the next solve sees
// what changed / why), and clears the stale round outputs while KEEPING the incremental
// working state (carried proofs). The hybrid auto/gate partition lives in the loop;
// this module just executes an already-decided set of changes.
import { retargetDeletedDependency } from "../core/oeq_edges.js";
import { existsSync } from "node:fs";
import { readFile, writeFile, rm, readdir, rename } from "node:fs/promises";
import { randomUUID } from "node:crypto";
import path from "node:path";
import { statePath } from "../../paths.js";
import { loadState, saveState } from "../../state.js";
import type { PipelineContext, StateJson } from "../../types.js";
import { assertMandateBasis, resolveRequiredCoreEditMandates } from "../solve/mandates.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import { coreJsonPath } from "./d0_core.js";
import {
  hotProofBytes,
  appendEscalationLog,
  changedSymbolNames,
  computeValidNodes,
  declaredSymbolScope,
  loadWorkingState,
  memberValid,
  normalizeWorkingState,
  proposalRevision,
  readEscalationLog,
  saveWorkingState,
  symbolBasis,
  type EscalationLogEntry,
  type WorkingState,
} from "./d0_working.js";

import {
  CoreSchema,
  type Core,
  type CoreAssumption,
  type CoreDefinition,
  type CoreStatement,
  type CoreSymbol,
  type ComparatorPromise,
} from "../core/schema.js";
import { archiveProofs, proofBytesInRoundFile } from "../proof_archive.js";
import { coreRevision, statementRevision } from "../core/revision.js";
import { recordProof, wiredSnapshot, withWiredDeps } from "../working_writer.js";
import {
  agentOeqSourceFromFingerprint,
  authoritativeStatementCatalog,
  oeqSourceFingerprint,
  resolvedStatementReplacementEndpoint,
} from "../solve/oeq_source.js";
import { companionPathFor } from "../solve/tex_companion.js";
import { proofContentClosureIntersects, rebuildAssumptionUsedBy } from "../core/dependencies.js";
import { normalizeSymbol } from "../core/preflight.js";
import {
  assertNoDecodedControlChars,
  assertSealableLatexPayload,
  normalizeRawModelJson,
  repairCoreLatexSerialization,
  repairLatexStringsDeep,
} from "../core/latex_serialization.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { extractNodeRefs } from "../core/node_ids.js";
import { truncateTexSafe } from "../../shared/tex_text.js";
import { findAuthoredNodeReferences, type AuthoredNodeReference } from "../core/text_references.js";
import { topologicallyOrderSymbols } from "../core/symbol_order.js";
import { topologicallyOrderDefinitions } from "../core/definition_order.js";
import { readTypedCore } from "../core/core_io.js";
import { assembleCore } from "../core/assemble.js";
import { runStructuralGate } from "../core/gate.js";

/** Statements added during D0 are durable in the working cursor but absent from the
 * frozen proto.  Reverse-dependency repair must see them as direct consumers. */
function carriedStatements(working: WorkingState | null): CoreStatement[] {
  return Object.values(working?.solved ?? {}).flatMap((record) => record.node ? [record.node] : []);
}

export interface RawChange {
  id: string;
  current?: string;
  based_on_revision?: string;
  proposed: string;
  reason?: string;
  direction?: string;
}

/** A solver-proposed NEW assumption (a single law/estimator condition the proof needs).
 *  Flows through the same auto/gate loop as statement/def changes (applied to the proto,
 *  pending approval). `standard_or_novel` is the solver's freeform tag, parsed below. */
export interface RawAssumption {
  id: string;
  condition: string;
  reason?: string;
  standard_or_novel?: string;
  not_crux?: string;
  /** The solver's symbol declaration for this condition. Optional (a payload written
   *  before the field existed carries none), and stored as `[]` when absent — see the
   *  apply site for why it is carried rather than stubbed. */
  free_symbols?: string[];
}

/** Typed frozen-core edits that cannot be expressed as a claim-only statement
 * narrowing or construction-only definition correction. Every replacement is a
 * complete schema-valid node; deletion and metadata rebuild are explicit variants. */
export type RawCoreEdit =
  | { kind: "assumption-replace"; id: string; proposed: CoreAssumption; reason?: string; direction: "correct" }
  | { kind: "assumption-delete"; id: string; reason?: string; direction: "delete-obsolete" }
  | {
      kind: "statement-replace";
      id: string;
      proposed: Omit<CoreStatement, "proof_tex"> & { partial_result?: string };
      reason?: string;
      direction: "correct";
      /** Phase 2: revision stamp of the view this edit was authored against
       *  (see core/revision.ts). Optional — absent on old artifacts, which use
       *  the byte-echo fallback. */
      based_on_revision?: string;
    }
  | { kind: "statement-delete"; id: string; replacement_id?: string; reason?: string; direction: "delete-obsolete" }
  | { kind: "definition-add"; id: string; proposed: CoreDefinition; reason?: string; direction: "correct" }
  | {
      kind: "definition-replace";
      id: string;
      proposed: CoreDefinition;
      reason?: string;
      direction: "correct";
      based_on_revision?: string;
    }
  | { kind: "definition-delete"; id: string; reason?: string; direction: "delete-obsolete" }
  | { kind: "bibliography-replace"; key: string; proposed: { key: string; citation?: string }; reason?: string; direction: "correct" }
  | { kind: "target-estimand-replace"; id: "metadata:target-estimand"; current: string; proposed: string; reason?: string; direction: "correct" }
  | { kind: "estimand-functional-replace"; id: "metadata:estimand-functional"; current: string; proposed: string; reason?: string; direction: "correct" }
  | { kind: "comparator-promise-table-replace"; id: "metadata:comparator-promise-table"; proposed: ComparatorPromise[]; reason?: string; direction: "correct" }
  | { kind: "symbol-add"; name: string; proposed: CoreSymbol; reason?: string; direction: "correct" }
  | { kind: "symbol-replace"; name: string; proposed: CoreSymbol; reason?: string; direction: "correct" }
  | { kind: "symbol-delete"; name: string; reason?: string; direction: "delete-obsolete" }
  | { kind: "rebuild-reverse-dependencies"; id: "metadata:reverse-dependencies"; reason?: string; direction: "correct" };

export function coreEditTarget(edit: RawCoreEdit): string {
  if (edit.kind === "bibliography-replace") return `bib:${edit.key}`;
  if (edit.kind === "symbol-add" || edit.kind === "symbol-replace" || edit.kind === "symbol-delete") return `sym:${edit.name}`;
  return edit.id;
}

/** Literal references that make deleting/remapping a node a claim/proof edit rather
 * than a graph edit. The working record's `proof_tex` is scanned separately because
 * frozen proto members keep their durable proof there, not on the proto statement. */
export function findUnsafeDeleteTextReferences(
  proto: Core,
  working: WorkingState | null,
  targetId: string,
): AuthoredNodeReference[] {
  const refs = findAuthoredNodeReferences(proto, targetId, { excludeNodeId: targetId });
  const target = targetId.toLowerCase();
  const seen = new Set(refs.map((ref) => ref.location));
  const add = (location: string, text: string | undefined): void => {
    if (!text || seen.has(location) || !extractNodeRefs(text).includes(target)) return;
    seen.add(location);
    refs.push({ location, text });
  };
  for (const [id, rec] of Object.entries(working?.solved ?? {})) {
    if (id === targetId) continue;
    if (rec.node) {
      add(`working.${id}.node.statement`, rec.node.statement);
      add(`working.${id}.node.proof_tex`, rec.node.proof_tex);
      add(`working.${id}.node.route`, rec.node.route);
      add(`working.${id}.node.justification`, rec.node.justification);
      add(`working.${id}.node.gap`, rec.node.gap);
      add(`working.${id}.node.consumer`, rec.node.consumer);
      add(`working.${id}.node.source`, JSON.stringify(rec.node.source ?? null));
    }
    add(`working.${id}.proof_tex`, rec.proof_tex);
  }
  // A statement note belongs to the statement it annotates. Deleting the node
  // deletes that note in the same transaction, so its map key (which necessarily
  // contains targetId) is not an inbound authored reference. Other prose and other
  // nodes' notes remain load-bearing and are still scanned.
  const proseOverlay = structuredClone(working?.prose_overlay ?? null);
  if (proseOverlay?.statement_notes !== undefined) delete proseOverlay.statement_notes[targetId];
  add("working.prose_overlay", JSON.stringify(proseOverlay));
  return refs;
}

/**
 * Why a `statement-replace` echo failed, or `null` when it matches.
 *
 * `statement-replace` is a DEPENDENCY/METADATA-only channel: it requires `kind`,
 * `statement`, and `status` to echo the node's CURRENT values byte-for-byte, and composes the final
 * node from the carried values. Proof text is deliberately absent from this channel:
 * requiring a model to reproduce a long LaTeX proof solely to discard it made valid
 * dependency rewiring effectively unappliable.
 *
 * That silent skip cost three solve rounds on 2026-07-19. The bundle guard caught the
 * drop — it refuses a partial apply — but reported only a COUNT ("selected 2, only 1
 * applicable"), so diagnosing it meant reading this source and hand-comparing fields.
 * The solver had bundled a re-proof into the edit: first sending `status: "to-prove"`
 * against a `proved` node, then `status: "proved"` plus a new proof against a `to-prove`
 * one. Naming the offending field turns that into one line of output.
 */
/**
 * Did this edit SHRINK the node's declared symbol list?
 *
 * `free_symbols` is load-bearing for soundness: it scopes which symbol changes reopen the
 * node. The metadata channel forces `statement` to echo byte-for-byte, but the declaration
 * rides in from the model payload unchecked — so a payload could echo the claim exactly,
 * drop `\eta` from the list, and in ONE step both escape detection and persist a node that
 * no future `\eta` edit can ever reopen.
 *
 * Only a defined→defined shrink counts. `undefined → [...]` is the ordinary migration of a
 * legacy node to a declaration: the node is only on this path because it is currently VALID,
 * i.e. no symbol has changed since it was proved, so recording what it uses does not alter
 * what it was proved against. `[...] → undefined` widens the scope back to "any symbol",
 * which is strictly more conservative and needs no invalidation.
 */
export function declarationNarrowed(
  prior: { free_symbols?: string[] } | undefined,
  next: { free_symbols?: string[] } | undefined,
): boolean {
  if (prior?.free_symbols === undefined || next?.free_symbols === undefined) return false;
  const after = new Set(next.free_symbols.map(normalizeSymbol));
  return prior.free_symbols.some((name) => !after.has(normalizeSymbol(name)));
}

/** Phase 2 (reference-by-revision-hash): when the edit carries
 *  `based_on_revision`, match it against the revisions of the LEGAL VIEWS of the
 *  target node — one comparison replaces the entire echo view-selection
 *  (`describeEchoMismatch` / `describePairedClaimEchoMismatch` remain as the
 *  fallback for edits without the field). Views are supplied by the caller; the
 *  open-target form (`openSolveTarget`) of each is added here, since a dispatch
 *  target is stamped in that form. A `kind` echo is still enforced against the
 *  matched view: the compose spreads `proposed`, so a wrong kind would land.
 *  Unknown hash → mismatch string with the hash (the caller skips fail-safe). */
export function describeRevisionMismatch(
  basedOnRevision: string,
  proposed: { id: string; kind?: string },
  views: Array<{ id: string; kind?: string; statement?: string; status?: string; source?: unknown; depends_on?: string[] }>,
  editId: string,
): string | null {
  if (proposed.id !== editId) return `payload id '${proposed.id}' does not match the edit target '${editId}'`;
  // Inline open-target form (same rule as solve/context.ts `openSolveTarget`,
  // which cannot be imported here without a module cycle): status re-opened,
  // `source` dropped — the shape a dispatch target is stamped in.
  const candidates = views.flatMap((view) => [
    view,
    { ...view, status: "to-prove", source: undefined },
  ]);
  const matched = candidates.find((view) => statementRevision(view) === basedOnRevision);
  if (matched === undefined) {
    return `based_on_revision ${basedOnRevision} matches no current view of ${editId} — ` +
      "the node changed since this edit was authored (stale edit; re-author against the current packet)";
  }
  if (proposed.kind !== matched.kind) {
    return `kind must echo the node's current value '${matched.kind}', got '${proposed.kind}' ` +
      "(this channel is dependency/metadata-only)";
  }
  return null;
}

export function describeEchoMismatch(
  proposed: { id: string; kind?: string; statement?: string; status?: string },
  current: { id: string; kind?: string; statement?: string; status?: string },
  editId: string,
): string | null {
  if (proposed.id !== editId) return `payload id '${proposed.id}' does not match the edit target '${editId}'`;
  if (proposed.kind !== current.kind) {
    return `kind must echo the node's current value '${current.kind}', got '${proposed.kind}' ` +
      "(this channel is dependency/metadata-only)";
  }
  if (proposed.statement !== current.statement) {
    return "statement must echo the node's current text byte-for-byte (claim text changes go through proposed_statement_changes)";
  }
  if (proposed.status !== current.status) {
    return `status must echo the node's current value '${current.status}', got '${proposed.status}' ` +
      "(this channel cannot change status; a paired proof in `proofs` does that)";
  }
  return null;
}

/** Validate the structural half of a selected same-id claim+metadata composition.
 * The claim channel owns the resulting statement/status. A solver may serialize
 * the structural half against either the immutable pre-bundle node or the already
 * assembled proposed-claim node, but it may not mix fields from those two views. */
function describePairedClaimEchoMismatch(
  proposed: { id: string; kind?: string; statement?: string; status?: string },
  before: { id: string; kind?: string; statement?: string; status?: string },
  after: { id: string; kind?: string; statement?: string; status?: string },
  editId: string,
): string | null {
  if (proposed.id !== editId) return `payload id '${proposed.id}' does not match the edit target '${editId}'`;
  if (proposed.kind !== before.kind || proposed.kind !== after.kind) {
    return `kind must echo the node's current value '${before.kind}', got '${proposed.kind}' ` +
      "(this channel is dependency/metadata-only)";
  }
  const echoesBefore = proposed.statement === before.statement && proposed.status === before.status;
  const echoesAfter = proposed.statement === after.statement && proposed.status === after.status;
  if (!echoesBefore && !echoesAfter) {
    return "statement/status must together echo either the pre-bundle node or the selected paired claim";
  }
  return null;
}

const CORE_EDIT_KINDS = [
  "assumption-replace",
  "assumption-delete",
  "statement-replace",
  "statement-delete",
  "definition-add",
  "definition-replace",
  "definition-delete",
  "bibliography-replace",
  "target-estimand-replace",
  "estimand-functional-replace",
  "comparator-promise-table-replace",
  "symbol-add",
  "symbol-replace",
  "symbol-delete",
  "rebuild-reverse-dependencies",
] as const;

/** The proposal CHANNELS a round can carry. A single node id can appear in more
 *  than one of them in the same round — a claim change on `thm:x` and a metadata-only
 *  `statement-replace` on `thm:x` are independent proposals that happen to share a
 *  target — which is precisely why a selector needs a channel as well as an id. */
const CHANNEL_QUALIFIERS = ["statement", "definition", "assumption", "core-edit"] as const;

/** Resolves `--ids`/`--id` selectors against proposal variants, and remembers which
 *  selectors actually matched something so the caller can name the ones that did not.
 *
 *  A selector is either a BARE id (`thm:x`) — which matches that id in EVERY channel,
 *  preserving the original behaviour — or a KIND-QUALIFIED id, written `<qualifier>:<id>`:
 *
 *    statement:thm:x           the claim-text change on thm:x, and nothing else
 *    core-edit:thm:x           any typed core edit targeting thm:x
 *    statement-replace:thm:x   only the statement-replace core edit on thm:x
 *    bibliography-replace:bib:K   only that bibliography edit
 *
 *  Qualifiers are unambiguous because no node id begins with one: statement/definition/
 *  assumption ids are `(thm|lem|prop|conj|oeq|def|ass):…`, and the synthetic core-edit
 *  targets are `bib:…`, `sym:…`, `metadata:…`. Parsing splits on the FIRST colon only,
 *  so the id half keeps its own colons. */
export interface ProposalSelector {
  matchesStatement(id: string): boolean;
  matchesDefinition(id: string): boolean;
  matchesAssumption(id: string): boolean;
  matchesCoreEdit(edit: RawCoreEdit): boolean;
  /** Selectors that matched no proposal variant in any channel. */
  unmatched(): string[];
}

type ParsedSelector = { raw: string; channel: (typeof CHANNEL_QUALIFIERS)[number] | null; editKind: string | null; id: string };

function parseOneSelector(raw: string): ParsedSelector {
  const colon = raw.indexOf(":");
  if (colon > 0) {
    const head = raw.slice(0, colon);
    const rest = raw.slice(colon + 1);
    if (rest.length > 0) {
      if ((CHANNEL_QUALIFIERS as readonly string[]).includes(head)) {
        return { raw, channel: head as ParsedSelector["channel"], editKind: null, id: rest };
      }
      if ((CORE_EDIT_KINDS as readonly string[]).includes(head)) {
        return { raw, channel: "core-edit", editKind: head, id: rest };
      }
    }
  }
  return { raw, channel: null, editKind: null, id: raw };
}

/** Reject a qualified selector whose id half is itself qualified (`statement:core-edit:thm:x`).
 *  Such a selector can never match, and silently treating it as unmatched hides a typo behind
 *  the generic "matched no proposal" error. */
export function validateProposalSelectors(raw: Iterable<string>): string[] {
  const bad: string[] = [];
  for (const s of raw) {
    const parsed = parseOneSelector(s);
    if (parsed.channel === null) continue;
    const inner = parseOneSelector(parsed.id);
    if (inner.channel !== null) bad.push(s);
  }
  return bad;
}

export function parseProposalSelectors(raw: Iterable<string>): ProposalSelector {
  const parsed = [...raw].map(parseOneSelector);
  const hit = new Set<string>();
  const match = (p: ParsedSelector, channel: ParsedSelector["channel"], id: string, editKind?: string): boolean => {
    if (p.id !== id) return false;
    if (p.channel !== null && p.channel !== channel) return false;
    if (p.editKind !== null && p.editKind !== editKind) return false;
    return true;
  };
  const any = (channel: ParsedSelector["channel"], id: string, editKind?: string): boolean => {
    let found = false;
    for (const p of parsed) {
      if (!match(p, channel, id, editKind)) continue;
      hit.add(p.raw);
      found = true;
    }
    return found;
  };
  return {
    matchesStatement: (id) => any("statement", id),
    matchesDefinition: (id) => any("definition", id),
    matchesAssumption: (id) => any("assumption", id),
    matchesCoreEdit: (edit) => any("core-edit", coreEditTarget(edit), edit.kind),
    unmatched: () => parsed.filter((p) => !hit.has(p.raw)).map((p) => p.raw),
  };
}

function toSelector(ids: Set<string> | ProposalSelector | null | undefined): ProposalSelector | null {
  if (ids === null || ids === undefined) return null;
  return ids instanceof Set ? parseProposalSelectors(ids) : ids;
}

/** Parse a solver's freeform `standard_or_novel` tag into a gate-valid assumption tag
 *  (exactly one of {standard, novel}, G6). Defaults to `novel` when no bibliography KEY is
 *  recognized — safe, since `novel` needs no cite resolution; reclassified at approval. */
export function parseAssumptionTag(
  s: string | undefined,
  bibKeys: string[],
): { standard: { name: string; cite: string } } | { novel: { flag: true; justification: string } } {
  const text = (s ?? "").trim();
  if (/^standard/i.test(text)) {
    // Boundary-anchored key match: a bare substring test let a short bibkey
    // (`Lee`, `Chen`) match inside an unrelated word or TeX and mis-attribute
    // the citation.
    const key = bibKeys.find((k) =>
      new RegExp(`(?<![A-Za-z0-9])${k.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![A-Za-z0-9])`).test(text),
    );
    if (key) {
      // PERSISTED field: a hard 80-char cut could land inside `\(...\)` and
      // seal an unbalanced math delimiter into `standard.name`, failing the
      // render/seal gates downstream. Back off to a math-safe cut.
      const name = truncateTexSafe(text.replace(/^standard:?\s*/i, ""), 80);
      return { standard: { name: name || "standard condition", cite: key } };
    }
  }
  return { novel: { flag: true, justification: text || "solver-proposed (pending approval)" } };
}


import { readRoundProposals, emptyProposals } from "../solve/proposals.js";

export async function readProposedChanges(
  ctx: PipelineContext,
): Promise<{
  basis_revision?: string;
  statements: RawChange[];
  definitions: RawChange[];
  assumptions: RawAssumption[];
  coreEdits: RawCoreEdit[];
  proofs: Array<{ id: string; proof_tex?: string; argues_proposed?: boolean }>;
  citationRevalidations: CoreStatement[];
}> {
  // Single accessor: `working.proposals` when present, legacy files otherwise.
  // Every consumer must see the SAME payload — reading a subset here is what let an
  // apply approve a statement change while discarding the proof written for it.
  const working = await loadWorkingState(ctx);
  const p = await readRoundProposals(ctx, working);
  return {
    ...(p.basis_revision === undefined ? {} : { basis_revision: p.basis_revision }),
    statements: p.statements as RawChange[],
    definitions: p.definitions as RawChange[],
    assumptions: p.assumptions as RawAssumption[],
    coreEdits: p.coreEdits as RawCoreEdit[],
    proofs: p.proofs as Array<{ id: string; proof_tex?: string; argues_proposed?: boolean }>,
    citationRevalidations: p.citationRevalidations ?? [],
  };
}

/** Exact proof-relevant identity for a cited-source revalidation receipt. Authored
 * motivation prose may be absent because apply keeps the canonical core node. */
function citedReceiptMatches(existing: CoreStatement, emitted: CoreStatement): boolean {
  return existing.id === emitted.id &&
    existing.kind === emitted.kind &&
    existing.statement === emitted.statement &&
    JSON.stringify(existing.depends_on ?? []) === JSON.stringify(emitted.depends_on ?? []) &&
    existing.status === "cited" && emitted.status === "cited" &&
    (existing.proof_tex ?? "") === (emitted.proof_tex ?? "") &&
    JSON.stringify(existing.source ?? null) === JSON.stringify(emitted.source ?? null) &&
    JSON.stringify(existing.free_symbols) === JSON.stringify(emitted.free_symbols) &&
    existing.route === emitted.route &&
    JSON.stringify(existing.external_refs) === JSON.stringify(emitted.external_refs);
}

/** Clear the stale round outputs (proposed-change files, assembled core, raw solve
 *  files); KEEP the working state + escalation log + proto. Proof bytes living only in
 *  the deleted files are copied to the cold archive first — see proof_archive.ts. */
export async function clearRoundOutputs(ctx: PipelineContext): Promise<void> {
  const dir = path.dirname(coreJsonPath(ctx));
  // Bytes still living in the working cursor are NOT displaced by deleting a raw file
  // that mirrors them — archiving them here would poison provenance (see hotProofBytes).
  const hot = hotProofBytes(await loadWorkingState(ctx));
  for (const f of await readdir(dir)) {
    if (
      /proposed_(statement|definition)_changes\.json$/.test(f) ||
      /proposed_assumptions\.json$/.test(f) ||
      /proposed_core_edits\.json$/.test(f) ||
      /proposed_proofs\.json$/.test(f) ||
      /proposal_review_packet\.json$/.test(f) ||
      /open_obligations\.json$/.test(f) ||
      // Per-round withheld-content diagnostic: stale copies presented a PREVIOUS
      // round's conflicts as current to the next inspector of the run directory.
      /withheld_content\.json$/.test(f) ||
      f === "core.json" ||
      f === `${ctx.qid}_core.json` ||
      /(^|_)solve_.*\.json$/.test(f)
    ) {
      // Only the raw payload channels can hold proof bytes that exist nowhere else
      // (withheld collisions, unmatched ids, duplicate re-proofs). core.json mirrors
      // the working cursor and the review packet mirrors `working.proposals`, so they
      // are not swept; and payloads that DID land in hot state are filtered out — the
      // archive records only bytes actually leaving hot state.
      if (/(^|_)solve_.*\.json$/.test(f) || /proposed_proofs\.json$/.test(f)) {
        // Phase 3: a solve unit's proof bytes may live in its TeX companion
        // (under discovery/solve_tex/).
        const companionFile = companionPathFor(path.join(dir, f));
        const companionText = existsSync(companionFile) ? await readFile(companionFile, "utf8") : undefined;
        const bytes = proofBytesInRoundFile(f, await readFile(path.join(dir, f), "utf8"), "round-cleared", companionText)
          .filter((p) => !hot.get(p.nodeId)?.has(p.proofTex));
        if (bytes.length > 0) await archiveProofs(dir, bytes);
        await rm(companionFile, { force: true });
      }
      await rm(path.join(dir, f), { force: true });
    }
  }
  // The apply consumed this round's outputs; their prompt-bound reuse receipts go
  // with them (a stale receipt is inert without its output file, but never keep one).
  await rm(path.join(dir, "solve_receipts"), { recursive: true, force: true });
}

interface D0ApplyTransaction {
  version: 1;
  transaction_id: string;
  proto_before: string;
  proto_after: string;
  working_after: WorkingState | null;
  escalation_entry: EscalationLogEntry;
  /** Optional complete state post-image for exceptional replayable store repairs. */
  state_after?: StateJson;
  /** Orchestrator-authored PROOF-IRRELEVANT edits (bin/d0_author_edits.ts): commit
   * leaves the stage pointer and every round output alone and only re-renders
   * core.json, so the change costs no re-solve and no re-dispatch. */
  authored_metadata_only?: true;
}

function applyTransactionPath(ctx: PipelineContext): string {
  return path.join(path.dirname(coreJsonPath(ctx)), "d0_apply_transaction.json");
}

/** Commit a fully prevalidated proto+working store replacement through the same
 * replayable transaction used by ordinary D0 applies.  Exceptional repair CLIs
 * must not hand-sequence these two authoritative stores. */
export async function commitD0StoreReplacement(args: {
  ctx: PipelineContext;
  expectedProtoBytes: string;
  protoAfter: Core;
  workingAfter: WorkingState;
  note: string;
  stateAfter?: StateJson;
}): Promise<string> {
  const txPath = applyTransactionPath(args.ctx);
  if (existsSync(txPath)) {
    throw new Error(`pending D0 apply transaction exists at ${txPath}; recover it before replacing stores`);
  }
  const protoPath = protoCoreJsonPath(args.ctx);
  const live = await readFile(protoPath, "utf8");
  if (live !== args.expectedProtoBytes) {
    throw new Error("D0 store replacement basis changed after validation; nothing was mutated");
  }
  const transactionId = `d0replace:${randomUUID()}`;
  const escalationEntry: EscalationLogEntry = {
    transaction_id: transactionId,
    round: args.workingAfter.round,
    changed: [],
    note: args.note,
    provenance_only: true,
  };
  await writeJsonAtomic(txPath, {
    version: 1,
    transaction_id: transactionId,
    proto_before: live,
    proto_after: JSON.stringify(CoreSchema.parse(args.protoAfter), null, 2),
    working_after: args.workingAfter,
    escalation_entry: escalationEntry,
    ...(args.stateAfter ? { state_after: args.stateAfter } : {}),
  } satisfies D0ApplyTransaction);
  const recovered = await recoverPendingApply(args.ctx);
  if (recovered === null) throw new Error("D0 store replacement transaction disappeared before commit");
  return transactionId;
}

async function writeTextAtomic(file: string, contents: string): Promise<void> {
  const temp = `${file}.tmp-${process.pid}-${Date.now()}`;
  try {
    await writeFile(temp, contents, "utf8");
    await rename(temp, file);
  } finally {
    await rm(temp, { force: true });
  }
}

/** Validation prefix of `recoverPendingApply`, exported so the replay harness grades a
 * pending transaction by EXACTLY the standard recovery applies — one validator, no
 * drift. Throws on the first violation. The live proto is read LAZILY (only after the
 * transaction's own shape and post-image are validated) to preserve recovery's error
 * precedence: a corrupt transaction reports corruption even when the proto is also
 * missing or unreadable. */
export async function validatePendingApplyTransaction(
  raw: unknown,
  readLiveProto: () => Promise<string>,
  txPath: string,
): Promise<{ tx: D0ApplyTransaction; liveProto: string }> {
  const tx = raw as D0ApplyTransaction;
  if (
    tx.version !== 1 || typeof tx.transaction_id !== "string" ||
    typeof tx.proto_before !== "string" || typeof tx.proto_after !== "string" ||
    tx.escalation_entry?.transaction_id !== tx.transaction_id
  ) throw new Error(`D0 apply transaction is corrupt at ${txPath}`);
  CoreSchema.parse(JSON.parse(tx.proto_after));
  const liveProto = await readLiveProto();
  if (liveProto !== tx.proto_before && liveProto !== tx.proto_after) {
    throw new Error(
      `D0 apply transaction ${tx.transaction_id} cannot replay: proto changed outside the transaction`,
    );
  }
  return { tx, liveProto };
}

/** Finish an interrupted multi-file apply before reading any live basis. The
 * transaction contains both post-images and an idempotent journal key, so a crash
 * after either store write is replayable instead of becoming a stale half-apply. */
export async function recoverPendingApply(ctx: PipelineContext): Promise<EscalationLogEntry["changed"] | null> {
  const txPath = applyTransactionPath(ctx);
  if (!existsSync(txPath)) return null;
  // protoPath is resolved lazily, inside the callback, so the legacy-name probe runs
  // only after the transaction's shape and post-image validate — HEAD's exact timing.
  let protoPath = "";
  const { tx, liveProto } = await validatePendingApplyTransaction(
    JSON.parse(await readFile(txPath, "utf8")),
    () => {
      protoPath = protoCoreJsonPath(ctx);
      return readFile(protoPath, "utf8");
    },
    txPath,
  );

  const sp = statePath(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1");
  if (tx.state_after) {
    await saveState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1", tx.state_after);
  } else if (tx.authored_metadata_only) {
    // No rewind: nothing was reopened, so `--resume` continues from the same stage.
  } else if (existsSync(sp)) {
    const state = await loadState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1");
    if (state.stage_completed !== "-0.5") {
      state.stage_completed = "-0.5";
      await saveState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1", state);
    }
  }
  if (liveProto !== tx.proto_after) await writeTextAtomic(protoPath, tx.proto_after);
  const journal = await readEscalationLog(ctx);
  if (!journal.some((entry) => entry.transaction_id === tx.transaction_id)) {
    await appendEscalationLog(ctx, tx.escalation_entry);
  }
  if (tx.working_after) await saveWorkingState(ctx, tx.working_after);
  if (tx.authored_metadata_only) {
    // Keep every round output (diagnostics, obligations, solve files); only the published
    // render moves, and it is the same pure render commitRound writes.
    const workingNow = tx.working_after ?? await loadWorkingState(ctx) ?? { round: 0, solved: {} } as WorkingState;
    const renderWorking = structuredClone(workingNow);
    normalizeWorkingState(renderWorking);
    await writeJsonAtomic(coreJsonPath(ctx), CoreSchema.parse(assembleCore(CoreSchema.parse(JSON.parse(tx.proto_after)) as Core, renderWorking)));
  } else {
    await clearRoundOutputs(ctx);
  }
  await rm(txPath, { force: true });
  return tx.escalation_entry.changed;
}

/** Consume a fully adjudicated, fully rejected proposal bundle without touching the
 * frozen core. This is intentionally separate from `applyProposedChanges`: selecting
 * zero ids there is ambiguous with a caller bug, while an all-rejected review needs an
 * explicit, auditable disposal operation before a correction directive can proceed. */
export async function discardAllProposedChanges(args: {
  ctx: PipelineContext;
  note: string;
  checkOnly?: boolean;
}): Promise<number> {
  const { ctx, note, checkOnly = false } = args;
  if (!note.trim()) throw new Error("discard-all requires a nonempty adjudication note");
  const working = await loadWorkingState(ctx);
  if (!working) throw new Error("discard-all requires a durable D0 working cursor");
  const journal = await readEscalationLog(ctx);
  const pendingMandates = journal
    .slice(Math.min(working.escalation_entries_consumed ?? 0, journal.length))
    .flatMap((entry) => entry.required_core_edit_mandates ?? []);
  const pendingCancellations = journal
    .slice(Math.min(working.escalation_entries_consumed ?? 0, journal.length))
    .flatMap((entry) => entry.cancelled_core_edit_mandates ?? []);
  const proto = await readTypedCore(protoCoreJsonPath(ctx));
  const liveMandates = resolveRequiredCoreEditMandates({
    mandates: [...(working.required_core_edit_mandates ?? []), ...pendingMandates],
    cancellations: pendingCancellations,
    core: proto,
    working,
    proposalRevision: working.proposal_revision,
  });
  if (liveMandates.length > 0) {
    throw new Error(
      "discard-all refuses a bundle containing independently adjudicated required core edits; " +
      "apply the complete mandated bundle or record an explicit cancellation directive",
    );
  }
  const proposals = await readProposedChanges(ctx);
  const count = proposals.statements.length + proposals.definitions.length +
    proposals.assumptions.length + proposals.coreEdits.length;
  if (count === 0) throw new Error("discard-all found no live D0 proposal variants");
  if (checkOnly) return count;

  const sp = statePath(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1");
  if (existsSync(sp)) {
    const state = await loadState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1");
    if (state.stage_completed !== "-0.5") {
      state.stage_completed = "-0.5";
      await saveState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1", state);
    }
  }
  // Journal the rejection before consuming its only hot carrier. `saveWorkingState`
  // archives any provisional proof bytes displaced by the clear.
  await appendEscalationLog(ctx, {
    round: working.round,
    changed: [],
    note: `DISCARDED ALL ${count} REVIEW-REJECTED PROPOSAL VARIANT(S): ${note.trim()}`,
  });
  working.proposals = emptyProposals() as unknown as typeof working.proposals;
  await saveWorkingState(ctx, working);
  await clearRoundOutputs(ctx);
  return count;
}

/** Apply the selected statement/definition changes to the proto, append the escalation
 *  entry, clear stale outputs. `ids` selects which proposed changes to apply (null = all).
 *  Returns the changed entries (empty if nothing matched). */
export async function applyProposedChanges(args: {
  ctx: PipelineContext;
  /** Selection. A plain `Set` of raw selector strings is wrapped with the default
   *  parsing; pass a `ProposalSelector` when the caller also needs `unmatched()`. */
  ids?: Set<string> | ProposalSelector | null;
  note?: string;
  directive?: string;
  /** Proof payloads explicitly rejected by the adjudicator. Their semantic variants
   * may still apply, but the target remains/reopens partial for a later reproof. */
  rejectedProofIds?: Set<string>;
  /** Validate the complete selected bundle in memory and return its change list
   * without mutating state, proto, working cursor, journal, or round outputs. */
  checkOnly?: boolean;
  /** bin/d0_author_edits.ts: the bundle is orchestrator-authored and proof-irrelevant.
   * The journal entry is provenance-only and the commit neither rewinds the stage nor
   * clears round outputs (it re-renders core.json). Fails closed unless every edit is a
   * statement-replace and nothing but statement justification/gap/consumer moves in the
   * proto or in any working record. */
  authoredMetadataOnly?: boolean;
  /** In-memory bundle for `authoredMetadataOnly` (bin/d0_author_edits.ts) so a preview or
   * a failure never touches the durable working cursor. Ignored otherwise. */
  proposalsOverride?: Awaited<ReturnType<typeof readProposedChanges>>;
  /** `authoredMetadataOnly`: per statement id, exactly the prose fields the orchestrator
   * supplied (compose echoes the rest from the carrier, which apply cannot tell apart). */
  authoredProseFields?: Record<string, ReadonlyArray<"justification" | "gap" | "consumer">>;
}): Promise<EscalationLogEntry["changed"]> {
  const { ctx, ids = null, note, directive, rejectedProofIds = new Set<string>(), checkOnly = false, authoredMetadataOnly = false } = args;
  if (args.proposalsOverride !== undefined && !authoredMetadataOnly) {
    throw new Error("proposalsOverride is only valid for an authored-metadata apply");
  }
  if (checkOnly && existsSync(applyTransactionPath(ctx))) {
    throw new Error(
      "D0 apply preview found an interrupted apply transaction; recover it with the apply CLI first, " +
      "then preview the committed state",
    );
  }
  const recovered = await recoverPendingApply(ctx);
  if (recovered !== null) return recovered;
  const sel = toSelector(ids);
  const protoPath = protoCoreJsonPath(ctx);
  const protoBytesAtRead = await readFile(protoPath, "utf8");
  // Parse through the raw-byte normalizer so a legacy proto persisted with an
  // under-escaped TeX escape (`"\theta"`) decodes to the intended backslash form.
  // `protoBytesAtRead` itself stays raw: the stale-write check below compares bytes.
  const proto = CoreSchema.parse(JSON.parse(normalizeRawModelJson(protoBytesAtRead))) as Core;
  // Canonicalize the frozen comparison basis before any `current` echo/staleness
  // checks. Legacy/model-authored JSON can decode `\texttt` as U+0009 + `exttt`;
  // the solver sees and re-emits the intended TeX spelling, so comparing before
  // repair falsely labels the proposal stale. The normalized proto is persisted
  // by the ordinary successful apply below.
  repairCoreLatexSerialization(proto);
  // Proof invalidation must see both sides of an atomic bundle. A definition or
  // assumption replacement can narrow `free_symbols` in the same transaction as a
  // symbol edit; consulting only the post-image would let that metadata change hide the
  // old proof's dependency immediately before the symbol basis is rebased.
  const protoBeforeEdits = structuredClone(proto);
  const working = await loadWorkingState(ctx);
  const workingBeforeEdits = working === null ? null : structuredClone(working);
  const preimageValidProofIds = computeValidNodes(workingBeforeEdits, protoBeforeEdits);
  const stmtById = authoritativeStatementCatalog(proto.statements, working);
  const defById = new Map(proto.definitions.map((d) => [d.id, d]));
  const assIds = new Set(proto.assumptions.map((a) => a.id));
  const bibKeys = (proto.bibliography ?? []).map((b) => b?.key).filter((k): k is string => typeof k === "string");
  const proposals = args.proposalsOverride ?? await readProposedChanges(ctx);
  const proposedProofIds = new Set(
    (proposals.proofs ?? [])
      .filter((proof) => typeof proof?.id === "string" && (proof.proof_tex ?? "").trim().length > 0)
      .map((proof) => proof.id),
  );
  const unknownRejectedProofIds = [...rejectedProofIds].filter((id) => !proposedProofIds.has(id));
  if (unknownRejectedProofIds.length > 0) {
    throw new Error(
      `Refusing D0 apply: explicitly rejected proof id(s) were not present in the reviewed bundle: ` +
        unknownRejectedProofIds.join(", "),
    );
  }
  if (rejectedProofIds.size > 0 && !note?.trim()) {
    throw new Error("Refusing D0 apply: explicit proof rejection requires a nonempty adjudication note");
  }
  const rejectedProofById = new Map(
    (proposals.proofs ?? [])
      .filter((proof) => rejectedProofIds.has(proof.id))
      .map((proof) => [proof.id, proof.proof_tex] as const),
  );
  const dedupe = <T>(values: T[]): T[] => {
    const seen = new Set<string>();
    return values.filter((value) => {
      const key = JSON.stringify(value);
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  };
  const statements = dedupe(proposals.statements);
  const definitions = dedupe(proposals.definitions);
  const assumptions = dedupe(proposals.assumptions);
  const citationRevalidations = dedupe(proposals.citationRevalidations ?? []);
  // Apply statement rewrites before statement deletions, and statement deletions before
  // definition cleanup. Live supersession bundles are emitted with mandates first, but
  // A→B cannot be validated/applied until B's reviewed dependency/claim cleanup has
  // landed; likewise carried obstruction lemmas must be deleted before their definitions.
  const editPriority = (edit: RawCoreEdit): number =>
    edit.kind === "statement-replace" ? 0 :
    edit.kind === "statement-delete" ? 1 :
    edit.kind === "definition-delete" ? 3 : 2;
  const coreEdits = dedupe(proposals.coreEdits)
    .map((edit, index) => ({ edit, index }))
    .sort((a, b) => editPriority(a.edit) - editPriority(b.edit) || a.index - b.index)
    .map(({ edit }) => edit);
  const hasPersistedReviewedBundle = statements.length > 0 || definitions.length > 0 ||
    assumptions.length > 0 || coreEdits.length > 0 || (proposals.proofs?.length ?? 0) > 0 ||
    citationRevalidations.length > 0;
  const hasPersistedDefinitionEdit = definitions.length > 0 ||
    coreEdits.some((edit) => edit.kind.startsWith("definition-"));
  if (hasPersistedReviewedBundle) {
    // Current solve commits seal every reviewed packet. Legacy hand-authored packets
    // without a seal retain their pre-existing per-edit checks, except definition
    // corrections (whose transitive semantic basis cannot be reconstructed safely).
    // Crucially, a PRESENT seal is universal: symbol/statement/proof-only bundles may
    // not ignore it merely because they contain no definition edit.
    if (proposals.basis_revision === undefined && hasPersistedDefinitionEdit) {
      throw new Error("Definition correction bundle lacks its persisted assembled-core basis revision; regenerate it");
    } else if (proposals.basis_revision !== undefined && working === null) {
      throw new Error("Reviewed D0 bundle lacks its persisted assembled-core basis revision; regenerate it");
    } else if (proposals.basis_revision !== undefined && working !== null) {
      const currentBasis = CoreSchema.parse(assembleCore(proto, working));
      if (proposals.basis_revision !== coreRevision(currentBasis)) {
        throw new Error("Reviewed D0 bundle no longer matches its persisted assembled-core basis; regenerate it");
      }
    }
  }
  const journal = await readEscalationLog(ctx);
  const pendingMandates = journal
    .slice(Math.min(working?.escalation_entries_consumed ?? 0, journal.length))
    .flatMap((entry) => entry.required_core_edit_mandates ?? []);
  const pendingCancellations = journal
    .slice(Math.min(working?.escalation_entries_consumed ?? 0, journal.length))
    .flatMap((entry) => entry.cancelled_core_edit_mandates ?? []);
  const mandateCandidates = [...(working?.required_core_edit_mandates ?? []), ...pendingMandates];
  const liveStateFile = statePath(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1");
  const liveProposalRevision = mandateCandidates.length > 0 && existsSync(liveStateFile)
    ? proposalRevision(await loadState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1"))
    : working?.proposal_revision;
  const mandates = resolveRequiredCoreEditMandates({
    mandates: mandateCandidates,
    cancellations: pendingCancellations,
    core: proto,
    working,
    proposalRevision: liveProposalRevision,
  });
  const mandatedCoreEdits = new Set<RawCoreEdit>();
  for (const mandate of mandates) {
    assertMandateBasis({
      mandate,
      core: proto,
      working,
      proposalRevision: liveProposalRevision,
    });
    // Compare under the SAME LaTeX repair on both sides. `coreEdits` come from
    // `working.proposals` (repaired on every load), while `mandate.edit` is in
    // the opaque set and keeps its sealed bytes — so a payload on which
    // `repairSerializedLatex` is not a no-op diverged BY REPAIR alone, and the
    // byte-compare then threw on every apply ("regenerate the packet"
    // deterministically reproduces it: a run deadlock, not a lost edit).
    const repairedMandateEdit = structuredClone(mandate.edit) as Record<string, unknown>;
    repairLatexStringsDeep(repairedMandateEdit);
    const match = coreEdits.find((edit) => JSON.stringify(edit) === JSON.stringify(repairedMandateEdit));
    if (!match) {
      throw new Error(
        `D0 apply lost or altered exact required core-edit mandate ${mandate.mandate_id}; regenerate the packet`,
      );
    }
    mandatedCoreEdits.add(match);
    if (sel && !sel.matchesCoreEdit(match)) {
      throw new Error(
        `D0 apply selection omits required core-edit mandate ${mandate.mandate_id}; mandated edits apply atomically`,
      );
    }
  }
  // A replacement endpoint is part of the mandate's frozen semantic snapshot. A
  // statement-replace may be necessary in the same reviewed bundle to remove A from
  // B's dependencies before A→B; permit only that stable structural cleanup.
  for (const mandate of mandates) {
    if (mandate.edit.kind !== "statement-delete" || mandate.edit.replacement_id === undefined) continue;
    const replacementId = mandate.edit.replacement_id;
    const sourceId = mandate.edit.id;
    const selectedClaimMutation = statements.some((change) =>
      change.id === replacementId && (!sel || sel.matchesStatement(change.id)));
    const selectedEndpointEdits = coreEdits.filter((edit) =>
      coreEditTarget(edit) === replacementId && (!sel || sel.matchesCoreEdit(edit)));
    const endpointCleanups = selectedEndpointEdits.filter(
      (edit): edit is Extract<RawCoreEdit, { kind: "statement-replace" }> =>
        edit.kind === "statement-replace");
    const cleanupDeps = endpointCleanups[0]?.proposed.depends_on;
    const endpointCurrentlyDependsOnSource =
      stmtById.get(replacementId)?.depends_on.includes(sourceId) === true ||
      working?.solved[replacementId]?.node?.depends_on.includes(sourceId) === true;
    const cleanupIsStable = cleanupDeps !== undefined &&
      !cleanupDeps.includes(sourceId) &&
      !cleanupDeps.includes(replacementId);
    if (
      selectedEndpointEdits.some((edit) => edit.kind !== "statement-replace") ||
      endpointCleanups.length > 1 ||
      (endpointCleanups.length === 1 && !cleanupIsStable) ||
      (selectedClaimMutation && endpointCleanups.length !== 1) ||
      (endpointCurrentlyDependsOnSource && !cleanupIsStable)
    ) {
      throw new Error(
        `D0 required delete ${sourceId}->${replacementId} requires one stable surviving replacement endpoint: ` +
        `no deletion, and any reviewed claim rewrite or dependency on ${sourceId} must be paired with one ` +
        `selected statement-replace removing both ${sourceId} and self-dependency ${replacementId}`,
      );
    }
  }
  // A `statement-replace` changes dependencies/metadata but — by its statement/status
  // echo requirement — never the claim text. When the SAME round also emits a proof for that
  // node, the solver wrote that proof against exactly this rewiring, in one unit, in one
  // output. Landing the edit while discarding its paired proof marks the node `partial`
  // and spends a whole solve round re-confirming a proof that was already correct for the
  // statement it is attached to. Commit them together instead.
  //
  // Deliberately NOT extended to `proposed_statement_changes`: those change the CLAIM, and
  // a unit owes "a proof OR a proposed change" per target, so a proof present in the same
  // round was written against the OLD text. That pairing would certify a proof against a
  // claim it never saw — which is the exact substitution the snapshot invariant exists to
  // catch. Claim changes stay partial.
  // A paired proof may only clear `partial` if the closure it now rests on is itself
  // sound after THIS apply. Two ways it would not be: the rewiring points at a node that
  // is itself partial this round, or the orchestrator accepted this edit while rejecting
  // another the new proof relies on (an apply-subset). `computeValidNodes` would re-stale
  // the node at the next solve either way — staleness propagates along `depends_on` to a
  // fixpoint — so this guard is not the only line of defence, but asserting validity we
  // have not checked is the wrong default when the whole point of the flag is to certify.
  // Definition/assumption corrections this bundle PROPOSED but is not applying. A proof
  // emitted in the same round was written against the CORRECTED formula, so settling it
  // when the operator accepted the statement edit and rejected the correction rests it on
  // content that never changed. Selection is per-id, so this is reachable with `--ids`.
  //
  // Covers ALL THREE channels a support correction can arrive through: the raw definition
  // and assumption change lists, AND typed core edits (definition-add/replace/delete,
  // assumption-replace). Omitting the core-edit channel left the same hole this guard was
  // written to close -- three auditors flagged it independently.
  const rejectedSupportIds = new Set<string>([
    ...definitions.filter((c) => sel && !sel.matchesDefinition(c.id)).map((c) => c.id),
    ...assumptions.filter((a) => sel && !sel.matchesAssumption(a.id)).map((a) => a.id),
    ...coreEdits
      .filter((e) => sel && !sel.matchesCoreEdit(e))
      .filter((e) => e.kind.startsWith("definition-") || e.kind.startsWith("assumption-"))
      .map((e) => coreEditTarget(e)),
    // A CITED node's `source` is support too: a proof written against a corrected locator
    // rests on that correction. A statement-replace carrying a new `source` is therefore a
    // fourth channel, and rejecting it while accepting the consumer settles the proof
    // against the locator it was written to replace.
    ...coreEdits
      .filter((e) => sel && !sel.matchesCoreEdit(e))
      .filter((e): e is Extract<RawCoreEdit, { kind: "statement-replace" }> => e.kind === "statement-replace")
      .filter((e) => {
        const current = proto.statements.find((st) => st.id === e.id);
        return current?.status === "cited" &&
          JSON.stringify(current.source ?? null) !== JSON.stringify(e.proposed?.source ?? null);
      })
      .map((e) => e.id),
  ]);
  // Definition-containing rounds cannot reach this check under a partial selection: the
  // coherence-closure guard above accepts or rejects every variant together. That is the
  // conservative substitute for inventing a second transitive definition graph solely in
  // apply; ordinary non-definition support still uses the direct closure below.
  const dependencyClosureValid = (node: CoreStatement): boolean =>
    (node.depends_on ?? []).every((dep) => {
      // A REJECTED correction invalidates the proof whatever KIND of node it sits on. This
      // test was inside the def:/ass: branch only, so adding cited statement ids to the set
      // produced a guard that could never read them -- the same cannot-fire shape this
      // sweep kept finding elsewhere. Check it for every dependency first.
      if (rejectedSupportIds.has(dep)) return false;
      if (dep.startsWith("def:") || dep.startsWith("ass:")) {
        return true; // otherwise carried in the snapshot itself
      }
      // A FROZEN dependency used to pass on existence alone, while an agent dependency had
      // to carry a non-partial record. But a frozen member's proof lives in the WORKING
      // cursor, not in the proto -- so an unproved or partial frozen dependency was treated
      // as discharged, and its consumer's `partial` flag was cleared on that basis.
      // A `cited` frozen node is genuinely self-discharged: its justification is the
      // citation, so it needs no working proof.
      const frozen = proto.statements.find((s) => s.id === dep);
      const rec = working?.solved[dep];
      // `partial` OUTRANKS the cited exemption: a cited leaf carrying a partial record is
      // awaiting revalidation of its claim or source (that is exactly how a reopened cited
      // node is represented), so it is not discharged yet.
      if (rec?.partial) return false;
      if (frozen?.status === "cited") return true;
      return rec !== undefined && !rec.partial;
    });
  const pairedProofById = new Map(
    (proposals.proofs ?? [])
      .filter((p) => typeof p?.id === "string" && (p.proof_tex ?? "").trim().length > 0)
      .filter((p) => !rejectedProofIds.has(p.id))
      .map((p) => [
        p.id,
        {
          proofTex: p.proof_tex as string,
          arguesProposed: (p as { argues_proposed?: unknown }).argues_proposed === true,
        },
      ] as const),
  );
  // Dedupe is keyed on CONTENT, so two proposals for the SAME id with DIFFERENT
  // proposed text both survive it, both apply in sequence (last writer wins on the
  // proto), and — because each contributes equally to the selected and applied
  // counts — the atomicity guard below cannot detect it. Silently applying the
  // second of two conflicting edits to one node is exactly the kind of unlogged
  // divergence that made core.json and proto_core.json disagree. Refuse instead.
  //
  // The guard covered `statements` and `definitions` only, leaving three channels where
  // the same silent last-writer-wins was still reachable: two PROOFS for one id collapse
  // in the Map built above, and two ASSUMPTIONS or two CORE EDITS on one target apply in
  // array order. Every channel that keys by id needs it.
  for (const [label, keys] of [
    ["statement", statements.filter((c) => !sel || sel.matchesStatement(c.id)).map((c) => c.id)],
    ["definition", definitions.filter((c) => !sel || sel.matchesDefinition(c.id)).map((c) => c.id)],
    ["assumption", assumptions.filter((a) => !sel || sel.matchesAssumption(a.id)).map((a) => a.id)],
    ["proof", (proposals.proofs ?? [])
      .filter((p) => typeof p?.id === "string" && (p.proof_tex ?? "").trim().length > 0)
      .map((p) => p.id)],
    ["citation revalidation", citationRevalidations.map((receipt) => receipt.id)],
    // Keyed by KIND+target: a statement-replace and a rebuild on one node are independent
    // and legitimate; two statement-replaces on it are not. `rebuild-reverse-dependencies`
    // is exempt — it is idempotent, so repeats are harmless whatever their stated reason.
    // Keyed by KIND+target so a statement-replace and a metadata rebuild on one node stay
    // independent. But DIFFERENT kinds can also be mutually exclusive -- a replace and a
    // delete, or an add and a replace, on the same object -- and those keys differ, so both
    // applied in array order and the later silently erased the earlier while the
    // selected-vs-applied count still matched. Collapse the mutually exclusive kinds onto
    // one key per target so any two of them conflict.
    ["core-edit", coreEdits
      .filter((e) => !sel || sel.matchesCoreEdit(e))
      .filter((e) => e.kind !== "rebuild-reverse-dependencies")
      .map((e) => {
        const EXCLUSIVE: Record<string, string> = {
          "statement-replace": "statement", "statement-delete": "statement",
          "definition-add": "definition", "definition-replace": "definition",
          "definition-delete": "definition",
          "symbol-add": "symbol", "symbol-replace": "symbol", "symbol-delete": "symbol",
          "assumption-replace": "assumption", "assumption-delete": "assumption",
        };
        return `${EXCLUSIVE[e.kind] ?? e.kind}:${coreEditTarget(e)}`;
      })],
  ] as const) {
    const byId = new Map<string, number>();
    for (const k of keys) byId.set(k, (byId.get(k) ?? 0) + 1);
    const conflicted = [...byId.entries()].filter(([, n]) => n > 1).map(([id]) => id);
    if (conflicted.length > 0) {
      throw new Error(
        `Refusing D0 apply: ${conflicted.length} ${label} id(s) carry MULTIPLE conflicting proposals ` +
          `(${conflicted.join(", ")}). Applying them in sequence would silently keep only the last. ` +
          `Resolve to one proposal per id before applying. Nothing was mutated.`,
      );
    }
  }
  // Validate only newly selected/model-authored publishable fields. Running the
  // strict TeX gate over the whole proto is not backward-compatible with legacy
  // formal DSL (for example `E_n\{a,b}`), while scanning raw working state also
  // misreads non-TeX fingerprints. New solve output is checked at ingest, but a
  // legacy/recovered proposal can predate that boundary, so apply repeats the
  // gate over exactly the bytes this transaction may introduce or promote.
  const selectedStatements = statements.filter((change) => !sel || sel.matchesStatement(change.id));
  const selectedDefinitions = definitions.filter((change) => !sel || sel.matchesDefinition(change.id));
  const selectedAssumptions = assumptions.filter((change) => !sel || sel.matchesAssumption(change.id));
  const selectedCoreEdits = coreEdits.filter((edit) => !sel || sel.matchesCoreEdit(edit));
  const atomicDefinitionDeleteIds = new Set(
    selectedCoreEdits.filter((edit) => edit.kind === "definition-delete").map((edit) => edit.id),
  );
  const hasDefinitionEdit = definitions.length > 0 ||
    coreEdits.some((edit) => edit.kind.startsWith("definition-"));
  const totalVariantCount = statements.length + definitions.length + assumptions.length + coreEdits.length;
  const selectedVariantCount = selectedStatements.length + selectedDefinitions.length +
    selectedAssumptions.length + selectedCoreEdits.length;
  if (hasDefinitionEdit && sel && selectedVariantCount !== totalVariantCount) {
    throw new Error("A bundle containing a definition edit must be selected as one complete coherence closure");
  }
  if (citationRevalidations.length > 0 && sel && selectedVariantCount !== totalVariantCount) {
    throw new Error(
      "A bundle containing cited-source revalidation receipts must be selected as one complete coherence closure",
    );
  }
  // A formula/claim correction and its complete post-image metadata are one
  // reviewed unit. Definition-containing bundles are all-or-nothing above;
  // these checks also reject incomplete legacy/current pairs explicitly.
  for (const change of definitions) {
    const changeSelected = selectedDefinitions.includes(change);
    const pairExists = coreEdits.some(
      (edit) => edit.kind === "definition-replace" && edit.id === change.id &&
        edit.proposed.construction === change.proposed,
    );
    const pairSelected = selectedCoreEdits.some(
      (edit) => edit.kind === "definition-replace" && edit.id === change.id &&
        edit.proposed.construction === change.proposed,
    );
    if (pairExists && changeSelected !== pairSelected) {
      throw new Error(`Definition correction pair ${change.id} must be selected atomically`);
    }
    if (changeSelected && !pairExists) {
      throw new Error(`Definition correction ${change.id} lacks its exact complete definition-replace; regenerate it`);
    }
    const pair = selectedCoreEdits.find(
      (edit): edit is Extract<RawCoreEdit, { kind: "definition-replace" }> =>
        edit.kind === "definition-replace" && edit.id === change.id &&
        edit.proposed.construction === change.proposed,
    );
    if (changeSelected && pair &&
        (change.based_on_revision === undefined || pair.based_on_revision === undefined)) {
      throw new Error(`Definition correction pair ${change.id} lacks a complete pre-bundle revision; regenerate it`);
    }
    if (changeSelected && pair && change.based_on_revision !== pair.based_on_revision) {
      throw new Error(`Definition correction pair ${change.id} must cite one frozen semantic-basis revision`);
    }
  }
  for (const edit of selectedCoreEdits) {
    if (edit.kind !== "definition-replace") continue;
    if (mandatedCoreEdits.has(edit)) continue;
    const authored = defById.get(edit.id);
    if (authored === undefined || edit.proposed.construction === authored.construction) continue;
    const pair = selectedDefinitions.find(
      (change) => change.id === edit.id && change.proposed === edit.proposed.construction &&
        change.based_on_revision === edit.based_on_revision,
    );
    if (pair === undefined) {
      throw new Error(`Construction-changing definition-replace ${edit.id} lacks its exact formula correction pair`);
    }
  }
  for (const change of statements) {
    const changeSelected = selectedStatements.includes(change);
    const pairExists = coreEdits.some(
      (edit) => edit.kind === "statement-replace" && edit.id === change.id &&
        edit.proposed.statement === change.proposed,
    );
    const pairSelected = selectedCoreEdits.some(
      (edit) => edit.kind === "statement-replace" && edit.id === change.id &&
        edit.proposed.statement === change.proposed,
    );
    if (pairExists && changeSelected !== pairSelected) {
      throw new Error(`Statement correction pair ${change.id} must be selected atomically`);
    }
    if (changeSelected && !pairExists) {
      throw new Error(`Statement correction ${change.id} lacks its exact complete statement-replace; regenerate it`);
    }
  }
  for (const edit of selectedCoreEdits) {
    if (edit.kind !== "statement-replace") continue;
    const authored = stmtById.get(edit.id);
    if (authored === undefined || edit.proposed.statement === authored.statement) continue;
    const pair = selectedStatements.find(
      (change) => change.id === edit.id && change.proposed === edit.proposed.statement &&
        (change.based_on_revision === undefined || edit.based_on_revision === undefined ||
          change.based_on_revision === edit.based_on_revision),
    );
    if (pair === undefined) {
      throw new Error(`Claim-changing statement-replace ${edit.id} lacks its exact statement correction pair`);
    }
  }
  const atomicStatementDeleteIds = new Set(
    selectedCoreEdits.filter((edit) => edit.kind === "statement-delete").map((edit) => edit.id),
  );
  // Statement deletion is validated against the complete selected transaction,
  // including symbol cleanup that executes later.  Simulate only structurally
  // applicable symbol operations; any other selected edit still trips the final
  // all-variants-applied guard, preserving atomicity.
  const atomicSymbolPostimage = structuredClone(proto.symbols);
  for (const edit of selectedCoreEdits) {
    if (edit.kind === "symbol-add") {
      if (!atomicSymbolPostimage.some((symbol) => symbol.name === edit.name) &&
          edit.proposed.name === edit.name) atomicSymbolPostimage.push(structuredClone(edit.proposed));
    } else if (edit.kind === "symbol-replace") {
      const index = atomicSymbolPostimage.findIndex((symbol) => symbol.name === edit.name);
      if (index >= 0 && edit.proposed.name === edit.name) {
        atomicSymbolPostimage[index] = structuredClone(edit.proposed);
      }
    } else if (edit.kind === "symbol-delete") {
      const index = atomicSymbolPostimage.findIndex((symbol) => symbol.name === edit.name);
      if (index >= 0) atomicSymbolPostimage.splice(index, 1);
    }
  }
  const coreEditPublishablePayload = (edit: RawCoreEdit): unknown => {
    switch (edit.kind) {
      case "assumption-replace":
      case "definition-add":
      case "definition-replace":
      case "bibliography-replace":
      case "symbol-add":
      case "symbol-replace":
        return edit.proposed;
      case "statement-replace": {
        // `statement` is an echo of durable old content, not a byte introduced
        // by this metadata/dependency channel. Validate only the authored delta.
        const { id: _id, kind: _kind, statement: _statement, status: _status, ...metadata } = edit.proposed;
        return metadata;
      }
      case "target-estimand-replace":
      case "estimand-functional-replace":
      case "comparator-promise-table-replace":
        return edit.proposed;
      default:
        return undefined;
    }
  };
  // Validate each selected change INDIVIDUALLY so one malformed field names its
  // own change instead of aborting the transaction with an opaque array index.
  // Apply stays atomic: any offense still refuses the whole transaction, but the
  // error enumerates exactly which change ids to exclude on re-selection, so the
  // other accepted changes apply without a solver round or manual byte hunting.
  const sealOffenders: string[] = [];
  const checkSealable = (kind: string, id: string, payload: unknown): void => {
    try {
      assertSealableLatexPayload(payload, `${kind} ${id}`);
    } catch (err) {
      sealOffenders.push(`${kind} ${id}: ${err instanceof Error ? err.message : String(err)}`);
    }
  };
  for (const change of selectedStatements) checkSealable("statement-change", change.id, change.proposed);
  for (const change of selectedDefinitions) checkSealable("definition-change", change.id, change.proposed);
  for (const change of selectedAssumptions) {
    checkSealable("assumption", change.id, {
      condition: change.condition,
      ...(change.free_symbols === undefined ? {} : { free_symbols: change.free_symbols }),
      ...parseAssumptionTag(change.standard_or_novel, bibKeys),
    });
  }
  for (const edit of selectedCoreEdits) {
    const payload = coreEditPublishablePayload(edit);
    if (payload !== undefined) checkSealable(`core-edit ${edit.kind}`, coreEditTarget(edit), payload);
  }
  for (const proof of proposals.proofs ?? []) {
    checkSealable("promotable-proof", proof.id, proof.proof_tex);
  }
  for (const receipt of citationRevalidations) {
    checkSealable("citation-revalidation", receipt.id, receipt);
  }
  if (sealOffenders.length > 0) {
    throw new Error(
      `Refusing D0 apply: ${sealOffenders.length} selected change(s) carry unsealable TeX in ` +
        `${protoPath}. Re-select without these ids (repair them via the mechanical rebuild lane); ` +
        `nothing was mutated.\n${sealOffenders.join("\n")}`,
    );
  }
  const recoveredMutationIds = new Set([
    ...selectedStatements.map((change) => change.id),
    ...selectedCoreEdits
      .filter((edit) => edit.kind === "statement-replace")
      .map((edit) => edit.id),
  ]);
  for (const id of recoveredMutationIds) {
    if (proto.statements.some((statement) => statement.id === id) || working?.solved[id]?.node) continue;
    const recovered = stmtById.get(id);
    const resolution = working?.resolved_oeqs?.[id];
    if (!working || recovered?.kind !== "openendedquestion" ||
        resolution === undefined || typeof resolution === "string") continue;
    recordProof(working, proto, {
      id,
      snapshotOf: recovered,
      proofTex: "",
      node: structuredClone(recovered),
      owner: id,
      partial: true,
    });
    delete working.resolved_oeqs![id];
    if (Object.keys(working.resolved_oeqs!).length === 0) delete working.resolved_oeqs;
    if (working.sealed_open_oeqs !== undefined) {
      delete working.sealed_open_oeqs[id];
      if (Object.keys(working.sealed_open_oeqs).length === 0) delete working.sealed_open_oeqs;
    }
    stmtById.set(id, working.solved[id].node!);
  }
  const originalStatements = new Map(proto.statements.map((s) => [s.id, structuredClone(s)] as const));
  const originalDefinitions = new Map(proto.definitions.map((d) => [d.id, structuredClone(d)] as const));
  const originalCarriedStatements = new Map(
    Object.entries(working?.solved ?? {})
      .filter((entry): entry is [string, NonNullable<(typeof entry)[1]>] => entry[1] !== undefined)
      .flatMap(([id, rec]) => rec.node ? [[id, structuredClone(rec.node)] as const] : []),
  );
  /** Demote an adjudicated, reopened OEQ's former answer to an ordinary carried
   * theorem. The theorem record is intentionally untouched. */
  const detachResolvedOeq = (sourceId: string): void => {
    if (working?.resolved_oeqs?.[sourceId] === undefined) return;
    delete working.resolved_oeqs[sourceId];
  };

  const changed: EscalationLogEntry["changed"] = [];

  /** Selected edits dropped by a validation, with the clause that rejected them. */

  const skipped: Array<{ id: string; kind: string; why: string }> = [];
  // Ids whose CLAIM this bundle rewrites. A proof paired in the same bundle was written
  // against the OLD claim, so attaching it to the new one — and clearing `partial` — would
  // present a proof of one statement as a proof of another.
  const claimChangedIds = new Set<string>();
  // Cited leaves this bundle reopens (claim changed, citation kept). They MUST become
  // exact required targets of the next solve: the supported revalidation channel is a
  // byte-faithful `added_lemmas` re-emission, and the dispatcher only puts a reopened
  // cited node on the solve frontier when it is explicitly required — without this, a
  // solver-proposed narrowing (no referee escalation naming the node) leaves the leaf
  // partial with no round ever directed at it.
  const reopenedCitedIds: string[] = [];
  for (const c of statements) {
    if (sel && !sel.matchesStatement(c.id)) continue;
    const s = stmtById.get(c.id);
    if (!s) {
      // Agent-added nodes intentionally do not live in the frozen proposal proto.
      // Their durable definition is the carried working-state node, independently
      // of whether its current proof is complete. Apply the correction there and
      // mark the proof partial so the next D0 assembly re-proves the new claim.
      const carried = working?.solved[c.id];
      const node = carried?.node;
      if (!carried || !node || node.id !== c.id) {
        skipped.push({ id: c.id, kind: "statement-change", why: "no carried node for this id in the working cursor" });
        continue;
      }
      if (c.current !== undefined && c.current !== originalCarriedStatements.get(c.id)?.statement) {
        // A stale proposal: the node moved since this change was generated. Applying it
        // would silently discard whatever moved it. Record the drop so the bundle guard
        // can name it instead of failing with a bare count.
        skipped.push({
          id: c.id, kind: "statement-change",
          why: "stale proposal — `current` no longer matches the carried node's statement, so applying it would discard the intervening change",
        });
        continue;
      }
      const prior = node.statement;
      claimChangedIds.add(c.id);
      node.statement = c.proposed;
      node.proof_tex = undefined;
      if (node.source !== undefined) {
        // A cited node awaiting source/claim revalidation remains a schema-valid
        // cited leaf in the durable catalog; `partial` carries the invalidation.
        // Encoding it as to-prove while retaining source violates G-cited and can
        // poison interruption recovery before the solver re-emits the citation.
        node.status = "cited";
        reopenedCitedIds.push(c.id);
      } else {
        node.status = "to-prove";
      }
      carried.node = node;
      // Deliberately NOT re-snapshotting: the record's bytes argued the PREVIOUS claim,
      // and the old-basis snapshot is what lets dispatch label them as such (mirroring
      // the frozen branch). `partial` alone carries the invalidation; the snapshot is
      // rewritten when a proof of the new claim lands.
      carried.partial = true;
      changed.push({
        id: c.id,
        kind: "statement",
        from: prior,
        to: c.proposed,
        reason: c.reason ?? "",
      });
      continue;
    }
    // FROZEN statements got no echo check while carried nodes did (above). A proposal
    // generated when the node said X, applied after it moved to Y, overwrote Y with the
    // proposal's text and the intervening change was lost with no error anywhere. Same
    // guard, same reporting, both branches.
    if (c.current !== undefined && c.current !== s.statement) {
      skipped.push({
        id: c.id, kind: "statement-change",
        why: "stale proposal — `current` no longer matches the frozen proto statement, so applying it would discard the intervening change",
      });
      continue;
    }
    const priorFrozenStatement = s.statement;
    changed.push({ id: c.id, kind: "statement", from: priorFrozenStatement, to: c.proposed, reason: c.reason ?? "" });
    claimChangedIds.add(c.id);
    s.statement = c.proposed;
    // An accepted narrowing of a resolved OEQ is a role transition, not a theorem
    // deletion: the old answer no longer discharges the whole residual question, but
    // its own unchanged theorem/proof remains valid partial-result mathematics. Remove
    // only the source->answer replacement now, while the adjudicated narrowing and the
    // durable theorem record are both in hand. On the next assembly the theorem follows
    // the ordinary agent-node carry path and the narrowed OEQ reopens. Out-of-band or
    // fingerprint mismatches follow the same detach-and-rederive rule in `planCarry`;
    // only an explicit remap to a different answer supersedes the old theorem.
    if (s.kind === "openendedquestion") detachResolvedOeq(c.id);
    // REOPEN a settled frozen node. Only the statement text was rewritten, so a node that
    // was `proved` kept its old proof_tex and status — the previous proof, of the PREVIOUS
    // claim, presented as proving the new one. The carried-node branch above already
    // clears its proof on a claim change; this branch did not. Real protos carry settled
    // statements (12 proved and one cited across the repo, proofs up to ~2.9k chars), so
    // this is reachable, not theoretical.
    //
    // `cited` reopens too: the citation documents the claim as it stood, and `source` must
    // go with it or the node fails the schema's cited <=> source rule.
    if (s.status === "proved" || s.status === "cited") {
      if (s.status === "cited" && s.source !== undefined) {
        // MIRROR THE CARRIED BRANCH, which documents this: a cited node awaiting
        // revalidation stays a schema-valid cited leaf and `partial` on its working record
        // carries the invalidation. Converting it to `to-prove` and deleting `source`
        // destroys the only durable copy of the locator, so the next solve cannot even
        // re-check the citation -- it can only re-prove the result from scratch.
        s.proof_tex = undefined;
        reopenedCitedIds.push(c.id);
      } else {
        s.status = "to-prove";
        s.proof_tex = undefined;
      }
      // Either way the CURSOR must reopen: a frozen member's proof lives there, and it
      // argued the previous claim. The BYTES stay as the node's single hot partial
      // repair basis — a narrowing usually preserves most of the argument, and blanking
      // them both restarted the next round from nothing and lost them forever. The
      // record's snapshot deliberately keeps the OLD basis, so staleness reads correctly
      // and dispatch can label the partial as arguing a previous claim. `partial` alone
      // carries the invalidation (a partial record is never a reusable proof).
      const rec = working?.solved[c.id];
      if (rec) {
        rec.partial = true;
      } else if (working && s.status === "cited") {
        // A frozen CITED member normally has NO working record (a citation needs no
        // proof of ours), so the `partial` marker above had nothing to land on and the
        // OLD citation silently re-certified the NEW claim — the exact laundering the
        // reopen contract forbids. Seed the record the contract expects: an OLD-basis
        // snapshot (so dispatch labels it as arguing the previous claim) carrying
        // `partial`, which outranks the cited exemption at every discharge gate until
        // the byte-faithful revalidation receipt lands.
        working.solved[c.id] = {
          proof_tex: "",
          snapshot: wiredSnapshot(proto, { ...s, statement: priorFrozenStatement }, ""),
          partial: true,
        };
      }
    }
  }
  for (const c of definitions) {
    if (sel && !sel.matchesDefinition(c.id)) continue;
    const d = defById.get(c.id);
    if (!d) {
      skipped.push({ id: c.id, kind: "definition-change", why: "no frozen proto definition with this id" });
      continue;
    }
    if (c.current !== undefined && c.current !== d.construction) {
      skipped.push({
        id: c.id, kind: "definition-change",
        why: "stale proposal — `current` no longer matches the definition's construction, so applying it would discard the intervening change",
      });
      continue;
    }
    changed.push({ id: c.id, kind: "definition", from: d.construction, to: c.proposed, reason: c.reason ?? "" });
    d.construction = c.proposed;
  }
  // NEW ASSUMPTIONS — add a solver-proposed assumption node to the proto (skip if it already
  // exists). Built as a gate-valid node (the solver's declared `free_symbols`, empty when it
  // declared none, plus a parsed standard/novel tag); the escalation-log entry records it for
  // approval-at-bank (the add-prove-approve-later trail). The declaration is carried rather
  // than stubbed to `[]` because it scopes symbol invalidation for every statement that
  // reaches a symbol only THROUGH this assumption.
  for (const a of assumptions) {
    if (sel && !sel.matchesAssumption(a.id)) continue;
    if (assIds.has(a.id)) {
      // Every selected-but-inapplicable variant must record WHY, or the partial-apply
      // refusal below fires with "No per-edit reason was recorded".
      skipped.push({ id: a.id, kind: "assumption", why: "an assumption with this id is already present in the frozen proto (no-op re-proposal)" });
      continue;
    }
    // Preserve ABSENT as absent: `?? []` here recorded a solver that omitted the field as
    // "uses no symbols", the unsafe reading (see AssumptionSchema.free_symbols).
    const node = {
      id: a.id,
      condition: a.condition,
      ...(a.free_symbols === undefined ? {} : { free_symbols: a.free_symbols }),
      ...parseAssumptionTag(a.standard_or_novel, bibKeys),
    };
    proto.assumptions.push(node as (typeof proto.assumptions)[number]);
    assIds.add(a.id);
    changed.push({ id: a.id, kind: "assumption", from: "", to: a.condition, reason: a.reason ?? "" });
  }

  // Assumption deletion validates that every structured and authored reference has
  // already been removed. Evaluate it after the bundle's statement/definition/prose
  // repairs, independent of the model's array order; reverse-edge rebuild remains last.
  const orderedCoreEdits = [...coreEdits].sort((a, b) => {
    const rank = (edit: RawCoreEdit): number =>
      edit.kind === "rebuild-reverse-dependencies" ? 2 : edit.kind === "assumption-delete" ? 1 : 0;
    return rank(a) - rank(b);
  });
  for (const edit of orderedCoreEdits) {
    const target = coreEditTarget(edit);
    if (sel && !sel.matchesCoreEdit(edit)) continue;
    if (edit.kind === "assumption-replace") {
      const i = proto.assumptions.findIndex((a) => a.id === edit.id);
      if (i === -1 || edit.proposed.id !== edit.id) {
        skipped.push({
          id: edit.id,
          kind: "assumption-replace",
          why: i === -1 ? "no frozen assumption with this id" : `payload id '${edit.proposed.id}' does not match the edit target`,
        });
        continue;
      }
      changed.push({
        id: edit.id,
        kind: "assumption",
        from: JSON.stringify(proto.assumptions[i]),
        to: JSON.stringify(edit.proposed),
        reason: edit.reason ?? "",
      });
      proto.assumptions[i] = edit.proposed;
    } else if (edit.kind === "assumption-delete") {
      const prior = proto.assumptions.find((a) => a.id === edit.id);
      if (!prior) {
        skipped.push({ id: edit.id, kind: "assumption-delete", why: "no frozen assumption with this id" });
        continue;
      }
      const inbound = proto.statements
        .filter((s) => s.depends_on.includes(edit.id))
        .map((s) => s.id);
      const carriedInbound = Object.entries(working?.solved ?? {})
        .filter(([, rec]) => rec.node?.depends_on.includes(edit.id))
        .map(([id]) => id);
      const textInbound = findUnsafeDeleteTextReferences(proto, working, edit.id);
      if (inbound.length > 0 || carriedInbound.length > 0 || textInbound.length > 0) {
        const locations = [
          ...inbound.map((id) => `${id}.depends_on`),
          ...carriedInbound.map((id) => `working.${id}.node.depends_on`),
          ...textInbound.map((ref) => ref.location),
        ];
        throw new Error(
          `Cannot delete assumption ${edit.id}: live premise references remain in ${[...new Set(locations)].join(", ")}. ` +
            "Remove the premise through explicit reviewed statement/definition/prose/proof edits in the same bundle; " +
            "assumption deletion never rewrites mathematical content implicitly.",
        );
      }
      proto.assumptions = proto.assumptions.filter((a) => a.id !== edit.id);
      assIds.delete(edit.id);
      rebuildAssumptionUsedBy(proto, carriedStatements(working));
      changed.push({
        id: edit.id,
        kind: "assumption",
        from: JSON.stringify(prior),
        to: "<deleted>",
        reason: edit.reason ?? "",
      });
    } else if (edit.kind === "statement-replace") {
      const i = proto.statements.findIndex((s) => s.id === edit.id);
      const prior = proto.statements[i];
      if (i === -1) {
        const carried = working?.solved[edit.id];
        const carriedNode = carried?.node;
        const originalNode = originalCarriedStatements.get(edit.id);
        if (!carried || !carriedNode || !originalNode) {
          skipped.push({ id: edit.id, kind: "statement-replace", why: "no carried node for this id in the working cursor" });
          continue;
        }
        // Phase 2: a revision-bearing edit pins its view by hash — the legal
        // views here are the pre-bundle original and (when the same bundle also
        // rewrote the claim) the selected paired-claim node. Edits without the
        // field keep the byte-echo fallback unchanged.
        const mismatch = edit.based_on_revision !== undefined
          ? describeRevisionMismatch(
              edit.based_on_revision,
              edit.proposed,
              claimChangedIds.has(edit.id) ? [originalNode, carriedNode] : [originalNode],
              edit.id,
            )
          : claimChangedIds.has(edit.id)
            ? describePairedClaimEchoMismatch(edit.proposed, originalNode, carriedNode, edit.id)
            : describeEchoMismatch(edit.proposed, originalNode, edit.id);
        if (mismatch) {
          skipped.push({ id: edit.id, kind: "statement-replace", why: mismatch });
          continue;
        }
        const { partial_result: _reviewPartial, ...proposedNode } = edit.proposed;
        const composed = {
          ...carriedNode,
          ...proposedNode,
          statement: carriedNode.statement,
          status: carriedNode.status,
          free_symbols: proposedNode.free_symbols,
          proof_tex: carriedNode.proof_tex,
        };
        changed.push({
          id: edit.id,
          kind: "statement",
          from: JSON.stringify(carriedNode),
          to: JSON.stringify(composed),
          reason: edit.reason ?? "",
        });
        if (
          !pairedProofById.has(edit.id) &&
          composed.status === "cited" && composed.source !== undefined && !claimChangedIds.has(edit.id)
        ) {
          // A source-corrected cited leaf is discharged by the corrected source
          // object itself; converting it to `to-prove` both violates G-cited and
          // creates an unnecessary D0 re-solve loop.
          //
          // But NOT when this bundle also rewrote the claim. This branch runs BEFORE the
          // paired-proof guard below, so a cited node whose claim changed took the
          // shortcut, cleared `partial`, and was settled by a citation that certifies the
          // OLD statement. The claim-change guard added for paired proofs did not cover
          // it; three independent auditors caught that in the same pass.
          carried.node = composed;
          carried.proof_tex = composed.proof_tex ?? "";
          carried.snapshot = wiredSnapshot(proto, composed, composed.proof_tex ?? "");
          delete carried.partial;
        } else if (
          // A metadata-only replacement does not owe a re-proof when the theorem's
          // proof-relevant snapshot is byte-for-byte unchanged. Previously even a
          // consumer/gap/route edit converted a finished agent theorem into partial
          // debt solely because no redundant paired proof was emitted.
          !pairedProofById.has(edit.id) &&
          composed.status === "proved" &&
          (carried.proof_tex ?? "").trim().length > 0 &&
          // A SHRINKING declaration is a basis change, so the node owes a re-derivation
          // rather than keeping its proof. Checked BEFORE `memberValid`, which would
          // otherwise evaluate the node against the already-narrowed scope and conclude it
          // is fine — the narrowing would escape detection and persist in the same step.
          !declarationNarrowed(carried.node, composed) &&
          memberValid(working, proto, composed) &&
          dependencyClosureValid(composed)
        ) {
          carried.node = { ...composed, proof_tex: carried.proof_tex };
          carried.snapshot = wiredSnapshot(proto, composed, carried.proof_tex ?? "");
          delete carried.partial;
        } else if (claimChangedIds.has(edit.id) && composed.status === "cited" && composed.source !== undefined) {
          // A changed cited claim remains a schema-valid cited leaf until the
          // source is revalidated. `partial` records that the retained source
          // still supports the old claim; do not silently erase its metadata.
          carried.node = { ...composed, proof_tex: undefined };
          carried.partial = true;
        } else {
          // Reopening a CITED node must drop `source` too: the schema ties
          // cited <=> source, so `to-prove` with a surviving source is invalid.
          carried.node = { ...composed, status: "to-prove", proof_tex: undefined, source: undefined };
          // When the SAME bundle also rewrote this node's claim, the claim-change branch
          // preserved the OLD-basis snapshot with the retained bytes; re-snapshotting
          // here against the new claim would erase what the bytes argued and mute the
          // previous-statement dispatch warning.
          if (!claimChangedIds.has(edit.id)) carried.snapshot = wiredSnapshot(proto, carried.node, carried.proof_tex ?? "");
          carried.partial = true;
        }
        continue;
      }
      const original = originalStatements.get(edit.id);
      if (!original) {
        skipped.push({ id: edit.id, kind: "statement-replace", why: "no frozen proto statement with this id" });
        continue;
      }
      const protoRecBefore = working?.solved[edit.id];
      const hasSettledOverlay = protoRecBefore !== undefined &&
        protoRecBefore.partial !== true &&
        protoRecBefore.proof_tex.trim().length > 0 &&
        original.status === "to-prove" &&
        memberValid(working, proto, original);
      // Frozen proto nodes remain `to-prove`; their proved status/proof live in the
      // working overlay. The solver and canonical review packet see that assembled
      // proved view, so statement-replace must echo IT, not the lower frozen storage
      // layer. Apply still composes back onto the frozen node below.
      const currentEchoView = hasSettledOverlay
        ? { ...original, status: "proved" as const, proof_tex: protoRecBefore.proof_tex }
        : original;
      // The pre-bundle view the solver actually saw is the ASSEMBLED one — with
      // any settled working overlay applied — for the paired branch too.
      // Phase 2: a revision-bearing edit pins the view by hash instead; legal
      // views are the assembled pre-bundle view, the bare frozen original, and
      // (paired branch) the post-claim node.
      const protoMismatch = edit.based_on_revision !== undefined
        ? describeRevisionMismatch(
            edit.based_on_revision,
            edit.proposed,
            // The settled-overlay variant is included UNCONDITIONALLY (audit
            // R2P23F1): a same-bundle claim change already marked the working
            // record partial by the time this loop runs, so `hasSettledOverlay`
            // can no longer see the settled view the solver was shown. Proof
            // bytes are not hashed, so the variant is just the status flip —
            // and a solver can only possess rev(proved) if the display DID
            // show the node settled.
            [
              currentEchoView,
              original,
              { ...original, status: "proved" as const },
              ...(claimChangedIds.has(edit.id) ? [prior] : []),
            ],
            edit.id,
          )
        : claimChangedIds.has(edit.id)
          ? describePairedClaimEchoMismatch(edit.proposed, currentEchoView, prior, edit.id)
          : describeEchoMismatch(edit.proposed, currentEchoView, edit.id);
      if (protoMismatch) {
        skipped.push({ id: edit.id, kind: "statement-replace", why: protoMismatch });
        continue;
      }
      const { partial_result: _reviewPartial, ...proposedNode } = edit.proposed;
      const composed = {
        ...prior,
        ...proposedNode,
        statement: prior.statement,
        status: prior.status,
        free_symbols: proposedNode.free_symbols,
        proof_tex: prior.proof_tex,
      };
      const proposedDependencies = new Set(composed.depends_on);
      const structuralBasisNarrowed =
        original.depends_on.some((dependency) => !proposedDependencies.has(dependency)) ||
        declarationNarrowed(original, composed);
      if (prior.kind === "openendedquestion" &&
          oeqSourceFingerprint(original) !== oeqSourceFingerprint(composed)) {
        detachResolvedOeq(edit.id);
      }
      changed.push({
        id: edit.id,
        kind: "statement",
        from: JSON.stringify(prior),
        to: JSON.stringify(composed),
        reason: edit.reason ?? "",
      });
      proto.statements[i] = composed;
      // Same pairing for a PROTO-frozen node. Its proof lives in the working cursor, not
      // in the proto, so commit it there; the snapshot must be taken AFTER the proto slot
      // is updated, since it closes over the node's own statement and dependency content.
      const protoRec = working?.solved[edit.id];
      if (claimChangedIds.has(edit.id)) {
        skipped.push({
          id: edit.id, kind: "proof-pairing",
          why: "this bundle also rewrites the node's claim, so the paired proof argues the OLD " +
            "statement — it is left unpaired and the node stays open for re-derivation",
        });
      } else if (
        protoRec &&
        hasSettledOverlay &&
        !structuralBasisNarrowed &&
        dependencyClosureValid(composed)
      ) {
        // This is metadata repair, not new proof content. Dependency growth only
        // declares additional settled support; it does not alter the statement or any
        // definition/assumption content the existing proof was checked against. The
        // accepted edit itself is the adjudicated assertion that the edge is direct —
        // requiring a literal `def:x` token in prose would reject semantic uses written
        // only in notation (the failure that motivated this branch). Re-snapshot the
        // durable proof against the repaired graph while keeping proof/status ownership
        // in working state.
        //
        // GUARDED: that justification holds only when the closure GREW. This proof was
        // never re-derived, and `snapshotBasisValid` checks content through this very map
        // — so if the accepted edit REMOVES a dependency, overwriting the snapshot
        // silently narrows the proof's staleness basis. A later correction to the dropped
        // definition would then leave `memberValid` true and carry a proof of the OLD
        // object forward as a proof of the new one. Re-snapshot only on growth.
        const repaired = wiredSnapshot(proto, composed, protoRec.proof_tex ?? "");
        const retainsAll = (prior: Record<string, string>, updated: Record<string, string>): boolean =>
          Object.keys(prior).every((key) => updated[key] !== undefined);
        const priorSnapshot = protoRec.snapshot;
        if (
          !priorSnapshot ||
          (retainsAll(priorSnapshot.defs, repaired.defs) &&
            retainsAll(priorSnapshot.assumptions, repaired.assumptions))
        ) {
          protoRec.snapshot = repaired;
          delete protoRec.partial;
        } else {
          skipped.push({
            id: edit.id, kind: "proof-pairing",
            why: "the accepted edit REMOVES content from this node's dependency closure, so " +
              "re-snapshotting the un-re-derived proof would drop it from the staleness basis — " +
              "the node keeps its original snapshot and re-derives if that content changes",
          });
          protoRec.partial = true;
        }
      } else if (structuralBasisNarrowed && working) {
        // A declaration/dependency shrink narrows the future staleness basis. It is
        // never metadata-only: preserve the old snapshot and make the settlement
        // explicitly partial until the node is re-derived/revalidated.
        if (protoRec) {
          protoRec.partial = true;
        } else {
          working.solved[edit.id] = {
            proof_tex: original.proof_tex ?? "",
            snapshot: wiredSnapshot(proto, original, original.proof_tex ?? ""),
            partial: true,
          };
        }
        if (composed.status === "cited") reopenedCitedIds.push(edit.id);
      }
    } else if (edit.kind === "statement-delete") {
      const priorFrozen = proto.statements.find((s) => s.id === edit.id);
      const priorCarried = working?.solved[edit.id]?.node;
      const prior = priorFrozen ?? priorCarried ?? stmtById.get(edit.id);
      if (!prior) {
        skipped.push({
          id: edit.id,
          kind: "statement-delete",
          why: "no frozen, carried, or canonically recoverable resolved-OEQ statement with this id",
        });
        continue;
      }
      const replacementId = edit.replacement_id;
      if (replacementId === edit.id) {
        throw new Error(`Cannot delete statement ${edit.id} by replacing it with itself`);
      }
      if (
        replacementId !== undefined &&
        (!stmtById.has(replacementId) || atomicStatementDeleteIds.has(replacementId))
      ) {
        throw new Error(
          `Cannot delete statement ${edit.id}: replacement ${replacementId} is not a surviving authoritative statement`,
        );
      }
      const durableReplacementId = resolvedStatementReplacementEndpoint(
        replacementId,
        working,
        atomicStatementDeleteIds,
      );
      const validationProto = {
        ...proto,
        symbols: atomicSymbolPostimage,
        statements: proto.statements.filter(
          (statement) => statement.id === edit.id || !atomicStatementDeleteIds.has(statement.id),
        ),
      };
      const validationWorking = working === null ? null : structuredClone(working);
      if (validationWorking) {
        for (const id of atomicStatementDeleteIds) if (id !== edit.id) delete validationWorking.solved[id];
      }
      const inbound = validationProto.statements
        .filter((s) => s.id !== edit.id && s.depends_on.includes(edit.id))
        .map((s) => s.id);
      const carriedInbound = Object.entries(validationWorking?.solved ?? {})
        .filter(([id, rec]) => id !== edit.id && rec.node?.depends_on.includes(edit.id))
        .map(([id]) => id);
      const symbolInbound = validationProto.symbols.filter((s) => s.ref === edit.id).map((s) => s.name);
      const textInbound = findUnsafeDeleteTextReferences(validationProto, validationWorking, edit.id);
      if (textInbound.length > 0) {
        throw new Error(
          `Cannot delete statement ${edit.id}${replacementId ? ` in favour of ${replacementId}` : ""}: ` +
            `literal claim/proof references remain in ${textInbound.map((ref) => ref.location).join(", ")}. ` +
            "Remapping depends_on cannot decide whether the replacement states the same conditions. " +
            "Restate/re-prove every citing node through explicit reviewed proposals, then apply the delete atomically.",
        );
      }
      if (replacementId === undefined && (inbound.length > 0 || carriedInbound.length > 0 || symbolInbound.length > 0)) {
        throw new Error(
          `Cannot delete statement ${edit.id} without replacement_id; live inbound references remain from ` +
            [...inbound, ...carriedInbound, ...symbolInbound.map((name) => `sym:${name}`)].join(", "),
        );
      }
      proto.statements = proto.statements
        .filter((s) => s.id !== edit.id)
        .map((s) => ({
          ...s,
          depends_on: retargetDeletedDependency(s.id, s.depends_on, edit.id, durableReplacementId),
        }));
      for (const symbol of proto.symbols) {
        if (symbol.ref !== edit.id) continue;
        if (durableReplacementId === undefined) delete symbol.ref;
        else symbol.ref = durableReplacementId;
      }
      // A removed frozen node must also be tombstoned in the incremental state;
      // otherwise the next D0 rebuild classifies it as an agent-added stale target
      // and silently resurrects it. Remap carried-node edges but retain their old
      // snapshots so ordinary validity propagation forces a re-proof when needed.
      if (working) {
        delete working.solved[edit.id];
        if (working.prose_overlay?.statement_notes !== undefined) {
          delete working.prose_overlay.statement_notes[edit.id];
          if (Object.keys(working.prose_overlay.statement_notes).length === 0) {
            delete working.prose_overlay.statement_notes;
          }
        }
        if (working.sealed_open_oeqs !== undefined) {
          delete working.sealed_open_oeqs[edit.id];
          if (Object.keys(working.sealed_open_oeqs).length === 0) delete working.sealed_open_oeqs;
        }
        for (const rec of Object.values(working.solved)) {
          if (!rec.node) continue;
          rec.node.depends_on = retargetDeletedDependency(rec.node.id, rec.node.depends_on, edit.id, durableReplacementId);
        }
        for (const [sourceId, resolution] of Object.entries(working.resolved_oeqs ?? {})) {
          const theoremId = typeof resolution === "string" ? resolution : resolution.theorem_id;
          if (sourceId !== edit.id && theoremId === edit.id &&
              !proto.statements.some((statement) => statement.id === sourceId) &&
              working.solved[sourceId] === undefined) {
            if (typeof resolution === "string") {
              throw new Error(
                `Cannot delete OEQ answer ${edit.id}: legacy resolution ${sourceId}->${theoremId} ` +
                  "has no source fingerprint from which to restore the agent-authored question",
              );
            }
            const restored = agentOeqSourceFromFingerprint(sourceId, resolution.source_fingerprint);
            if (!restored) {
              throw new Error(
                `Cannot delete OEQ answer ${edit.id}: source fingerprint for ${sourceId} is not a valid open question`,
              );
            }
            recordProof(working, proto, {
              id: sourceId,
              snapshotOf: restored,
              proofTex: "",
              node: restored,
              owner: sourceId,
              partial: true,
            });
          }
          if (sourceId !== edit.id && theoremId === edit.id) {
            const reopened = proto.statements.find((statement) => statement.id === sourceId) ??
              working.solved[sourceId]?.node;
            if (reopened?.kind === "openendedquestion") {
              working.sealed_open_oeqs ??= {};
              working.sealed_open_oeqs[sourceId] = oeqSourceFingerprint(reopened);
            }
          }
          if (sourceId === edit.id || theoremId === edit.id) delete working.resolved_oeqs![sourceId];
        }
        if (working.resolved_oeqs !== undefined && Object.keys(working.resolved_oeqs).length === 0) {
          delete working.resolved_oeqs;
        }
      }
      rebuildAssumptionUsedBy(proto, carriedStatements(working));
      changed.push({
        id: edit.id,
        kind: "statement",
        from: JSON.stringify(prior),
        to: replacementId ? `<deleted; inbound edges remapped to ${replacementId}>` : "<deleted>",
        reason: edit.reason ?? "",
      });
    } else if (edit.kind === "definition-add") {
      if (proto.definitions.some((d) => d.id === edit.id) || edit.proposed.id !== edit.id) {
        skipped.push({
          id: edit.id, kind: "definition-add",
          why: edit.proposed.id !== edit.id
            ? `payload id '${edit.proposed.id}' does not match the edit target`
            : "a definition with this id is already present in the frozen proto (no-op re-proposal)",
        });
        continue;
      }
      proto.definitions.push(edit.proposed);
      changed.push({
        id: edit.id,
        kind: "definition",
        from: "",
        to: JSON.stringify(edit.proposed),
        reason: edit.reason ?? "",
      });
    } else if (edit.kind === "definition-replace") {
      const i = proto.definitions.findIndex((d) => d.id === edit.id);
      if (i === -1 || edit.proposed.id !== edit.id) {
        skipped.push({
          id: edit.id, kind: "definition-replace",
          why: i === -1 ? "no frozen definition with this id" : `payload id '${edit.proposed.id}' does not match the edit target`,
        });
        continue;
      }
      // A definition's `free_symbols` scopes symbol invalidation for EVERY node that
      // cites it (`declaredSymbolScope` unions the closure's declarations), so shrinking
      // it silently stops a whole subtree from reopening when one of the dropped symbols
      // is re-defined.
      //
      // Only the construction-IDENTICAL case needs handling. When `construction` also
      // changed, every dependent's snapshot already fails on the text and they re-derive
      // against the new declaration — sound with no intervention. When it did not, the
      // edit is pure bookkeeping: nothing any proof rests on moved, so reopening the
      // dependents (the statement channel's answer to the same narrowing) would destroy N
      // proofs to correct a list. Retain the union instead — the scope stays a superset of
      // what each proof was checked against, which is the whole soundness requirement, and
      // over-declaring only ever costs a re-derivation that a later symbol edit triggers.
      const priorDef = proto.definitions[i];
      const originalDef = originalDefinitions.get(edit.id) ?? priorDef;
      const pairedRevision = selectedDefinitions.find(
        (change) => change.id === edit.id && change.proposed === edit.proposed.construction,
      )?.based_on_revision;
      const authoredRevision = edit.based_on_revision ?? pairedRevision;
      if (authoredRevision === undefined && !mandatedCoreEdits.has(edit)) {
        skipped.push({
          id: edit.id, kind: "definition-replace",
          why: "missing complete pre-bundle revision; regenerate this whole-definition replacement",
        });
        continue;
      }
      // Whole-node replacements preserve every omitted optional field from the
      // current post-formula view. A solver must express an intentional removal
      // explicitly (for array metadata, as an empty array); absence never means
      // "silently delete metadata".
      const completedDef = { ...priorDef, ...edit.proposed };
      // Omitted free_symbols deliberately means the conservative "any symbol"
      // scope for legacy metadata-only replacements; current correction pairs
      // must declare it at fresh-ingestion validation.
      completedDef.free_symbols = edit.proposed.free_symbols;
      const retained = originalDef.construction === completedDef.construction &&
        declarationNarrowed(originalDef, completedDef)
        ? (originalDef.free_symbols ?? []).filter(
            (name) => !(completedDef.free_symbols ?? []).some((k) => normalizeSymbol(k) === normalizeSymbol(name)),
          )
        : [];
      const appliedDef = retained.length === 0
        ? completedDef
        : { ...completedDef, free_symbols: [...(completedDef.free_symbols ?? []), ...retained] };
      changed.push({
        id: edit.id,
        kind: "definition",
        from: JSON.stringify(priorDef),
        to: JSON.stringify(appliedDef),
        reason: retained.length === 0
          ? (edit.reason ?? "")
          : `${edit.reason ?? ""} [free_symbols retained: ${retained.join(", ")} — dropped while ` +
            `\`construction\` was unchanged, so the declaration is kept a superset of what the ` +
            `citing proofs were checked against]`.trim(),
      });
      proto.definitions[i] = appliedDef;
    } else if (edit.kind === "definition-delete") {
      const prior = proto.definitions.find((d) => d.id === edit.id);
      if (!prior) {
        skipped.push({ id: edit.id, kind: "definition-delete", why: "no frozen definition with this id" });
        continue;
      }
      // Validate the complete reviewed postimage, not transient emitter order:
      // another definition in this same atomic bundle may be the only remaining
      // reference and may itself be deleted later in the loop.
      const validationCore = {
        ...proto,
        definitions: proto.definitions.filter(
          (definition) => definition.id === edit.id || !atomicDefinitionDeleteIds.has(definition.id),
        ),
      };
      const textInbound = findUnsafeDeleteTextReferences(validationCore, working, edit.id);
      const structuredInbound = [
        ...validationCore.statements
          .filter((statement) => statement.depends_on.includes(edit.id))
          .map((statement) => `statement:${statement.id}`),
        ...Object.values(working?.solved ?? {})
          .filter((record) => record.node?.depends_on.includes(edit.id))
          .map((record) => `working:${record.node!.id}`),
        ...validationCore.symbols
          .filter((symbol) => symbol.ref === edit.id)
          .map((symbol) => `symbol:${symbol.name}`),
      ];
      if (textInbound.length > 0 || structuredInbound.length > 0) {
        throw new Error(
          `Cannot delete definition ${edit.id}: authored or structured references remain in ` +
            `${[...textInbound.map((ref) => ref.location), ...structuredInbound].join(", ")}. ` +
            "Deleting a graph edge cannot safely rewrite authored mathematics; restate/re-prove the citing nodes first.",
        );
      }
      proto.definitions = proto.definitions.filter((d) => d.id !== edit.id);
      rebuildAssumptionUsedBy(proto, carriedStatements(working));
      changed.push({ id: edit.id, kind: "definition", from: JSON.stringify(prior), to: "<deleted>", reason: edit.reason ?? "" });
    } else if (edit.kind === "bibliography-replace") {
      const i = proto.bibliography.findIndex((b) => b.key === edit.key);
      if (edit.proposed.key !== edit.key) {
        skipped.push({ id: target, kind: "bibliography-replace", why: `payload key '${edit.proposed.key}' does not match the edit target` });
        continue;
      }
      if (i === -1) {
        // The typed core-edit schema has no separate bibliography-add variant.
        // Solvers therefore use bibliography-replace for a newly required source
        // key as well as for corrections to an existing entry.
        proto.bibliography.push(edit.proposed);
        changed.push({ id: target, kind: "bibliography", from: "", to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
      } else {
        changed.push({ id: target, kind: "bibliography", from: JSON.stringify(proto.bibliography[i]), to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
        proto.bibliography[i] = edit.proposed;
      }
    } else if (edit.kind === "target-estimand-replace") {
      // Refuse a blind overwrite: `current` must echo the estimand byte-for-byte. The
      // estimand is the anchor of what the run committed to deliver, so an edit that did
      // not see the text it replaces cannot be told apart from silent drift.
      if (edit.current !== proto.target_estimand) {
        skipped.push({ id: target, kind: "target-estimand-replace", why: `\`current\` does not echo the core's target_estimand byte-for-byte — re-read it and re-emit` });
        continue;
      }
      changed.push({ id: target, kind: "metadata", from: proto.target_estimand, to: edit.proposed, reason: edit.reason ?? "" });
      proto.target_estimand = edit.proposed;
    } else if (edit.kind === "estimand-functional-replace") {
      // Same echo contract; `""` echoes an absent field.
      const currentFunctional = proto.estimand_functional ?? "";
      if (edit.current !== currentFunctional) {
        skipped.push({ id: target, kind: "estimand-functional-replace", why: `\`current\` does not echo the core's estimand_functional byte-for-byte (use "" if the field is absent) — re-read it and re-emit` });
        continue;
      }
      changed.push({ id: target, kind: "metadata", from: currentFunctional, to: edit.proposed, reason: edit.reason ?? "" });
      proto.estimand_functional = edit.proposed;
    } else if (edit.kind === "comparator-promise-table-replace") {
      changed.push({
        id: edit.id,
        kind: "metadata",
        from: JSON.stringify(proto.comparator_promise_table ?? proto.comparator_promises ?? []),
        to: JSON.stringify(edit.proposed),
        reason: edit.reason ?? "",
      });
      proto.comparator_promise_table = edit.proposed;
      // Canonicalize the legacy alias away so later consumers cannot observe two
      // contradictory promise tables after a D0 repair.
      delete proto.comparator_promises;
    } else if (edit.kind === "symbol-add") {
      if (proto.symbols.some((s) => s.name === edit.name) || edit.proposed.name !== edit.name) {
        skipped.push({
          id: target, kind: "symbol-add",
          why: edit.proposed.name !== edit.name
            ? `payload name '${edit.proposed.name}' does not match the edit target`
            : "a symbol with this name is already present in the frozen proto (no-op re-proposal)",
        });
        continue;
      }
      proto.symbols.push(edit.proposed);
      changed.push({ id: target, kind: "symbol", from: "", to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
    } else if (edit.kind === "symbol-replace") {
      const i = proto.symbols.findIndex((s) => s.name === edit.name);
      if (i === -1 || edit.proposed.name !== edit.name) {
        skipped.push({
          id: target, kind: "symbol-replace",
          why: i === -1 ? "no frozen symbol with this name" : `payload name '${edit.proposed.name}' does not match the edit target`,
        });
        continue;
      }
      changed.push({ id: target, kind: "symbol", from: JSON.stringify(proto.symbols[i]), to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
      proto.symbols[i] = edit.proposed;
    } else if (edit.kind === "symbol-delete") {
      const prior = proto.symbols.find((s) => s.name === edit.name);
      if (!prior) {
        skipped.push({ id: target, kind: "symbol-delete", why: "no frozen symbol with this name" });
        continue;
      }
      proto.symbols = proto.symbols.filter((s) => s.name !== edit.name);
      changed.push({ id: target, kind: "symbol", from: JSON.stringify(prior), to: "<deleted>", reason: edit.reason ?? "" });
    } else {
      rebuildAssumptionUsedBy(proto, carriedStatements(working));
      changed.push({ id: edit.id, kind: "metadata", from: "stale reverse dependencies", to: "rebuilt direct used_by inverse", reason: edit.reason ?? "" });
    }
  }
  if (changed.length !== selectedVariantCount) {
    // Name WHICH selected edit was dropped and WHY. The count alone is safe but not
    // diagnosable: it cost three solve rounds of source-reading on 2026-07-19.
    const why = skipped.length > 0
      ? ` Dropped: ${skipped.map((d) => `${d.id} (${d.kind}) — ${d.why}`).join("; ")}.`
      : " No per-edit reason was recorded, which is itself a gap: report it.";
    throw new Error(
      `Refusing partial D0 apply: selected ${selectedVariantCount} proposal variant(s), but only ` +
        `${changed.length} were applicable.${why} No proto, working cursor, escalation log, or outputs were mutated on disk.`,
    );
  }
  if (changed.length === 0 && !directive) return changed;

  // A successful semantic symbol replacement/deletion advances the global basis in
  // this transaction. First reopen every OLD proof whose declared scope intersects the
  // changed symbol set (undeclared legacy scope means "all symbols"). Reviewed proofs
  // can then re-close below against the accepted postimage; unrelated records remain
  // reusable. Finally the cursor is rebased to the new table before final validity is
  // checked. Without this sequence a newly promoted proof was immediately stale against
  // the old cursor basis, while blindly rebasing would launder every unreviewed old proof.
  const legacySymbolBasisMissing = working !== null && working.symbol_basis === undefined;
  const appliedChangedSymbols = working ? changedSymbolNames(working, proto) : new Set<string>();
  // `changedSymbolNames` compares against the durable prior basis, which intentionally
  // returns empty for legacy cursors that predate `symbol_basis`. An APPLY transaction has
  // stronger evidence: it knows exactly which accepted symbol meanings it just replaced
  // or deleted. Add those names directly so a legacy cursor cannot carry old proofs over
  // the edit. With no prior basis, conservatively reopen every proof because old runs may
  // also predate complete `free_symbols` declarations.
  for (const edit of selectedCoreEdits) {
    if (edit.kind === "symbol-replace" || edit.kind === "symbol-delete") {
      appliedChangedSymbols.add(edit.name);
    }
  }
  // Some accepted graph edits mutate a symbol's semantic `ref` mechanically (for
  // example statement-delete with a replacement). Those are real fingerprint changes
  // even though the surfaced bundle contains no explicit symbol edit. Diff the complete
  // transaction pre/post image so every implicit semantic rewrite participates.
  const transactionSymbolBasisBefore = symbolBasis(
    protoBeforeEdits, carriedStatements(workingBeforeEdits), workingBeforeEdits?.resolved_oeqs,
  );
  const transactionSymbolBasisAfter = symbolBasis(proto, carriedStatements(working), working?.resolved_oeqs);
  for (const [name, fingerprint] of Object.entries(transactionSymbolBasisBefore)) {
    if (transactionSymbolBasisAfter[name] !== fingerprint) appliedChangedSymbols.add(name);
  }
  // Deferral is reserved for a SETTLED proof newly reopened by this transaction's
  // symbol change.  A pre-existing partial helper (or a helper independently broken by
  // a same-bundle claim/core edit) must remain a hard promotion blocker.  Re-evaluate
  // the immutable preimage records against the postimage while rebasing their symbol
  // basis to the postimage: this suppresses exactly the symbol delta and leaves every
  // other invalidator visible.
  const independentlyValidPostimageProofIds = (() => {
    if (!workingBeforeEdits || !working) return new Set<string>();
    const probe = structuredClone(workingBeforeEdits);
    probe.symbol_basis = transactionSymbolBasisAfter;
    for (const id of Object.keys(probe.solved)) {
      if (working.solved[id] === undefined) delete probe.solved[id];
    }
    for (const [id, current] of Object.entries(working.solved)) {
      const prior = probe.solved[id];
      if (!prior) continue;
      if (current.node) prior.node = structuredClone(current.node);
      // A semantic core edit may already have reopened this record before the symbol
      // invalidation pass. Preserve that causal evidence; restoring the preimage's
      // settled flag here would misclassify simultaneous claim/dependency debt as
      // symbol-only debt.
      if (current.partial === true) prior.partial = true;
    }
    const valid = computeValidNodes(probe, proto);
    const dependencyKey = (node: CoreStatement | undefined): string =>
      [...new Set(node?.depends_on ?? [])].sort().join("\u0000");
    for (const id of [...valid]) {
      const preRecord = workingBeforeEdits.solved[id];
      const postRecord = working.solved[id];
      const preNode = protoBeforeEdits.statements.find((statement) => statement.id === id) ?? preRecord?.node;
      const postNode = proto.statements.find((statement) => statement.id === id) ?? postRecord?.node;
      // Dependency substitutions are semantic proof-basis changes even when the old
      // snapshot target was deleted and computeValidNodes can no longer propagate its
      // staleness. They are never attributable solely to a symbol edit.
      if (dependencyKey(preNode) !== dependencyKey(postNode)) valid.delete(id);
    }
    return valid;
  })();
  const symbolInvalidatedProofIds = new Set<string>();
  if (working && appliedChangedSymbols.size > 0) {
    for (const [id, rec] of Object.entries(working.solved)) {
      const node = proto.statements.find((statement) => statement.id === id) ?? rec.node;
      if (!node) continue;
      const preRec = workingBeforeEdits?.solved[id];
      const preNode = protoBeforeEdits.statements.find((statement) => statement.id === id) ??
        preRec?.node ?? rec.node ?? node;
      const preScope = declaredSymbolScope(protoBeforeEdits, preNode, preRec?.snapshot ?? rec.snapshot);
      const postScope = declaredSymbolScope(proto, node, rec.snapshot);
      const touched = legacySymbolBasisMissing || preScope === null || postScope === null ||
        [...appliedChangedSymbols].some((name) => {
          const normalized = normalizeSymbol(name);
          return preScope.has(normalized) || postScope.has(normalized);
        });
      if (touched) {
        rec.partial = true;
        if (preimageValidProofIds.has(id) && independentlyValidPostimageProofIds.has(id)) {
          symbolInvalidatedProofIds.add(id);
        }
      }
    }
  }

  // CITED-SOURCE REVALIDATION. The receipt was authored and reviewed against this
  // same atomic bundle. Consume it only now, after the selected postimage and symbol
  // invalidation exist, and only when every proof-relevant byte still matches the
  // canonical cited node. This lets cited leaves settle before consumer-proof
  // promotion without allowing a source or claim substitution through added_lemmas.
  if (working) {
    for (const receipt of citationRevalidations) {
      const rec = working.solved[receipt.id];
      const frozen = proto.statements.find((statement) => statement.id === receipt.id);
      const node = frozen ?? rec?.node;
      if (!node || !rec || !citedReceiptMatches({ ...node, proof_tex: rec.proof_tex }, receipt)) {
        throw new Error(
          `Refusing D0 apply: cited revalidation ${receipt.id} does not exactly match the selected postimage`,
        );
      }
      recordProof(working, proto, {
        id: receipt.id,
        snapshotOf: node,
        proofTex: "",
        ...(!frozen ? { node, owner: rec.owner } : {}),
      });
    }
  }

  // REVIEWED-PROOF PROMOTION. Every proof in the proposal carrier was adjudicated with
  // this atomic bundle, not only proofs whose ids also carry a claim edit. Seed the
  // monotone fixpoint from the complete reviewed proof set so standalone helpers can
  // settle first and unlock their consumers. A claim-changing proof must additionally
  // DECLARE `argues_proposed`; unchanged-claim proofs need no such flag.
  //
  // Verified, not trusted: promotion requires that the basis the proof declared actually
  // materialized — the statement change applied (id ∈ claimChangedIds), the node stands
  // reopened as `to-prove` (cited nodes keep the conservative source-revalidation path),
  // the proof's content closure touches NO bundle proposal that adjudication left
  // unapplied (a partially-accepted basis is ambiguous), and the dependency closure is
  // discharged. D0.5 still reviews the promoted proof like any other.
  if (working) {
    // Count proposal VARIANTS per target id across every channel and compare with the
    // applied (`changed`) entries per id. A bare-id applied set aliased distinct same-id
    // variants: accepting `statement:thm:x` while rejecting `core-edit:thm:x` removed
    // thm:x from the unapplied set, so a proof authored against the rejected rewire
    // could be promoted. An id counts as materialized only when EVERY variant targeting
    // it applied.
    const proposedCount = new Map<string, number>();
    const bump = (id: string): void => { proposedCount.set(id, (proposedCount.get(id) ?? 0) + 1); };
    statements.forEach((c) => bump(c.id));
    definitions.forEach((c) => bump(c.id));
    assumptions.forEach((a) => bump(a.id));
    coreEdits.filter((e) => e.kind !== "rebuild-reverse-dependencies").forEach((e) => bump(coreEditTarget(e)));
    const appliedCount = new Map<string, number>();
    for (const entry of changed) {
      if (entry.id === "metadata:reverse-dependencies") continue; // rebuild edits are excluded from proposedCount too
      appliedCount.set(entry.id, (appliedCount.get(entry.id) ?? 0) + 1);
    }
    const unappliedIds = new Set(
      [...proposedCount.entries()].filter(([id, n]) => (appliedCount.get(id) ?? 0) < n).map(([id]) => id),
    );
    for (const dep of rejectedSupportIds) unappliedIds.add(dep);
    // GLOBAL invalidators mirror the merge-side deferral rule (merge.ts,
    // `hasGlobalProofInvalidation`): symbol and bibliography meaning, and a newly
    // proposed assumption, are not addressed by literal `ass:/def:/thm:` references,
    // so the closure walk below cannot see them. If any such proposal was left
    // unapplied, the basis the proof declared did not fully materialize — no
    // promotion this apply (the ordinary reopen/re-solve path stands).
    const GLOBAL_EDIT_KINDS = new Set(["symbol-add", "symbol-replace", "symbol-delete", "bibliography-replace"]);
    const hasUnappliedGlobalInvalidator =
      assumptions.some((a) => unappliedIds.has(a.id)) ||
      coreEdits.some((e) => GLOBAL_EDIT_KINDS.has(e.kind) && unappliedIds.has(coreEditTarget(e)));
    const carriedNodes = Object.values(working.solved).flatMap((r) => (r.node ? [r.node] : []));
    // Promotion is a monotone dependency problem, not a proposal-order problem. A
    // consumer can precede a same-bundle helper in `claimChangedIds`; revisit deferred
    // consumers after each successful helper promotion until the closure stabilizes.
    const pendingPromotionIds = new Set(pairedProofById.keys());
    const validatedReviewedProofIds = new Set<string>();
    const promotionBlockers = new Map<string, string>();
    const unresolvedPromotionDeps = new Map<string, string[]>();
    let promotedThisPass = true;
    while (promotedThisPass && pendingPromotionIds.size > 0) {
      promotedThisPass = false;
      for (const id of [...pendingPromotionIds]) {
        const paired = pairedProofById.get(id);
        if (!paired || (claimChangedIds.has(id) && !paired.arguesProposed)) {
          promotionBlockers.set(id, "claim-changing proof lacks argues_proposed:true");
          pendingPromotionIds.delete(id);
          continue;
        }
        const frozen = proto.statements.find((s) => s.id === id);
        const rec = working.solved[id];
        const node = frozen ?? rec?.node;
        if (!node || !rec || rec.proof_tex !== paired.proofTex || node.status === "cited") {
          promotionBlockers.set(id, "missing node/exact durable proof record, or node is cited");
          pendingPromotionIds.delete(id);
          continue;
        }
        if (hasUnappliedGlobalInvalidator) {
          promotionBlockers.set(id, "a global proof-basis proposal was left unapplied");
          continue;
        }
        if (proofContentClosureIntersects({
          core: proto, node, proofText: paired.proofTex, changedIds: unappliedIds, extraStatements: carriedNodes,
        })) {
          promotionBlockers.set(id, "proof closure intersects an unapplied proposal target");
          pendingPromotionIds.delete(id);
          continue;
        }
        // Use the same wired edge set that the durable snapshot and reuse checker use.
        // Otherwise a proof-text-only reference could be snapshotted as a dependency
        // after promotion despite its helper still being partial.
        const wiredNode = withWiredDeps(node, paired.proofTex);
        const unresolvedDeps = wiredNode.depends_on.filter((dep) =>
          !dependencyClosureValid({ ...wiredNode, depends_on: [dep] }),
        );
        if (unresolvedDeps.length > 0) {
          promotionBlockers.set(id, `unresolved proof dependencies: ${unresolvedDeps.join(", ")}`);
          unresolvedPromotionDeps.set(id, unresolvedDeps);
          continue;
        }
        if (rec.partial !== true) {
          validatedReviewedProofIds.add(id);
          promotionBlockers.delete(id);
          pendingPromotionIds.delete(id);
          continue;
        }
        const provedNode = { ...node, status: "proved" as const, proof_tex: paired.proofTex };
        const snapshot = wiredSnapshot(proto, provedNode, paired.proofTex);
        if (rec) {
          if (rec.node) rec.node = provedNode;
          rec.proof_tex = paired.proofTex;
          rec.snapshot = snapshot;
          delete rec.partial;
        } else {
          working.solved[id] = { proof_tex: paired.proofTex, snapshot };
        }
        pendingPromotionIds.delete(id);
        validatedReviewedProofIds.add(id);
        promotionBlockers.delete(id);
        promotedThisPass = true;
      }
    }
    const unpromotedReviewedProofs = [...pairedProofById].flatMap(([id, paired]) => {
      const rec = working.solved[id];
      return validatedReviewedProofIds.has(id) && rec !== undefined &&
        rec.partial !== true && rec.proof_tex === paired.proofTex
        ? []
        : [id];
    });
    // A same-round global symbol correction can invalidate an already-settled sibling
    // prerequisite that the directive owner was explicitly forbidden to re-prove. In
    // that shape the reviewed consumer proof cannot promote in this transaction, but
    // rejecting the accepted symbol edit creates an endless apply/discard/re-solve loop:
    // the next owner can change another shared symbol and stale the sibling again.
    //
    // Land the accepted semantic edit while keeping every affected proof visibly PARTIAL
    // only when the whole unresolved promotion chain bottoms out in a proof reopened by
    // that applied symbol edit. Plain D0 resume then targets exactly this stale closure.
    // Missing dependencies, rejected support, malformed claim proofs, and every other
    // incomplete bundle still fail closed below.
    const symbolDeferredProofs = new Set(symbolInvalidatedProofIds);
    for (let grew = true; grew; ) {
      grew = false;
      for (const id of unpromotedReviewedProofs) {
        if (symbolDeferredProofs.has(id)) continue;
        const deps = unresolvedPromotionDeps.get(id);
        if (deps && deps.length > 0 && deps.every((dep) => symbolDeferredProofs.has(dep))) {
          symbolDeferredProofs.add(id);
          grew = true;
        }
      }
    }
    const deferredReviewedProofs = unpromotedReviewedProofs.filter((id) => {
      const deps = unresolvedPromotionDeps.get(id);
      return symbolDeferredProofs.has(id) && deps !== undefined &&
        deps.length > 0 && deps.every((dep) => symbolDeferredProofs.has(dep));
    });
    // A transitive consumer need not mention the edited symbol in its own declared
    // scope, so the direct invalidation pass above may not have marked it. Deferral is
    // an explicit promise that D0 will re-solve the whole affected closure; persist that
    // promise rather than merely exempting the consumer from the final validity check.
    for (const id of deferredReviewedProofs) {
      const rec = working.solved[id];
      if (rec) rec.partial = true;
    }
    const hardUnpromotedReviewedProofs = unpromotedReviewedProofs.filter(
      (id) => !deferredReviewedProofs.includes(id),
    );
    if (hardUnpromotedReviewedProofs.length > 0) {
      throw new Error(
        `Refusing D0 apply: reviewed provisional proof(s) did not reach a complete exact postimage ` +
          `after dependency-ordered promotion: ${hardUnpromotedReviewedProofs.join(", ")}. ` +
          `Blockers: ${hardUnpromotedReviewedProofs.map((id) => `${id} (${promotionBlockers.get(id) ?? "not validated"})`).join("; ")}. ` +
          `Claim-changing proofs require argues_proposed:true and every proof dependency/support edit must apply.`,
      );
    }
    // Explicit rejection is stronger than any pre-existing settled carrier. Reopen
    // the target after all ordinary reuse/promotion branches, preserving proof bytes
    // only as partial repair material. This also makes the final validity check reject
    // every accepted downstream proof that tried to rely on the rejected result.
    for (const id of rejectedProofIds) {
      const frozen = proto.statements.find((statement) => statement.id === id);
      const priorRecord = working.solved[id];
      const node = frozen ?? priorRecord?.node;
      const proofTex = rejectedProofById.get(id);
      if (!node || proofTex === undefined) {
        throw new Error(`Refusing D0 apply: rejected proof target ${id} has no live statement carrier`);
      }
      if (frozen) {
        frozen.status = "to-prove";
        delete frozen.proof_tex;
      }
      const reopenedNode = priorRecord?.node
        ? { ...priorRecord.node, status: "to-prove" as const, proof_tex: undefined }
        : undefined;
      working.solved[id] = {
        ...(priorRecord ?? {}),
        ...(reopenedNode ? { node: reopenedNode } : {}),
        proof_tex: proofTex,
        snapshot: wiredSnapshot(proto, node, proofTex),
        partial: true,
      };
    }
    if (appliedChangedSymbols.size > 0) {
      working.symbol_basis = symbolBasis(proto, carriedStatements(working), working.resolved_oeqs);
    }
    const validPostimage = computeValidNodes(working, proto);
    const invalidReviewedProofs = [...pairedProofById.keys()].filter(
      (id) => !deferredReviewedProofs.includes(id) && !validPostimage.has(id),
    );
    if (invalidReviewedProofs.length > 0) {
      throw new Error(
        `Refusing D0 apply: reviewed proof(s) would be immediately stale in the final postimage: ` +
          `${invalidReviewedProofs.join(", ")}. Nothing was mutated on disk.`,
      );
    }
  }

  // Reverse dependency lists are a derived view of the final accepted graph, not
  // authored content. Normalize once after every selected edit/proof promotion so
  // statement rewires and deletions cannot require a separate model proposal and
  // adjudication round. This happens on the in-memory transaction image before any
  // artifact is published.
  rebuildAssumptionUsedBy(proto, carriedStatements(working));

  // Persist the same narrow JSON/LaTeX repairs used by assembled cores. This is
  // especially important for legacy proto strings containing a decoded control
  // byte (for example under-escaped `\\forall`): a later rebuild must not
  // reintroduce the corruption after a clean render.
  repairCoreLatexSerialization(proto);
  // Symbol-add appends by construction, so a newly introduced prerequisite can land
  // after an older shorthand that references it. Canonicalize the declared-symbol DAG
  // after every accepted bundle; this changes only array order, never payload bytes.
  proto.symbols = topologicallyOrderSymbols(proto.symbols);
  // Definition-add also appends, so a new prerequisite can otherwise land after
  // an older constructed definition that names it. Preserve every payload byte
  // and canonicalize only the accepted definition DAG order.
  proto.definitions = topologicallyOrderDefinitions(proto.definitions);
  // Fail loudly before persisting: a control character still present after both
  // repair layers means an escaping corruption neither could safely resolve.
  assertNoDecodedControlChars(proto, `proto core after apply (${protoPath})`);
  CoreSchema.parse(proto);
  // NORMALIZED on both sides, matching `preflight.checkSymbolDeclarations` and
  // `d0_working.declaredSymbolScope`. Raw equality here diverged from those two: a
  // declaration spelled `\(\eta\)` against a table entry `\eta` passes the D0-SOLVE
  // checkpoint under normalized equality and then hard-refuses the ENTIRE adjudication
  // bundle at this line under raw equality — a lost round, reported against a symbol the
  // operator can plainly see is declared. Both spellings are common: 1605 of 3958 real
  // symbol names are `\(…\)`-wrapped.
  const declaredSymbols = new Set(proto.symbols.map((symbol) => normalizeSymbol(symbol.name)));
  // Statements and definitions are checked alongside assumptions because `free_symbols`
  // is what scopes symbol invalidation: a `symbol-delete` (or rename) that orphans a
  // declaration leaves a name that can never match a changed symbol again, so the node
  // stops being reopened by the very edits it depends on — silent under-invalidation
  // rather than a loud dangling reference. Nodes that declare nothing are skipped: they
  // are the fail-safe case and are reopened by any symbol change regardless.
  const undeclaredFreeSymbols = [
    ...proto.assumptions.map((a) => [a.id, a.free_symbols] as const),
    ...proto.definitions.map((d) => [d.id, d.free_symbols] as const),
    ...proto.statements.map((s) => [s.id, s.free_symbols] as const),
  ].flatMap(([id, freeSymbols]) =>
    (freeSymbols ?? [])
      .filter((name) => !declaredSymbols.has(normalizeSymbol(name)))
      .map((name) => `${id}:${name}`),
  );
  if (undeclaredFreeSymbols.length > 0) {
    throw new Error(
      `Refusing D0 apply: free symbols remain undeclared after the selected bundle: ` +
      undeclaredFreeSymbols.join(", "),
    );
  }
  // Applying a reviewed bundle is a publication boundary for the frozen semantic
  // postimage.  Topological canonicalizers deliberately leave cycles unchanged so
  // the structural gate can diagnose them, but APPLY historically never invoked
  // that gate.  An old symbol rewritten to reference a same-bundle symbol-add could
  // therefore persist a two-way dependency cycle and spend the next solve round only
  // to fail G1.  Gate the assembled postimage now (without requiring discharge: an
  // apply may intentionally reopen proofs) before check mode returns or any durable
  // transaction is written. Keep the narrower free-symbol diagnostic above stable.
  const postApplyGate = runStructuralGate(
    assembleCore(proto, working ?? { round: 0, solved: {} }),
    { requireDischarged: false },
  );
  if (!postApplyGate.ok) {
    const details = postApplyGate.violations
      .map((violation) => `[${violation.code}] ${violation.where}: ${violation.message}`)
      .join("; ");
    throw new Error(
      `Refusing D0 apply: selected bundle fails the structural gate in its assembled postimage: ${details}. ` +
        `Nothing was mutated on disk.`,
    );
  }
  if (authoredMetadataOnly) {
    // (1) Only statement-replace edits may ride this channel, asserted on the EDIT kinds.
    const foreignKinds = selectedCoreEdits.filter((edit) => edit.kind !== "statement-replace");
    if (foreignKinds.length > 0 || statements.length > 0 || definitions.length > 0 || assumptions.length > 0 ||
        (proposals.proofs?.length ?? 0) > 0 || citationRevalidations.length > 0 || reopenedCitedIds.length > 0 ||
        changed.some((c) => c.kind !== "statement")) {
      throw new Error(
        "authored metadata apply accepts statement-replace prose edits only " +
          `(got ${foreignKinds.map((edit) => edit.kind).join(", ") || "a non-statement change"}) — nothing was mutated`,
      );
    }
    // (2) The real safety property: no working record moved except the prose fields
    // inside an agent-authored node, and no proto byte moved except statement prose.
    // A cited shortcut, a proof reopen, or a render-wired edge leaking into the proto
    // would all show up here. Runs before the preview return so --check refuses
    // exactly what the real apply refuses.
    const PROSE = ["justification", "gap", "consumer"] as const;
    const stripProse = <T extends Record<string, unknown>>(node: T): T => {
      const copy = { ...node };
      for (const field of PROSE) delete copy[field];
      return copy;
    };
    const proseFreeRecord = (record: unknown): unknown => {
      const copy = structuredClone(record) as { node?: Record<string, unknown> } | undefined;
      if (copy?.node) copy.node = stripProse(copy.node);
      return copy;
    };
    const beforeSolved = workingBeforeEdits?.solved ?? {};
    const afterSolved = working?.solved ?? {};
    const movedRecords = [...new Set([...Object.keys(beforeSolved), ...Object.keys(afterSolved)])]
      .filter((id) => JSON.stringify(proseFreeRecord(beforeSolved[id])) !== JSON.stringify(proseFreeRecord(afterSolved[id])));
    if (movedRecords.length > 0 ||
        JSON.stringify(workingBeforeEdits?.resolved_oeqs ?? {}) !== JSON.stringify(working?.resolved_oeqs ?? {})) {
      throw new Error(
        `authored metadata apply would move working record(s) ${movedRecords.join(", ") || "(resolutions)"} beyond prose — nothing was mutated`,
      );
    }
    // `assumption.used_by` is derived reverse metadata that every apply rebuilds
    // mechanically; it is not authored content and is excluded from the diff.
    const proseFreeProto = (core: Core): string =>
      JSON.stringify({
        ...core,
        statements: core.statements.map((statement) => stripProse(statement as unknown as Record<string, unknown>)),
        assumptions: core.assumptions.map(({ used_by: _usedBy, ...assumption }) => assumption),
      });
    if (proseFreeProto(protoBeforeEdits) !== proseFreeProto(proto)) {
      const movedStatements = proto.statements
        .filter((after) => {
          const before = protoBeforeEdits.statements.find((s) => s.id === after.id);
          return before === undefined ||
            JSON.stringify(stripProse(before as unknown as Record<string, unknown>)) !== JSON.stringify(stripProse(after as unknown as Record<string, unknown>));
        })
        .map((statement) => statement.id);
      const movedKeys = (Object.keys({ ...protoBeforeEdits, ...proto }) as Array<keyof Core>)
        .filter((key) => key !== "statements" && key !== "assumptions" && JSON.stringify(protoBeforeEdits[key]) !== JSON.stringify(proto[key]));
      const movedAssumptions = proto.assumptions
        .filter((after) => {
          const before = protoBeforeEdits.assumptions.find((a) => a.id === after.id);
          const { used_by: _b, ...b } = before ?? { id: undefined };
          const { used_by: _a, ...a } = after;
          return before === undefined || JSON.stringify(a) !== JSON.stringify(b);
        })
        .map((a) => a.id);
      movedKeys.push(...(movedAssumptions as Array<keyof Core>));
      throw new Error(
        `authored metadata apply would change the frozen proto beyond statement prose (${[...movedStatements, ...movedKeys.map(String)].join(", ") || "?"}) — nothing was mutated`,
      );
    }
  }
  if (checkOnly) return changed;
  // Rewind the stage pointer BEFORE publishing any part of the multi-file
  // apply. If the process dies after this point, plain resume is constrained to
  // D0 and cannot review/advance an old core against a partially updated proto.
  // PROTO CONFLICT RE-CHECK. Runs before EVERY persistent mutation — the stage-cursor
  // rewind and the working save both follow it. It previously sat after both, so a
  // detected conflict threw while claiming "nothing was mutated" having already durably
  // rewound the pipeline cursor and changed the working state.
  //
  // Honest about what this is: a re-read and compare, NOT an atomic compare-and-swap. Two
  // applies can both pass this check and then both rename, and the second still wins. It
  // narrows the window from "the whole apply" to "between this read and the rename"; it
  // does not serialize concurrent applies. Closing it properly needs an exclusive lock,
  // which brings stale-lock recovery of its own — deliberately not taken on here, because
  // the orchestrator is single-threaded and different qids use different run directories.
  const protoBytesNow = await readFile(protoPath, "utf8");
  if (protoBytesNow !== protoBytesAtRead) {
    throw new Error(
      "d0_apply_change: proto_core.json changed while this apply was preparing — another apply, a " +
        "directive, or a hand edit committed first. Nothing was mutated on disk. Re-read the current " +
        "proposals and re-run so the adjudication is made against the live proto.",
    );
  }

  if (authoredMetadataOnly) {
    // The render overlays `working.prose_overlay.statement_notes[id]` over the proto at
    // assembly, so an authored value must land in an EXISTING overlay note too or core.json
    // would keep showing the old (possibly stale) prose. Exactly the SUPPLIED fields are
    // synced — unconditionally, so a stale overlay is overwritten even when the proto
    // already carries the authored text. Entries are never created here.
    const notes = working?.prose_overlay?.statement_notes;
    if (notes) {
      for (const edit of selectedCoreEdits) {
        if (edit.kind !== "statement-replace") continue;
        const note = notes[edit.id];
        if (!note) continue;
        for (const field of args.authoredProseFields?.[edit.id] ?? []) {
          const authored = edit.proposed[field];
          if (authored !== undefined) note[field] = authored;
        }
      }
    }
  }
  const transactionId = `d0apply:${randomUUID()}`;
  const escalationEntry: EscalationLogEntry = {
    transaction_id: transactionId,
    round: working?.round ?? 0,
    changed,
    note,
    ...(authoredMetadataOnly ? { provenance_only: true as const } : {}),
    ...(rejectedProofIds.size > 0 ? { rejected_proof_ids: [...rejectedProofIds].sort() } : {}),
    directive,
    // Reopened cited leaves are dischargeable ONLY through a directed round: the
    // dispatcher promotes a stale cited lemma to a repair root — and merge accepts its
    // byte-faithful revalidation receipt — strictly for EXACT REQUIRED targets. A
    // referee escalation names them in its own entry; a solver-proposed narrowing has
    // no such entry, so the apply journal must require them itself.
    ...(reopenedCitedIds.length > 0 ? { required_core_targets: [...new Set(reopenedCitedIds)] } : {}),
  };
  if (working) {
    working.proposals = emptyProposals() as unknown as typeof working.proposals;
    working.required_core_edit_mandates = [];
  }
  // One durable intent precedes every store mutation. Recovery accepts only the exact
  // before/after proto bytes and journals by transaction_id, making each replay step
  // idempotent across crashes between proto, journal, and working-cursor writes.
  await writeJsonAtomic(applyTransactionPath(ctx), {
    version: 1,
    transaction_id: transactionId,
    proto_before: protoBytesAtRead,
    proto_after: JSON.stringify(proto, null, 2),
    working_after: working,
    escalation_entry: escalationEntry,
    ...(authoredMetadataOnly ? { authored_metadata_only: true as const } : {}),
  } satisfies D0ApplyTransaction);
  const committed = await recoverPendingApply(ctx);
  if (committed === null) throw new Error("D0 apply transaction disappeared before commit");
  return committed;
}
