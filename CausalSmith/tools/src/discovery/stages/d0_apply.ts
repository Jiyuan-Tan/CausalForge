// Apply D0-SOLVE proposed changes to the frozen proto + record an escalation entry.
//
// Shared by the CLI (`bin/d0_apply_change.ts`, human-driven) and the automated D0
// revise loop (`runStage0SolveLoop`). Applying a change edits the FROZEN PROTO (the
// spec the next solve reads), appends an escalation-log entry (so the next solve sees
// what changed / why), and clears the stale round outputs while KEEPING the incremental
// working state (carried proofs). The hybrid auto/gate partition lives in the loop;
// this module just executes an already-decided set of changes.
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
  loadWorkingState,
  memberValid,
  proposalRevision,
  readEscalationLog,
  saveWorkingState,
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
import { statementRevision } from "../core/revision.js";
import { recordProof, wiredSnapshot } from "../working_writer.js";
import { agentOeqSourceFromFingerprint, oeqSourceFingerprint } from "../solve/oeq_source.js";
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

/** Statements added during D0 are durable in the working cursor but absent from the
 * frozen proto.  Reverse-dependency repair must see them as direct consumers. */
function carriedStatements(working: WorkingState | null): CoreStatement[] {
  return Object.values(working?.solved ?? {}).flatMap((record) => record.node ? [record.node] : []);
}

export interface RawChange {
  id: string;
  current?: string;
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
  | { kind: "definition-replace"; id: string; proposed: CoreDefinition; reason?: string; direction: "correct" }
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
      add(`working.${id}.node.source.verbatim_statement`, rec.node.source?.verbatim_statement);
    }
    add(`working.${id}.proof_tex`, rec.proof_tex);
  }
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

/** The four proposal CHANNELS a round can carry. A single node id can appear in more
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
  statements: RawChange[];
  definitions: RawChange[];
  assumptions: RawAssumption[];
  coreEdits: RawCoreEdit[];
  proofs: Array<{ id: string; proof_tex?: string }>;
}> {
  // Single accessor: `working.proposals` when present, legacy files otherwise.
  // Every consumer must see the SAME payload — reading a subset here is what let an
  // apply approve a statement change while discarding the proof written for it.
  const working = await loadWorkingState(ctx);
  const p = await readRoundProposals(ctx, working);
  return {
    statements: p.statements as RawChange[],
    definitions: p.definitions as RawChange[],
    assumptions: p.assumptions as RawAssumption[],
    coreEdits: p.coreEdits as RawCoreEdit[],
    proofs: p.proofs as Array<{ id: string; proof_tex?: string }>,
  };
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
  await clearRoundOutputs(ctx);
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
  /** Validate the complete selected bundle in memory and return its change list
   * without mutating state, proto, working cursor, journal, or round outputs. */
  checkOnly?: boolean;
}): Promise<EscalationLogEntry["changed"]> {
  const { ctx, ids = null, note, directive, checkOnly = false } = args;
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
  const working = await loadWorkingState(ctx);
  const stmtById = new Map(proto.statements.map((s) => [s.id, s]));
  const defById = new Map(proto.definitions.map((d) => [d.id, d]));
  const assIds = new Set(proto.assumptions.map((a) => a.id));
  const bibKeys = (proto.bibliography ?? []).map((b) => b?.key).filter((k): k is string => typeof k === "string");
  const proposals = await readProposedChanges(ctx);
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
  // KNOWN GAP, deliberately not closed: a correction rejected on def:inner is not detected
  // when a consumer reaches it only through def:outer's `inputs`. A transitive closure over
  // the definition graph was implemented and REVERTED. It introduced a dependency notion --
  // statement/definition ids reachable through definition inputs -- that nothing else in
  // the pipeline implements, and the next audit round demanded that notion be honoured by
  // pruneOrphanLemmas, computeValidNodes and snapshotMember too, while disagreeing with
  // itself about whether the closure should read the pre- or post-apply definition graph
  // (using the old graph rejects proofs that an accepted rewiring has just made valid).
  //
  // A guard with one documented level of indirection missing is better than a guard that
  // asserts an invariant the rest of the system does not hold. Closing this properly means
  // giving definitions a first-class dependency edge everywhere, which is a design change,
  // not a patch.
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
  const atomicStatementDeleteIds = new Set(
    selectedCoreEdits.filter((edit) => edit.kind === "statement-delete").map((edit) => edit.id),
  );
  const selectedProofIds = new Set<string>([
    ...selectedStatements.map((change) => change.id),
    ...selectedCoreEdits
      .filter((edit) => edit.kind === "statement-replace")
      .map((edit) => edit.id),
  ]);
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
  for (const proof of (proposals.proofs ?? []).filter((p) => selectedProofIds.has(p.id))) {
    checkSealable("promotable-proof", proof.id, proof.proof_tex);
  }
  if (sealOffenders.length > 0) {
    throw new Error(
      `Refusing D0 apply: ${sealOffenders.length} selected change(s) carry unsealable TeX in ` +
        `${protoPath}. Re-select without these ids (repair them via the mechanical rebuild lane); ` +
        `nothing was mutated.\n${sealOffenders.join("\n")}`,
    );
  }
  const originalStatements = new Map(proto.statements.map((s) => [s.id, structuredClone(s)] as const));
  const originalCarriedStatements = new Map(
    Object.entries(working?.solved ?? {})
      .filter((entry): entry is [string, NonNullable<(typeof entry)[1]>] => entry[1] !== undefined)
      .flatMap(([id, rec]) => rec.node ? [[id, structuredClone(rec.node)] as const] : []),
  );
  const selectedVariantCount =
    statements.filter((c) => !sel || sel.matchesStatement(c.id)).length +
    definitions.filter((c) => !sel || sel.matchesDefinition(c.id)).length +
    assumptions.filter((a) => !sel || sel.matchesAssumption(a.id)).length +
    coreEdits.filter((edit) => !sel || sel.matchesCoreEdit(edit)).length;

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
    if (s.kind === "openendedquestion" && c.direction === "narrow") detachResolvedOeq(c.id);
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
          ...proposedNode,
          statement: carriedNode.statement,
          status: carriedNode.status,
          proof_tex: carriedNode.proof_tex,
        };
        changed.push({
          id: edit.id,
          kind: "statement",
          from: JSON.stringify(carriedNode),
          to: JSON.stringify(composed),
          reason: edit.reason ?? "",
        });
        const pairedCarried = pairedProofById.get(edit.id)?.proofTex;
        if (composed.status === "cited" && composed.source !== undefined && !claimChangedIds.has(edit.id)) {
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
          pairedCarried !== undefined &&
          // Same rule as the frozen branch: a proof paired in a bundle that ALSO rewrites
          // this node's claim argues the old statement. Fall through to the open branch,
          // which keeps the node `to-prove` and partial so the next round re-derives it.
          !claimChangedIds.has(edit.id) &&
          dependencyClosureValid(composed)
        ) {
          const proved = { ...composed, status: "proved" as const, proof_tex: pairedCarried };
          carried.node = proved;
          carried.proof_tex = pairedCarried;
          carried.snapshot = wiredSnapshot(proto, proved, pairedCarried);
          delete carried.partial;
        } else if (
          // A metadata-only replacement does not owe a re-proof when the theorem's
          // proof-relevant snapshot is byte-for-byte unchanged. Previously even a
          // consumer/gap/route edit converted a finished agent theorem into partial
          // debt solely because no redundant paired proof was emitted.
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
        ...proposedNode,
        statement: prior.statement,
        status: prior.status,
        proof_tex: prior.proof_tex,
      };
      const proposedDependencies = new Set(composed.depends_on);
      const structuralBasisNarrowed =
        original.depends_on.some((dependency) => !proposedDependencies.has(dependency)) ||
        declarationNarrowed(original, composed);
      const depSet = (deps: string[]): string => [...new Set(deps)].sort().join("\u0000");
      if (
        prior.kind === "openendedquestion" &&
        depSet(prior.depends_on) !== depSet(composed.depends_on)
      ) detachResolvedOeq(edit.id);
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
      const pairedProto = pairedProofById.get(edit.id)?.proofTex;
      const protoRec = working?.solved[edit.id];
      if (claimChangedIds.has(edit.id)) {
        skipped.push({
          id: edit.id, kind: "proof-pairing",
          why: "this bundle also rewrites the node's claim, so the paired proof argues the OLD " +
            "statement — it is left unpaired and the node stays open for re-derivation",
        });
      } else if (pairedProto !== undefined && protoRec && dependencyClosureValid(composed)) {
        protoRec.proof_tex = pairedProto;
        protoRec.snapshot = wiredSnapshot(proto, composed, pairedProto);
        delete protoRec.partial;
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
      const prior = priorFrozen ?? priorCarried;
      if (!prior) {
        skipped.push({ id: edit.id, kind: "statement-delete", why: "no frozen or carried statement with this id" });
        continue;
      }
      const replacementId = edit.replacement_id;
      if (replacementId === edit.id) {
        throw new Error(`Cannot delete statement ${edit.id} by replacing it with itself`);
      }
      if (
        replacementId !== undefined &&
        !proto.statements.some((s) => s.id === replacementId) &&
        working?.solved[replacementId]?.node?.id !== replacementId
      ) {
        throw new Error(
          `Cannot delete statement ${edit.id}: replacement ${replacementId} is not a frozen or carried statement node`,
        );
      }
      const validationProto = {
        ...proto,
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
      const symbolInbound = proto.symbols.filter((s) => s.ref === edit.id).map((s) => s.name);
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
          depends_on: s.depends_on.map((d) => d === edit.id ? replacementId! : d),
        }));
      for (const symbol of proto.symbols) {
        if (symbol.ref !== edit.id) continue;
        if (replacementId === undefined) delete symbol.ref;
        else symbol.ref = replacementId;
      }
      // A removed frozen node must also be tombstoned in the incremental state;
      // otherwise the next D0 rebuild classifies it as an agent-added stale target
      // and silently resurrects it. Remap carried-node edges but retain their old
      // snapshots so ordinary validity propagation forces a re-proof when needed.
      if (working) {
        delete working.solved[edit.id];
        for (const rec of Object.values(working.solved)) {
          if (!rec.node) continue;
          rec.node.depends_on = replacementId === undefined
            ? rec.node.depends_on.filter((d) => d !== edit.id)
            : rec.node.depends_on.map((d) => d === edit.id ? replacementId : d);
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
      const retained = priorDef.construction === edit.proposed.construction &&
        declarationNarrowed(priorDef, edit.proposed)
        ? (priorDef.free_symbols ?? []).filter(
            (name) => !(edit.proposed.free_symbols ?? []).some((k) => normalizeSymbol(k) === normalizeSymbol(name)),
          )
        : [];
      const appliedDef = retained.length === 0
        ? edit.proposed
        : { ...edit.proposed, free_symbols: [...(edit.proposed.free_symbols ?? []), ...retained] };
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
      const textInbound = findUnsafeDeleteTextReferences(proto, working, edit.id);
      if (textInbound.length > 0) {
        throw new Error(
          `Cannot delete definition ${edit.id}: literal claim/proof references remain in ` +
            `${textInbound.map((ref) => ref.location).join(", ")}. ` +
            "Deleting a graph edge cannot safely rewrite authored mathematics; restate/re-prove the citing nodes first.",
        );
      }
      proto.definitions = proto.definitions.filter((d) => d.id !== edit.id);
      for (const s of proto.statements) s.depends_on = s.depends_on.filter((d) => d !== edit.id);
      for (const rec of Object.values(working?.solved ?? {})) {
        if (rec.node) rec.node.depends_on = rec.node.depends_on.filter((d) => d !== edit.id);
      }
      for (const symbol of proto.symbols) if (symbol.ref === edit.id) delete symbol.ref;
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

  // PAIRED-PROOF PROMOTION for applied claim changes. A paired proof that DECLARED it
  // argues the PROPOSED text (`argues_proposed`, set by the solver in the same bundle as
  // the statement change) is attached now — to the claim it argued, which adjudication
  // just made current — instead of reopening the node for a full re-derivation round
  // whose only job would be re-emitting this proof. The blanket "a paired proof argues
  // the OLD statement" rule above still governs undeclared proofs.
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
    const pendingPromotionIds = new Set(hasUnappliedGlobalInvalidator ? [] : claimChangedIds);
    let promotedThisPass = true;
    while (promotedThisPass && pendingPromotionIds.size > 0) {
      promotedThisPass = false;
      for (const id of [...pendingPromotionIds]) {
        const paired = pairedProofById.get(id);
        if (!paired?.arguesProposed) {
          pendingPromotionIds.delete(id);
          continue;
        }
        const frozen = proto.statements.find((s) => s.id === id);
        const rec = working.solved[id];
        const node = frozen ?? rec?.node;
        if (!node || node.status !== "to-prove") {
          pendingPromotionIds.delete(id);
          continue;
        }
        if (proofContentClosureIntersects({
          core: proto, node, proofText: paired.proofTex, changedIds: unappliedIds, extraStatements: carriedNodes,
        })) {
          pendingPromotionIds.delete(id);
          continue;
        }
        if (!dependencyClosureValid(node)) continue;
        node.status = "proved";
        node.proof_tex = paired.proofTex;
        const snapshot = wiredSnapshot(proto, node, paired.proofTex);
        if (rec) {
          if (rec.node) rec.node = node;
          rec.proof_tex = paired.proofTex;
          rec.snapshot = snapshot;
          delete rec.partial;
        } else {
          working.solved[id] = { proof_tex: paired.proofTex, snapshot };
        }
        pendingPromotionIds.delete(id);
        promotedThisPass = true;
      }
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

  const transactionId = `d0apply:${randomUUID()}`;
  const escalationEntry: EscalationLogEntry = {
    transaction_id: transactionId,
    round: working?.round ?? 0,
    changed,
    note,
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
  } satisfies D0ApplyTransaction);
  const committed = await recoverPendingApply(ctx);
  if (committed === null) throw new Error("D0 apply transaction disappeared before commit");
  return committed;
}
