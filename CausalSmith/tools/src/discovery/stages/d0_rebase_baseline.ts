/**
 * Guarded D0 baseline rebase for an extension of an already accepted core.
 *
 * This is deliberately not part of the ordinary stage machine.  It repairs the
 * exceptional case where a later D-1 revision replaced an accepted D0 core even
 * though the operator intended to extend it.  The accepted core becomes the new
 * frozen proto and its proof bytes become ordinary carried proto-member proofs.
 */
import { CoreSchema, coreNodeIds, type Core } from "../core/schema.js";
import { assembleCore } from "../core/assemble.js";
import {
  snapshotMember,
  symbolBasis,
  WORKING_STORE_FORMAT,
  type WorkingState,
  type EscalationLogEntry,
} from "./d0_working.js";

export interface BaselineRebaseExpectations {
  sourceRevision: string;
  sourceRound: number;
  sourceIds: readonly string[];
  sourceProtoIds: readonly string[];
  currentRevision: string;
  currentRound: number;
  currentEscalationEntries: number;
  currentIds: readonly string[];
  discardCurrentIds: readonly string[];
  discardCurrentSolvedIds: readonly string[];
  qid: string;
  specialization: string;
}

export interface BaselineRebasePlan {
  proto: Core;
  working: WorkingState;
  renderedCore: Core;
  sourceIds: string[];
  currentIds: string[];
}

export interface ExtensionRebasePlan {
  proto: Core;
  working: WorkingState;
  renderedCore: Core;
  preservedIds: string[];
  addedIds: string[];
}

function sortedUnique(xs: Iterable<string>): string[] {
  return [...new Set(xs)].sort();
}

function sortedRecord(record: Record<string, string>): Record<string, string> {
  return Object.fromEntries(Object.entries(record).sort(([a], [b]) => a.localeCompare(b)));
}

function assertExactSet(label: string, actual: Iterable<string>, expected: readonly string[]): string[] {
  const a = sortedUnique(actual);
  const e = sortedUnique(expected);
  if (e.length !== expected.length) {
    throw new Error(`${label}: expected id list contains duplicates`);
  }
  if (JSON.stringify(a) !== JSON.stringify(e)) {
    const as = new Set(a);
    const es = new Set(e);
    const missing = e.filter((id) => !as.has(id));
    const extra = a.filter((id) => !es.has(id));
    throw new Error(
      `${label}: id set mismatch; missing=[${missing.join(", ")}], extra=[${extra.join(", ")}]`,
    );
  }
  return a;
}

function proposalCount(w: WorkingState): number {
  const p = w.proposals;
  if (!p) return 0;
  return p.statements.length + p.definitions.length + p.assumptions.length + p.coreEdits.length + p.proofs.length;
}

function assertCleanCursor(label: string, w: WorkingState): void {
  const proposals = proposalCount(w);
  if (proposals !== 0) {
    throw new Error(`${label}: cursor has ${proposals} unadjudicated proposal item(s); discard/apply them first`);
  }
  if ((w.required_core_edit_mandates ?? []).length !== 0) {
    throw new Error(`${label}: cursor has outstanding exact core-edit mandates`);
  }
}

function frozenNode(node: Core["statements"][number]): Core["statements"][number] {
  const copy = structuredClone(node);
  copy.status = "to-prove";
  delete copy.proof_tex;
  // GP2 requires every D-1 statement to be to-prove and to omit D0's proof
  // strategy. CoreSchema also permits `source` iff status=cited. Compare every
  // accepted statement through that legal D-1 claim view, then restore the
  // sealed D0-only metadata below.
  delete copy.route;
  delete copy.source;
  return copy;
}

/** Meaning-bearing claim metadata that an embedded D0-added node must share
 * exactly with the accepted core before its proof may be re-owned/carried. */
function statementClaimView(node: Core["statements"][number]): unknown {
  return {
    id: node.id,
    kind: node.kind,
    statement: node.statement,
    free_symbols: node.free_symbols,
    depends_on: node.depends_on,
  };
}

function byId<T extends { id: string }>(xs: readonly T[]): Map<string, T> {
  return new Map(xs.map((x) => [x.id, x]));
}

/**
 * Rebase an accepted D0 core onto an additive D-1.2 proposal.  Unlike the
 * historical repair transaction above, this preserves the newly proposed
 * nodes as open targets.  Every accepted addressable node, symbol, and
 * bibliography entry must survive byte-semantically; otherwise the proposal is
 * a replacement and this extension route fails closed.
 */
export function prepareD0ExtensionRebase(args: {
  sourceCore: Core;
  sourceWorking: WorkingState;
  extensionProto: Core;
  sourceRevision: string;
  extensionRevision: string;
  escalationEntries: number;
}): ExtensionRebasePlan {
  const sourceCore = CoreSchema.parse(args.sourceCore);
  const proto = CoreSchema.parse(args.extensionProto);
  if (sourceCore.qid !== proto.qid || sourceCore.specialization !== proto.specialization) {
    throw new Error("extension rebase: source/proposal run identity mismatch");
  }
  if (sourceCore.cluster !== proto.cluster) {
    throw new Error("extension rebase: source/proposal cluster mismatch");
  }
  if (args.sourceWorking.proposal_revision !== args.sourceRevision) {
    throw new Error(
      `extension rebase: source cursor revision mismatch; expected ${args.sourceRevision}, found ` +
        `${args.sourceWorking.proposal_revision ?? "<none>"}`,
    );
  }
  if (args.extensionRevision === args.sourceRevision) {
    throw new Error("extension rebase: proposal revision did not advance");
  }
  assertCleanCursor("extension source", args.sourceWorking);
  if (JSON.stringify(args.sourceWorking.symbol_basis ?? {}) !== JSON.stringify(symbolBasis(sourceCore))) {
    throw new Error("extension rebase: source symbol basis is stale relative to the accepted core");
  }

  const compareCatalog = <T extends { id: string }>(
    label: string,
    source: readonly T[],
    candidate: readonly T[],
    normalize: (x: T) => unknown = (x) => x,
  ): void => {
    const candidateById = byId(candidate);
    for (const prior of source) {
      const next = candidateById.get(prior.id);
      if (!next) throw new Error(`extension rebase: accepted ${label} ${prior.id} was omitted`);
      if (JSON.stringify(normalize(next)) !== JSON.stringify(normalize(prior))) {
        throw new Error(`extension rebase: accepted ${label} ${prior.id} was changed`);
      }
    }
  };
  compareCatalog("assumption", sourceCore.assumptions, proto.assumptions);
  compareCatalog("definition", sourceCore.definitions, proto.definitions);
  const extensionStatements = byId(proto.statements);
  for (const accepted of sourceCore.statements) {
    const proposed = extensionStatements.get(accepted.id);
    if (!proposed) continue; // compareCatalog below emits the canonical omission error
    if (
      proposed.status !== "to-prove" ||
      proposed.source !== undefined ||
      proposed.proof_tex !== undefined ||
      (proposed.route ?? "").trim() !== ""
    ) {
      throw new Error(
        `extension rebase: accepted statement ${accepted.id} must use the GP2 to-prove proposal form`,
      );
    }
  }
  const acceptedStatementIds = new Set(sourceCore.statements.map((statement) => statement.id));
  for (const proposed of proto.statements) {
    if (
      !acceptedStatementIds.has(proposed.id) &&
      (proposed.status !== "to-prove" ||
        proposed.source !== undefined ||
        proposed.proof_tex !== undefined ||
        (proposed.route ?? "").trim() !== "")
    ) {
      throw new Error(
        `extension rebase: new statement ${proposed.id} must remain in the open GP2 proposal form ` +
          `(no proof, citation, or D0 route)`,
      );
    }
  }
  compareCatalog("statement", sourceCore.statements, proto.statements, (s) => frozenNode(s));
  compareCatalog("symbol", sourceCore.symbols.map((s) => ({ ...s, id: s.name })), proto.symbols.map((s) => ({ ...s, id: s.name })));
  compareCatalog(
    "bibliography entry",
    (sourceCore.bibliography ?? []).map((b) => ({ ...b, id: b.key })),
    (proto.bibliography ?? []).map((b) => ({ ...b, id: b.key })),
  );

  // The proposal author cannot legally re-emit a cited status/source or a D0
  // proof route under GP2. Reinstall each cited statement exactly and restore
  // the exact accepted route on proved statements only after claim equivalence
  // is checked. The extension model never gets authority to rewrite or invent
  // those sealed bytes.
  const acceptedStatements = byId(sourceCore.statements);
  proto.statements = proto.statements.map((statement) => {
    const accepted = acceptedStatements.get(statement.id);
    if (!accepted) return statement;
    if (accepted.status === "cited") return structuredClone(accepted);
    const restored = structuredClone(statement);
    if (accepted.route === undefined) delete restored.route;
    else restored.route = accepted.route;
    return restored;
  });

  const solved: WorkingState["solved"] = {};
  const protoStatements = byId(proto.statements);
  for (const statement of sourceCore.statements) {
    const sourceRecord = args.sourceWorking.solved[statement.id];
    if (statement.status === "cited") {
      if (sourceRecord !== undefined) {
        throw new Error(
          `extension rebase: accepted cited statement ${statement.id} has an inconsistent solved record`,
        );
      }
      continue;
    }
    if (statement.status === "to-prove") {
      if (statement.proof_tex !== undefined || statement.source !== undefined || sourceRecord !== undefined) {
        throw new Error(
          `extension rebase: accepted open statement ${statement.id} has inconsistent proof/citation state`,
        );
      }
      // A banked core may deliberately retain an OEQ/conjecture. It stays a
      // frozen open proto member; no solved record is manufactured or carried.
      continue;
    }
    if (!(statement.proof_tex ?? "").trim()) {
      throw new Error(`extension rebase: accepted proved statement ${statement.id} has no proof bytes`);
    }
    if (!sourceRecord || sourceRecord.partial || sourceRecord.proof_tex !== statement.proof_tex) {
      throw new Error(`extension rebase: accepted proof bytes for ${statement.id} do not match the cursor`);
    }
    if (
      sourceRecord.node &&
      JSON.stringify(statementClaimView(statement)) !== JSON.stringify(statementClaimView(sourceRecord.node))
    ) {
      throw new Error(
        `extension rebase: accepted carried node ${statement.id} has stale claim metadata`,
      );
    }
    const historicalSnapshot = snapshotMember(sourceCore, sourceRecord.node ?? statement);
    const snapshotMatches = historicalSnapshot.stmt === sourceRecord.snapshot.stmt &&
      JSON.stringify(sortedUnique(historicalSnapshot.depends_on ?? [])) ===
        JSON.stringify(sortedUnique(sourceRecord.snapshot.depends_on ?? [])) &&
      JSON.stringify(sortedRecord(historicalSnapshot.defs)) ===
        JSON.stringify(sortedRecord(sourceRecord.snapshot.defs)) &&
      JSON.stringify(sortedRecord(historicalSnapshot.assumptions)) ===
        JSON.stringify(sortedRecord(sourceRecord.snapshot.assumptions));
    if (!snapshotMatches) {
      throw new Error(`extension rebase: accepted proof basis for ${statement.id} is stale`);
    }
    const target = protoStatements.get(statement.id)!;
    solved[statement.id] = {
      proof_tex: statement.proof_tex,
      snapshot: snapshotMember(proto, target),
    };
  }

  const working: WorkingState = {
    round: args.sourceWorking.round,
    escalation_entries_consumed: args.escalationEntries + 1,
    proposal_revision: args.extensionRevision,
    symbol_basis: symbolBasis(proto),
    solved,
    proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    resolved_oeqs: {},
    required_core_edit_mandates: [],
    store_format: WORKING_STORE_FORMAT,
  };
  const renderedCore = CoreSchema.parse(assembleCore(proto, working));
  const renderedStatements = byId(renderedCore.statements);
  for (const accepted of sourceCore.statements) {
    if (JSON.stringify(renderedStatements.get(accepted.id)) !== JSON.stringify(accepted)) {
      throw new Error(
        `extension rebase: accepted statement ${accepted.id} was not restored exactly after rebase`,
      );
    }
  }
  const sourceIds = sortedUnique(coreNodeIds(sourceCore));
  const protoIds = sortedUnique(coreNodeIds(proto));
  const sourceSet = new Set(sourceIds);
  return {
    proto,
    working,
    renderedCore,
    preservedIds: sourceIds,
    addedIds: protoIds.filter((id) => !sourceSet.has(id)),
  };
}

/** Build and fully validate the replacement stores without touching disk. */
export function prepareD0BaselineRebase(args: {
  sourceCore: Core;
  sourceProto: Core;
  sourceWorking: WorkingState;
  currentProto: Core;
  currentWorking: WorkingState;
  /** Journal rows after currentWorking.escalation_entries_consumed. */
  currentPendingEscalations?: readonly EscalationLogEntry[];
  expectations: BaselineRebaseExpectations;
}): BaselineRebasePlan {
  const sourceCore = CoreSchema.parse(args.sourceCore);
  const sourceProto = CoreSchema.parse(args.sourceProto);
  const currentProto = CoreSchema.parse(args.currentProto);
  const { sourceWorking, currentWorking, expectations: e } = args;
  for (const [label, core] of [["source core", sourceCore], ["source proto", sourceProto], ["current proto", currentProto]] as const) {
    if (core.qid !== e.qid || (core.specialization ?? e.specialization) !== e.specialization) {
      throw new Error(`${label}: run identity mismatch (found ${core.qid}/${core.specialization ?? "<none>"})`);
    }
  }
  if (sourceCore.cluster !== sourceProto.cluster || sourceCore.cluster !== currentProto.cluster) {
    throw new Error("source/current cluster mismatch");
  }

  if (sourceWorking.proposal_revision !== e.sourceRevision || sourceWorking.round !== e.sourceRound) {
    throw new Error(
      `source cursor mismatch: expected ${e.sourceRevision} round ${e.sourceRound}, found ` +
        `${sourceWorking.proposal_revision ?? "<none>"} round ${sourceWorking.round}`,
    );
  }
  if (currentWorking.proposal_revision !== e.currentRevision || currentWorking.round !== e.currentRound) {
    throw new Error(
      `current cursor mismatch: expected ${e.currentRevision} round ${e.currentRound}, found ` +
        `${currentWorking.proposal_revision ?? "<none>"} round ${currentWorking.round}`,
    );
  }
  const pendingEscalations = args.currentPendingEscalations ?? [];
  const consumed = currentWorking.escalation_entries_consumed ?? 0;
  if (consumed + pendingEscalations.length !== e.currentEscalationEntries) {
    throw new Error(
      `current escalation cursor mismatch: consumed ${consumed} + supplied tail ${pendingEscalations.length} ` +
        `does not equal expected journal length ${e.currentEscalationEntries}`,
    );
  }
  const actionableTail = pendingEscalations.filter((entry) =>
    entry.provenance_only !== true &&
    (entry.changed.length > 0 || !!entry.directive || !!entry.require_core_changes ||
    (entry.required_core_targets ?? []).length > 0 || (entry.required_core_edits ?? []).length > 0 ||
    (entry.required_core_edit_mandates ?? []).length > 0 ||
    (entry.cancelled_core_edit_mandates ?? []).length > 0 || !!entry.cancel_require_core_changes ||
    (entry.cancelled_core_targets ?? []).length > 0));
  if (actionableTail.length > 0) {
    throw new Error(
      `current cursor has ${actionableTail.length} pending actionable escalation journal row(s); consume/adjudicate them first`,
    );
  }
  assertCleanCursor("source", sourceWorking);
  assertCleanCursor("current", currentWorking);
  const sourceIds = assertExactSet("source core", coreNodeIds(sourceCore), e.sourceIds);
  assertExactSet("source proto", coreNodeIds(sourceProto), e.sourceProtoIds);
  if (JSON.stringify(sourceWorking.symbol_basis ?? {}) !== JSON.stringify(symbolBasis(sourceCore))) {
    throw new Error("historical source symbol basis is stale relative to the accepted core");
  }
  const currentIds = assertExactSet("current proto", coreNodeIds(currentProto), e.currentIds);
  const sourceIdSet = new Set(sourceIds);
  assertExactSet("explicit current-id discard", currentIds.filter((id) => !sourceIdSet.has(id)), e.discardCurrentIds);
  const sourceSolvedProofs = new Map(
    Object.entries(sourceWorking.solved).map(([id, record]) => [id, record.proof_tex] as const),
  );
  const discardedSolvedIds = Object.entries(currentWorking.solved)
    .filter(([id, record]) => sourceSolvedProofs.get(id) !== record.proof_tex)
    .map(([id]) => id);
  assertExactSet("explicit current-proof discard", discardedSolvedIds, e.discardCurrentSolvedIds);

  const proto = structuredClone(sourceCore);
  const solved: WorkingState["solved"] = {};
  for (const statement of proto.statements) {
    if (statement.status === "cited") continue;
    if (statement.status !== "proved" || !(statement.proof_tex ?? "").trim()) {
      throw new Error(
        `source core ${statement.id} is not an accepted proved node with nonempty proof bytes`,
      );
    }
    const sourceRecord = sourceWorking.solved[statement.id];
    if (!sourceRecord || sourceRecord.partial || sourceRecord.proof_tex !== statement.proof_tex) {
      throw new Error(
        `source proof mismatch for ${statement.id}: accepted core and carried cursor are not byte-identical`,
      );
    }
    if (sourceRecord.node) {
      if (JSON.stringify(statementClaimView(statement)) !== JSON.stringify(statementClaimView(sourceRecord.node))) {
        throw new Error(`source carried node mismatch for ${statement.id}: historical claim metadata is stale`);
      }
    }
    const historicalSnapshot = snapshotMember(sourceCore, sourceRecord.node ?? statement);
    const snapshotMatches = historicalSnapshot.stmt === sourceRecord.snapshot.stmt &&
      JSON.stringify(sortedUnique(historicalSnapshot.depends_on ?? [])) ===
        JSON.stringify(sortedUnique(sourceRecord.snapshot.depends_on ?? [])) &&
      JSON.stringify(sortedRecord(historicalSnapshot.defs)) === JSON.stringify(sortedRecord(sourceRecord.snapshot.defs)) &&
      JSON.stringify(sortedRecord(historicalSnapshot.assumptions)) ===
        JSON.stringify(sortedRecord(sourceRecord.snapshot.assumptions));
    if (!snapshotMatches) {
      throw new Error(`source proof basis mismatch for ${statement.id}: historical snapshot is stale`);
    }
    const proof = statement.proof_tex;
    statement.status = "to-prove";
    delete statement.proof_tex;
    // The accepted agent-added node is now a frozen proto member.  Re-snapshot it
    // against that new baseline instead of retaining its former agent ownership.
    solved[statement.id] = {
      proof_tex: proof,
      snapshot: snapshotMember(proto, statement),
    };
  }

  const expectedSolved = sortedUnique(sourceCore.statements.filter((s) => s.status === "proved").map((s) => s.id));
  assertExactSet("source carried proofs", Object.keys(solved), expectedSolved);

  const working: WorkingState = {
    round: currentWorking.round,
    // A note-only discard receipt is inert and is consumed by this explicit
    // operator transaction.  Actionable tail rows were rejected above.
    // The replayable replacement transaction appends one provenance-only receipt.
    escalation_entries_consumed: e.currentEscalationEntries + 1,
    proposal_revision: e.currentRevision,
    symbol_basis: symbolBasis(proto),
    solved,
    proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
    resolved_oeqs: {},
    required_core_edit_mandates: [],
    store_format: WORKING_STORE_FORMAT,
  };
  const renderedCore = CoreSchema.parse(assembleCore(proto, working));

  // Re-rendering must recover the accepted source exactly.  This catches a
  // supposedly "mechanical" rebase that would silently alter dependencies,
  // assumptions, prose overlays, or proof status.
  if (JSON.stringify(renderedCore) !== JSON.stringify(sourceCore)) {
    throw new Error("rebased proto + carried proofs do not render byte-equivalent accepted core JSON");
  }
  return { proto, working, renderedCore, sourceIds, currentIds };
}
