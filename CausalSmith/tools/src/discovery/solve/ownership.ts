// Who may write what, in a multi-unit D0 solve round.
//
// WHY THIS IS ITS OWN FILE. D0 dispatches several solve units in parallel, each a
// separate LLM call. When two of them emit a payload for the same node, the merge
// must resolve it deterministically or the assembled core depends on dispatch order.
// Getting that wrong has aborted whole rounds repeatedly (comparator lemma, a shared
// symbol, sibling statements, the reverse-dependency rebuild), and each fix was
// applied in the middle of a 1200-line function where the ownership model as a whole
// was never visible. It is visible here.
//
// The model, in three layers:
//   1. PARTITION      weakly-connected components of the to-prove dependency graph
//                     decide which unit gets which targets (see groupToProveByComponent)
//   2. SEMANTIC OWNER every dispatched statement id maps to exactly one unit
//   3. SHARED UPSTREAM for a purely shared exact bundle, one unit runs alone and is
//                     canonical writer for the UNION of shared payloads; deferred
//                     units re-enter only after acceptance (never one owner per pair)
//
// Everything is decided from unit CONTENT, never array order, so Promise scheduling
// cannot change who owns what.
//
// GOVERNING PRINCIPLE (2026-08-30, after repeated round aborts): ownership exists to
// adjudicate COMPETING emissions deterministically — it must bound damage, never
// abort a round. A channel with exactly one emitted payload (or byte-identical
// payloads) cannot depend on dispatch order, so when the computed owner stayed
// silent the sole emission is credited (sole-emitter fallback) instead of
// quarantined; genuinely competing different payloads are withheld from everyone
// (conflict drop); and an ambiguously reachable shared durable node is left
// unowned rather than thrown on. The only remaining fatal is intra-unit
// self-contradiction, which casts doubt on that unit's whole output.

import type { CoreStatement } from "../core/schema.js";
import { coreEditTarget, type RawCoreEdit } from "../stages/d0_apply.js";
import type { SolveUnitOutput } from "./schemas.js";

export type SolveDispatchUnit = { targets: CoreStatement[]; label: string; priorContext: string };

/** Recover durable proof ownership for the live assembled proof closure.
 *
 * Agent-authored helpers can be shelved (and therefore absent from
 * `core.statements`) while a published statement still depends on them.  A later
 * solver may complete those helpers through `proofs[]` without re-emitting their
 * declarations.  Ownership projection runs before merge's carried-statement
 * fallback, so it must follow the dependency closure here or it will quarantine
 * the only proof bytes before merge can attach them.  Starting from published and
 * exact-required roots keeps unrelated historical shelved debt unwritable. */
export function selectLiveDurableProofOwners(args: {
  coreStatements: ReadonlyArray<CoreStatement>;
  requiredIds: ReadonlySet<string>;
  durableRecords: ReadonlyMap<string, { owner: string; node: CoreStatement; proofDependencies?: string[] }>;
  activeTargetOwners: ReadonlyMap<string, string>;
  statementPostimages?: ReadonlyMap<string, CoreStatement>;
  /** Nodes for which this round actually carries a write-capable payload. A
   * shared immutable dependency needs no elected writer merely because several
   * active roots read it; omitting it keeps the persisted proof untouched. */
  writableIds?: ReadonlySet<string>;
}): Map<string, string> {
  const coreById = new Map(args.coreStatements.map((statement) => [statement.id, statement] as const));
  const direct = new Set<string>([
    ...args.coreStatements.map((statement) => statement.id),
    ...args.requiredIds,
  ]);
  const reachableOwners = new Map<string, Set<string>>();
  for (const [root, owner] of args.activeTargetOwners) {
    const seen = new Set<string>([root]);
    const queue = [root];
    while (queue.length > 0) {
      const id = queue.shift()!;
      const durable = args.durableRecords.get(id);
      const statement = args.statementPostimages?.get(id) ?? coreById.get(id) ?? durable?.node;
      if (!statement) continue;
      const dependencies = new Set([
        ...statement.depends_on,
        ...(durable?.proofDependencies ?? []),
      ]);
      for (const dependency of dependencies) {
        const activeOwner = args.activeTargetOwners.get(dependency);
        if (activeOwner !== undefined) {
          // A current-round dispatch is the strongest ownership receipt.  A
          // sibling may depend on that target, but dependency reachability must
          // not cross the explicit semantic-owner boundary and reassign either
          // the target or its private proof closure to the consumer.  Targets in
          // the same WCC share one owner, so following that edge remains safe.
          if (activeOwner === owner && !seen.has(dependency)) {
            seen.add(dependency);
            queue.push(dependency);
          }
          continue;
        }
        const isDurable = args.durableRecords.has(dependency);
        if (!isDurable && !coreById.has(dependency)) continue;
        // Published proto/core nodes predate durable owner receipts.  They are
        // nevertheless part of the same live proof closure and may require an
        // exact paired statement/proof revalidation when an upstream definition
        // changes.  Give such reachable ownerless nodes the active root owner;
        // the caller admits only complete paired postimages and still rejects a
        // node reached from more than one active root below.
        if (isDurable || coreById.has(dependency)) {
          const owners = reachableOwners.get(dependency) ?? new Set<string>();
          owners.add(owner);
          reachableOwners.set(dependency, owners);
        }
        if (!seen.has(dependency)) {
          seen.add(dependency);
          queue.push(dependency);
        }
      }
    }
  }
  const owners = new Map<string, string>();
  for (const id of direct) {
    const activeOwner = args.activeTargetOwners.get(id);
    if (activeOwner !== undefined) {
      // Active targets are already governed by semanticTargetOwners at the
      // capability boundary; this fallback map is only for undispatched nodes.
      continue;
    }
    const record = args.durableRecords.get(id);
    if (record) {
      // Records store the mathematical owner id, while a WCC dispatch may choose
      // another member as its canonical unit label.  Normalize an active recorded
      // owner through the current semantic map so harmless component relabeling
      // cannot strand its durable children.
      owners.set(id, args.activeTargetOwners.get(record.owner) ?? record.owner);
    }
  }
  for (const [id, candidates] of reachableOwners) {
    if (candidates.size > 1) {
      if (args.writableIds !== undefined && !args.writableIds.has(id)) continue;
      // Two active components legitimately reach one shared node whenever the
      // dispatch partition split them: coupling edges run only through OPEN
      // statements (groupToProveByComponent), so a shared durable/published
      // dependency never merges units. This used to THROW, which aborted whole
      // paid rounds deterministically on every resume (exp_multiarm 3x,
      // eid_periodic, exp_two_wave, 2026-08-29/30). Resolve by content instead:
      // the durable record's owner keeps the node when it is itself one of the
      // reaching components; otherwise the node stays UNOWNED — a sole emission
      // still lands through projection's sole-emitter fallback, and competing
      // emissions are withheld by the cross-unit conflict guard. Either way the
      // outcome is content-determined, never dispatch-order-determined.
      const record = args.durableRecords.get(id);
      const recordOwner = record !== undefined
        ? args.activeTargetOwners.get(record.owner) ?? record.owner
        : undefined;
      if (recordOwner !== undefined && candidates.has(recordOwner)) {
        owners.set(id, recordOwner);
      } else {
        // Actually unowned: the direct pass above may have preseeded the stale
        // record owner for a published node — a stale label that no current unit
        // carries would otherwise satisfy the sole-emitter fallback's
        // owner-not-live test and quietly authorize one of the CONTESTED units.
        owners.delete(id);
        console.warn(
          `[D0-SOLVE] shared live durable node '${id}' is reachable from multiple units ` +
            `(${[...candidates].sort().join(", ")}); leaving it unowned instead of aborting the round.`,
        );
      }
      continue;
    }
    const owner = [...candidates][0];
    if (owner !== undefined) owners.set(id, owner);
  }
  return owners;
}

/** Pick one directive-wide emission owner from unit CONTENT, never array order.
 * The broadest component sees the most local mathematics; lexical label order is
 * a stable tie-breaker, so Promise scheduling or a reordered dispatch array cannot
 * change which payload becomes canonical. */
export function selectDirectiveEmissionOwnerLabel(
  units: ReadonlyArray<{ targets: ReadonlyArray<unknown>; label: string }>,
): string | null {
  if (units.length === 0) return null;
  const headlineRank = (label: string): number => {
    if (label.startsWith("thm:")) return 5;
    if (label.startsWith("conj:")) return 4;
    if (label.startsWith("oeq:")) return 3;
    if (label.startsWith("prop:")) return 2;
    if (label.startsWith("lem:")) return 1;
    return 0;
  };
  return [...units].sort((a, b) => {
    const byBreadth = b.targets.length - a.targets.length;
    if (byBreadth !== 0) return byBreadth;
    const byHeadline = headlineRank(b.label) - headlineRank(a.label);
    if (byHeadline !== 0) return byHeadline;
    return a.label < b.label ? -1 : a.label > b.label ? 1 : 0;
  })[0].label;
}

/** Every dispatched statement target has one semantic owner: the component that
 * is actually solving it. Build the map from unit contents so reversing dispatch
 * order cannot reassign a target. Duplicate membership should never occur after
 * WCC partitioning, but is resolved with the same deterministic selector rather
 * than insertion order if an upstream regression creates it. */
export function selectSemanticTargetOwners(
  units: ReadonlyArray<{ targets: ReadonlyArray<{ id: string }>; label: string }>,
): Map<string, string> {
  const candidates = new Map<string, Array<{ targets: ReadonlyArray<{ id: string }>; label: string }>>();
  for (const unit of units) {
    for (const target of unit.targets) {
      const bucket = candidates.get(target.id) ?? [];
      bucket.push(unit);
      candidates.set(target.id, bucket);
    }
  }
  const owners = new Map<string, string>();
  for (const id of [...candidates.keys()].sort()) {
    const bucket = candidates.get(id)!;
    const labels = [...new Set(bucket.map((unit) => unit.label))].sort();
    if (labels.length !== 1) {
      console.warn(
        `[D0-SOLVE] semantic target '${id}' appears under multiple dispatch labels ` +
          `(${labels.join(", ")}); leaving it unowned so every competing emission is quarantined.`,
      );
      continue;
    }
    const owner = selectDirectiveEmissionOwnerLabel(bucket);
    if (owner !== null) owners.set(id, owner);
  }
  return owners;
}

export interface QuarantinedCapabilityEmission {
  unit: string;
  owner: string;
  category: string;
  target: string;
  operation?: string;
}

export interface EmissionCapability {
  category: string;
  target: string;
  semanticIds: string[];
  /** Operation discriminator for multi-operation channels such as core edits. */
  operation?: string;
  /** Singleton emissions belong to the directive-wide owner when no dispatched
   * statement id supplies a narrower semantic owner. */
  singleton: boolean;
  /** This payload is one half of an owner-authored statement correction. Durable
   * provenance may authorize it only when merge has verified the complete pair. */
  durableCorrection?: boolean;
}

/** One centralized capability classifier for every solver output channel. New
 * singleton channels must be added here, so ownership cannot regress one payload
 * category at a time. A semantic statement owner always overrides the broader
 * directive owner. `null` means deliberately unowned/local and therefore still
 * subject to ordinary duplicate-conflict detection across units. */
function capabilityOwner(args: {
  capability: EmissionCapability;
  semanticTargetOwners: ReadonlyMap<string, string>;
  directiveOwnerLabel: string | null;
}): string | null {
  const semanticOwners = [...new Set(
    args.capability.semanticIds
      .map((id) => args.semanticTargetOwners.get(id))
      .filter((owner): owner is string => owner !== undefined),
  )].sort();
  if (semanticOwners.length > 1) {
    throw new Error(
      `Stage 0-SOLVE ambiguous write capability for ${args.capability.target}: ${semanticOwners.join(", ")}`,
    );
  }
  if (semanticOwners.length === 1) return semanticOwners[0];
  if (!args.capability.singleton) return null;
  // Undirected cold solves intentionally have no cross-unit singleton owner;
  // their independently discovered payloads remain coequal and the conflict
  // guard adjudicates them. Directed rounds with dispatched units always select
  // an owner; an exact directive with no dispatch fails at the exact-target gate.
  if (args.directiveOwnerLabel === null) return null;
  return args.directiveOwnerLabel;
}

function isCatalogCoreEdit(edit: RawCoreEdit): boolean {
  return edit.kind === "assumption-replace" || edit.kind === "assumption-delete" ||
    edit.kind === "definition-add" || edit.kind === "definition-replace" || edit.kind === "definition-delete" ||
    edit.kind === "bibliography-replace" ||
    edit.kind === "target-estimand-replace" ||
    edit.kind === "estimand-functional-replace" ||
    edit.kind === "comparator-promise-table-replace" ||
    edit.kind === "symbol-add" || edit.kind === "symbol-replace" || edit.kind === "symbol-delete" ||
    edit.kind === "rebuild-reverse-dependencies";
}

/** Project every output channel through its declared write capability BEFORE
 * duplicate comparison or merge. Unauthorized emissions are not coequal payloads.
 * The authorized owner wins deterministically, independent of completion order;
 * exact targets with only unauthorized emissions fail closed. */
export function projectOutputsToWriteCapabilities(args: {
  outputs: SolveUnitOutput[];
  dispatch: SolveDispatchUnit[];
  semanticTargetOwners: ReadonlyMap<string, string>;
  /** Durable ownership for an agent-authored node that is not a dispatched target
   * this round. This is deliberately supplied only for live current-core nodes,
   * exact targets, or nodes carrying a same-round statement edit; it must not turn
   * every shelved historical helper into writable ambient state. */
  durableTargetOwners?: ReadonlyMap<string, string>;
  /** Undispatched carried nodes whose durable owner emitted one complete paired
   * statement-change + statement-replace transaction in this same unit. */
  durableCorrectionTargetOwners?: ReadonlyMap<string, string>;
  /** Targets for which more than one unit emitted a complete correction
   * transaction. Every transaction channel is quarantined, including an
   * otherwise authorized owner's proof, so identical siblings cannot collapse
   * into an apparently valid edit. */
  deniedCorrectionTargets?: ReadonlySet<string>;
  directiveOwnerLabel: string | null;
  /** The owner ran as a validated upstream phase. Its silence is intentional and
   * must not be bypassed by a downstream sole-emitter fallback. */
  strictSharedOwner?: boolean;
  requiredCoreTargets: ReadonlySet<string>;
  /** Explicit cross-cutting ids assigned to the staged directive owner. */
  sharedTargetIds?: ReadonlySet<string>;
  existingStatementIds?: ReadonlySet<string>;
}): { outputs: SolveUnitOutput[]; quarantined: QuarantinedCapabilityEmission[] } {
  const required = (target: string): boolean => args.requiredCoreTargets.has(target);
  const shared = (target: string): boolean => args.sharedTargetIds?.has(target) === true;
  const proofCap = (id: string): EmissionCapability => ({
    category: "proof", target: id, semanticIds: [id], singleton: required(id),
  });
  const resolutionCap = (sourceId: string, theoremId: string): EmissionCapability => ({
    // The source OEQ owns the resolution transaction. The answer theorem may be
    // a sibling target (or an already-carried agent node), so including it here
    // would manufacture an ambiguity between two legitimate semantic owners.
    category: "oeq-resolution", target: sourceId, semanticIds: [sourceId], singleton: true,
  });
  const addedNodeCap = (statement: CoreStatement): EmissionCapability => ({
    category: statement.status === "cited" ? "cited-added-node" : "added-node",
    target: statement.id,
    semanticIds: [statement.id],
    singleton: required(statement.id) || shared(statement.id),
  });
  const statementChangeCap = (id: string): EmissionCapability => ({
    category: "statement-change", target: id, semanticIds: [id], singleton: required(id), durableCorrection: true,
  });
  const definitionChangeCap = (id: string): EmissionCapability => ({
    category: "definition-change", target: id, semanticIds: [], singleton: true,
  });
  const assumptionCap = (id: string): EmissionCapability => ({
    category: "assumption", target: id, semanticIds: [], singleton: true,
  });
  const coreEditCap = (edit: RawCoreEdit): EmissionCapability => {
    const target = coreEditTarget(edit);
    return {
      category: "core-edit",
      target,
      operation: edit.kind,
      semanticIds: [target],
      singleton: isCatalogCoreEdit(edit) || required(target),
      durableCorrection: edit.kind === "statement-replace" || edit.kind === "statement-delete",
    };
  };
  const proseCap = (): EmissionCapability => ({
    category: "prose-updates", target: "prose:paper-wide", semanticIds: [], singleton: true,
  });
  const statementNoteCap = (id: string): EmissionCapability => ({
    category: "statement-note", target: id, semanticIds: [id], singleton: true,
  });

  // This is only the cheap raw-emission check.  Merge performs the decisive
  // category/operation-specific check against the final normalized carrier;
  // doing that here would incorrectly reject a sealed mandate that outranks a
  // worker's sibling emission but is not itself a raw worker output.
  const authorizedEmissions = new Set<string>();
  // A carried agent node has no frozen proto declaration, so it can temporarily be
  // absent from `core.statements` while a narrowing proposal is pending. Its recorded
  // owner is still the only unit allowed to refresh the proof. Start with that durable
  // fallback, then let this round's explicit dispatch ownership override it.
  const effectiveSemanticOwners = new Map(args.semanticTargetOwners);
  const proofSemanticOwners = new Map(args.durableTargetOwners ?? []);
  const correctionSemanticOwners = new Map(args.durableTargetOwners ?? []);
  // Existing-node motivation prose belongs to the one directive-wide prose
  // writer, not to a mathematical proof-closure owner. Same-round new nodes are
  // the exception: their emitter owns their initial note until they are durable.
  const noteSemanticOwners = new Map<string, string>();
  // A shelved/partial agent node remains in the durable catalog under its owner.
  // Solvers often re-emit the completed byte-identical node through added_lemmas;
  // treat that channel as an owner-authored recovery, while merge's existing-node
  // identity checks still reject a claim collision or unauthorized replacement.
  const addedNodeSemanticOwners = new Map(args.durableTargetOwners ?? []);
  for (const [id, owner] of args.durableCorrectionTargetOwners ?? []) {
    correctionSemanticOwners.set(id, owner);
  }
  for (const [id, owner] of args.semanticTargetOwners) {
    proofSemanticOwners.set(id, owner);
    correctionSemanticOwners.set(id, owner);
  }
  const dispatchLabelsByTarget = new Map<string, Set<string>>();
  for (const unit of args.dispatch) {
    for (const target of unit.targets) {
      const labels = dispatchLabelsByTarget.get(target.id) ?? new Set<string>();
      labels.add(unit.label);
      dispatchLabelsByTarget.set(target.id, labels);
    }
  }
  const contestedDispatchTargets = new Set(
    [...dispatchLabelsByTarget].filter(([, labels]) => labels.size > 1).map(([id]) => id),
  );
  for (const unit of args.dispatch) {
    for (const target of unit.targets) {
      // Duplicate dispatch membership is itself a contested ownership claim. Do
      // not let iteration order manufacture an owner after the selector above
      // deliberately left the target unowned.
      if ((dispatchLabelsByTarget.get(target.id)?.size ?? 0) !== 1) continue;
      // An explicit current-round dispatch always supersedes historical provenance.
      // The durable map is only a fallback for a node absent from this dispatch.
      effectiveSemanticOwners.set(target.id, unit.label);
      proofSemanticOwners.set(target.id, unit.label);
      correctionSemanticOwners.set(target.id, unit.label);
      addedNodeSemanticOwners.set(target.id, unit.label);
    }
  }
  const newStatementEmitters = new Map<string, Set<string>>();
  const noteNewStatementEmitter = (id: string, unit: string): void => {
    const emitters = newStatementEmitters.get(id) ?? new Set<string>();
    emitters.add(unit);
    newStatementEmitters.set(id, emitters);
  };
  for (let i = 0; i < args.outputs.length; i += 1) {
    for (const statement of args.outputs[i].added_lemmas) {
      noteNewStatementEmitter(statement.id, args.dispatch[i].label);
    }
    for (const resolution of args.outputs[i].resolved_oeqs) {
      noteNewStatementEmitter(resolution.theorem.id, args.dispatch[i].label);
    }
  }
  for (const [id, emitters] of newStatementEmitters) {
    if (emitters.size === 1 && !args.existingStatementIds?.has(id)) {
      const emitter = [...emitters][0];
      const singletonNode = required(id) || shared(id);
      effectiveSemanticOwners.set(id, emitter);
      proofSemanticOwners.set(id, emitter);
      correctionSemanticOwners.set(id, emitter);
      noteSemanticOwners.set(id, singletonNode ? args.directiveOwnerLabel ?? emitter : emitter);
      // Only explicitly shared/exact nodes are directive-wide singletons. A
      // unique citation/helper used by one proof remains owned by its emitter.
      if (!singletonNode) addedNodeSemanticOwners.set(id, emitter);
    }
  }
  const unitLabels = new Set(args.dispatch.map((unit) => unit.label));
  // Emission census: which unit emitted which bytes, per (category, target)
  // channel. Ownership exists to adjudicate COMPETING emissions deterministically;
  // a channel whose emitted payloads are byte-identical (usually a single emitter)
  // cannot depend on dispatch order, so quarantining it because the computed owner
  // stayed silent only converts finished work into a round abort — which is what
  // repeatedly killed the 2026-08-29/30 runs (stale durable owner labels, catalog
  // def:/sym: payloads owned by a silent coordinator, undispatched helper proofs).
  const emissionCensus = new Map<string, Map<string, Set<string>>>();
  const censusKey = (category: string, target: string): string => `${category}\u0000${target}`;
  const recordEmission = (category: string, target: string, unit: string, payload: unknown): void => {
    const key = censusKey(category, target);
    const byUnit = emissionCensus.get(key) ?? new Map<string, Set<string>>();
    emissionCensus.set(key, byUnit);
    const payloads = byUnit.get(unit) ?? new Set<string>();
    byUnit.set(unit, payloads);
    payloads.add(JSON.stringify(payload));
  };
  for (let i = 0; i < args.outputs.length; i += 1) {
    const unit = args.dispatch[i].label;
    const output = args.outputs[i];
    for (const proof of output.proofs) recordEmission("proof", proof.id, unit, proof);
    for (const replacement of output.resolved_oeqs) {
      recordEmission("oeq-resolution", replacement.source_id, unit, replacement);
    }
    for (const statement of output.added_lemmas) {
      recordEmission(
        statement.status === "cited" ? "cited-added-node" : "added-node",
        statement.id, unit, statement,
      );
    }
    for (const change of output.proposed_statement_changes) recordEmission("statement-change", change.id, unit, change);
    for (const change of output.proposed_definition_changes) recordEmission("definition-change", change.id, unit, change);
    for (const assumption of output.proposed_assumptions) recordEmission("assumption", assumption.id, unit, assumption);
    for (const edit of output.proposed_core_edits) {
      recordEmission("core-edit", coreEditTarget(edit), unit, coreEditConflictPayload(edit));
    }
    for (const obligation of output.open_obligations) recordEmission("open-obligation", obligation.node_id, unit, obligation);
    // Prose channels deliberately stay OUT of the census: a non-owner's prose that
    // slipped past projection would be dropped late under the noise reason
    // `unauthorized-prose-owner` (no checkpoint) or, in a directed round, turn a
    // stray note into a whole-round abort. Keeping it a projection quarantine
    // preserves the checkpoint; no-op notes are discharged before projection.
  }
  const identicalCensusPayload = (byUnit: ReadonlyMap<string, Set<string>>): boolean => {
    const payloads = new Set<string>();
    for (const set of byUnit.values()) for (const payload of set) payloads.add(payload);
    return payloads.size === 1;
  };
  const semanticOwnersFor = (capability: EmissionCapability): ReadonlyMap<string, string> =>
    capability.category === "proof"
      ? proofSemanticOwners
      : capability.category === "statement-note"
        ? noteSemanticOwners
      : capability.category === "added-node" || capability.category === "cited-added-node"
        ? addedNodeSemanticOwners
        : capability.durableCorrection === true
          ? correctionSemanticOwners
          : effectiveSemanticOwners;
  // A cleanup proposal emitted alongside an OEQ resolution belongs to the same
  // source-owned transaction. The answer theorem can already exist as a stale
  // projection (and therefore have a different semantic owner), but its paired
  // statement overlay must not be quarantined from the resolution that carries it.
  const resolutionStatementOwners = new Map<string, string>();
  for (let i = 0; i < args.outputs.length; i += 1) {
    for (const resolution of args.outputs[i].resolved_oeqs) {
      resolutionStatementOwners.set(resolution.theorem.id, args.dispatch[i].label);
    }
  }
  const localTargetOwner = (id: string): string | undefined =>
    effectiveSemanticOwners.get(id) ??
    args.dispatch.find((unit) => unit.targets.some((target) => target.id === id))?.label;
  const obligationOwners = (id: string): string[] =>
    [...new Set([
      localTargetOwner(id),
      // A coordinator may attest an exact directed residual because it owns the
      // round-wide transaction, but that authority does not extend to unrelated
      // nodes merely because the round happens to have a directive.
      required(id) ? args.directiveOwnerLabel ?? undefined : undefined,
    ].filter((owner): owner is string => owner !== undefined))].sort();
  /** Sole-emitter fallback: authorize a payload the computed owner never competed
   * for. It applies only when the owner cannot or does not speak for this channel —
   * the owner is null, a stale durable label no current unit carries, or a
   * coordinator-default (directive-wide singleton) owner with no semantic claim on
   * the target — and every emitted payload for the channel is byte-identical
   * (usually a single emitter). A LIVE dispatched semantic owner's silence stays a
   * veto: that unit is mid-work on the node, so a sibling cannot self-authorize
   * around it. Cited nodes keep the coordinator requirement — an external-literature
   * claim must carry the directive mantle, not just any emitter's say-so. */
  const soleEmitterAllowed = (unitLabel: string, capability: EmissionCapability, owner: string | null): boolean => {
    if (capability.category === "cited-added-node") return false;
    if (args.deniedCorrectionTargets?.has(capability.target)) return false;
    // A proof with NO computed owner at all has no ownership trail: the node was
    // never dispatched, is not exact-required, and joined no durable/postimage
    // closure this round (a rejected root postimage must not mint helper proof
    // authority). Such proof bytes stay quarantined; every observed round abort
    // involved a NON-null owner (a stale durable label or a silent coordinator
    // default), which the fallback below does cover.
    if (capability.category === "proof" && owner === null) return false;
    // A claim-CHANGING transaction on an EXISTING statement rewrites carried
    // mathematics; that channel keeps a strict ownership requirement (a live
    // dispatch owner, the durable record's owner via the verified correction
    // pair, or the required-target coordinator) — a sole emitter with no such
    // standing must not rewrite a shared helper merely because its recorded
    // owner label went stale (audit 2026-08-30, blocker 1). Proofs, added
    // nodes, and catalog payloads — the channels behind every observed round
    // abort — keep the fallback.
    if (capability.durableCorrection === true && args.existingStatementIds?.has(capability.target) === true) {
      return false;
    }
    const byUnit = emissionCensus.get(censusKey(capability.category, capability.target));
    if (byUnit === undefined || !byUnit.has(unitLabel)) return false;
    if (owner !== null && byUnit.has(owner)) return false;
    if (args.strictSharedOwner === true && owner !== null && unitLabels.has(owner)) return false;
    const semanticBacked = capability.semanticIds.some((id) => semanticOwnersFor(capability).has(id));
    if (owner !== null && semanticBacked && unitLabels.has(owner)) return false;
    return identicalCensusPayload(byUnit);
  };
  const obligationAllowed = (unit: string, id: string): boolean => {
    if (obligationOwners(id).includes(unit)) return true;
    // An obligation with NO eligible owner (undispatched, not exact-required) used
    // to be quarantined unconditionally, which converted an honest residual
    // attestation into an omission and could abort the round downstream. A sole,
    // uncontested attestation cannot depend on dispatch order — credit it.
    if (obligationOwners(id).length > 0) return false;
    const byUnit = emissionCensus.get(censusKey("open-obligation", id));
    if (byUnit === undefined || !byUnit.has(unit)) return false;
    return identicalCensusPayload(byUnit);
  };
  const capabilitiesFor = (output: SolveUnitOutput): EmissionCapability[] => [
    ...output.proofs.map((proof) => proofCap(proof.id)),
    ...output.resolved_oeqs.map((replacement) => resolutionCap(replacement.source_id, replacement.theorem.id)),
    ...output.added_lemmas.map(addedNodeCap),
    ...output.proposed_statement_changes.map((change) => statementChangeCap(change.id)),
    ...output.proposed_definition_changes.map((change) => definitionChangeCap(change.id)),
    ...output.proposed_assumptions.map((assumption) => assumptionCap(assumption.id)),
    ...output.proposed_core_edits.map(coreEditCap),
    ...(output.prose_updates ? [proseCap()] : []),
    ...(output.prose_updates?.statement_notes ?? []).map((note) => statementNoteCap(note.id)),
  ];
  for (let i = 0; i < args.outputs.length; i += 1) {
    const unit = args.dispatch[i];
    for (const capability of capabilitiesFor(args.outputs[i])) {
      const owner = capabilityOwner({
        capability,
        semanticTargetOwners: semanticOwnersFor(capability),
        directiveOwnerLabel: args.directiveOwnerLabel,
      });
      if (owner === unit.label || soleEmitterAllowed(unit.label, capability, owner)) {
        authorizedEmissions.add(capability.target);
      }
    }
    for (const obligation of args.outputs[i].open_obligations) {
      if (obligationAllowed(unit.label, obligation.node_id)) {
        authorizedEmissions.add(obligation.node_id);
      }
    }
  }

  const quarantined: QuarantinedCapabilityEmission[] = [];
  const projected = args.outputs.map((output, i): SolveUnitOutput => {
    const unit = args.dispatch[i];
    const allowed = (capability: EmissionCapability): boolean => {
      if (contestedDispatchTargets.has(capability.target)) {
        quarantined.push({
          unit: unit.label,
          owner: "(contested dispatch ownership)",
          category: capability.category,
          target: capability.target,
          ...(capability.operation !== undefined ? { operation: capability.operation } : {}),
        });
        return false;
      }
      if (args.deniedCorrectionTargets?.has(capability.target) &&
          (capability.category === "proof" || capability.category === "statement-change" ||
            (capability.category === "core-edit" && capability.durableCorrection === true))) {
        quarantined.push({
          unit: unit.label,
          owner: "(ambiguous correction transaction)",
          category: capability.category,
          target: capability.target,
          ...(capability.operation !== undefined ? { operation: capability.operation } : {}),
        });
        return false;
      }
      const owner = capabilityOwner({
        capability,
        semanticTargetOwners: semanticOwnersFor(capability),
        directiveOwnerLabel: args.directiveOwnerLabel,
      });
      if (owner === unit.label) return true;
      if (soleEmitterAllowed(unit.label, capability, owner)) {
        console.warn(
          `[D0-SOLVE] sole-emitter fallback accepted ${capability.category} for '${capability.target}' ` +
            `from unit '${unit.label}' (computed owner '${owner ?? "none"}' emitted nothing for it).`,
        );
        return true;
      }
      // An ownerless added node is genuinely new and belongs to its emitter. A
      // standalone proof is different: if its id was not dispatched and is not an
      // exact directed target, accepting it would let any unit overwrite unrelated
      // carried mathematics.
      if (owner === null &&
          capability.category !== "proof" &&
          !(
            args.existingStatementIds?.has(capability.target) &&
            (capability.category === "statement-change" ||
              (capability.category === "core-edit" && capability.durableCorrection === true))
          ) &&
          !(
            (capability.category === "added-node" || capability.category === "cited-added-node") &&
            args.existingStatementIds?.has(capability.target)
          )) return true;
      quarantined.push({
        unit: unit.label,
        owner: owner ?? "(no dispatched semantic owner)",
        category: capability.category,
        target: capability.target,
        ...(capability.operation !== undefined ? { operation: capability.operation } : {}),
      });
      return false;
    };
    const survivingResolutions = output.resolved_oeqs.filter((replacement) =>
      allowed(resolutionCap(replacement.source_id, replacement.theorem.id))
    );
    const survivingResolutionAnswerIds = new Set(
      survivingResolutions.map((replacement) => replacement.theorem.id),
    );
    const rawResolutionAnswerIds = new Set(
      output.resolved_oeqs.map((replacement) => replacement.theorem.id),
    );
    const resolutionLinkedStatementChangeAllowed = (change: { id: string }): boolean => {
      if (rawResolutionAnswerIds.has(change.id) && !survivingResolutionAnswerIds.has(change.id)) {
        quarantined.push({
          unit: unit.label,
          owner: "(rejected OEQ resolution transaction)",
          category: "statement-change",
          target: change.id,
        });
        return false;
      }
      return (resolutionStatementOwners.get(change.id) === unit.label && survivingResolutionAnswerIds.has(change.id)) ||
        allowed(statementChangeCap(change.id));
    };
    return {
      ...output,
      proofs: output.proofs.filter((proof) => allowed(proofCap(proof.id))),
      resolved_oeqs: survivingResolutions,
      added_lemmas: output.added_lemmas.filter((statement) =>
        allowed(addedNodeCap(statement))
      ),
      proposed_statement_changes: output.proposed_statement_changes.filter((change) =>
        resolutionLinkedStatementChangeAllowed(change)
      ),
      proposed_definition_changes: output.proposed_definition_changes.filter((change) =>
        allowed(definitionChangeCap(change.id))
      ),
      proposed_assumptions: output.proposed_assumptions.filter((assumption) =>
        allowed(assumptionCap(assumption.id))
      ),
      proposed_core_edits: output.proposed_core_edits.filter((edit) =>
        allowed(coreEditCap(edit))
      ),
      open_obligations: output.open_obligations.filter((obligation) => {
        if (contestedDispatchTargets.has(obligation.node_id)) {
          quarantined.push({
            unit: unit.label,
            owner: "(contested dispatch ownership)",
            category: "open-obligation",
            target: obligation.node_id,
          });
          return false;
        }
        if (obligationAllowed(unit.label, obligation.node_id)) return true;
        quarantined.push({
          unit: unit.label,
          owner: obligationOwners(obligation.node_id).join(" or ") || "(no eligible owner)",
          category: "open-obligation",
          target: obligation.node_id,
        });
        return false;
      }),
      prose_updates: output.prose_updates && allowed(proseCap())
        ? {
            ...output.prose_updates,
            statement_notes: output.prose_updates.statement_notes.filter((note) =>
              allowed(statementNoteCap(note.id))
            ),
          }
        : undefined,
    };
  });

  quarantined.sort((a, b) => {
    const ak = `${a.target}\u0000${a.unit}\u0000${a.category}`;
    const bk = `${b.target}\u0000${b.unit}\u0000${b.category}`;
    return ak < bk ? -1 : ak > bk ? 1 : 0;
  });
  for (const receipt of quarantined) {
    console.warn(
      `[D0-SOLVE] quarantined unauthorized ${receipt.category} for '${receipt.target}' from unit ` +
        `'${receipt.unit}' (capability owner: '${receipt.owner}').`,
    );
  }
  return { outputs: projected, quarantined };
}

/** Payload used to decide whether two emissions of the same core edit CONFLICT.
 *
 * `rebuild-reverse-dependencies` is a pure recomputation of `used_by` from the
 * graph: `kind`/`id`/`direction` are schema literals, so the operation carries NO
 * parameters and applying it twice equals applying it once. Its only free field is
 * `reason`, human-readable prose. Comparing whole objects therefore made two units
 * requesting the SAME no-op-if-repeated rebuild "conflict" whenever they worded
 * their rationale differently — which is what aborted a full D0 round on
 * stat_pn_weak_event_honest_inference (round 36, ~1.4h of solving discarded over a
 * prose mismatch). Ownership rules cannot fix this: even the authorized owner
 * collides with a stray sibling, and two identical rebuilds from anyone are
 * harmless. So compare the OPERATION, not the rationale.
 *
 * Deliberately narrow: every other edit kind carries a substantive payload whose
 * `reason` may signal genuinely different intent, and is still compared in full. */
export function coreEditConflictPayload(edit: RawCoreEdit): unknown {
  if (edit.kind === "rebuild-reverse-dependencies") {
    const { reason: _reason, ...operation } = edit as RawCoreEdit & { reason?: string };
    return operation;
  }
  return edit;
}

/** One id emitted with conflicting content by two independent solve units. */
export interface SolveEmissionConflict {
  category: string;
  id: string;
  /** Unit labels that emitted a payload for this id, in dispatch order. */
  units: string[];
}

/** Independent solve units may discover the same helper/edit. Identical repeats
 * are harmless, but silently taking the first conflicting payload makes the
 * assembled core depend on dispatch order.
 *
 * This used to THROW, which aborted the whole round and discarded every unit's
 * work — including units that had nothing to do with the collision. That is a
 * recurring, expensive failure: `rebuild-reverse-dependencies` cost ~1.4h of
 * solving over a prose mismatch (narrowed above), and
 * stat_cot_observational_efficiency later lost a round when two units minted the
 * SAME NEW lemma id (`lem:isonormal-hilbert-schmidt-calibration`) with different
 * statements and proofs, discarding three unrelated repairs with it.
 *
 * Ownership tables cannot prevent that class: they assign owners for ids that
 * ALREADY EXIST, and a helper invented mid-round by two units at once has no
 * owner to assign. So the collision is structural, not a compliance failure, and
 * the remedy has to bound the damage rather than detect one more shape.
 *
 * Report instead of throwing. The caller DROPS every conflicting variant — taking
 * neither, so the assembled core still cannot depend on dispatch order, which was
 * the original and correct concern — and surfaces the conflict for adjudication
 * while the rest of the round proceeds. A consumer left citing a dropped helper is
 * caught downstream by the existing undeclared-dependency check, which names it. */
export function collectConflictingSolveEmissions(
  outputs: SolveUnitOutput[],
  /** Unit labels, index-parallel with `outputs` (the dispatch array). */
  unitLabels: ReadonlyArray<string> = [],
): SolveEmissionConflict[] {
  // Per-id: what each unit emitted, and the running attribution. Tracking payloads PER
  // UNIT (not just the first one seen) is load-bearing for two reasons found by re-audit:
  //   * a unit repeating an IDENTICAL payload after another unit already conflicted was
  //     compared against the OTHER unit's payload, read as self-contradiction, and threw
  //     the whole round — a false fatal on harmless input;
  //   * a third emitter arriving after the conflict object was cloned never appeared in
  //     the diagnostic, so the report concealed one producer of the withheld content.
  const seen = new Map<string, Map<string, string>>();
  const order = new Map<string, string[]>();
  const conflicted = new Map<string, SolveEmissionConflict>();
  const record = (category: string, id: string, unit: string, value: unknown): void => {
    const key = `${category}:${id}`;
    const encoded = JSON.stringify(value);
    const byUnit = seen.get(key) ?? new Map<string, string>();
    seen.set(key, byUnit);
    const units = order.get(key) ?? [];
    order.set(key, units);
    units.push(unit);

    // INTRA-unit self-contradiction stays FATAL: a unit sees its own whole output, so two
    // DIFFERENT payloads under one id there is avoidable incoherence, and it casts doubt
    // on the rest of that unit's work. Compare against THIS unit's own earlier payload.
    const own = byUnit.get(unit);
    if (own !== undefined && own !== encoded) {
      throw new Error(`Stage 0-SOLVE emitted conflicting duplicate ${category} payloads for ${id}`);
    }
    byUnit.set(unit, encoded);

    // CROSS-unit: any other unit disagreeing makes this id contested. Recompute the
    // attribution every time so a late emitter is never omitted from the diagnostic.
    const distinct = new Set(byUnit.values());
    if (distinct.size > 1) conflicted.set(key, { category, id, units: [...units] });
    else conflicted.delete(key);
  };
  for (const [index, output] of outputs.entries()) {
    const unit = unitLabels[index] ?? `unit ${index}`;
    for (const proof of output.proofs) record("proof", proof.id, unit, proof);
    for (const statement of output.added_lemmas) record("statement", statement.id, unit, statement);
    for (const replacement of output.resolved_oeqs) {
      record("oeq-resolution", replacement.source_id, unit, replacement);
      record("statement", replacement.theorem.id, unit, replacement.theorem);
    }
    for (const change of output.proposed_statement_changes) record("statement-change", change.id, unit, change);
    for (const change of output.proposed_definition_changes) record("definition-change", change.id, unit, change);
    for (const assumption of output.proposed_assumptions) record("assumption", assumption.id, unit, assumption);
    for (const edit of output.proposed_core_edits) {
      record("core-edit", coreEditTarget(edit), unit, coreEditConflictPayload(edit));
    }
    for (const obligation of output.open_obligations) {
      record("open-obligation", obligation.node_id, unit, obligation);
    }
  }
  return [...conflicted.values()];
}

/** Remove every payload for a conflicted id, from every unit.
 *
 * Dropping ALL variants (rather than keeping one) is what preserves the
 * dispatch-order independence the original throw was protecting. */
export function dropConflictingSolveEmissions(
  outputs: SolveUnitOutput[],
  conflicts: SolveEmissionConflict[],
): SolveUnitOutput[] {
  if (conflicts.length === 0) return outputs;
  const dropped = new Set(conflicts.map((c) => `${c.category}:${c.id}`));
  const keep = (category: string, id: string): boolean => !dropped.has(`${category}:${id}`);
  return outputs.map((output) => ({
    ...output,
    proofs: output.proofs.filter((p) => keep("proof", p.id)),
    added_lemmas: output.added_lemmas.filter((s) => keep("statement", s.id)),
    resolved_oeqs: output.resolved_oeqs.filter(
      (r) => keep("oeq-resolution", r.source_id) && keep("statement", r.theorem.id),
    ),
    proposed_statement_changes: output.proposed_statement_changes.filter((c) => keep("statement-change", c.id)),
    proposed_definition_changes: output.proposed_definition_changes.filter((c) => keep("definition-change", c.id)),
    proposed_assumptions: output.proposed_assumptions.filter((a) => keep("assumption", a.id)),
    proposed_core_edits: output.proposed_core_edits.filter((e) => keep("core-edit", coreEditTarget(e))),
    open_obligations: output.open_obligations.filter((o) => keep("open-obligation", o.node_id)),
  }));
}

/** Human-readable diagnostic for the round's checkpoint message. */
export function formatSolveEmissionConflicts(conflicts: SolveEmissionConflict[]): string {
  return [
    `${conflicts.length} cross-unit id collision(s) — two solve units emitted DIFFERENT content under the ` +
      `same id. Every variant was withheld (taking either would make the core depend on dispatch order); ` +
      `the rest of the round was kept. Name one canonical owner in a directive and re-solve just these:`,
    ...conflicts.map((c) => `  [${c.category}] ${c.id} — emitted by ${c.units.join(", ")}`),
  ].join("\n");
}
