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
//   3. DIRECTIVE OWNER one unit is elected canonical writer for cross-cutting payloads
//                     (comparators, definitions, assumptions, catalog/metadata edits)
//
// Everything is decided from unit CONTENT, never array order, so Promise scheduling
// cannot change who owns what.

import type { CoreStatement } from "../core/schema.js";
import { coreEditTarget, type RawCoreEdit } from "../stages/d0_apply.js";
import type { SolveUnitOutput } from "./schemas.js";

export type SolveDispatchUnit = { targets: CoreStatement[]; label: string; priorContext: string };

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
      throw new Error(
        `Stage 0-SOLVE ambiguous semantic ownership for ${id}: ${labels.join(", ")}`,
      );
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
}

export interface EmissionCapability {
  category: string;
  target: string;
  semanticIds: string[];
  /** Singleton emissions belong to the directive-wide owner when no dispatched
   * statement id supplies a narrower semantic owner. */
  singleton: boolean;
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
  directiveOwnerLabel: string | null;
  requiredCoreTargets: ReadonlySet<string>;
}): { outputs: SolveUnitOutput[]; quarantined: QuarantinedCapabilityEmission[] } {
  const required = (target: string): boolean => args.requiredCoreTargets.has(target);
  const proofCap = (id: string): EmissionCapability => ({
    category: "proof", target: id, semanticIds: [id], singleton: required(id),
  });
  const resolutionCap = (sourceId: string, theoremId: string): EmissionCapability => ({
    category: "oeq-resolution", target: sourceId, semanticIds: [sourceId, theoremId], singleton: true,
  });
  const addedNodeCap = (statement: CoreStatement): EmissionCapability => ({
    category: statement.status === "cited" ? "cited-added-node" : "added-node",
    target: statement.id,
    semanticIds: [statement.id],
    singleton: statement.status === "cited" || required(statement.id),
  });
  const statementChangeCap = (id: string): EmissionCapability => ({
    category: "statement-change", target: id, semanticIds: [id], singleton: required(id),
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
      semanticIds: [target],
      singleton: isCatalogCoreEdit(edit) || required(target),
    };
  };
  const obligationCap = (id: string): EmissionCapability => ({
    category: "open-obligation", target: id, semanticIds: [id], singleton: false,
  });
  const proseCap = (): EmissionCapability => ({
    category: "prose-updates", target: "prose:paper-wide", semanticIds: [], singleton: true,
  });

  const authorizedEmissions = new Set<string>();
  const capabilitiesFor = (output: SolveUnitOutput): EmissionCapability[] => [
    ...output.proofs.map((proof) => proofCap(proof.id)),
    ...output.resolved_oeqs.map((replacement) => resolutionCap(replacement.source_id, replacement.theorem.id)),
    ...output.added_lemmas.map(addedNodeCap),
    ...output.proposed_statement_changes.map((change) => statementChangeCap(change.id)),
    ...output.proposed_definition_changes.map((change) => definitionChangeCap(change.id)),
    ...output.proposed_assumptions.map((assumption) => assumptionCap(assumption.id)),
    ...output.proposed_core_edits.map(coreEditCap),
    ...(output.prose_updates ? [proseCap()] : []),
  ];
  for (let i = 0; i < args.outputs.length; i += 1) {
    const unit = args.dispatch[i];
    for (const capability of capabilitiesFor(args.outputs[i])) {
      const owner = capabilityOwner({
        capability,
        semanticTargetOwners: args.semanticTargetOwners,
        directiveOwnerLabel: args.directiveOwnerLabel,
      });
      if (owner === unit.label) authorizedEmissions.add(capability.target);
    }
  }

  const quarantined: QuarantinedCapabilityEmission[] = [];
  const projected = args.outputs.map((output, i): SolveUnitOutput => {
    const unit = args.dispatch[i];
    const allowed = (capability: EmissionCapability): boolean => {
      const owner = capabilityOwner({
        capability,
        semanticTargetOwners: args.semanticTargetOwners,
        directiveOwnerLabel: args.directiveOwnerLabel,
      });
      if (owner === null || owner === unit.label) return true;
      quarantined.push({ unit: unit.label, owner, category: capability.category, target: capability.target });
      return false;
    };
    return {
      ...output,
      proofs: output.proofs.filter((proof) => allowed(proofCap(proof.id))),
      resolved_oeqs: output.resolved_oeqs.filter((replacement) =>
        allowed(resolutionCap(replacement.source_id, replacement.theorem.id))
      ),
      added_lemmas: output.added_lemmas.filter((statement) =>
        allowed(addedNodeCap(statement))
      ),
      proposed_statement_changes: output.proposed_statement_changes.filter((change) =>
        allowed(statementChangeCap(change.id))
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
      open_obligations: output.open_obligations.filter((obligation) =>
        allowed(obligationCap(obligation.node_id))
      ),
      prose_updates: output.prose_updates && allowed(proseCap()) ? output.prose_updates : undefined,
    };
  });

  quarantined.sort((a, b) => {
    const ak = `${a.target}\u0000${a.unit}\u0000${a.category}`;
    const bk = `${b.target}\u0000${b.unit}\u0000${b.category}`;
    return ak < bk ? -1 : ak > bk ? 1 : 0;
  });
  for (const receipt of quarantined) {
    if (args.requiredCoreTargets.has(receipt.target) && !authorizedEmissions.has(receipt.target)) {
      throw new Error(
        `Stage 0-SOLVE exact target ${receipt.target} had unauthorized-only ${receipt.category} emission ` +
          `from ${receipt.unit}; capability owner ${receipt.owner} emitted no authorized payload`,
      );
    }
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
