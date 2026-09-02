import type { Core } from "../discovery/core/schema.js";
import { objIdToNodeId } from "../graph/from_note.js";
import type { Plan } from "./plan/schema.js";
import { formalizationCoreContextValue } from "./core_context.js";

export const F2_REVISION_TARGETS_HEADER =
  "Declarations to edit (one obj_id per line, verbatim):";

/** Recover only the exact target block written by the proof-review dispatcher. */
export function revisionTargetsFromRedirect(redirect: string | null | undefined): string[] {
  if (!redirect) return [];
  const lines = redirect.split(/\r?\n/);
  const start = lines.lastIndexOf(F2_REVISION_TARGETS_HEADER);
  if (start < 0) return [];
  const targets: string[] = [];
  for (const line of lines.slice(start + 1)) {
    if (!line.startsWith("- ")) break;
    const target = line.slice(2).trim();
    if (target) targets.push(target);
  }
  return [...new Set(targets)];
}

export interface F2RevisionContext {
  requested_targets: string[];
  resolved_targets: string[];
  plan: Record<string, unknown>;
  core: Record<string, unknown>;
  omitted_counts: {
    plan_nodes: number;
    env_entries: number;
    symbols: number;
    assumptions: number;
    definitions: number;
    statements: number;
    citations: number;
  };
}

export function hasCompleteScaffoldCoverage(
  plan: Plan,
  tags: { nodes: Set<string>; envs: Set<string> },
): boolean {
  const deliveredNodes = Object.entries(plan.nodes)
    .filter(([, node]) => node.delivery_status !== "undelivered")
    .map(([id]) => id);
  const undeliveredNodes = Object.entries(plan.nodes)
    .filter(([, node]) => node.delivery_status === "undelivered")
    .map(([id]) => id);
  return deliveredNodes.every((id) => tags.nodes.has(id))
    && undeliveredNodes.every((id) => !tags.nodes.has(id))
    && plan.env.every((env) => tags.envs.has(env.id));
}

type CoreNode = Core["assumptions"][number] | Core["definitions"][number] | Core["statements"][number];

function envTarget(target: string, envIds: Set<string>): string | null {
  if (envIds.has(target)) return target;
  const compact = target.replace(/-/g, "").toUpperCase();
  return envIds.has(compact) ? compact : null;
}

function nodeRefs(id: string, node: CoreNode, plan: Plan): string[] {
  const refs = new Set<string>();
  if ("depends_on" in node) for (const dep of node.depends_on) refs.add(dep);
  if ("by_member_properties" in node) {
    for (const dep of node.by_member_properties ?? []) refs.add(dep);
    for (const input of node.inputs ?? []) refs.add(input);
  }
  const entry = plan.nodes[id];
  for (const dep of entry?.members ?? []) refs.add(dep);
  for (const dep of entry?.hyps ?? []) refs.add(dep);
  return [...refs];
}

/**
 * Build the smallest deterministic F2 revise packet that still contains:
 * the changed target, its prerequisites, and declarations forced downstream by
 * changing that target. An unknown target returns null so callers retain the
 * old full-context prompt.
 */
export function buildF2RevisionContext(
  core: Core,
  plan: Plan,
  requestedTargets: string[],
): F2RevisionContext | null {
  const requested = [...new Set(requestedTargets.map((t) => t.trim()).filter(Boolean))];
  if (requested.length === 0) return null;

  const assumptions = new Map(core.assumptions.map((node) => [node.id, node] as const));
  const definitions = new Map(core.definitions.map((node) => [node.id, node] as const));
  const statements = new Map(core.statements.map((node) => [node.id, node] as const));
  const coreNodes = new Map<string, CoreNode>([
    ...assumptions,
    ...definitions,
    ...statements,
  ]);
  const envIds = new Set(plan.env.map((entry) => entry.id));
  const symbolNames = new Set(core.symbols.map((symbol) => symbol.name));
  const leanNameToId = new Map(
    Object.entries(plan.nodes).map(([id, entry]) => [entry.lean_name, id] as const),
  );

  const changedNodes = new Set<string>();
  const changedSymbols = new Set<string>();
  const selectedEnvs = new Set<string>();
  const selectedSymbols = new Set<string>();
  const resolvedTargets: string[] = [];
  for (const target of requested) {
    if (target.startsWith("sym:") && symbolNames.has(target.slice(4))) {
      changedSymbols.add(target.slice(4));
      resolvedTargets.push(target);
      continue;
    }
    const env = envTarget(target, envIds);
    if (env) {
      selectedEnvs.add(env);
      resolvedTargets.push(env);
      continue;
    }
    const normalized = objIdToNodeId(target);
    const nodeId = coreNodes.has(target)
      ? target
      : coreNodes.has(normalized)
        ? normalized
        : leanNameToId.get(target);
    if (!nodeId || !coreNodes.has(nodeId)) return null;
    changedNodes.add(nodeId);
    resolvedTargets.push(nodeId);
  }

  // A shared symbol/environment change starts at every declaration that realizes
  // or directly uses it; those declarations are the actual forced edit frontier.
  for (const env of plan.env) {
    if (selectedEnvs.has(env.id)) {
      for (const symbol of env.binds_symbols) changedSymbols.add(symbol);
    }
  }
  // If x changes, every symbol whose definition references x changes as well.
  // Then retain the prerequisite symbols referenced by that changed closure.
  let grew = true;
  while (grew) {
    grew = false;
    for (const symbol of core.symbols) {
      if (changedSymbols.has(symbol.name)) continue;
      if ((symbol.refs ?? []).some((ref) => changedSymbols.has(ref))) {
        changedSymbols.add(symbol.name);
        grew = true;
      }
    }
  }
  for (const symbol of changedSymbols) selectedSymbols.add(symbol);
  grew = true;
  while (grew) {
    grew = false;
    for (const symbol of core.symbols) {
      if (!selectedSymbols.has(symbol.name)) continue;
      for (const ref of symbol.refs ?? []) {
        if (!selectedSymbols.has(ref)) {
          selectedSymbols.add(ref);
          grew = true;
        }
      }
    }
  }
  for (const env of plan.env) {
    if (env.binds_symbols.some((symbol) => changedSymbols.has(symbol))) selectedEnvs.add(env.id);
  }
  if (changedSymbols.size > 0) {
    // The schema deliberately defines an absent declaration as “may use any
    // symbol.” Guessing from prose would be unstable, so legacy/underspecified
    // symbol edits keep the old full-context path.
    if ([...coreNodes.values()].some((node) => !("free_symbols" in node) || node.free_symbols === undefined)) {
      return null;
    }
    for (const [id, node] of coreNodes) {
      if (node.free_symbols?.some((symbol) => changedSymbols.has(symbol))) changedNodes.add(id);
    }
    for (const symbol of core.symbols) {
      if (changedSymbols.has(symbol.name) && symbol.ref && coreNodes.has(symbol.ref)) {
        changedNodes.add(symbol.ref);
      }
    }
  }

  const upstream = new Map<string, Set<string>>();
  const downstream = new Map<string, Set<string>>();
  for (const [id, node] of coreNodes) {
    const deps = new Set(nodeRefs(id, node, plan).filter((dep) => coreNodes.has(dep)));
    upstream.set(id, deps);
    for (const dep of deps) {
      const consumers = downstream.get(dep) ?? new Set<string>();
      consumers.add(id);
      downstream.set(dep, consumers);
    }
  }

  const selectedNodes = new Set(changedNodes);
  const addClosure = (seeds: Iterable<string>, edges: Map<string, Set<string>>) => {
    const queue = [...seeds];
    while (queue.length > 0) {
      const id = queue.shift()!;
      for (const next of edges.get(id) ?? []) {
        if (selectedNodes.has(next)) continue;
        selectedNodes.add(next);
        queue.push(next);
      }
    }
  };
  // Only changes propagate downstream. Prerequisites added for context do not
  // pull in their unrelated sibling consumers.
  addClosure(changedNodes, downstream);
  addClosure(selectedNodes, upstream);

  for (const id of selectedNodes) {
    const node = coreNodes.get(id)!;
    const declared = "free_symbols" in node ? node.free_symbols : undefined;
    if (declared) for (const symbol of declared) selectedSymbols.add(symbol);
    else {
      // Same schema contract: a missing declaration may use any symbol. This
      // broadens only the small symbol/env context, not the edit-node frontier.
      for (const symbol of symbolNames) selectedSymbols.add(symbol);
    }
  }
  // A node edit still needs the ambient sampling-world declaration to typecheck.
  // Add that environment as context, but do not treat all of its symbols as
  // changed targets (which would incorrectly expand the edit frontier globally).
  if (changedNodes.size > 0) {
    for (const env of plan.env) {
      if (!env.binds_sampling_model) continue;
      selectedEnvs.add(env.id);
      for (const symbol of env.binds_symbols) selectedSymbols.add(symbol);
    }
  }
  // Symbol definitions may reference other symbols; retain that small closure.
  grew = true;
  while (grew) {
    grew = false;
    for (const symbol of core.symbols) {
      if (!selectedSymbols.has(symbol.name)) continue;
      for (const ref of symbol.refs ?? []) {
        if (!selectedSymbols.has(ref)) {
          selectedSymbols.add(ref);
          grew = true;
        }
      }
    }
  }
  // A symbol may name the core definition that realizes it (`ref`). For an
  // ordinary theorem target this is prerequisite context, not a changed target:
  // include it and its own prerequisites without pulling its sibling consumers.
  grew = true;
  while (grew) {
    const beforeNodes = selectedNodes.size;
    const beforeSymbols = selectedSymbols.size;
    for (const symbol of core.symbols) {
      if (selectedSymbols.has(symbol.name) && symbol.ref && coreNodes.has(symbol.ref)) {
        selectedNodes.add(symbol.ref);
      }
    }
    addClosure(selectedNodes, upstream);
    for (const id of selectedNodes) {
      const node = coreNodes.get(id)!;
      if (node.free_symbols) {
        for (const symbol of node.free_symbols) selectedSymbols.add(symbol);
      } else {
        for (const symbol of symbolNames) selectedSymbols.add(symbol);
      }
    }
    for (const symbol of core.symbols) {
      if (!selectedSymbols.has(symbol.name)) continue;
      for (const ref of symbol.refs ?? []) selectedSymbols.add(ref);
    }
    grew = selectedNodes.size !== beforeNodes || selectedSymbols.size !== beforeSymbols;
  }
  for (const env of plan.env) {
    if (env.binds_symbols.some((symbol) => selectedSymbols.has(symbol))) selectedEnvs.add(env.id);
  }

  const selectedPlanNodes = Object.fromEntries(
    Object.entries(plan.nodes).filter(([id]) => selectedNodes.has(id)),
  );
  const citedIds = new Set(
    Object.values(selectedPlanNodes).map((entry) => entry.source).filter((id): id is string => !!id),
  );
  const coreView = formalizationCoreContextValue(core);
  const selectedAssumptions = core.assumptions.filter((node) => selectedNodes.has(node.id));
  const selectedDefinitions = core.definitions.filter((node) => selectedNodes.has(node.id));
  const selectedStatements = (coreView.statements as Array<{ id: string }>).filter(
    (node) => selectedNodes.has(node.id),
  );
  const selectedCore: Record<string, unknown> = {
    qid: core.qid,
    ...(core.specialization ? { specialization: core.specialization } : {}),
    ...(core.cluster ? { cluster: core.cluster } : {}),
    symbols: core.symbols.filter((symbol) => selectedSymbols.has(symbol.name)),
    assumptions: selectedAssumptions,
    definitions: selectedDefinitions,
    statements: selectedStatements,
    ...(core.sampling_model ? { sampling_model: core.sampling_model } : {}),
    ...(core.estimand_functional ? { estimand_functional: core.estimand_functional } : {}),
    target_estimand: core.target_estimand,
  };
  const selectedPlan: Record<string, unknown> = {
    qid: plan.qid,
    ...(plan.specialization ? { specialization: plan.specialization } : {}),
    ...(plan.cluster ? { cluster: plan.cluster } : {}),
    ...(plan.lean_subdir ? { lean_subdir: plan.lean_subdir } : {}),
    env: plan.env.filter((entry) => selectedEnvs.has(entry.id)),
    nodes: selectedPlanNodes,
    citations: plan.citations.filter((citation) => citedIds.has(citation.id)),
    ...(plan.feasibility ? { feasibility: plan.feasibility } : {}),
  };

  return {
    requested_targets: requested,
    resolved_targets: [...new Set(resolvedTargets)],
    plan: selectedPlan,
    core: selectedCore,
    omitted_counts: {
      plan_nodes: Object.keys(plan.nodes).length - Object.keys(selectedPlanNodes).length,
      env_entries: plan.env.length - selectedEnvs.size,
      symbols: core.symbols.length - selectedSymbols.size,
      assumptions: core.assumptions.length - selectedAssumptions.length,
      definitions: core.definitions.length - selectedDefinitions.length,
      statements: core.statements.length - selectedStatements.length,
      citations: plan.citations.length - (selectedPlan.citations as unknown[]).length,
    },
  };
}
