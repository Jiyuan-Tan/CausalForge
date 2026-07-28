import type { FormalizationGraph, GraphEdge, GraphNode } from "./types.js";
import { markUnreviewed } from "./mutate.js";

function nodeSourceShape(node: GraphNode): unknown {
  return {
    obj_id: node.obj_id,
    kind: node.kind,
    provenance: node.provenance,
    // frozen_body/frozen_title are later review/presentation enrichment. F1 owns
    // the canonical statement and anchor, not those receipts.
    nl: { statement: node.nl.statement, tex_anchor: node.nl.tex_anchor },
    delivery: node.delivery,
    assumption: node.assumption,
    standard: node.standard,
    gate: node.gate,
    setup: node.setup,
    // A null-file Lean link is an F1 reuse decision and therefore belongs to the
    // plan-derived shape. Production links (file != null) are F2/F3 state.
    reuse: node.lean.file === null ? node.lean.decl_name : null,
  };
}

function sameSourceShape(a: GraphNode, b: GraphNode): boolean {
  return JSON.stringify(nodeSourceShape(a)) === JSON.stringify(nodeSourceShape(b));
}

function edgeKey(edge: GraphEdge): string {
  return `${edge.kind}:${edge.from}->${edge.to}:${edge.source}`;
}

/**
 * Merge a freshly derived core+plan graph into a graph that later F stages have
 * already enriched.
 *
 * F1 owns the from-note/core structure, but it does not own Lean links, proof
 * state, reviewer receipts, extracted edges, or agent-introduced nodes. A revise
 * pass therefore replaces only the structural layer and invalidates review state
 * for structurally changed nodes plus their consumers. It must never reseed the
 * entire graph and silently turn every reviewed node back into `unreviewed`.
 */
export function mergeStage1RevisionGraph(
  previous: FormalizationGraph,
  rebuilt: FormalizationGraph,
): FormalizationGraph {
  const oldById = new Map(previous.nodes.map((node) => [node.id, node] as const));
  const rebuiltIds = new Set(rebuilt.nodes.map((node) => node.id));
  const changed = new Set<string>();

  const structuralNodes = rebuilt.nodes.map((fresh) => {
    const old = oldById.get(fresh.id);
    if (!old) {
      changed.add(fresh.id);
      return fresh;
    }
    const sourceUnchanged = sameSourceShape(old, fresh);
    if (!sourceUnchanged) changed.add(fresh.id);

    const freshSelectsReuse = fresh.lean.decl_name !== null && fresh.lean.file === null;
    const oldHasProductionLink = old.lean.file !== null;
    return {
      ...fresh,
      nl: sourceUnchanged ? old.nl : fresh.nl,
      // F1 cannot alter production Lean or its proof body. Preserve that state
      // even when the plan statement changed; the review is invalidated below.
      lean: freshSelectsReuse
        ? fresh.lean
        : oldHasProductionLink
          ? old.lean
          : fresh.lean,
      proof: old.proof,
      review: old.review,
    };
  });

  // F2/F3 may introduce auxiliary nodes that are intentionally absent from the
  // typed core. Preserve them. A removed from-note node, by contrast, reflects a
  // real core/plan deletion and must not survive the structural refresh.
  const retainedExtras = previous.nodes.filter(
    (node) => !rebuiltIds.has(node.id) && node.provenance !== "from-note",
  );
  const nodes = [...structuralNodes, ...retainedExtras];
  const retainedIds = new Set(nodes.map((node) => node.id));

  const freshStructuralEdges = rebuilt.edges;
  const freshEdgeKeys = new Set(freshStructuralEdges.map(edgeKey));
  const oldCoreDeclaredEdges = previous.edges.filter(
    (edge) =>
      edge.source === "declared" && rebuiltIds.has(edge.from) && rebuiltIds.has(edge.to),
  );
  const oldCoreEdgeKeys = new Set(oldCoreDeclaredEdges.map(edgeKey));
  for (const edge of freshStructuralEdges) {
    if (!oldCoreEdgeKeys.has(edgeKey(edge))) changed.add(edge.from);
  }
  for (const edge of oldCoreDeclaredEdges) {
    if (!freshEdgeKeys.has(edgeKey(edge))) changed.add(edge.from);
  }

  const preservedEdges = previous.edges.filter((edge) => {
    if (!retainedIds.has(edge.from) || !retainedIds.has(edge.to)) return false;
    if (edge.source === "extracted") return true;
    // Preserve declared edges involving an auxiliary node. Declared core/plan
    // edges are authoritative in the rebuilt structural layer.
    return !rebuiltIds.has(edge.from) || !rebuiltIds.has(edge.to);
  });
  const edges = [...freshStructuralEdges];
  const seenEdges = new Set(edges.map(edgeKey));
  for (const edge of preservedEdges) {
    if (!seenEdges.has(edgeKey(edge))) {
      edges.push(edge);
      seenEdges.add(edgeKey(edge));
    }
  }

  // Graph dependency edges point consumer -> dependency. Invalidate the changed
  // node and every transitive consumer. setup-of is oriented setup -> theorem, so
  // it needs the corresponding special case.
  const consumers = new Map<string, Set<string>>();
  const addConsumer = (dependency: string, consumer: string) => {
    const set = consumers.get(dependency) ?? new Set<string>();
    set.add(consumer);
    consumers.set(dependency, set);
  };
  for (const edge of edges) {
    if (edge.kind === "setup-of") addConsumer(edge.from, edge.to);
    else addConsumer(edge.to, edge.from);
  }
  const dirty = new Set(changed);
  const queue = [...changed];
  while (queue.length > 0) {
    const id = queue.shift()!;
    for (const consumer of consumers.get(id) ?? []) {
      if (dirty.has(consumer)) continue;
      dirty.add(consumer);
      queue.push(consumer);
    }
  }

  let merged: FormalizationGraph = {
    ...rebuilt,
    nodes,
    edges,
    symbolReview: previous.symbolReview,
  };
  for (const id of dirty) {
    if (merged.nodes.some((node) => node.id === id)) merged = markUnreviewed(merged, id);
  }
  return merged;
}
