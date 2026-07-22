import type {
  AssumptionClass,
  FormalizationGraph,
  GraphEdge,
  GraphNode,
  NodeKind,
  ProofState,
  Provenance,
  ReviewStatus,
} from "./types.js";

function clone(g: FormalizationGraph): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => ({ ...n })), edges: g.edges.map((e) => ({ ...e })) };
}

export interface AddNodeInput {
  id: string;
  kind: NodeKind;
  provenance: Provenance;
  nl_statement: string;
  tex_anchor: string;
}

export function addNode(g: FormalizationGraph, input: AddNodeInput): FormalizationGraph {
  if (g.nodes.some((n) => n.id === input.id)) throw new Error(`duplicate node id: ${input.id}`);
  const node: GraphNode = {
    id: input.id,
    kind: input.kind,
    provenance: input.provenance,
    nl: { statement: input.nl_statement, tex_anchor: input.tex_anchor, frozen: input.provenance === "from-note" },
    lean: { decl_name: null, file: null },
    review: { status: "unreviewed", passed_hash: null },
    proof: { state: "sorry", sorry_count: 0 },
  };
  const out = clone(g);
  out.nodes.push(node);
  return out;
}

export function addEdge(g: FormalizationGraph, edge: GraphEdge): FormalizationGraph {
  const ids = new Set(g.nodes.map((n) => n.id));
  if (!ids.has(edge.from) || !ids.has(edge.to)) {
    throw new Error(`edge endpoint missing: ${edge.from} -> ${edge.to}`);
  }
  const dup = g.edges.some((e) => e.kind === edge.kind && e.from === edge.from && e.to === edge.to);
  if (dup) return g;
  const out = clone(g);
  out.edges.push({ ...edge });
  return out;
}

export interface AddAssumptionInput {
  /** the theorem/lemma the assumption attaches to */
  node: string;
  id: string;
  statement: string;
  tier: 1 | 2;
  classification: AssumptionClass;
  anchor: string;
  provenance: Provenance;
}

export function addAssumption(g: FormalizationGraph, input: AddAssumptionInput): FormalizationGraph {
  if (!g.nodes.some((n) => n.id === input.node)) throw new Error(`parent node missing: ${input.node}`);
  let out = addNode(g, {
    id: input.id,
    kind: "assumption",
    provenance: input.provenance,
    nl_statement: input.statement,
    tex_anchor: input.anchor,
  });
  out = {
    ...out,
    nodes: out.nodes.map((n) =>
      n.id === input.id ? { ...n, assumption: { tier: input.tier, classification: input.classification } } : n,
    ),
  };
  out = addEdge(out, { kind: "proof-uses", from: input.node, to: input.id, source: "declared" });
  return out;
}

function updateNode(g: FormalizationGraph, id: string, fn: (n: GraphNode) => GraphNode): FormalizationGraph {
  if (!g.nodes.some((n) => n.id === id)) throw new Error(`node not found: ${id}`);
  return {
    ...g,
    nodes: g.nodes.map((n) => (n.id === id ? fn({ ...n }) : { ...n })),
    edges: g.edges.map((e) => ({ ...e })),
  };
}

export function setLean(g: FormalizationGraph, id: string, declName: string, file: string): FormalizationGraph {
  return updateNode(g, id, (n) => ({ ...n, lean: { decl_name: declName, file } }));
}

export function setProof(g: FormalizationGraph, id: string, state: ProofState, sorryCount: number): FormalizationGraph {
  return updateNode(g, id, (n) => ({ ...n, proof: { state, sorry_count: sorryCount } }));
}

/** Set a node's review verdict + the statement hash it was reviewed at. */
export function setNodeReview(
  g: FormalizationGraph,
  id: string,
  status: ReviewStatus,
  hash: string,
  note?: string,
): FormalizationGraph {
  return updateNode(g, id, (n) => ({
    ...n,
    review: { status, passed_hash: hash, ...(note ? { note } : {}) },
  }));
}

/** Convenience: record a faithful match. */
export function markPassed(g: FormalizationGraph, id: string, hash: string): FormalizationGraph {
  return setNodeReview(g, id, "matched", hash);
}

/** Flip a node back to unreviewed (e.g. its statement changed or it gained an
 *  assumption), clearing the prior reviewed-at hash so the dirty frontier picks it up. */
export function markUnreviewed(g: FormalizationGraph, id: string): FormalizationGraph {
  return updateNode(g, id, (n) => ({ ...n, review: { status: "unreviewed", passed_hash: null } }));
}
