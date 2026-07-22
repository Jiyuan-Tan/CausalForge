import { findHiddenStatementDefs } from "../formalization/crosswalk.js";
import { parseAnnotatedDecls } from "./extractor.js";
import { addNode } from "./mutate.js";
import type { FormalizationGraph, NodeKind } from "./types.js";

/**
 * Mint an `agent-introduced` definition node for every build-inline def reached
 * from a theorem statement that is not already a node — the graph-native version
 * of F4's `findHiddenStatementDefs` AUX surface. Idempotent: a def already linked
 * to some node (by decl_name) is skipped. Node id = `aux_<declName>`.
 */
export async function mintHiddenDefNodes(graph: FormalizationGraph, leanDir: string): Promise<FormalizationGraph> {
  const hidden = await findHiddenStatementDefs(leanDir);
  const linked = new Set(graph.nodes.map((n) => n.lean.decl_name).filter(Boolean) as string[]);
  let g = graph;
  for (const h of hidden) {
    if (linked.has(h.name)) continue;
    const id = `aux_${h.name}`;
    if (g.nodes.some((n) => n.id === id)) continue;
    g = addNode(g, {
      id,
      kind: "definition",
      provenance: "agent-introduced",
      nl_statement: `(hidden def ${h.name}, flavor ${h.flavor})`,
      tex_anchor: "",
    });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, lean: { decl_name: h.name, file: h.file } } : n)) };
    linked.add(h.name);
  }
  return g;
}

/** Lean keyword → graph node kind for an agent-introduced annotated decl. */
function kindOfDecl(declKind: string): NodeKind {
  return declKind === "theorem" || declKind === "lemma" ? "lemma" : "definition";
}

/**
 * Mint an `agent-introduced` node for every `-- @node:<id>`-annotated declaration whose
 * id is not already in the graph. This is how a proof-filler registers a NEW helper lemma
 * it introduced (a decomposed sub-goal, a reusable substrate fact): it tags the decl, and
 * this step turns the tag into a reviewable node (proof helpers are `lemma`, build-inline
 * objects are `definition`). Unlike `mintHiddenDefNodes` (statement-reachable defs only),
 * this also captures lemmas reached purely through PROOFS, which would otherwise stay
 * invisible to node-level review. Idempotent; never relabels a node as `from-note`.
 */
export async function mintAnnotatedNodes(graph: FormalizationGraph, leanDir: string): Promise<FormalizationGraph> {
  const decls = await parseAnnotatedDecls(leanDir);
  let g = graph;
  for (const d of decls) {
    if (g.nodes.some((n) => n.id === d.nodeId)) continue;
    g = addNode(g, {
      id: d.nodeId,
      kind: kindOfDecl(d.declKind),
      provenance: "agent-introduced",
      nl_statement: `(agent-introduced ${d.declKind} ${d.declName})`,
      tex_anchor: "",
    });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === d.nodeId ? { ...n, lean: { decl_name: d.declName, file: d.file } } : n)) };
  }
  return g;
}
