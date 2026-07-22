import type { FormalizationGraph, GraphNode } from "../graph/types.js";
import type { ComponentSpec } from "./components.js";

/**
 * The Lean component set of a paper object, read from the GRAPH (no codex): the node's own
 * `lean.decl_name` plus the decls of its `statement-uses` neighbours that are themselves
 * formalized. This is how a node "with multiple lines of Lean code" enumerates all its pieces
 * deterministically from the verified graph instead of by codex discovery.
 *
 * Returns `[]` when the obj_id is unknown or the node carries no Lean decl — the caller then
 * falls back to codex component discovery, so no Lean piece is ever silently dropped.
 */
export function graphComponentSpecs(graph: FormalizationGraph, objId: string): ComponentSpec[] {
  const byKey = new Map<string, GraphNode>();
  for (const n of graph.nodes) {
    byKey.set(n.id, n);
    if (n.obj_id) byKey.set(n.obj_id, n);
  }
  const node = byKey.get(objId);
  if (!node?.lean?.decl_name) return [];
  const specs: ComponentSpec[] = [{ type: "decl", decl: node.lean.decl_name }];
  const seen = new Set([node.lean.decl_name]);
  for (const e of graph.edges) {
    if (e.kind !== "statement-uses" || e.from !== node.id) continue;
    const nbr = byKey.get(e.to);
    const decl = nbr?.lean?.decl_name;
    if (decl && !seen.has(decl)) {
      seen.add(decl);
      specs.push({ type: "decl", decl });
    }
  }
  return specs;
}
