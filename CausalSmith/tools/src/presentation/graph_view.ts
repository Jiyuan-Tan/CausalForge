// The single seam between the formalization graph and causalsmith. Imports ONLY
// graph/types.ts (schema) + graph/store.ts (read-only IO) — never the graph
// engine (cli/mutate/skeleton/from_note), so an in-flight causalsmith edit can never
// crash a paper run. See doc/presentation/2026-06-17-causalsmith-graph-simplification-design.md.
import { loadGraph, graphPath } from "../graph/store.js";
import { isUndeliveredNode, type FormalizationGraph, type GraphNode, type NodeKind } from "../graph/types.js";

export type { FormalizationGraph, GraphNode } from "../graph/types.js";
export type EnvName = "theoremv" | "assumptionv" | "lemmav" | "definitionv" | "citedv" | "propositionv" | "remarkv";

/** The subset of env kinds an outline `env_overrides:` line may re-kind an object to:
 *  a constructive definition/assumption swap, a proposition tier, or a (non-load-bearing)
 *  remark. Theorems/lemmas/cited results are never override targets. */
export const OVERRIDE_ENVS = ["definitionv", "assumptionv", "propositionv", "remarkv"] as const;
export type OverrideEnv = (typeof OVERRIDE_ENVS)[number];

const ENV_BY_KIND: Partial<Record<NodeKind, EnvName>> = {
  theorem: "theoremv",
  lemma: "lemmav",
  assumption: "assumptionv",
  definition: "definitionv",
};

/** The env for a node kind, or null for kinds that are not paper envs (setup, gate).
 *  Kind-only — a `gate` node's env depends on its `gate_class`, so render/block code
 *  must use `envForNode`; this stays for the kind→env callers that have no node. */
export function envForKind(kind: NodeKind): EnvName | null {
  return ENV_BY_KIND[kind] ?? null;
}

/** A CITED node: a `gate` whose class is `cited` — an imported external theorem the
 *  paper relies on but does not prove (matched against a citation at F2.5). Guards on
 *  `gate_class`, NOT bare `kind`, so a stray `gated` gate (discharged before banking)
 *  is still excluded from the paper. */
export function isCitedNode(n: GraphNode): boolean {
  return n.kind === "gate" && n.gate?.gate_class === "cited";
}

/** The paper env for a node. Cited gates are deliberately NOT paper environments:
 *  they remain machine-visible external dependencies, but their consumers carry a
 *  theorem-local verification-scope footnote instead of presenting the borrowed
 *  theorem as an assumption/result of this paper. */
export function envForNode(n: GraphNode): EnvName | null {
  return isUndeliveredNode(n) ? "remarkv" : isCitedNode(n) ? null : envForKind(n.kind);
}

/** Frozen (from-note) nodes that render as a formal env. Cited imported results are
 *  dependency metadata, not numbered paper objects. */
export function renderedNodes(g: FormalizationGraph): GraphNode[] {
  return g.nodes.filter((n) => n.nl.frozen && envForNode(n) !== null);
}

/** Outgoing statement-uses targets of a node id (as nodes). */
function statementUsesTargets(g: FormalizationGraph, id: string): GraphNode[] {
  const byId = new Map(g.nodes.map((n) => [n.id, n]));
  return g.edges
    .filter((e) => e.kind === "statement-uses" && e.from === id)
    .map((e) => byId.get(e.to))
    .filter((n): n is GraphNode => n != null);
}

/** Paper-env edge targets a node must \ref: the targets that are actually RENDERED
 *  as paper envs (`frozen` + env-kind), matching `renderedNodes`. Non-frozen
 *  targets (library reuse, `aux_*` proof helpers) get no `\label` in the paper, so
 *  they must NOT enter the cross-reference set. */
export function refTargets(g: FormalizationGraph, id: string): GraphNode[] {
  return statementUsesTargets(g, id).filter((n) => n.nl.frozen && envForNode(n) !== null);
}

/** Cited propositions on which a printed result is formally conditional. Follow only
 *  `statement-uses`: a cited proposition must occur in the consumer's Lean type to be a
 *  trust-boundary dependency. A merely contextual/proof-comparison citation must not acquire
 *  a formalization disclaimer. The traversal handles a packaged local proposition whose type
 *  in turn exposes the cited gate. */
export function citedDependencies(g: FormalizationGraph, id: string): GraphNode[] {
  const byId = new Map(g.nodes.map((n) => [n.id, n] as const));
  const uses = new Map<string, string[]>();
  for (const e of g.edges) {
    if (e.kind !== "statement-uses") continue;
    const row = uses.get(e.from) ?? [];
    row.push(e.to);
    uses.set(e.from, row);
  }
  const out: GraphNode[] = [];
  const seen = new Set<string>([id]);
  const queue = [...(uses.get(id) ?? [])];
  while (queue.length > 0) {
    const next = queue.shift()!;
    if (seen.has(next)) continue;
    seen.add(next);
    const node = byId.get(next);
    if (!node) continue;
    if (isCitedNode(node)) {
      out.push(node);
      continue;
    }
    queue.push(...(uses.get(next) ?? []));
  }
  return out;
}

/**
 * AGENT-INTRODUCED helper lemmas — every node authored during this run (`provenance ===
 * "agent-introduced"`) that carries a Lean decl and is not itself a rendered paper object. These
 * are machine-checked but get no NL/paper env; the web bundle surfaces them as an "Auxiliary Lean
 * lemmas" group so the interactive audit trail is complete. Stable on input order.
 *
 * Deliberately NOT a reachability closure over `proof-uses`/`statement-uses`: those edges are an
 * INCOMPLETE dependency record (heuristically extracted — on a real run roughly half of the
 * agent-introduced helpers have NO edge to the theorem they support, e.g. the entire lower-bound
 * and feasible-maximizer machinery), so any graph walk from the rendered nodes silently drops
 * genuine helpers. A per-qid graph contains only this paper's own development, so the
 * provenance + decl filter is the honest, direction-agnostic definition; a stale/abandoned decl
 * self-filters downstream at snippet extraction (no source → logged and skipped).
 */
export function auxiliaryNodes(g: FormalizationGraph): GraphNode[] {
  const rendered = new Set(renderedNodes(g).map((n) => n.id));
  return g.nodes.filter(
    (n) => n.provenance === "agent-introduced" && n.lean.decl_name != null && !rendered.has(n.id),
  );
}

/** Topological order over `nodes` by statement-uses edges (dependency before
 *  dependent), stable on the input order for ties / independent nodes. Cycle-safe:
 *  the edges are a Lean parse → acyclic; a residual cycle still terminates via the
 *  progress guard, emitting the remaining nodes in input order. */
export function topoOrder(g: FormalizationGraph, nodes: GraphNode[]): GraphNode[] {
  const keep = new Set(nodes.map((n) => n.id));
  const byId = new Map(nodes.map((n) => [n.id, n]));
  const deps = new Map<string, Set<string>>(); // id -> ids it uses (within `keep`)
  for (const n of nodes) deps.set(n.id, new Set());
  for (const e of g.edges) {
    if (e.kind === "statement-uses" && keep.has(e.from) && keep.has(e.to) && e.from !== e.to) {
      deps.get(e.from)!.add(e.to);
    }
  }
  const out: GraphNode[] = [];
  const done = new Set<string>();
  const order = nodes.map((n) => n.id);
  let progress = true;
  while (out.length < nodes.length && progress) {
    progress = false;
    for (const id of order) {
      if (done.has(id)) continue;
      if ([...deps.get(id)!].every((d) => done.has(d))) {
        out.push(byId.get(id)!);
        done.add(id);
        progress = true;
      }
    }
  }
  for (const id of order) if (!done.has(id)) out.push(byId.get(id)!);
  return out;
}

/** Load the banked graph for a bank entry directory. */
export async function loadBankGraph(
  dir: string,
  qid: string,
  spec: string,
): Promise<FormalizationGraph> {
  return loadGraph(graphPath(dir, qid, spec));
}
