// Build the formalization graph from the typed core + F1 plan (the plan-driven
// replacement for `buildGraphFromMd`). The graph is the universal interchange the
// proof loop (F3/F4), the crosswalk, and the bank all hang off — keying its nodes by
// CORE node ids (`ass:…`, `def:…`, `thm:…`) so the `-- @node: <core id>` tags F2
// emits link straight to graph nodes. See CausalSmith/doc/research/F1_F2_PLAN_REDESIGN.md.
import { createEmptyGraph } from "./store.js";
import { addEdge, addNode } from "./mutate.js";
import type { FormalizationGraph, NodeKind } from "./types.js";
import { buildDagFromCore } from "../discovery/core/dag.js";
import type { Core } from "../discovery/core/schema.js";
import type { Plan } from "../formalization/plan/schema.js";

function withSetup(g: FormalizationGraph, id: string, mods: string[]): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, setup: { required_modules: mods } } : n)) };
}
function withExternalLean(g: FormalizationGraph, id: string, decl: string): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, lean: { decl_name: decl, file: null } } : n)) };
}
function withStandard(
  g: FormalizationGraph,
  id: string,
  std: { name: string; cite: string; citation?: string },
): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, standard: std } : n)) };
}
function withGate(
  g: FormalizationGraph,
  id: string,
  gate: { gate_class?: "gated" | "cited"; source?: string },
): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, gate } : n)) };
}
function withDelivery(
  g: FormalizationGraph,
  id: string,
  delivery: { role?: "headline" | "headline-support" | "secondary"; status: "deliver" | "undelivered"; reason?: string },
): FormalizationGraph {
  return { ...g, nodes: g.nodes.map((n) => (n.id === id ? { ...n, delivery } : n)) };
}

/** Stamp a causalsmith-compatible obj-id alias on every node (deterministic, by kind
 *  in node order): setup→S-k, definition→P-k, assumption→A-k, lemma→L-k, theorem→T-k.
 *  Lets a core-keyed graph (`id = thm:foo`) correlate with a `parseNoteBlocks`-keyed
 *  bridge note and the causalsmith `graphCrosswalk`. */
function withObjIdAliases(g: FormalizationGraph): FormalizationGraph {
  const counters: Record<string, number> = {};
  const prefix: Record<string, string> = {
    setup: "S", definition: "P", assumption: "A", lemma: "L", theorem: "T",
  };
  return {
    ...g,
    nodes: g.nodes.map((n) => {
      const p = prefix[n.kind];
      if (!p) return n; // gate or unknown kind → no alias
      counters[p] = (counters[p] ?? 0) + 1;
      return { ...n, obj_id: `${p}-${counters[p]}` };
    }),
  };
}

/**
 * Build the graph from `core` (structure + node NL) and an optional `plan` (Lean
 * realization decisions). Nodes:
 *  - setup nodes from `plan.env` S-blocks (required_modules; reuse → library-backed),
 *    or one synthesized fallback when the plan has no env;
 *  - one node per core node id (assumption / definition / statement), NL from the
 *    core's condition / construction / statement, kind from the plan's `lean_kind`
 *    (statement → theorem|lemma, with OEQ residuals allowed to be definition
 *    Props) falling back to the core node kind;
 *  - a `reuse` node → library-backed (decl_name set, file null).
 * Edges: `proof-uses` from each statement's `depends_on`; `setup-of` from every setup
 * node to every theorem. Realized (Lean-side) edges come later from F2/F3 extraction.
 */
export function buildGraphFromCorePlan(core: Core, spec: string, plan: Plan | null): FormalizationGraph {
  let g = createEmptyGraph(core.qid, spec);
  const dag = buildDagFromCore(core);

  // --- setup nodes from plan.env (or one fallback) ---
  const setupIds: string[] = [];
  for (const e of plan?.env ?? []) {
    if (g.nodes.some((n) => n.id === e.id)) continue;
    g = addNode(g, {
      id: e.id,
      kind: "setup",
      provenance: "from-note",
      nl_statement: e.notes ? `${e.world} — ${e.notes}` : e.world,
      tex_anchor: "",
    });
    g = withSetup(g, e.id, e.modules);
    if (e.disposition === "reuse" && e.reuse) g = withExternalLean(g, e.id, e.reuse);
    setupIds.push(e.id);
  }
  if (setupIds.length === 0) {
    g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "the environment / substrate of the run", tex_anchor: "" });
    g = withSetup(g, "setup", []);
    setupIds.push("setup");
  }

  // --- content nodes (assumptions ∪ definitions ∪ statements) ---
  const nl = new Map<string, string>();
  for (const a of core.assumptions) nl.set(a.id, a.condition);
  for (const d of core.definitions) nl.set(d.id, d.construction);
  for (const s of core.statements) nl.set(s.id, s.statement);

  // Citation provenance per assumption: the core's `standard` tag ({name, cite}) plus the
  // matching `bibliography` entry's free text, so causalsmith can gloss + reference each
  // assumption. A novel assumption carries no `standard` (absent ⇒ novel-to-this-work).
  const bibText = new Map((core.bibliography ?? []).map((b) => [b.key, b.citation] as const));
  const stdById = new Map(
    core.assumptions
      .filter((a) => a.standard)
      .map((a) => [a.id, { name: a.standard!.name, cite: a.standard!.cite, citation: bibText.get(a.standard!.cite) }] as const),
  );

  // Only genuinely unresolved OEQs reach F1. D0 replaces a solved OEQ with the theorem that states
  // its actual answer. Fail closed on legacy/malformed `proved + openendedquestion` cores instead of
  // silently discarding their proof at the D0 -> F1 boundary.
  const provedOeq = (core.statements ?? []).find((s) => s.kind === "openendedquestion" && s.status === "proved");
  if (provedOeq) {
    throw new Error(
      `fromCore: proved open-ended question '${provedOeq.id}' was not normalized to a thm: resolution node at D0`,
    );
  }
  const oeqIds = new Set((core.statements ?? []).filter((s) => s.kind === "openendedquestion").map((s) => s.id));
  for (const id of dag.nodes) {
    if (g.nodes.some((n) => n.id === id)) continue;
    const ck = dag.kindOf.get(id);
    const pnode = plan?.nodes[id];
    const kind: NodeKind =
      ck === "assumption"
        ? "assumption"
        : ck === "statement"
          ? oeqIds.has(id) ? "definition" : pnode?.gate ? "gate" : pnode?.lean_kind === "def" ? "definition" : pnode?.lean_kind === "lemma" ? "lemma" : "theorem"
          : "definition"; // definition-class | definition-construction
    g = addNode(g, { id, kind, provenance: "from-note", nl_statement: nl.get(id) ?? id, tex_anchor: "" });
    if (pnode?.gate) g = withGate(g, id, { gate_class: pnode.gate_class, source: pnode.source });
    if (pnode && (pnode.delivery_role || pnode.delivery_status === "undelivered")) {
      g = withDelivery(g, id, {
        role: pnode.delivery_role,
        status: pnode.delivery_status ?? "deliver",
        reason: pnode.delivery_reason,
      });
    }
    if (pnode?.disposition === "reuse" && pnode.reuse) g = withExternalLean(g, id, pnode.reuse);
    const std = stdById.get(id);
    if (std) g = withStandard(g, id, std);
  }

  // --- declared dependency edges (proof-uses) from each statement's depends_on ---
  for (const s of core.statements) {
    for (const dep of s.depends_on) {
      if (dep !== s.id && dag.nodes.has(dep)) {
        g = addEdge(g, { kind: "proof-uses", from: s.id, to: dep, source: "declared" });
      }
    }
  }
  // --- setup-of edges to every theorem ---
  for (const n of g.nodes) {
    if (n.kind === "theorem" && n.delivery?.status !== "undelivered") for (const sid of setupIds) {
      g = addEdge(g, { kind: "setup-of", from: sid, to: n.id, source: "declared" });
    }
  }
  return withObjIdAliases(g);
}
