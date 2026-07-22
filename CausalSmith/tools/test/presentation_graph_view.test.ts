import { describe, it, expect } from "vitest";
import {
  citedDependencies, renderedNodes, envForKind, envForNode, isCitedNode, topoOrder, refTargets,
} from "../src/presentation/graph_view.js";
import type { FormalizationGraph, GraphNode, GraphEdge } from "../src/graph/types.js";

const node = (id: string, kind: GraphNode["kind"], over: Partial<GraphNode> = {}): GraphNode => ({
  id, kind, provenance: "from-note",
  nl: { statement: `stmt ${id}`, tex_anchor: "", frozen: true },
  lean: { decl_name: `${id}_decl`, file: "F.lean" },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
  ...over,
});
const edge = (from: string, to: string, kind: GraphEdge["kind"] = "statement-uses"): GraphEdge =>
  ({ kind, from, to, source: "extracted" });
const graph = (nodes: GraphNode[], edges: GraphEdge[] = []): FormalizationGraph =>
  ({ qid: "q", specialization: "v1", nodes, edges });

describe("renderedNodes", () => {
  it("keeps frozen paper-env kinds, drops setups and non-frozen", () => {
    const g = graph([
      node("t1", "theorem"),
      node("s1", "setup"),
      node("p1", "definition", { provenance: "library", nl: { statement: "x", tex_anchor: "", frozen: false } }),
      node("a1", "assumption"),
    ]);
    expect(renderedNodes(g).map((n) => n.id)).toEqual(["t1", "a1"]);
  });
});

describe("envForKind", () => {
  it("maps kinds to envs", () => {
    expect(envForKind("theorem")).toBe("theoremv");
    expect(envForKind("lemma")).toBe("lemmav");
    expect(envForKind("assumption")).toBe("assumptionv");
    expect(envForKind("definition")).toBe("definitionv");
    expect(envForKind("setup")).toBeNull();
    expect(envForKind("gate")).toBeNull(); // kind-only: a gate's env depends on gate_class
  });
});

const citedGate = (id: string, over: Partial<GraphNode> = {}): GraphNode =>
  node(id, "gate", { gate: { gate_class: "cited", source: "cite:bonvini-kennedy-2022" }, ...over });

describe("isCitedNode / envForNode (cited gates)", () => {
  it("isCitedNode is true only for gate+gate_class:cited", () => {
    expect(isCitedNode(citedGate("c1"))).toBe(true);
    expect(isCitedNode(node("g1", "gate", { gate: { gate_class: "gated" } }))).toBe(false);
    expect(isCitedNode(node("g2", "gate"))).toBe(false); // no gate_class
    expect(isCitedNode(node("t1", "theorem"))).toBe(false);
  });
  it("envForNode hides cited gates from numbered paper envs, other kinds by kind", () => {
    expect(envForNode(citedGate("c1"))).toBeNull();
    expect(envForNode(node("g1", "gate", { gate: { gate_class: "gated" } }))).toBeNull();
    expect(envForNode(node("t1", "theorem"))).toBe("theoremv");
    expect(envForNode(node("t2", "theorem", {
      delivery: { status: "undelivered", role: "secondary", reason: "secondary overflow" },
    }))).toBe("remarkv");
  });
  it("renderedNodes excludes every gate, including frozen cited dependencies", () => {
    const g = graph([
      node("t1", "theorem"),
      citedGate("c1"),
      node("g1", "gate", { gate: { gate_class: "gated" } }),
    ]);
    expect(renderedNodes(g).map((n) => n.id)).toEqual(["t1"]);
  });
  it("refTargets excludes a cited gate while citedDependencies preserves it", () => {
    const g = graph([node("t1", "theorem"), citedGate("c1")], [edge("t1", "c1")]);
    expect(refTargets(g, "t1")).toEqual([]);
    expect(citedDependencies(g, "t1").map((n) => n.id)).toEqual(["c1"]);
  });
  it("citedDependencies follows transitive statement interfaces but ignores proof-only comparators", () => {
    const g = graph(
      [node("t1", "theorem"), node("p1", "definition"), citedGate("c1"), citedGate("c2")],
      [edge("t1", "p1"), edge("p1", "c1"), edge("t1", "c2", "proof-uses")],
    );
    expect(citedDependencies(g, "t1").map((n) => n.id)).toEqual(["c1"]);
  });
});

describe("topoOrder", () => {
  it("orders dependencies before dependents (A uses B ⇒ B first)", () => {
    const g = graph([node("a", "assumption"), node("b", "definition")], [edge("a", "b")]);
    expect(topoOrder(g, renderedNodes(g)).map((n) => n.id)).toEqual(["b", "a"]);
  });
});

describe("refTargets", () => {
  it("returns the paper-env edge targets a node must \\ref", () => {
    const g = graph(
      [node("a", "assumption"), node("p", "definition"), node("s", "setup")],
      [edge("a", "p"), edge("a", "s")],
    );
    expect(refTargets(g, "a").map((n) => n.id)).toEqual(["p"]); // setup excluded
  });
});

describe("refTargets excludes non-frozen targets (C1 regression)", () => {
  it("keeps only frozen paper-env targets", () => {
    const g = graph(
      [node("t1", "theorem"),
       // a non-frozen agent helper of env-kind: NOT a paper env (no \label), must be excluded from refs
       node("aux", "definition", { provenance: "agent-introduced",
         nl: { statement: "aux", tex_anchor: "", frozen: false },
         lean: { decl_name: "auxDecl", file: "F.lean" } }),
       node("p7", "definition")],
      [edge("t1", "aux"), edge("t1", "p7")],
    );
    expect(refTargets(g, "t1").map((n) => n.id)).toEqual(["p7"]); // aux excluded (non-frozen)
  });
});

describe("topoOrder edge cases", () => {
  it("preserves input order for independent nodes", () => {
    const g = graph([node("b", "definition"), node("a", "definition"), node("c", "definition")]);
    expect(topoOrder(g, renderedNodes(g)).map((n) => n.id)).toEqual(["b", "a", "c"]);
  });
  it("is cycle-safe: emits all nodes even if a residual cycle exists", () => {
    const g = graph([node("x", "definition"), node("y", "definition")], [edge("x", "y"), edge("y", "x")]);
    const out = topoOrder(g, renderedNodes(g)).map((n) => n.id);
    expect(out.sort()).toEqual(["x", "y"]); // both present, no infinite loop
  });
});

