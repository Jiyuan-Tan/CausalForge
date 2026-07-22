import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge } from "../../src/graph/mutate.js";
import { graphDerivedSkeleton, renderDependencyBlock } from "../../src/graph/skeleton.js";

function g() {
  let x = createEmptyGraph("q", "v1");
  x = addNode(x, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "env", tex_anchor: "" });
  x = addNode(x, { id: "a1", kind: "assumption", provenance: "from-note", nl_statement: "ov", tex_anchor: "L5" });
  x = addNode(x, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
  x = addNode(x, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  x = { ...x, nodes: x.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  x = addEdge(x, { kind: "setup-of", from: "setup", to: "t1", source: "declared" });
  x = addEdge(x, { kind: "proof-uses", from: "t1", to: "a1", source: "declared" });
  x = addEdge(x, { kind: "statement-uses", from: "t1", to: "l1", source: "extracted" });
  return x;
}

describe("graphDerivedSkeleton", () => {
  it("projects P/L/T/A nodes to rows; skips setup; carries the lean anchor", () => {
    const skel = graphDerivedSkeleton(g());
    const t1 = skel.find((e) => e.obj_id === "T-1")!;
    expect(t1.kind).toBe("theorem");
    expect(t1.lean?.decl).toBe("t1_thm");
    expect(skel.find((e) => e.obj_id === "setup")).toBeUndefined();
    expect(skel.find((e) => e.obj_id === "A-1")?.kind).toBe("assumption");
  });
  it("attaches per-row dependency edges resolved to obj_ids", () => {
    const skel = graphDerivedSkeleton(g());
    const t1 = skel.find((e) => e.obj_id === "T-1")!;
    expect(t1.uses).toEqual(["L-1"]); // statement-uses only
    expect(t1.proofUses).toEqual(["A-1"]); // proof-uses kept separate (not a statement-drift criterion)
    expect(t1.boundTo).toEqual(["setup"]);
    expect(skel.find((e) => e.obj_id === "A-1")!.usedBy).toEqual(["T-1"]);
  });
});

describe("renderDependencyBlock", () => {
  it("lists each object's statement-uses/proof-uses + setup binding, with a faithfulness instruction", () => {
    const block = renderDependencyBlock(graphDerivedSkeleton(g()));
    expect(block).toContain("DEPENDENCY EDGES");
    expect(block).toContain("T-1 [setup: setup] statement-uses: L-1 proof-uses: A-1");
    // proof-uses must be marked NOT a statement-drift criterion (sorry-OK)
    expect(block).toContain("NOT statement faithfulness");
  });
  it("is empty when no row has edges", () => {
    let x = createEmptyGraph("q", "v1");
    x = addNode(x, { id: "p1", kind: "definition", provenance: "from-note", nl_statement: "d", tex_anchor: "" });
    expect(renderDependencyBlock(graphDerivedSkeleton(x))).toBe("");
  });
});
