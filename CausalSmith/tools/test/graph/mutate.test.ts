import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addAssumption, addEdge, addNode, markPassed, setLean, setNodeReview, setProof } from "../../src/graph/mutate.js";

describe("mutate", () => {
  it("addNode inserts a node and rejects duplicate ids", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "l7", kind: "lemma", provenance: "agent-introduced", nl_statement: "helper bound", tex_anchor: "" });
    expect(g.nodes.map((n) => n.id)).toEqual(["l7"]);
    expect(g.nodes[0].provenance).toBe("agent-introduced");
    expect(g.nodes[0].nl.frozen).toBe(false); // agent-introduced ⇒ not frozen
    expect(() => addNode(g, { id: "l7", kind: "lemma", provenance: "agent-introduced", nl_statement: "x", tex_anchor: "" })).toThrow(/duplicate/i);
  });

  it("from-note nodes default to frozen NL", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "tex:L1" });
    expect(g.nodes[0].nl.frozen).toBe(true);
  });

  it("addEdge rejects when an endpoint is missing", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    expect(() => addEdge(g, { kind: "proof-uses", from: "t1", to: "l9", source: "declared" })).toThrow(/endpoint/i);
  });

  it("addEdge de-duplicates identical edges", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
    g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
    expect(g.edges).toHaveLength(1);
  });

  it("addAssumption creates an assumption node with tier + classification", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addAssumption(g, {
      node: "t1",
      id: "a4",
      statement: "tail-only overlap",
      tier: 2,
      classification: "faithful-refinement",
      anchor: "tex:L120-124",
      provenance: "agent-introduced",
    });
    const a = g.nodes.find((n) => n.id === "a4")!;
    expect(a.kind).toBe("assumption");
    expect(a.assumption).toEqual({ tier: 2, classification: "faithful-refinement" });
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: "a4", source: "declared" });
  });

  it("setLean / setProof / markPassed update the right node", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = setLean(g, "t1", "t1_main", "T1.lean");
    g = setProof(g, "t1", "complete", 0);
    g = markPassed(g, "t1", "deadbeef");
    const t = g.nodes.find((n) => n.id === "t1")!;
    expect(t.lean).toEqual({ decl_name: "t1_main", file: "T1.lean" });
    expect(t.proof).toEqual({ state: "complete", sorry_count: 0 });
    expect(t.review).toEqual({ status: "matched", passed_hash: "deadbeef" });
  });

  it("setNodeReview sets an explicit review status", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = setNodeReview(g, "l1", "derived", "h2");
    expect(g.nodes[0].review).toEqual({ status: "derived", passed_hash: "h2" });
    g = setNodeReview(g, "l1", "drift", "h3");
    expect(g.nodes[0].review.status).toBe("drift");
  });
});
