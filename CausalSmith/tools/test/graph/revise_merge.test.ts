import { describe, expect, it } from "vitest";
import { addEdge, addNode, markPassed, setLean, setProof } from "../../src/graph/mutate.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { mergeStage1RevisionGraph } from "../../src/graph/revise_merge.js";

function baseGraph() {
  let graph = createEmptyGraph("q", "s");
  graph = addNode(graph, {
    id: "def:x",
    kind: "definition",
    provenance: "from-note",
    nl_statement: "old definition",
    tex_anchor: "",
  });
  graph = addNode(graph, {
    id: "thm:y",
    kind: "theorem",
    provenance: "from-note",
    nl_statement: "headline",
    tex_anchor: "",
  });
  graph = addEdge(graph, {
    kind: "proof-uses",
    from: "thm:y",
    to: "def:x",
    source: "declared",
  });
  return graph;
}

describe("mergeStage1RevisionGraph", () => {
  it("preserves later-stage enrichment when the F1 structure is unchanged", () => {
    let previous = baseGraph();
    previous = setLean(previous, "def:x", "Q.x", "Basic.lean");
    previous = setProof(previous, "def:x", "complete", 0);
    previous = markPassed(previous, "def:x", "hash-x");
    previous = markPassed(previous, "thm:y", "hash-y");
    previous = addNode(previous, {
      id: "aux:z",
      kind: "lemma",
      provenance: "agent-introduced",
      nl_statement: "auxiliary fact",
      tex_anchor: "",
    });
    previous = setLean(previous, "aux:z", "Q.z", "Aux.lean");
    previous = addEdge(previous, {
      kind: "statement-uses",
      from: "thm:y",
      to: "aux:z",
      source: "extracted",
    });
    previous.symbolReview = { "sym:X": { verdict: "matched", hash: "sym-hash" } };

    const merged = mergeStage1RevisionGraph(previous, baseGraph());

    expect(merged.nodes).toHaveLength(3);
    expect(merged.nodes.find((node) => node.id === "def:x")?.lean).toEqual({
      decl_name: "Q.x",
      file: "Basic.lean",
    });
    expect(merged.nodes.find((node) => node.id === "def:x")?.proof.state).toBe("complete");
    expect(merged.nodes.find((node) => node.id === "def:x")?.review.status).toBe("matched");
    expect(merged.nodes.find((node) => node.id === "thm:y")?.review.status).toBe("matched");
    expect(merged.nodes.find((node) => node.id === "aux:z")?.lean.decl_name).toBe("Q.z");
    expect(merged.edges).toContainEqual({
      kind: "statement-uses",
      from: "thm:y",
      to: "aux:z",
      source: "extracted",
    });
    expect(merged.symbolReview).toEqual(previous.symbolReview);
  });

  it("invalidates only a changed node and its transitive consumers", () => {
    let previous = baseGraph();
    previous = markPassed(previous, "def:x", "hash-x");
    previous = markPassed(previous, "thm:y", "hash-y");

    let rebuilt = createEmptyGraph("q", "s");
    rebuilt = addNode(rebuilt, {
      id: "def:x",
      kind: "definition",
      provenance: "from-note",
      nl_statement: "corrected definition",
      tex_anchor: "",
    });
    rebuilt = addNode(rebuilt, {
      id: "thm:y",
      kind: "theorem",
      provenance: "from-note",
      nl_statement: "headline",
      tex_anchor: "",
    });
    rebuilt = addEdge(rebuilt, {
      kind: "proof-uses",
      from: "thm:y",
      to: "def:x",
      source: "declared",
    });

    const merged = mergeStage1RevisionGraph(previous, rebuilt);

    expect(merged.nodes.find((node) => node.id === "def:x")?.nl.statement).toBe("corrected definition");
    expect(merged.nodes.find((node) => node.id === "def:x")?.review.status).toBe("unreviewed");
    expect(merged.nodes.find((node) => node.id === "thm:y")?.review.status).toBe("unreviewed");
  });

  it("drops removed from-note nodes but retains agent-introduced nodes", () => {
    let previous = baseGraph();
    previous = addNode(previous, {
      id: "aux:z",
      kind: "lemma",
      provenance: "agent-introduced",
      nl_statement: "auxiliary fact",
      tex_anchor: "",
    });

    let rebuilt = createEmptyGraph("q", "s");
    rebuilt = addNode(rebuilt, {
      id: "thm:y",
      kind: "theorem",
      provenance: "from-note",
      nl_statement: "headline",
      tex_anchor: "",
    });

    const merged = mergeStage1RevisionGraph(previous, rebuilt);
    expect(merged.nodes.map((node) => node.id)).toEqual(["thm:y", "aux:z"]);
  });
});
