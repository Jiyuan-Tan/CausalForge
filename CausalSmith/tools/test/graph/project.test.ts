import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge } from "../../src/graph/mutate.js";
import { toMarkdown, toDot } from "../../src/graph/project.js";

function g() {
  let x = createEmptyGraph("stat_demo", "v1");
  x = addNode(x, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main result", tex_anchor: "tex:L1" });
  x = addNode(x, { id: "l1", kind: "lemma", provenance: "agent-introduced", nl_statement: "helper", tex_anchor: "" });
  x = addEdge(x, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
  return x;
}

describe("projection", () => {
  it("toMarkdown lists nodes by kind with provenance + NL", () => {
    const md = toMarkdown(g());
    expect(md).toContain("# stat_demo");
    expect(md).toContain("t1");
    expect(md).toContain("main result");
    expect(md).toContain("agent-introduced");
  });
  it("toDot emits a digraph with an edge", () => {
    const dot = toDot(g());
    expect(dot).toContain("digraph");
    expect(dot).toContain('"t1" -> "l1"');
  });
});
