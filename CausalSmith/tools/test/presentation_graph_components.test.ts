import { describe, it, expect } from "vitest";
import { graphComponentSpecs } from "../src/presentation/graph_components.js";
import type { FormalizationGraph } from "../src/graph/types.js";

const node = (
  id: string,
  obj_id: string,
  decl: string | null,
): FormalizationGraph["nodes"][number] => ({
  id,
  obj_id,
  kind: "definition",
  provenance: "from-note",
  nl: { statement: id, tex_anchor: "", frozen: true },
  lean: { decl_name: decl, file: decl ? "Basic.lean" : null },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
});

const g: FormalizationGraph = {
  qid: "q",
  specialization: "s",
  nodes: [node("def:a", "P-1", "declA"), node("def:helper", "P-2", "declHelper"), node("def:bare", "P-3", null)],
  edges: [
    { kind: "statement-uses", from: "def:a", to: "def:helper", source: "declared" },
    // a proof-uses edge must NOT contribute to the statement's component set
    { kind: "proof-uses", from: "def:a", to: "def:bare", source: "declared" },
  ],
};

describe("graphComponentSpecs", () => {
  it("returns the node's own decl plus statement-uses neighbours that carry a Lean decl", () => {
    expect(graphComponentSpecs(g, "P-1")).toEqual([
      { type: "decl", decl: "declA" },
      { type: "decl", decl: "declHelper" },
    ]);
  });
  it("resolves by node id as well as obj_id", () => {
    expect(graphComponentSpecs(g, "def:a")).toEqual([
      { type: "decl", decl: "declA" },
      { type: "decl", decl: "declHelper" },
    ]);
  });
  it("returns just the own decl when there are no formalized statement-uses neighbours", () => {
    expect(graphComponentSpecs(g, "P-2")).toEqual([{ type: "decl", decl: "declHelper" }]);
  });
  it("returns [] for a node with no Lean decl", () => {
    expect(graphComponentSpecs(g, "P-3")).toEqual([]);
  });
  it("returns [] for an unknown obj_id", () => {
    expect(graphComponentSpecs(g, "Z-9")).toEqual([]);
  });
});
