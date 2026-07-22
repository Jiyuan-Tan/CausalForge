import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, setNodeReview } from "../../src/graph/mutate.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";
import { gateReviewPlan } from "../../src/graph/review_plan.js";

function fixture() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "l1" ? { ...n, lean: { decl_name: "l1_h", file: "T1.lean" } } : n)) };
  g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
  g = setNodeReview(g, "t1", "matched", "h_t1");
  g = setNodeReview(g, "l1", "drift", "h_l1");
  return g;
}

describe("gateReviewPlan", () => {
  it("dirty nodes → reaudit; non-dirty reviewed nodes → carried with their status", () => {
    const g = fixture();
    const skel = graphDerivedSkeleton(g);
    const plan = gateReviewPlan(g, skel, ["l1", "t1"]); // both dirty (l1 changed, t1 dependent)
    expect(plan.reaudit.map((r) => r.obj_id).sort()).toEqual(["L-1", "T-1"]);
    expect(plan.carried).toEqual([]);
  });

  it("nothing dirty → all carried with their node.review status (freeze)", () => {
    const g = fixture();
    const skel = graphDerivedSkeleton(g);
    const plan = gateReviewPlan(g, skel, []);
    expect(plan.reaudit).toEqual([]);
    const byId = Object.fromEntries(plan.carried.map((c) => [c.obj_id, c.status]));
    expect(byId["T-1"]).toBe("matched"); // matched + unchanged → carried (frozen)
    expect(byId["L-1"]).toBe("drift"); // drift + unchanged → carried, still blocking
  });
});
