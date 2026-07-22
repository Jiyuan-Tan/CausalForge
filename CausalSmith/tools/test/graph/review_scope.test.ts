import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, addAssumption, setNodeReview } from "../../src/graph/mutate.js";
import { reviewTargets, convergenceTargets, incrementalSymbolRows } from "../../src/graph/review_scope.js";

function fixture() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
  g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "helper t1 uses", tex_anchor: "" });
  g = addNode(g, { id: "l9", kind: "lemma", provenance: "agent-introduced", nl_statement: "orphan helper", tex_anchor: "" });
  g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" }); // t1 uses l1
  // a2 = a NEW assumption on l1 (which t1 uses) → in t1's uses-closure
  g = addAssumption(g, { node: "l1", id: "a2", statement: "bounded", tier: 2, classification: "regularity-bookkeeping", anchor: "", provenance: "agent-introduced" });
  // a7 = an assumption on the ORPHAN l9 (no frozen theorem uses it)
  g = addAssumption(g, { node: "l9", id: "a7", statement: "x", tier: 2, classification: "faithful-refinement", anchor: "", provenance: "agent-introduced" });
  return g;
}

describe("reviewTargets", () => {
  it("a dirty frozen theorem is a statement target", () => {
    const t = reviewTargets(fixture(), ["t1"]);
    expect(t.statementTargets).toEqual(["t1"]);
  });

  it("a new assumption in a frozen theorem's uses-closure is an assumption target (even on a helper)", () => {
    const t = reviewTargets(fixture(), []); // a2/a7 are unreviewed by construction
    expect(t.assumptionTargets).toContain("a2"); // a2 on l1, which t1 uses → in closure
    expect(t.assumptionTargets).not.toContain("a7"); // a7 on orphan l9 → not in any frozen closure
  });

  it("a non-frozen (agent-introduced) theorem statement is NOT a statement target", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t2", kind: "theorem", provenance: "agent-introduced", nl_statement: "aux", tex_anchor: "" });
    g = setNodeReview(g, "t2", "unreviewed", "");
    expect(reviewTargets(g, ["t2"]).statementTargets).toEqual([]);
  });

  it("a from-note definition is a definition target (paper object — checked even if reached only via a lemma); library/agent-introduced defs are not", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    g = addNode(g, { id: "p_tex", kind: "definition", provenance: "from-note", nl_statement: "the loss class", tex_anchor: "" });
    g = addNode(g, { id: "p_lib", kind: "definition", provenance: "library", nl_statement: "imported", tex_anchor: "" });
    g = addNode(g, { id: "p_aux", kind: "definition", provenance: "agent-introduced", nl_statement: "scaffold helper", tex_anchor: "" });
    const t = reviewTargets(g, []); // all unreviewed by construction
    expect(t.definitionTargets).toEqual(["p_tex"]);
  });

  it("keeps an undelivered theorem out of F2.5 statement review but includes it in the F4 delivery-role audit", () => {
    let g = createEmptyGraph("q", "v1");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    g = addNode(g, { id: "t2", kind: "theorem", provenance: "from-note", nl_statement: "secondary", tex_anchor: "" });
    g = {
      ...g,
      nodes: g.nodes.map((n) => n.id === "t2" ? {
        ...n,
        delivery: { status: "undelivered", role: "secondary", reason: "citation overflow" },
      } : n),
    };
    expect(reviewTargets(g, ["t1", "t2"]).statementTargets).toEqual(["t1"]);
    expect(reviewTargets(g, ["t1", "t2"]).deliveryTargets).toEqual([]);
    expect(convergenceTargets(g).statementTargets).toEqual(["t1"]);
    expect(convergenceTargets(g).deliveryTargets).toEqual(["t2"]);
  });
});

describe("incrementalSymbolRows — symbol-tier incremental review", () => {
  const isPass = (v: string) => v === "matched" || v === "equivalent" || v === "untagged";
  const built = [
    { id: "sym:Y", hash: "hY" },
    { id: "sym:Z", hash: "hZ" },
    { id: "sym:P", hash: "hP" },
  ];

  it("first pass (no prior state) reviews every symbol", () => {
    expect(incrementalSymbolRows(built, undefined, "delta", isPass).map((s) => s.id)).toEqual([
      "sym:Y", "sym:Z", "sym:P",
    ]);
  });

  it("delta skips a symbol whose cluster is UNCHANGED and last verdict PASSED", () => {
    const prior = {
      "sym:Y": { verdict: "matched", hash: "hY" }, // pass + same hash → skip
      "sym:Z": { verdict: "untagged", hash: "hZ" }, // untagged counts as pass → skip
    };
    expect(incrementalSymbolRows(built, prior, "delta", isPass).map((s) => s.id)).toEqual(["sym:P"]);
  });

  it("delta RE-REVIEWS a previously-passed symbol whose cluster hash CHANGED (e.g. a new @realizes tag)", () => {
    const prior = { "sym:Y": { verdict: "matched", hash: "OLD" } }; // hash differs from built hY
    expect(incrementalSymbolRows(built, prior, "delta", isPass).map((s) => s.id)).toContain("sym:Y");
  });

  it("delta always RE-REVIEWS a previously-DRIFTED symbol even if unchanged", () => {
    const prior = { "sym:Y": { verdict: "drift", hash: "hY" } }; // same hash but not a pass → review
    expect(incrementalSymbolRows(built, prior, "delta", isPass).map((s) => s.id)).toContain("sym:Y");
  });

  it("convergence reviews EVERY symbol regardless of prior matched state", () => {
    const prior = {
      "sym:Y": { verdict: "matched", hash: "hY" },
      "sym:Z": { verdict: "matched", hash: "hZ" },
      "sym:P": { verdict: "matched", hash: "hP" },
    };
    expect(incrementalSymbolRows(built, prior, "convergence", isPass).map((s) => s.id)).toEqual([
      "sym:Y", "sym:Z", "sym:P",
    ]);
  });
});
