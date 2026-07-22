import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, setProof, setNodeReview } from "../../src/graph/mutate.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";

function thm(complete: boolean, matched: boolean) {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = setProof(g, "t1", complete ? "complete" : "sorry", complete ? 0 : 1);
  if (matched) g = setNodeReview(g, "t1", "matched", "h");
  return g;
}
const refreshOf = (g: ReturnType<typeof thm>) => ({ graph: g, skeleton: graphDerivedSkeleton(g), dirty: ["t1"], hashes: { t1: "h" } });

describe("runProofReviewLoop", () => {
  it("converges: review ok → fill → complete → convergence review → completed", async () => {
    const states = [refreshOf(thm(false, false)), refreshOf(thm(true, true))];
    let ri = 0;
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q", specialization: "v1" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => states[Math.min(ri++, states.length - 1)],
      review: async (s) => ({ graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: null, summary: "proved t1" }),
    });
    expect(outcome.status).toBe("completed");
  });

  it("escalates when the reviewer flags a blocking finding", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q", specialization: "v1" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => refreshOf(thm(false, false)),
      review: async (s) => ({ graph: s.graph, ok: false, escalate: null, blocking: ["A-2"], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: null, summary: "" }),
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") expect(outcome.route).toBe("hint");
  });

  it("escalates build-substrate when the filler hits a substrate wall", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q", specialization: "v1" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => refreshOf(thm(false, false)),
      review: async (s) => ({ graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: { kind: "needs-substrate", reason: "concentration bound" }, summary: "" }),
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      expect(outcome.route).toBe("build-substrate");
      expect(outcome.phase).toBe("3");
    }
  });

  it("escalates bank-partial after K stale iterations", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q", specialization: "v1" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => refreshOf(thm(false, false)), // never progresses
      review: async (s) => ({ graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: null, summary: "no progress" }),
      noProgressK: 2,
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") expect(outcome.route).toBe("bank-partial");
  });
});
