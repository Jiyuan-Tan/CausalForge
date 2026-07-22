import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, setProof, setNodeReview } from "../../src/graph/mutate.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import type { ReviewerResult } from "../../src/formalization/proof_reviewer.js";
import type { FillerResult } from "../../src/formalization/proof_filler.js";
import type { FormalizationGraph } from "../../src/graph/types.js";

/** A graph whose single frozen theorem is proved + matched → frozen closure is complete. */
function settledGraph(): FormalizationGraph {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
  g = setProof(g, "t1", "complete", 0);
  g = setNodeReview(g, "t1", "matched", "h");
  return g;
}

const rs = () => ({ graph: settledGraph(), skeleton: [], dirty: [], hashes: {} });
const okReview = (g: FormalizationGraph): ReviewerResult => ({ graph: g, ok: true, escalate: null, blocking: [], substrateGates: [] });
const throwingDeps = { runCodex: (async () => { throw new Error("seam should be stubbed"); }) as never };

describe("proof-review loop — Phase A statement/scaffold gate", () => {
  it("a scaffold-mismatch reroutes to F2 (scaffold seam), then proceeds once the re-review clears", async () => {
    let reviewCalls = 0;
    const scaffoldCalls: { redirect: string; targets: string[] }[] = [];
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q", specialization: "v1" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      scaffold: async (a) => { scaffoldCalls.push(a); },
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s): Promise<ReviewerResult> => {
        reviewCalls++;
        if (reviewCalls === 1) {
          return { graph: s.graph, ok: false, escalate: { kind: "scaffold-mismatch", obj_id: "t1", reason: "H7 budget missing from t1's binder" }, blocking: ["t1"], substrateGates: [] };
        }
        return okReview(s.graph);
      },
    });
    expect(scaffoldCalls).toHaveLength(1);
    expect(scaffoldCalls[0].targets).toEqual(["t1"]);
    expect(outcome.status).toBe("completed");
  });

  it("a note-wrong defect ESCALATES without re-scaffolding (the note is the frozen contract)", async () => {
    const scaffoldCalls: unknown[] = [];
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q", specialization: "v1" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      scaffold: async (a) => { scaffoldCalls.push(a); },
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s): Promise<ReviewerResult> => ({
        graph: s.graph, ok: false,
        escalate: { kind: "note-wrong", obj_id: "t1", reason: "note assumes a hypothesis the .tex never states" },
        blocking: ["t1"], substrateGates: [],
      }),
    });
    expect(scaffoldCalls).toHaveLength(0);
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      expect(outcome.route).toBe("fix-source");
      expect(outcome.reason).toContain("note-wrong");
    }
  });

  it("an unadjudicable escalation (no rerouteable target) routes to `unclear`, NOT `fix-source`", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q", specialization: "v1" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      scaffold: async () => {},
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s): Promise<ReviewerResult> => ({
        graph: s.graph, ok: false,
        // No obj_id / blocking targets, so Phase A can't reroute to F2 — falls through to reviewerRoute.
        escalate: { kind: "unadjudicable", obj_id: undefined, reason: "can't place fault between note and Lean" },
        blocking: [], substrateGates: [],
      }),
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      expect(outcome.route).toBe("unclear");
      expect(outcome.reason).toContain("unadjudicable");
    }
  });

  it.each(["missing-review-evidence", "missing-review-target", "unparsable-output", "missing-peer-reviewer"])(
    "routes reviewer/infrastructure failure '%s' to the orchestrator without editing Lean",
    async (kind) => {
      const scaffoldCalls: unknown[] = [];
      const outcome = await runProofReviewLoop({
        ctx: { repoRoot: "/tmp", qid: "q", specialization: "v1" },
        deps: throwingDeps,
        buildCheck: async () => ({ ok: true, errors: "" }),
        refresh: async () => rs(),
        scaffold: async (a) => { scaffoldCalls.push(a); },
        fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
        review: async (s): Promise<ReviewerResult> => ({
          graph: s.graph, ok: false,
          escalate: { kind, obj_id: "t1", reason: "review evidence unavailable" },
          blocking: ["t1"], substrateGates: [],
        }),
      });
      expect(scaffoldCalls).toHaveLength(0);
      expect(outcome.status).toBe("escalate");
      if (outcome.status === "escalate") expect(outcome.reason).toContain(kind);
    },
  );
});
