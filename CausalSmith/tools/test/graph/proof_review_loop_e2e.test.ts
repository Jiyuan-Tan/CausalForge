import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { graphPath, saveGraph, loadGraph } from "../../src/graph/store.js";
import { addEdge } from "../../src/graph/mutate.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { provisionLoopEnv } from "./loop_test_env.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "loop-e2e-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

// A reviewer JSON that matches the single frozen theorem; the convergence dual-review
// reuses the same stub. The filler is never invoked (the Lean is already proven).
const reviewerOut = JSON.stringify({
  status: "ok",
  statement_verdicts: [{ obj_id: "T-1", verdict: "matched", note: "ok" }],
  assumption_verdicts: [],
  substrate_gates: [],
  escalate: null,
});

describe("proof-review loop end-to-end (real modules, stubbed LLM)", () => {
  it("refresh → review(matched) → frozen closure complete → convergence → completed", async () => {
    // F1 .md + graph on disk
    const md = "### T-block: t1 — Rate theorem\n**Statement.** the rate bound holds.\n";
    await writeFile(path.join(dir, "q_v1.md"), md, "utf8");
    await saveGraph(graphPath(dir, "q", "v1"), await buildGraphFromMd("q", "v1", path.join(dir, "q_v1.md")));
    // a PROVEN scaffold (no sorry), annotated so extract links it
    const leanDir = path.join(dir, "lean");
    await mkdir(leanDir, { recursive: true });
    await writeFile(path.join(leanDir, "T1.lean"), "-- @node: t1\ntheorem t1_thm : True := by trivial\n", "utf8");
    await provisionLoopEnv(dir);

    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps: {
        runCodex: (async () => ({ stdout: reviewerOut })) as never,
        runClaude: (async () => reviewerOut) as never,
      },
      buildCheck: async () => ({ ok: true, errors: "" }),
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
    });

    expect(outcome.status).toBe("completed");
    // the loop persisted the graph with t1 reviewed matched + proof complete
    const g = await loadGraph(graphPath(dir, "q", "v1"));
    const t1 = g.nodes.find((n) => n.id === "t1")!;
    expect(t1.review.status).toBe("matched");
    expect(t1.proof.state).toBe("complete");
  });

  it("persists a matched verdict for an exact case-sensitive agent node id", async () => {
    const md = "### T-block: t1 — Rate theorem\n**Statement.** the rate bound holds.\n";
    await writeFile(path.join(dir, "q_v1.md"), md, "utf8");
    let graph = await buildGraphFromMd("q", "v1", path.join(dir, "q_v1.md"));
    graph = {
      ...graph,
      nodes: [
        ...graph.nodes,
        {
          id: "hP_pointwise_witness",
          kind: "assumption",
          provenance: "agent-introduced",
          nl: { statement: "the selected kernel obeys the pointwise envelope", tex_anchor: "", frozen: false },
          lean: { decl_name: null, file: null },
          review: { status: "unreviewed", passed_hash: null },
          proof: { state: "complete", sorry_count: 0 },
        },
      ],
    };
    graph = addEdge(graph, { kind: "proof-uses", from: "t1", to: "hP_pointwise_witness", source: "declared" });
    await saveGraph(graphPath(dir, "q", "v1"), graph);
    const leanDir = path.join(dir, "lean");
    await mkdir(leanDir, { recursive: true });
    await writeFile(path.join(leanDir, "T1.lean"), "-- @node: t1\ntheorem t1_thm : True := by trivial\n", "utf8");
    await provisionLoopEnv(dir);
    const exactReviewerOut = JSON.stringify({
      status: "ok",
      statement_verdicts: [{ obj_id: "T-1", verdict: "matched", note: "ok" }],
      assumption_verdicts: [{ obj_id: "hP_pointwise_witness", verdict: "faithful-refinement", note: "exact" }],
      substrate_gates: [],
      escalate: null,
    });

    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps: {
        runCodex: (async () => ({ stdout: exactReviewerOut })) as never,
        runClaude: (async () => exactReviewerOut) as never,
      },
      buildCheck: async () => ({ ok: true, errors: "" }),
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
    });

    expect(outcome.status).toBe("completed");
    const persisted = await loadGraph(graphPath(dir, "q", "v1"));
    expect(persisted.nodes.find((n) => n.id === "hP_pointwise_witness")!.review.status).toBe("matched");
    expect(persisted.nodes.find((n) => n.id === "hP_pointwise_witness")!.review.note).toBe("exact");
  });
});
