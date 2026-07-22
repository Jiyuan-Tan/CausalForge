import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { graphPath, saveGraph } from "../../src/graph/store.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { provisionLoopEnv } from "./loop_test_env.js";
import { pipelineLogPath } from "../../src/paths.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "loop-f35-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const reviewerOut = JSON.stringify({
  status: "ok",
  statement_verdicts: [{ obj_id: "T-1", verdict: "matched", note: "ok" }],
  assumption_verdicts: [],
  substrate_gates: [],
  escalate: null,
});

async function setup() {
  const md = "### T-block: t1 — Rate theorem\n**Statement.** the rate bound holds.\n";
  await writeFile(path.join(dir, "q_v1.md"), md, "utf8");
  await saveGraph(graphPath(dir, "q", "v1"), await buildGraphFromMd("q", "v1", path.join(dir, "q_v1.md")));
  const leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "T1.lean"), "-- @node: t1\ntheorem t1_thm : True := by trivial\n", "utf8");
  await provisionLoopEnv(dir);
  return leanDir;
}

const deps = {
  runCodex: (async () => ({ stdout: reviewerOut })) as never,
  runClaude: (async () => reviewerOut) as never,
};

describe("proof-review loop F3.5 unused-hypothesis gate", () => {
  it("a definite-transitive finding blocks completion and escalates to fix-source", async () => {
    const leanDir = await setup();
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      lintUnused: async () => ({ blocking: ["T1.lean:2 t1_thm.hExtra (via bridge_lemma)"], advisory: [] }),
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      expect(outcome.route).toBe("fix-source");
      expect(outcome.phase).toBe("3.5");
      expect(outcome.reason).toContain("F3.5 unused-hypothesis");
    }
  });

  it("advisory-only findings do NOT block — the loop still completes", async () => {
    const leanDir = await setup();
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      lintUnused: async () => ({ blocking: [], advisory: ["T1.lean:2 t1_thm.hMaybe (wildcard may use)"] }),
    });
    expect(outcome.status).toBe("completed");
    const phaseRows = (await readFile(pipelineLogPath(dir, "q", "v1"), "utf8"))
      .trim()
      .split("\n")
      .map((line) => JSON.parse(line) as { stage: string; status: string });
    // The reviewer/filler dispatches now route through the framework dispatch boundary
    // (dispatchAgent/dispatchClaudeAgent), which logs a "dispatch"/"dispatch-complete"
    // pair around each underlying model call in addition to the loop's own per-phase
    // "completed" entries — same calls as before, just newly visible in pipeline.jsonl.
    expect(phaseRows.map((row) => [row.stage, row.status])).toEqual([
      ["2.5", "dispatch"],
      ["2.5", "dispatch-complete"],
      ["2.5", "completed"],
      ["2.5", "dispatch"],
      ["2.5", "dispatch-complete"],
      ["3", "completed"],
      ["3.5", "completed"],
      ["4", "dispatch"],
      ["4", "dispatch-complete"],
      ["4", "dispatch"],
      ["4", "dispatch-complete"],
      ["4", "completed"],
    ]);
  });

  it("the gate runs BEFORE the convergence review (a block pre-empts convergence)", async () => {
    const leanDir = await setup();
    let convergenceRan = false;
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      review: async (s, mode) => {
        if (mode === "convergence") convergenceRan = true;
        return { graph: s.graph, blocking: [], escalate: null } as never;
      },
      lintUnused: async () => ({ blocking: ["T1.lean:2 t1_thm.hExtra (via bridge_lemma)"], advisory: [] }),
    });
    expect(outcome.status).toBe("escalate");
    expect(convergenceRan).toBe(false); // a definite-transitive block short-circuits before F4
  });
});
