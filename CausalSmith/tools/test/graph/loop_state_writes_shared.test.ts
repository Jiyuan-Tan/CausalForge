import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { graphPath, saveGraph } from "../../src/graph/store.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { provisionLoopEnv } from "./loop_test_env.js";
import { saveState, createInitialState } from "../../src/state.js";

// REGRESSION: `pipeline.ts` loads state ONCE at run start and re-saves that same in-memory object
// after each stage. The loop wrote `proof_loop_counters` / `cited_checks` straight to disk via its
// own loadState→saveState, so the pipeline's stale copy CLOBBERED them (last-writer-wins,
// deterministic — not a race). Effects: the iteration caps became inert (every resume got a fresh
// budget → unbounded re-rolls) and `cited_checks: []` defeated bankEntry's cited-mismatch refusal.
// Fix: the loop must ALSO write into the SHARED state object the pipeline will save.
let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "loop-shared-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const driftOut = JSON.stringify({
  status: "ok",
  statement_verdicts: [{ obj_id: "t1", verdict: "scaffold-mismatch", note: "drifted" }],
  assumption_verdicts: [],
  substrate_gates: [],
  escalate: { kind: "scaffold-mismatch", reason: "t1 drifted", targets: ["t1"] },
});

async function setup() {
  const md = "### T-block: t1 — Rate theorem\n**Statement.** the rate bound holds.\n";
  await writeFile(path.join(dir, "q_v1.md"), md, "utf8");
  await saveGraph(graphPath(dir, "q", "v1"), await buildGraphFromMd("q", "v1", path.join(dir, "q_v1.md")));
  const leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "T1.lean"), "-- @node: t1\ntheorem t1_thm : True := by trivial\n", "utf8");
  await saveState(dir, "q", "v1", createInitialState("q"));
  await provisionLoopEnv(dir);
  return leanDir;
}

const deps = {
  runCodex: (async () => ({ stdout: driftOut })) as never,
  runClaude: (async () => driftOut) as never,
};

describe("the loop writes its state onto the SHARED object, so the pipeline cannot clobber it", () => {
  it("iteration counters land on the shared state the pipeline will re-save", async () => {
    const leanDir = await setup();
    const shared = createInitialState("q"); // the object pipeline.ts holds and later saves

    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps,
      state: shared,
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      scaffold: async () => {},
      buildCheck: async () => ({ ok: true, errors: "" }),
    });
    expect(outcome.status).toBe("escalate");

    // Were the loop's writes visible on the SHARED object? If not, pipeline.ts's stale re-save
    // silently erases them and the caps are inert.
    expect(shared.flags.proof_loop_counters).toBeDefined();
    expect(shared.flags.proof_loop_counters?.scaffold_rounds ?? 0).toBeGreaterThan(0);
    expect(shared.flags.proof_loop_cap_hit).toBeTruthy();
  });
});
