import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { graphPath, saveGraph } from "../../src/graph/store.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { provisionLoopEnv } from "./loop_test_env.js";
import { createInitialState } from "../../src/state.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "loop-build-")); });
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
  // NB: sorry-free TEXT, but the build gate is what decides whether it compiles.
  await writeFile(path.join(leanDir, "T1.lean"), "-- @node: t1\ntheorem t1_thm : True := by trivial\n", "utf8");
  await provisionLoopEnv(dir);
  return leanDir;
}

const deps = {
  runCodex: (async () => ({ stdout: reviewerOut })) as never,
  runClaude: (async () => reviewerOut) as never,
};

describe("proof-review loop: the tree must COMPILE before the loop can complete", () => {
  it("routes a RED lake build back to F3 with diagnostics and completes after the repair", async () => {
    const leanDir = await setup();
    let builds = 0;
    let repairDirective = "";
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps,
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      buildCheck: async () => ++builds === 1
        ? { ok: false, errors: "ZariskiLocus.lean:142: 'change' tactic failed" }
        : { ok: true, errors: "" },
      fill: async (graph, directive) => {
        repairDirective = directive ?? "";
        return { graph, escalate: null, summary: "fixed compile error" };
      },
    });
    expect(outcome.status).toBe("completed");
    expect(builds).toBe(2);
    expect(repairDirective).toContain("F3 LOCAL COMPILE REPAIR");
    expect(repairDirective).toContain("ZariskiLocus.lean:142");
  });

  it("a GREEN lake build lets the loop complete", async () => {
    const leanDir = await setup();
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps,
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      buildCheck: async () => ({ ok: true, errors: "" }),
    });
    expect(outcome.status).toBe("completed");
  });

  it("caps repeated identical build failures without running F3.5 or F4 on a red tree", async () => {
    const leanDir = await setup();
    let convergenceRan = false;
    let lintRan = false;
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
      deps,
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      review: async (s, mode) => {
        if (mode === "convergence") convergenceRan = true;
        return { graph: s.graph, blocking: [], escalate: null } as never;
      },
      lintUnused: async () => { lintRan = true; return { blocking: [], advisory: [] }; },
      buildCheck: async () => ({ ok: false, errors: "GenericSlopes.lean:25: apply failed" }),
      fill: async (graph) => ({ graph, escalate: null, summary: "no repair progress" }),
      noProgressK: 2,
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      expect(outcome.route).toBe("bank-partial");
      expect(outcome.reason).toContain("identically red");
    }
    expect(lintRan).toBe(false);        // F3.5 must not lint a non-compiling tree
    expect(convergenceRan).toBe(false); // F4 must not certify a non-compiling tree
  });

  // REGRESSION (2026-07-21 audit): the identically-red comparand was an in-process local, so
  // every `--resume` reset `stale` to 0 and refunded the circuit breaker a full fresh budget —
  // exactly the resume-reset class the persisted proof_loop_counters exist to stop. The
  // signature must persist WITH `stale`, so a resumed loop continues the count.
  it("the identically-red no-progress cap survives a resume (persisted build-error signature)", async () => {
    const leanDir = await setup();
    const shared = createInitialState("q"); // the shared object a resume would re-seed from
    let builds = 0;
    const run = () =>
      runProofReviewLoop({
        ctx: { repoRoot: dir, qid: "q", specialization: "v1" },
        deps,
        state: shared,
        formalizationDir: dir,
        leanDir,
        corePath: path.join(dir, "core.json"),
        review: async (s) => ({ graph: s.graph, blocking: [], escalate: null }) as never,
        lintUnused: async () => ({ blocking: [], advisory: [] }),
        buildCheck: async () => { builds++; return { ok: false, errors: "GenericSlopes.lean:25: apply failed" }; },
        fill: async (graph) => ({ graph, escalate: null, summary: "no repair progress" }),
        noProgressK: 3,
      });

    const first = await run();
    expect(first.status).toBe("escalate");
    const firstBuilds = builds;
    expect(firstBuilds).toBeGreaterThan(1); // fresh budget: several rounds before the cap

    // "Resume": same shared state, same red error. The persisted signature + stale count must
    // trip the cap on the FIRST build, not re-run the whole budget.
    builds = 0;
    const second = await run();
    expect(second.status).toBe("escalate");
    if (second.status === "escalate") expect(second.route).toBe("bank-partial");
    expect(builds).toBe(1);
  });
});
