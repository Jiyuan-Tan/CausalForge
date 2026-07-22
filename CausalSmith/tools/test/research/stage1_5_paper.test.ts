/**
 * Stage 1.5 paper-scoped per-theorem review propagation tests.
 *
 * Verifies that when state.theorems is non-empty, runStage1_5:
 *   1. All theorems pass: state.theorems entries unchanged (no mutation on pass).
 *   2. One theorem fails: entry gets status="stuck" and failure_reason set.
 *   3. Legacy (state.theorems undefined): no propagation, no crash.
 *   4. Legacy (state.theorems empty []): no propagation, no crash.
 *   5. Pre-existing "failed" entry preserved when reviewer says pass.
 */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage1_5 } from "../../src/pipeline_stages.js";
import { promptPath, planPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { TheoremEntry } from "../../src/shared/paper_batch_types.js";

let repoRoot: string;

function makeCtx(root: string): PipelineContext {
  return {
    repoRoot: root,
    qid: "pid_manski1990test",
    specialization: "default",
    dryRun: false,
    resume: false,
  };
}

function makeState(theorems?: TheoremEntry[]): StateJson {
  const base: Record<string, unknown> = {
    stage_completed: "1",
    lean_subdir: "CausalSmith/PartialID/PidManski1990Test",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: {
      rewound_from_stage0: null,
      rewound_from_stage4d: null,
      local_fix_from_4d: false,
      missing_architecture: false,
    },
  };
  if (theorems !== undefined) base.theorems = theorems;
  return base as unknown as StateJson;
}

function makeEntry(id: string, status: TheoremEntry["status"] = "pending", failure_reason?: string): TheoremEntry {
  return {
    theorem_local_id: id,
    origin_theorem_id: `pid_manski1990test_${id}`,
    statement: `stmt_${id}`,
    proof_sketch: `sketch_${id}`,
    status,
    stage_completed: "1",
    lean_file_relpath: null,
    ...(failure_reason !== undefined ? { failure_reason } : {}),
  };
}

/**
 * Build StageDeps whose runCodex returns the given review JSON.
 * Stage 1.5 reviewer uses runCodex; intervention judge uses runClaude.
 * We stub runClaude to return route=user so the boundary halts at "checkpoint".
 */
function makeDeps(reviewJson: Record<string, unknown>): StageDeps {
  const interventionJson = JSON.stringify({
    route: "user",
    reason: "test stub — escalate to user",
    proposed_action: "manual review required",
  });
  return {
    runCodex: async (_opts: unknown) => ({
      stdout: JSON.stringify(reviewJson),
      stderr: "",
    }),
    runClaude: async (_opts: unknown) => interventionJson,
    lean: undefined as never,
  };
}

/**
 * Build StageDeps for the "reject then pass" scenario.
 * Call sequence inside runReviewBoundary(cap=1):
 *   call 1 (runCodex) → reviewer → returns rejectJson
 *   [boundary dispatches Stage 1 producer via runClaude with a checkpoint-style result]
 *   BUT cap=1 means after one rejection the boundary immediately escalates to intervention.
 * So for per-theorem failure propagation, we only need to observe the FIRST reviewer call.
 *
 * To make the reject path result in "checkpoint" (not an infinite loop), we stub
 * runClaude for the intervention to return route=user.
 */
function makeRejectDeps(args: {
  rejectJson: Record<string, unknown>;
}): StageDeps {
  // Stage 1 producer (runClaude) returns a stage-output JSON
  const stage1Json = JSON.stringify({
    status: "completed",
    message: "stage 1 retry ok",
    artifacts: [],
    theorems: [{ theorem_local_id: "t1" }, { theorem_local_id: "t2" }],
  });
  // Intervention judge (runClaude) returns route=user
  const interventionJson = JSON.stringify({
    route: "user",
    reason: "test stub — escalate to user",
    proposed_action: "manual review required",
  });

  let claudeCallCount = 0;
  return {
    runCodex: async (_opts: unknown) => ({
      stdout: JSON.stringify(args.rejectJson),
      stderr: "",
    }),
    runClaude: async (_opts: unknown) => {
      claudeCallCount++;
      // First call: Stage 1 producer retry
      if (claudeCallCount === 1) return stage1Json;
      // Subsequent: intervention judge
      return interventionJson;
    },
    lean: undefined as never,
  };
}

/**
 * Write minimal prompt stubs needed by runStage1_5 and its producer (runStage1).
 */
async function writePromptStubs(root: string): Promise<void> {
  const stubPrompt = async (name: string, body: string) => {
    const target = promptPath(root, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, body);
  };

  await stubPrompt("stage1_5_reuse_soundness.txt", "stub stage1_5_reuse_soundness");
  await stubPrompt("stage1_template.txt", "stub stage1_template");
  await stubPrompt("intervention.txt", "stub intervention");

  // formalization dir for appendReview + baseBrief
  const fmlDir = path.join(root, "doc", "research", "active", "pid_manski1990test");
  await mkdir(fmlDir, { recursive: true });
  // F1.5's plan-gate prelint and F1 (its producer on a revise loop) now fail loud
  // on a missing core.json (readRequired — see the F-stage hardening pass); D0
  // always emits one in production, so tests must too.
  const coreDir = path.join(fmlDir, "discovery");
  await mkdir(coreDir, { recursive: true });
  await writeFile(
    path.join(coreDir, "core.json"),
    JSON.stringify({
      qid: "pid_manski1990test",
      symbols: [],
      assumptions: [],
      statements: [],
      target_estimand: "stub target estimand",
    }),
  );
  // The gate now actually RUNS against a real core.json (previously it no-op'd
  // whenever core.json was absent). Pair it with a gate-clean empty plan.json —
  // an empty core has no nodes to cover, so an empty plan gates ok:true — so the
  // pre-lint passes through to the LLM reviewer these tests are exercising.
  const plan = planPath(root, "pid_manski1990test", "default");
  await mkdir(path.dirname(plan), { recursive: true });
  await writeFile(plan, JSON.stringify({ qid: "pid_manski1990test", nodes: {} }));
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stage15-paper-"));
  await writePromptStubs(repoRoot);
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage 1.5 paper-scoped per-theorem verdict propagation", () => {
  it("scenario 1: all theorems pass — state.theorems entries are unchanged", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);

    const reviewJson = {
      status: "pass",
      notes: "both NL artifacts pass all F-Q-P-H-N-L-X checks",
      theorems_review: [
        { theorem_local_id: "t1", verdict: "pass" },
        { theorem_local_id: "t2", verdict: "pass" },
      ],
    };
    const deps = makeDeps(reviewJson);

    const result = await runStage1_5({ ctx, state, deps });

    expect(result.stage).toBe("1.5");
    // A PASS halts at the consolidated CKPT 1 (checkpointOnPass) — the
    // orchestrator audits the settled F1 plan + F1.5 reuse review before F2.
    expect(result.status).toBe("checkpoint");

    expect(state.theorems![0].status).toBe("pending");
    expect(state.theorems![0].failure_reason).toBeUndefined();
    expect(state.theorems![1].status).toBe("pending");
    expect(state.theorems![1].failure_reason).toBeUndefined();
  });

  it("scenario 2: one theorem fails — stuck status and failure_reason set", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);

    // Reviewer rejects; cap=1 → boundary escalates to intervention immediately.
    const rejectJson = {
      status: "reject",
      classification: "F",
      perItemFindings: [
        { label: "T2", verdict: "FLAG-F", one_line: "t2 T-block missing positivity assumption" },
      ],
      verbatim_critique: "T-block for t2 omits H_pos from .tex line 42.",
      theorems_review: [
        { theorem_local_id: "t1", verdict: "pass" },
        {
          theorem_local_id: "t2",
          verdict: "fail",
          findings: [{ one_line: "t2 T-block missing positivity assumption" }],
        },
      ],
    };
    const deps = makeRejectDeps({ rejectJson });

    const result = await runStage1_5({ ctx, state, deps });

    // Boundary cap=1; after one rejection, intervention routes to user → checkpoint
    expect(result.stage).toBe("1.5");
    expect(["checkpoint", "completed"]).toContain(result.status);

    // t1 untouched (pass)
    expect(state.theorems![0].status).toBe("pending");
    expect(state.theorems![0].failure_reason).toBeUndefined();

    // t2 marked stuck by first (and only) reviewer call
    expect(state.theorems![1].status).toBe("stuck");
    expect(state.theorems![1].failure_reason).toMatch(/t2 T-block missing positivity/);
  });

  it("scenario 3: legacy (state.theorems undefined) — no propagation, no crash", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState(undefined);
    expect((state as unknown as Record<string, unknown>).theorems).toBeUndefined();

    const reviewJson = {
      status: "pass",
      notes: "single-theorem legacy run",
    };
    const deps = makeDeps(reviewJson);

    const result = await runStage1_5({ ctx, state, deps });

    expect(result.stage).toBe("1.5");
    expect(result.status).toBe("checkpoint");
    expect((state as unknown as Record<string, unknown>).theorems).toBeUndefined();
  });

  it("scenario 4: legacy (state.theorems empty []) — bypasses propagation, no crash", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState([]);

    const reviewJson = {
      status: "pass",
      notes: "empty theorems array",
      theorems_review: [{ theorem_local_id: "ghost", verdict: "fail", findings: [{ one_line: "ghost" }] }],
    };
    const deps = makeDeps(reviewJson);

    const result = await runStage1_5({ ctx, state, deps });

    expect(result.stage).toBe("1.5");
    expect(result.status).toBe("checkpoint");
    expect(state.theorems).toEqual([]);
  });

  it("scenario 5: pre-existing 'failed' entry preserved when reviewer says pass", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [
      makeEntry("t1", "failed", "Stage 1 did not produce NL block for t1"),
      makeEntry("t2"),
    ];
    const state = makeState(entries);

    const reviewJson = {
      status: "pass",
      notes: "t2 passes; t1 already handled upstream",
      theorems_review: [
        { theorem_local_id: "t1", verdict: "pass" },
        { theorem_local_id: "t2", verdict: "pass" },
      ],
    };
    const deps = makeDeps(reviewJson);

    await runStage1_5({ ctx, state, deps });

    // t1 must keep its earlier "failed" status
    expect(state.theorems![0].status).toBe("failed");
    expect(state.theorems![0].failure_reason).toBe("Stage 1 did not produce NL block for t1");

    // t2 untouched (pass verdict)
    expect(state.theorems![1].status).toBe("pending");
    expect(state.theorems![1].failure_reason).toBeUndefined();
  });
});
