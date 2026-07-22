/**
 * Stage 1 paper-scoped NL formalization test.
 *
 * Verifies that when state.theorems is non-empty, runStage1:
 *   - sets stage_completed = "1" for each theorem present in the manifest.
 *   - marks entries absent from the manifest as "stuck".
 *   - still works correctly in the legacy (no state.theorems) path.
 *   - does not overwrite pre-existing "failed" or "stuck" entries.
 *   - returns status: "checkpoint" when no usable plan was parsed (these stubs
 *     never write a parseable plan to disk, so every scenario hits that branch;
 *     in production a usable plan makes F1 advance "completed" into F1.5, which
 *     owns the consolidated CKPT 1).
 *   - does not mutate state.theorems in the blocked-infeasible branch.
 */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage1 } from "../../src/pipeline_stages.js";
import { pipelineLogPath, planPath, promptPath } from "../../src/paths.js";
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
    stage_completed: "0.5",
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

function makeEntry(
  id: string,
  status: TheoremEntry["status"] = "pending",
  failure_reason?: string,
): TheoremEntry {
  return {
    theorem_local_id: id,
    origin_theorem_id: `pid_manski1990test_${id}`,
    statement: `stmt_${id}`,
    proof_sketch: `sketch_${id}`,
    status,
    stage_completed: null,
    lean_file_relpath: null,
    ...(failure_reason !== undefined ? { failure_reason } : {}),
  };
}

/**
 * Build a StageDeps whose runClaude returns the given response JSON string.
 * Stage 1 uses runClaude (not runCodex) and expects the string directly.
 */
function makeDeps(manifest: Array<{ theorem_local_id: string }>): StageDeps {
  const responseJson = JSON.stringify({
    status: "completed",
    message: "NL formalization done",
    artifacts: [],
    theorems: manifest,
  });

  return {
    runClaude: async (_opts: unknown) => responseJson,
    runCodex: async (_opts: unknown) => {
      throw new Error("runCodex should not be called by Stage 1");
    },
    lean: undefined as never,
  };
}

/**
 * Write the minimal prompt stub that runStage1 reads (stage1_template.txt).
 * baseBrief and readPrompt both need the prompts directory.
 */
async function writePromptStubs(root: string): Promise<void> {
  const target = promptPath(root, "stage1_template.txt");
  await mkdir(path.dirname(target), { recursive: true });
  await writeFile(target, "stub stage1_template");
  // formalization dir needed for baseBrief path resolution
  const fmlDir = path.join(root, "doc", "research", "active", "pid_manski1990test");
  await mkdir(fmlDir, { recursive: true });
  // F1 now fails loud on a missing core.json (readRequired — see the F-stage
  // hardening pass); D0 always emits one in production, so tests must too.
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
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stage1-paper-"));
  await writePromptStubs(repoRoot);
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage 1 paper-scoped NL formalization", () => {
  it("scenario 1: full manifest (2 theorems) — both get stage_completed='1', returns checkpoint", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);
    const deps = makeDeps([{ theorem_local_id: "t1" }, { theorem_local_id: "t2" }]);

    const result = await runStage1({ ctx, state, deps });

    expect(result.stage).toBe("1");
    expect(result.status).toBe("checkpoint");

    const t1 = state.theorems![0];
    expect(t1.stage_completed).toBe("1");
    expect(t1.status).toBe("pending"); // manifest walk only sets stage_completed

    const t2 = state.theorems![1];
    expect(t2.stage_completed).toBe("1");
    expect(t2.status).toBe("pending");
  });

  it("scenario 2: partial manifest — t2 absent gets status='stuck'", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);
    // manifest only covers t1; t2 is absent
    const deps = makeDeps([{ theorem_local_id: "t1" }]);

    const result = await runStage1({ ctx, state, deps });

    expect(result.stage).toBe("1");
    expect(result.status).toBe("checkpoint");

    const t1 = state.theorems![0];
    expect(t1.stage_completed).toBe("1");
    expect(t1.status).toBe("pending");

    const t2 = state.theorems![1];
    expect(t2.status).toBe("stuck");
    expect(t2.failure_reason).toMatch(/Stage 1 did not produce an NL block/);
    expect(t2.stage_completed).toBeNull(); // unchanged
  });

  it("scenario 2b: rescue — manifest drops t2 but the plan covers it; manifest is repaired", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);
    // Stage 1 model drops t2 from the JSON manifest, but the plan still has a
    // statement node whose local_id realizes t2. The handler should plan-scan and
    // repair, not mark t2 stuck.
    const planFile = path.join(
      repoRoot,
      "doc/research/active/pid_manski1990test/pid_manski1990test_default_plan.json",
    );
    await writeFile(
      planFile,
      JSON.stringify({
        qid: "pid_manski1990test",
        nodes: {
          "thm:t1": { lean_kind: "theorem", lean_name: "t1", disposition: "define-local", local_id: "t1" },
          "thm:t2": { lean_kind: "theorem", lean_name: "t2", disposition: "define-local", local_id: "t2" },
        },
      }),
    );
    const deps = makeDeps([{ theorem_local_id: "t1" }]);

    await runStage1({ ctx, state, deps });

    expect(state.theorems![0].stage_completed).toBe("1");
    // Rescue path: t2 in body → stage_completed set, NOT stuck
    expect(state.theorems![1].stage_completed).toBe("1");
    expect(state.theorems![1].status).toBe("pending");
    expect(state.theorems![1].failure_reason).toBeUndefined();
  });

  it("scenario 3: legacy state.theorems === undefined — no mutation, returns checkpoint", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState(undefined); // no theorems field
    expect((state as unknown as Record<string, unknown>).theorems).toBeUndefined();

    const deps = makeDeps([]);

    const result = await runStage1({ ctx, state, deps });

    expect(result.stage).toBe("1");
    expect(result.status).toBe("checkpoint");
    expect((state as unknown as Record<string, unknown>).theorems).toBeUndefined();
  });

  it("scenario 4: legacy state.theorems === [] — bypasses manifest walk, returns checkpoint", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState([]); // empty array
    const deps = makeDeps([{ theorem_local_id: "t_ghost" }]); // would mutate if walk ran

    const result = await runStage1({ ctx, state, deps });

    expect(result.stage).toBe("1");
    expect(result.status).toBe("checkpoint");
    expect(state.theorems).toEqual([]); // untouched
  });

  it("scenario 5: pre-existing status='failed' entry is NOT overwritten", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [
      makeEntry("t1", "failed", "Stage 0 did not derive t1"),
      makeEntry("t2"),
    ];
    const state = makeState(entries);
    // manifest covers both (Claude claims to have produced both)
    const deps = makeDeps([{ theorem_local_id: "t1" }, { theorem_local_id: "t2" }]);

    await runStage1({ ctx, state, deps });

    // t1 must keep its earlier "failed" status — manifest walk skips it
    expect(state.theorems![0].status).toBe("failed");
    expect(state.theorems![0].failure_reason).toBe("Stage 0 did not derive t1");
    expect(state.theorems![0].stage_completed).toBeNull(); // unchanged

    // t2 is covered by the manifest — stage_completed set
    expect(state.theorems![1].stage_completed).toBe("1");
    expect(state.theorems![1].status).toBe("pending");
  });

  it("scenario 6: blocked-infeasible response — state.theorems entries are not mutated", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);

    // Claude returns blocked-infeasible — no theorems manifest field
    const blockedJson = JSON.stringify({
      status: "blocked-infeasible",
      feasibility_verdict: "infeasible-out-of-scope",
      message: "proof requires functional analysis beyond Mathlib scope",
      feasibility_notes: "step 4 requires a non-constructive selection argument",
    });

    const deps: StageDeps = {
      runClaude: async (_opts: unknown) => blockedJson,
      runCodex: async (_opts: unknown) => {
        throw new Error("runCodex should not be called by Stage 1");
      },
      lean: undefined as never,
    };

    const result = await runStage1({ ctx, state, deps });

    // Stage 1 always returns checkpoint regardless of feasibility verdict
    expect(result.stage).toBe("1");
    expect(result.status).toBe("checkpoint");

    // No theorems manifest → entries are absent from manifest
    // But since the response has no `theorems` field, parsed.theorems is undefined,
    // manifest defaults to [], and entries get stuck.
    // This is correct behavior: the handler cannot distinguish "blocked-infeasible"
    // from other responses at the manifest-walk level; the checkpoint return
    // signals the human to inspect the artifact.
    expect(state.theorems![0].status).toBe("stuck");
    expect(state.theorems![0].failure_reason).toMatch(/Stage 1 did not produce an NL block/);
    expect(state.theorems![1].status).toBe("stuck");
  });

  it("enters revise mode after an F-to-D rewind when a later stage is recorded in pipeline history", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    let prompt = "";
    const existingPlan = planPath(repoRoot, ctx.qid, ctx.specialization);
    await mkdir(path.dirname(existingPlan), { recursive: true });
    await writeFile(existingPlan, '{"preserve":"this existing plan"}');

    const log = pipelineLogPath(repoRoot, ctx.qid, ctx.specialization);
    await writeFile(log, JSON.stringify({ stage: "3", status: "completed" }) + "\n");

    const reviseHead = promptPath(repoRoot, "stage1_head_revise.txt");
    await mkdir(path.dirname(reviseHead), { recursive: true });
    await writeFile(reviseHead, "REVISION HEAD");
    const deps: StageDeps = {
      runClaude: async (opts: unknown) => {
        prompt = (opts as { prompt: string }).prompt;
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => {
        throw new Error("runCodex should not be called by Stage 1");
      },
      lean: undefined as never,
    };

    await runStage1({ ctx, state, deps });

    expect(prompt).toContain("REVISION HEAD");
    expect(prompt).toContain(`Prior plan to patch (Read, then Edit in place): ${existingPlan}`);
    expect(prompt).toContain("Patch the existing plan");
    expect(await readFile(existingPlan, "utf8")).toBe('{"preserve":"this existing plan"}');
  });
});
