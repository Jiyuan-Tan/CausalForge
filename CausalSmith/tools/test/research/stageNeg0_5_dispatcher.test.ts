/**
 * Stage -0.5 kernel-replace dispatcher unit test.
 *
 * Two scenarios:
 *   (A) Cold-start v1 → reviewer REJECT with C-definitional-unfold flag
 *       → dispatcher MUST set current_mode="kernel-replace", append 0 to
 *         kernel_replace_used_angles, call runStageNeg1_2, and NOT pivot.
 *   (B) After kernel-replace already used on angle 0, reviewer REJECT with
 *       same flag → dispatcher MUST fall through to the REJECT branch and
 *       pivot (current_angle_index advances, exhausted_angles records 0).
 *
 * The whole point is to prove that the hoisted dispatcher fires on REJECT
 * (not just REVISE) and respects the once-per-angle cap. No Codex calls.
 */
import { describe, it, expect, beforeEach, afterEach, vi } from "vitest";
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { promptPath } from "../../src/paths.js";
import { loadState, saveState } from "../../src/state.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";

// Mock the runStageNeg1_2 producer. We capture every call but do not run
// any real producer logic. The mock must populate last_draft_handoff and
// bump current_version so the producer-first guard does not re-fire and the
// outer loop converges.
const runStageNeg1_2Calls: Array<{ mode: string | undefined; version: number | undefined }> = [];
vi.mock("../../src/discovery/stages/neg1_2.js", async () => {
  const actual = await vi.importActual<typeof import("../../src/discovery/stages/neg1_2.js")>(
    "../../src/discovery/stages/neg1_2.js",
  );
  return {
    ...actual,
    runStageNeg1_2: vi.fn(async (args: { state: StateJson }) => {
      const pf = args.state.proposed_from!;
      runStageNeg1_2Calls.push({
        mode: pf.current_mode as string | undefined,
        version: pf.current_version,
      });
      // Simulate what a real producer would set so the outer loop advances.
      pf.current_version = (pf.current_version ?? 0) + 1;
      pf.last_draft_handoff = JSON.stringify({ status: "completed", mode: pf.current_mode });
      pf.last_draft_status = "completed";
      return { stage: "-1.2", status: "completed", message: "mock producer" };
    }),
  };
});

// Import the unit under test AFTER vi.mock so the mocked runStageNeg1_2
// import is the one used by stageNeg0_5. With vitest's `--no-isolate`
// mode (used by `npm test` to share workers), the underlying module
// graph may have already cached the real stageNeg1_2 module from a
// sibling test file — in that case vi.mock's factory never runs and
// stageNeg0_5 calls the real producer (which then misses prompt
// fixtures and throws). Reset module state so the import below
// re-evaluates with the mock applied.
vi.resetModules();
const { runStageNeg0_5 } = await import("../../src/discovery/stages/neg0_5.js");
const { NEG1_ENV_FAILURE_RETRY_BUDGET } = await import("../../src/discovery/stages/neg1_2.js");

let repoRoot: string;

function makeCtx(root: string): PipelineContext {
  return {
    repoRoot: root,
    qid: "eid_dispatcher_test",
    specialization: "v1",
    dryRun: false,
    resume: false,
    proposeTopic: "test topic for dispatcher unit test",
    noveltyTarget: "flagship",
  } as PipelineContext;
}

function makeState(overrides: Partial<NonNullable<StateJson["proposed_from"]>> = {}): StateJson {
  const base: Record<string, unknown> = {
    stage_completed: "-1.2",
    lean_subdir: "CausalSmith/ExactID/EID_DispatcherTest",
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
      scaffold_redirect: null,
      scaffold_redirect_count: 0,
    },
    proposed_from: {
      topic: "test topic",
      novelty_target: "flagship",
      pivot_budget_used: 0,
      final_verdict: "pending",
      proposal_path: path.join(
        repoRoot,
        "doc",
        "formalization",
        "research",
        "eid_dispatcher_test",
        "eid_dispatcher_test_v1_proposal.tex",
      ),
      novelty_justification: "test",
      chosen_qid: "eid_dispatcher_test",
      chosen_specialization: "v1",
      seed_list: ["seed a", "seed b", "seed c"],
      current_angle_index: 0,
      current_version: 1,
      current_mode: "cold-start",
      exhausted_angles: [],
      iterations: [],
      archived_proposals: [],
      last_draft_handoff: JSON.stringify({ status: "completed", mode: "cold-start" }),
      last_draft_status: "completed",
      last_reviewer_verdict: "",
      ...overrides,
    },
  };
  return base as unknown as StateJson;
}

// Reviewer returns REJECT @ field with a kernel-level C-definitional-unfold
// flag, then ACCEPT on any subsequent call so the loop terminates.
function makeDeps(reviewerSequence: Array<Record<string, unknown>>): StageDeps {
  let callIndex = 0;
  return {
    runCodex: async () => {
      const json = reviewerSequence[Math.min(callIndex, reviewerSequence.length - 1)];
      callIndex += 1;
      return { stdout: JSON.stringify(json), stderr: "", exitCode: 0 } as never;
    },
    runClaude: async () => {
      throw new Error("runClaude should not be called by Stage -0.5");
    },
    lean: undefined as never,
  } as unknown as StageDeps;
}

async function writeFixtures(root: string, qid: string, spec: string): Promise<void> {
  // Prompts that runStageNeg0_5 reads on entry.
  for (const name of [
    "stage_neg1_review.txt",
    "stage_neg1_review_core.txt",
    "stage_neg1_review_upgrade_directive.txt",
    "stage_flagship_rubric.txt",
  ]) {
    const p = promptPath(root, name);
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, `stub ${name}`);
  }
  // Output-JSON template the reviewer dispatcher copies into the qid folder
  // before invoking runNeg1Review. Minimal stub — the test's mocked runCodex
  // never reads it, but renderNeg1ReviewOutputTemplate reads it to render.
  const tmplPath = path.join(
    root,
    "tools",
    "src",
    "templates",
    "stage_neg1_review_output_template.json",
  );
  await mkdir(path.dirname(tmplPath), { recursive: true });
  await writeFile(tmplPath, "{}\n");
  // Proposal .tex that the reviewer reads.
  const fmlDir = path.join(root, "doc", "research", "active", qid);
  await mkdir(fmlDir, { recursive: true });
  await writeFile(path.join(fmlDir, `${qid}_${spec}_proposal.tex`), "stub proposal");
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stageneg05-dispatcher-"));
  await writeFixtures(repoRoot, "eid_dispatcher_test", "v1");
  runStageNeg1_2Calls.length = 0;
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

const rejectWithKernelFlag = {
  verdict: "REJECT",
  publishability_tier: "field",
  per_theorem_calls: [],
  structure_flags: [],
  novelty_flags: [],
  soundness_flags: [
    {
      label: "Conjecture 1",
      code: "C-definitional-unfold",
      one_line: "iff unfolds definitions",
    },
  ],
  strengthening_paths: [],
  recommended_next_step: "Reject this version.",
};

const acceptVerdict = {
  verdict: "ACCEPT",
  publishability_tier: "flagship",
  per_theorem_calls: [],
  structure_flags: [],
  novelty_flags: [],
  soundness_flags: [],
  strengthening_paths: [],
  recommended_next_step: "Accept.",
};

const reviseVerdict = {
  verdict: "REVISE",
  publishability_tier: "flagship",
  per_theorem_calls: [],
  structure_flags: [],
  novelty_flags: [],
  soundness_flags: [
    { label: "Conjecture 1", code: "C-wellposed", one_line: "Define the sample law explicitly." },
  ],
  strengthening_paths: [],
  recommended_next_step: "Revise this angle.",
};

const rejectWithBrokenDraftFlags = {
  verdict: "REJECT",
  publishability_tier: "field",
  per_theorem_calls: [],
  structure_flags: [],
  // 1× N-promissory + 1× C-sanity = 2 draft-broken flags (threshold is ≥2),
  // and NO kernel-level flag — exactly the draft-rebuild trigger pattern.
  novelty_flags: [
    {
      label: "Theorem 1",
      code: "N-promissory-object",
      one_line: "Exhibit doesn't compute the focal object from primitives.",
    },
  ],
  soundness_flags: [
    {
      label: "Theorem 1",
      code: "C-sanity",
      one_line: "Arithmetic in Exhibit 9.1 doesn't recompute; λ* = 20/7 is wrong.",
    },
  ],
  strengthening_paths: [],
  recommended_next_step: "Reject; rebuild witness from primitives.",
};

describe("Stage -0.5 kernel-replace dispatcher", () => {
  it("halts after REVISE before starting the next proposer", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const result = await runStageNeg0_5({ ctx, state, deps: makeDeps([reviseVerdict]) });

    expect(result.status).toBe("checkpoint");
    expect(state.proposed_from!.angle_checkpoint).toMatchObject({
      kind: "revise", angle: 0, version: 1, verdict: "REVISE",
    });
    expect(runStageNeg1_2Calls).toEqual([]);
  });

  it("persists a nested proposer result before dispatching its reviewer", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState({
      current_mode: "revise",
      last_draft_handoff: undefined,
    });
    await saveState(repoRoot, ctx.qid, ctx.specialization, state);
    const deps = makeDeps([acceptVerdict]);
    deps.runCodex = async () => { throw new Error("simulated reviewer crash"); };

    await expect(runStageNeg0_5({ ctx, state, deps })).rejects.toThrow(/simulated reviewer crash/);

    const onDisk = await loadState(repoRoot, ctx.qid, ctx.specialization);
    expect(onDisk.proposed_from!.current_version).toBe(2);
    expect(onDisk.proposed_from!.last_draft_handoff).toContain("completed");
  });

  it("scenario A: REJECT + C-definitional-unfold on cold-start v1 routes to kernel-replace, NOT pivot", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    // First reviewer call: REJECT with kernel-level flag.
    // Second reviewer call (after kernel-replace producer ran): ACCEPT, to terminate.
    const deps = makeDeps([rejectWithKernelFlag, acceptVerdict]);

    await runStageNeg0_5({ ctx, state, deps });

    const pf = state.proposed_from!;
    // Dispatcher fired exactly once on angle 0.
    expect(pf.kernel_replace_used_angles).toEqual([0]);
    // Angle did NOT advance (no pivot).
    expect(pf.current_angle_index).toBe(0);
    expect(pf.exhausted_angles).toEqual([]);
    // runStageNeg1_2 was called with mode=kernel-replace at least once.
    const kernelReplaceCalls = runStageNeg1_2Calls.filter((c) => c.mode === "kernel-replace");
    expect(kernelReplaceCalls.length).toBeGreaterThanOrEqual(1);
    // Iterations recorded the v1 REJECT.
    expect(pf.iterations?.some((it) => it.angle === 0 && it.verdict === "REJECT")).toBe(true);
    // Final verdict is ACCEPT (from the second reviewer call after kernel-replace).
    expect(pf.final_verdict).toBe("ACCEPT");
  });

  it("scenario B: REJECT after kernel-replace is exhausted halts at an angle-boundary checkpoint", async () => {
    const ctx = makeCtx(repoRoot);
    // State: angle 0 already burned its kernel-replace. Another REJECT
    // with the same flag should NOT re-fire the dispatcher.
    const state = makeState({
      current_version: 2,
      current_mode: "kernel-replace",
      kernel_replace_used_angles: [0],
      iterations: [
        { angle: 0, version: 1, mode: "cold-start", verdict: "REJECT", tier: "field" },
      ],
    });
    // The reviewer rejects; no new-angle producer may start before the CLI
    // resolves the persisted angle-boundary checkpoint.
    const deps = makeDeps([rejectWithKernelFlag, acceptVerdict]);

    await runStageNeg0_5({ ctx, state, deps });

    const pf = state.proposed_from!;
    // Dispatcher did NOT fire again — array unchanged.
    expect(pf.kernel_replace_used_angles).toEqual([0]);
    expect(pf.current_angle_index).toBe(0);
    expect(pf.exhausted_angles).toEqual([]);
    expect(pf.angle_checkpoint).toMatchObject({ kind: "angle-boundary", angle: 0, verdict: "REJECT" });
  });

  it("scenario C: REJECT + 2× draft-broken flags (no kernel flag) routes to draft-rebuild, NOT pivot", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    // First reviewer call: REJECT with N-promissory-object + C-sanity (no kernel-level flag).
    // Second reviewer call (after draft-rebuild ran): ACCEPT.
    const deps = makeDeps([rejectWithBrokenDraftFlags, acceptVerdict]);

    await runStageNeg0_5({ ctx, state, deps });

    const pf = state.proposed_from!;
    // Draft-rebuild dispatcher fired exactly once on angle 0.
    expect(pf.draft_rebuild_used_angles).toEqual([0]);
    // Kernel-replace did NOT fire (no kernel-level flag).
    expect(pf.kernel_replace_used_angles ?? []).toEqual([]);
    // Angle did NOT advance.
    expect(pf.current_angle_index).toBe(0);
    expect(pf.exhausted_angles).toEqual([]);
    // runStageNeg1_2 was called with mode=draft-rebuild at least once.
    const draftRebuildCalls = runStageNeg1_2Calls.filter((c) => c.mode === "draft-rebuild");
    expect(draftRebuildCalls.length).toBeGreaterThanOrEqual(1);
    expect(pf.final_verdict).toBe("ACCEPT");
  });

  it("scenario D: REJECT after draft-rebuild is exhausted halts before pivot", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState({
      current_version: 2,
      current_mode: "draft-rebuild",
      draft_rebuild_used_angles: [0],
      iterations: [
        { angle: 0, version: 1, mode: "cold-start", verdict: "REJECT", tier: "field" },
      ],
    });
    const deps = makeDeps([rejectWithBrokenDraftFlags, acceptVerdict]);

    await runStageNeg0_5({ ctx, state, deps });

    const pf = state.proposed_from!;
    // Draft-rebuild did NOT fire again.
    expect(pf.draft_rebuild_used_angles).toEqual([0]);
    expect(pf.current_angle_index).toBe(0);
    expect(pf.exhausted_angles).toEqual([]);
    expect(pf.angle_checkpoint).toMatchObject({ kind: "angle-boundary", angle: 0, verdict: "REJECT" });
  });

  it("scenario E: kernel-level flag wins over draft-broken flags when both are present (kernel-replace fires, not draft-rebuild)", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    // Reviewer returns both C-definitional-unfold AND C-sanity + N-promissory.
    // Dispatcher placement (kernel-replace before draft-rebuild) means kernel-replace wins.
    const mixedVerdict = {
      ...rejectWithBrokenDraftFlags,
      soundness_flags: [
        ...rejectWithBrokenDraftFlags.soundness_flags,
        { label: "Conjecture 1", code: "C-definitional-unfold", one_line: "iff unfolds defs." },
      ],
    };
    const deps = makeDeps([mixedVerdict, acceptVerdict]);

    await runStageNeg0_5({ ctx, state, deps });

    const pf = state.proposed_from!;
    expect(pf.kernel_replace_used_angles).toEqual([0]);
    expect(pf.draft_rebuild_used_angles ?? []).toEqual([]); // NOT consumed
  });

  it("scenario F: ACCEPT preserves proto-core proposal_path when the single artifact exists", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const corePath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(corePath), { recursive: true });
    await writeFile(corePath, JSON.stringify({ schema_version: 1, qid: ctx.qid }), "utf8");

    await runStageNeg0_5({ ctx, state, deps: makeDeps([acceptVerdict]) });

    expect(state.proposed_from!.final_verdict).toBe("ACCEPT");
    expect(state.proposed_from!.proposal_path).toBe(corePath);
  });

  it("scenario G: reviewer prompt names the proto core, never a stale legacy .tex", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const corePath = protoCoreJsonPath(ctx);
    await mkdir(path.dirname(corePath), { recursive: true });
    await writeFile(corePath, JSON.stringify({ schema_version: 1, qid: ctx.qid }), "utf8");

    const legacyTex = path.join(
      repoRoot,
      "doc",
      "research",
      "active",
      ctx.qid,
      `${ctx.qid}_${ctx.specialization}_proposal.tex`,
    );
    const deps = makeDeps([acceptVerdict]);
    deps.runCodex = async ({ prompt }: { prompt: string }) => {
      expect(prompt).toContain(`proposal_path: ${corePath}`);
      expect(prompt).not.toContain(`proposal_path: ${legacyTex}`);
      return { stdout: JSON.stringify(acceptVerdict), stderr: "", exitCode: 0 } as never;
    };

    await runStageNeg0_5({ ctx, state, deps });
    expect(state.proposed_from!.proposal_path).toBe(corePath);
  });

  it("raises the cap gate when the env-failure retry budget is exhausted", async () => {
    // The abort persists an over-budget counter with last_draft_status still
    // "env-failure", so the `--resume` its own message prescribed re-entered the branch,
    // incremented again and re-aborted forever — a healthy angle permanently dead with
    // no announced escape. `stage_neg1_fallback` is the designed gate: its CapGate.clear
    // resets `neg1_env_failure_retries`.
    const ctx = makeCtx(repoRoot);
    const state = makeState({ last_draft_status: "env-failure" });
    state.flags.neg1_env_failure_retries = NEG1_ENV_FAILURE_RETRY_BUDGET + 5;

    const result = await runStageNeg0_5({ ctx, state, deps: makeDeps([acceptVerdict]) });

    expect(result.status).toBe("blocked");
    expect(state.flags.stage_neg1_fallback, "the abort must raise its recovery gate").toBeTruthy();
    expect(result.message).toMatch(/--clear-gate stage_neg1_fallback/);
    // The angle is preserved (no pivot) — that half of the contract must not regress.
    expect(state.proposed_from!.current_angle_index).toBe(0);
  });
});
