/**
 * Stage 2 paper-scoped scaffold test.
 *
 * Verifies that when state.theorems is non-empty, runStage2:
 *   - populates lean_decl_name, lean_file_relpath, stage_completed, status
 *     per entry based on the parsed manifest.
 *   - marks entries absent from the manifest as "stuck".
 *   - still works correctly in the legacy (no state.theorems) path.
 */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage2 } from "../../src/pipeline_stages.js";
import {
  findDuplicateLeanNodeAnchors,
  parseLeanNodeTags,
  undeliveredBlockFromPlan,
  blockingPostSyncPlanViolations,
} from "../../src/formalization/stage2.js";
import { promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { TheoremEntry } from "../../src/shared/paper_batch_types.js";

let repoRoot: string;

describe("F2 post-sync plan gate", () => {
  it("blocks structural P2/P4 drift but leaves P5/P6 lookup drift advisory", () => {
    const violations = [
      { code: "P2", where: "def:class", message: "non-member" },
      { code: "P4", where: "thm:main", message: "uncovered assumption" },
      { code: "P5", where: "thm:main", message: "reuse lookup" },
      { code: "P6", where: "thm:main", message: "module lookup" },
    ] as const;
    expect(blockingPostSyncPlanViolations(violations as never).map((v) => v.code)).toEqual(["P2", "P4"]);
  });
});

/**
 * Construct a minimal PipelineContext that points at our temp repoRoot.
 * The prompt is written by beforeEach.
 */
function makeCtx(root: string): PipelineContext {
  return {
    repoRoot: root,
    qid: "manski1990test",
    specialization: "default",
    dryRun: false,
    resume: false,
  };
}

/**
 * Minimal StateJson with lean_subdir and theorems populated.
 */
function makeState(theorems: TheoremEntry[]): StateJson {
  return {
    stage_completed: "1.5",
    lean_subdir: "CausalSmith/PartialID/Manski1990Test",
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
    theorems,
  } as unknown as StateJson;
}

function makeEntry(id: string): TheoremEntry {
  return {
    theorem_local_id: id,
    origin_theorem_id: `manski1990test_${id}`,
    statement: `stmt_${id}`,
    proof_sketch: `sketch_${id}`,
    status: "pending",
    stage_completed: null,
    lean_file_relpath: null,
  };
}

/**
 * Build a fake StageDeps whose runClaude writes a dummy .lean file and returns
 * the structured manifest JSON.
 */
function makeDeps(leanDir: string, manifest: Array<{ theorem_local_id: string; lean_decl_name?: string }>): StageDeps {
  const leanFilePath = path.join(leanDir, "Manski1990Test.lean");
  const responseJson = JSON.stringify({
    status: "completed",
    message: "scaffold done",
    artifacts: [leanFilePath],
    theorems: manifest,
  });

  const write = async () => {
    // Write a minimal .lean file so relative-path computation works.
    await mkdir(leanDir, { recursive: true });
    await writeFile(
      leanFilePath,
      manifest
        .filter((m) => m.lean_decl_name)
        .map((m) => `theorem ${m.lean_decl_name} : True := by\n  sorry`)
        .join("\n\n") || "-- generated stub\n",
    );
  };
  return {
    // F2 dispatches codex (MODEL_PLAN.stage2) now; keep runClaude wired too so the
    // test is agnostic to the configured runner. The codex path reads `.stdout`.
    runClaude: async (_opts: unknown) => { await write(); return responseJson; },
    runCodex: async (_opts: unknown) => { await write(); return { stdout: responseJson, stderr: "" }; },
    lean: undefined as never,
  };
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stage2-paper-layout-"));
  // Write a stub stage2_scaffold.txt prompt (runStage2 reads it).
  const target = promptPath(repoRoot, "stage2_scaffold.txt");
  await mkdir(path.dirname(target), { recursive: true });
  await writeFile(target, "stub prompt");
  await writeFile(promptPath(repoRoot, "stage2_head_revise.txt"), "=== REVISE MODE ===");
});

describe("Stage 2 undelivered directive", () => {
  it("instructs F2 to remove the declaration and never replace it with sorry/gate/Prop", () => {
    const block = undeliveredBlockFromPlan(JSON.stringify({
      qid: "q",
      nodes: {
        "thm:secondary": {
          lean_kind: "theorem",
          lean_name: "secondary",
          disposition: "define-local",
          delivery_role: "secondary",
          delivery_status: "undelivered",
          delivery_reason: "citation overflow",
        },
      },
    }));
    expect(block).toContain("thm:secondary (secondary): citation overflow");
    expect(block).toContain("remove any existing Lean declaration");
    expect(block).toContain("Prop definition, axiom, gate, weakened theorem, or `sorry`");
  });
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("Stage 2 paper-scoped scaffold", () => {
  it("discovers node and environment tags recursively in nested helper modules", async () => {
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const nested = path.join(leanDir, "Helpers", "Nested.lean");
    await mkdir(path.dirname(nested), { recursive: true });
    await writeFile(nested, "-- @env: env:nested\n-- @node: thm:nested\ntheorem nested : True := by trivial\n");

    const tags = await parseLeanNodeTags(leanDir);
    expect(tags.nodes).toEqual(new Set(["thm:nested"]));
    expect(tags.envs).toEqual(new Set(["env:nested"]));
  });

  it("ignores indented in-body metadata while retaining column-zero canonical tags", async () => {
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const nested = path.join(leanDir, "Helpers", "Indented.lean");
    await mkdir(path.dirname(nested), { recursive: true });
    await writeFile(
      nested,
      "-- @node: def:primary\ndef primary : Prop :=\n  -- @node: def:primary\n  True\n",
    );

    const tags = await parseLeanNodeTags(leanDir);
    const duplicates = await findDuplicateLeanNodeAnchors(leanDir);

    expect(tags.nodes).toEqual(new Set(["def:primary"]));
    expect(duplicates).toEqual([]);
  });

  it("hard-stops F2 when nested helpers contain duplicate canonical node anchors", async () => {
    const ctx = { ...makeCtx(repoRoot), resume: true };
    const state = makeState([]);
    state.stage_completed = "5";
    delete (state as unknown as Record<string, unknown>).theorems;
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const nested = path.join(leanDir, "Helpers", "Duplicate.lean");
    await mkdir(path.dirname(nested), { recursive: true });
    await writeFile(
      nested,
      "-- @node: thm:duplicate\ntheorem primary : True := by trivial\n" +
        "-- @node: thm:duplicate\nlemma companion : True := by trivial\n",
    );
    const responseJson = JSON.stringify({
      status: "completed",
      message: "scaffold done",
      artifacts: [nested],
    });
    const deps: StageDeps = {
      runClaude: async () => responseJson,
      runCodex: async () => ({ stdout: responseJson, stderr: "" }),
      lean: undefined as never,
    };

    await expect(runStage2({ ctx, state, deps })).rejects.toThrow(
      /F2 duplicate @node gate failed[\s\S]*thm:duplicate/,
    );
  });

  it("explicit post-F2 resume uses revise semantics and restores unchanged active proofs", async () => {
    const ctx = { ...makeCtx(repoRoot), resume: true };
    const state = makeState([]);
    state.stage_completed = "5";
    delete (state as unknown as Record<string, unknown>).theorems;

    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const leanFile = path.join(leanDir, "Manski1990Test.lean");
    const nestedHelper = path.join(leanDir, "Helpers", "Preserved.lean");
    await mkdir(leanDir, { recursive: true });
    await mkdir(path.dirname(nestedHelper), { recursive: true });
    await writeFile(leanFile, "theorem keepProof (n : Nat) : n + 0 = n := by\n  simp\n");
    await writeFile(nestedHelper, "theorem nestedKeepProof (n : Nat) : n + 0 = n := by\n  simp\n");

    let producerPrompt = "";
    const responseJson = JSON.stringify({
      status: "completed",
      message: "scaffold done",
      artifacts: [leanFile],
    });
    const overwriteWithColdStyleSorry = async (opts: { prompt?: string }) => {
      producerPrompt = opts.prompt ?? "";
      await writeFile(leanFile, "theorem keepProof (n : Nat) : n + 0 = n := by\n  sorry\n");
      return { stdout: responseJson, stderr: "" };
    };
    const deps: StageDeps = {
      runClaude: async (opts: unknown) => (await overwriteWithColdStyleSorry(opts as { prompt?: string })).stdout,
      runCodex: async (opts: unknown) => overwriteWithColdStyleSorry(opts as { prompt?: string }),
      lean: undefined as never,
    };

    await runStage2({ ctx, state, deps });

    expect(producerPrompt).toContain("On-disk files to patch");
    expect(producerPrompt).toContain(nestedHelper);
    expect(producerPrompt).toContain("for every DELIVERED node, tag EXACTLY ONE canonical primary declaration");
    expect(producerPrompt).toContain("an UNDELIVERED node emits no declaration and no tag");
    expect(producerPrompt).not.toContain("tag every emitted decl");
    const after = await readFile(leanFile, "utf8");
    expect(after).toMatch(/theorem keepProof \(n : Nat\) : n \+ 0 = n := by\s+simp/);
    expect(after).not.toMatch(/\bsorry\b/);
    expect(after).not.toContain("PRIOR PROOF (carry-over: auto");
    expect(await readFile(nestedHelper, "utf8")).toMatch(/nestedKeepProof[\s\S]*by\s+simp/);
  });

  it("populates lean_decl_name, lean_file_relpath, stage_completed='2', status='in_progress' per manifest entry", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);

    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const manifest = [
      { theorem_local_id: "t1", lean_decl_name: "t1_thm" },
      { theorem_local_id: "t2", lean_decl_name: "t2_thm" },
    ];
    const deps = makeDeps(leanDir, manifest);

    const result = await runStage2({ ctx, state, deps });

    expect(result.stage).toBe("2");
    expect(result.status).toBe("completed");

    const t1 = state.theorems![0];
    expect(t1.lean_decl_name).toBe("t1_thm");
    expect(t1.lean_file_relpath).toBe("Manski1990Test.lean");
    expect(t1.stage_completed).toBe("2");
    expect(t1.status).toBe("in_progress");

    const t2 = state.theorems![1];
    expect(t2.lean_decl_name).toBe("t2_thm");
    expect(t2.lean_file_relpath).toBe("Manski1990Test.lean");
    expect(t2.stage_completed).toBe("2");
    expect(t2.status).toBe("in_progress");
  });

  it("marks an entry as 'stuck' when absent from the manifest", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);

    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    // manifest only covers t1; t2 is absent
    const manifest = [{ theorem_local_id: "t1", lean_decl_name: "t1_thm" }];
    const deps = makeDeps(leanDir, manifest);

    await runStage2({ ctx, state, deps });

    const t1 = state.theorems![0];
    expect(t1.status).toBe("in_progress");
    expect(t1.lean_decl_name).toBe("t1_thm");

    const t2 = state.theorems![1];
    expect(t2.status).toBe("stuck");
    expect(t2.failure_reason).toMatch(/Stage 2 did not produce/);
    expect(t2.lean_decl_name).toBeUndefined();
  });

  it("recovers missing manifest rows from all Lean artifacts and records the containing file", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1"), makeEntry("t2")];
    const state = makeState(entries);
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const basic = path.join(leanDir, "Basic.lean");
    const t2file = path.join(leanDir, "Tt2.lean");
    const responseJson = JSON.stringify({
      status: "completed",
      message: "scaffold done",
      artifacts: [basic, t2file],
      theorems: [{ theorem_local_id: "t1", lean_decl_name: "t1_thm" }],
    });
    const write = async () => {
      await mkdir(leanDir, { recursive: true });
      await writeFile(basic, "theorem t1_thm : True := by\n  sorry\n");
      await writeFile(t2file, "-- @node: t2\ntheorem t2_thm : True := by\n  sorry\n");
    };
    const deps: StageDeps = {
      runClaude: async () => { await write(); return responseJson; },
      runCodex: async () => { await write(); return { stdout: responseJson, stderr: "" }; },
      lean: undefined as never,
    };
    await runStage2({ ctx, state, deps });
    expect(state.theorems![0].lean_file_relpath).toBe("Basic.lean");
    expect(state.theorems![1].lean_decl_name).toBe("t2_thm");
    expect(state.theorems![1].lean_file_relpath).toBe("Tt2.lean");
  });

  it("treats manifest rows without lean_decl_name as missing and marks unrecovered rows stuck", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1")];
    const state = makeState(entries);
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const deps = makeDeps(leanDir, [{ theorem_local_id: "t1" }]);
    await runStage2({ ctx, state, deps });
    expect(state.theorems![0].status).toBe("stuck");
    expect(state.theorems![0].lean_decl_name).toBeUndefined();
  });

  it("leaves state.theorems untouched when undefined (legacy single-theorem path)", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState([]);
    // override: remove theorems entirely to simulate legacy state
    delete (state as unknown as Record<string, unknown>).theorems;

    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    const manifest: Array<{ theorem_local_id: string; lean_decl_name: string }> = [];
    const deps = makeDeps(leanDir, manifest);

    const result = await runStage2({ ctx, state, deps });

    // Stage result still reports completed; no crash.
    expect(result.stage).toBe("2");
    expect(result.status).toBe("completed");
    expect((state as unknown as Record<string, unknown>).theorems).toBeUndefined();
  });

  it("preserves the blocked-missing-architecture branch untouched", async () => {
    const ctx = makeCtx(repoRoot);
    const entries: TheoremEntry[] = [makeEntry("t1")];
    const state = makeState(entries);

    const blockedJson = JSON.stringify({
      status: "blocked-missing-architecture",
      message: "missing FooClass",
      missing_items: [
        {
          kind: "typeclass",
          name_suggestion: "FooClass",
          purpose: "needed for theorem t1",
          why_substantial: "full new typeclass",
        },
      ],
    });

    const deps: StageDeps = {
      runClaude: async (_opts: unknown) => blockedJson,
      runCodex: async (_opts: unknown) => ({ stdout: blockedJson, stderr: "" }),
      lean: undefined as never,
    };

    const result = await runStage2({ ctx, state, deps });

    expect(result.status).toBe("blocked");
    expect(state.flags.missing_architecture).toBe(true);
    expect(state.flags.missing_architecture_items?.[0].name_suggestion).toBe("FooClass");
    // entries should not have been updated by the paper-scoped branch
    expect(entries[0].status).toBe("pending");
  });

  it("legacy single-theorem mode (state.theorems undefined): no mutation, behaves as before", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState([]);
    // Construct a StateJson WITHOUT theorems[] (remove it entirely to simulate legacy state).
    delete (state as unknown as Record<string, unknown>).theorems;

    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    // Mock runClaude to return a legacy-shaped output: {status:"completed", artifacts:[...]}
    // — no `theorems` manifest field.
    const legacyJson = JSON.stringify({
      status: "completed",
      message: "scaffold done",
      artifacts: [path.join(leanDir, "Manski1990Test.lean")],
    });

    const write = async () => {
      await mkdir(leanDir, { recursive: true });
      await writeFile(path.join(leanDir, "Manski1990Test.lean"), "-- generated stub\n");
    };
    const deps: StageDeps = {
      runClaude: async (_opts: unknown) => { await write(); return legacyJson; },
      runCodex: async (_opts: unknown) => { await write(); return { stdout: legacyJson, stderr: "" }; },
      lean: undefined as never,
    };

    const result = await runStage2({ ctx, state, deps });

    // Assert that state.theorems remains undefined (no mutation introduced).
    expect((state as unknown as Record<string, unknown>).theorems).toBeUndefined();
    // No current_theorem_index should be set either.
    expect((state as unknown as Record<string, unknown>).current_theorem_index).toBeUndefined();
    // The handler returned status "completed" (no crash on the missing manifest).
    expect(result.status).toBe("completed");
    expect(result.stage).toBe("2");
    // flags.missing_architecture should stay false (the blocked branch was not triggered).
    expect(state.flags.missing_architecture).toBe(false);
  });

  it("legacy mode (state.theorems is []): empty array bypasses manifest walk", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState([]);
    // state.theorems is an empty array (not undefined).

    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    // Same mocked legacy output as above. No theorems manifest field.
    const legacyJson = JSON.stringify({
      status: "completed",
      message: "scaffold done",
      artifacts: [path.join(leanDir, "Manski1990Test.lean")],
    });

    const write = async () => {
      await mkdir(leanDir, { recursive: true });
      await writeFile(path.join(leanDir, "Manski1990Test.lean"), "-- generated stub\n");
    };
    const deps: StageDeps = {
      runClaude: async (_opts: unknown) => { await write(); return legacyJson; },
      runCodex: async (_opts: unknown) => { await write(); return { stdout: legacyJson, stderr: "" }; },
      lean: undefined as never,
    };

    const result = await runStage2({ ctx, state, deps });

    // Verify the array remains empty (no crash on the empty check).
    expect(state.theorems).toEqual([]);
    // The handler completed without errors.
    expect(result.status).toBe("completed");
    expect(result.stage).toBe("2");
    // flags.missing_architecture should stay false.
    expect(state.flags.missing_architecture).toBe(false);
  });
});
