// Post-pivot F-era retirement (2026-07 cross-stage rewind audit).
//
// After a stage_neg1 PIVOT the on-disk plan.json / .lean tree describe the ABANDONED
// angle, but `laterStageEverRan` reads an append-only log — monotone for the run's
// lifetime — so F1 stayed in patch mode pointed at the dead plan and F2 kept patching
// the dead scaffold ("preserve existing proof bodies" grafts the new angle's mathematics
// onto dead work). The pivot now sets `f1_plan_retired` / `f2_scaffold_retired`; each
// stage cold-starts once and clears ITS OWN marker, so revise rounds on the NEW angle's
// artifacts patch normally afterwards. (The previous attempt cleared one shared flag in
// F1, which made the F2 half dead code — F1 runs first — hence the two markers.)

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage1 } from "../../src/formalization/stage1.js";
import { runStage2 } from "../../src/formalization/stage2.js";
import { pipelineLogPath, planPath, promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const QID = "pid_manski1990test";
let repoRoot: string;

function makeCtx(): PipelineContext {
  return { repoRoot, qid: QID, specialization: "default", dryRun: false, resume: false } as PipelineContext;
}

function makeState(flags: Record<string, unknown> = {}): StateJson {
  return {
    stage_completed: "0.5",
    lean_subdir: "CausalSmith/PartialID/Manski1990Test",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    flags: { rewound_from_stage0: null, local_fix_from_4d: false, missing_architecture: false, ...flags },
  } as unknown as StateJson;
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "f-era-retirement-"));
  const stub = async (name: string, body: string) => {
    const p = promptPath(repoRoot, name);
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, body, "utf8");
  };
  await stub("stage1_template.txt", "stub stage1_template");
  await stub("stage1_head_revise.txt", "REVISION HEAD");
  await stub("stage2_scaffold.txt", "stub stage2 prompt");
  await stub("stage2_head_revise.txt", "=== REVISE MODE ===");
  // F1 fails loud on a missing core.json.
  const coreDir = path.join(repoRoot, "doc", "research", "active", QID, "discovery");
  await mkdir(coreDir, { recursive: true });
  await writeFile(
    path.join(coreDir, "core.json"),
    JSON.stringify({ qid: QID, symbols: [], assumptions: [], statements: [], target_estimand: "stub" }),
  );
  // Durable history: a later stage ran → monotone patch mode without the marker.
  await writeFile(
    pipelineLogPath(repoRoot, QID, "default"),
    JSON.stringify({ stage: "3", status: "completed" }) + "\n",
  );
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

// ── F1 ──────────────────────────────────────────────────────────────────────────────

function stage1Deps(opts: { writePlan?: boolean } = {}): { deps: StageDeps; prompt: () => string } {
  let prompt = "";
  const deps: StageDeps = {
    runClaude: async (o: unknown) => {
      prompt = (o as { prompt: string }).prompt;
      if (opts.writePlan) {
        // A minimal SCHEMA-VALID plan (PlanSchema: qid + nodes), i.e. what a real cold
        // pass leaves on disk for the new angle.
        const p = planPath(repoRoot, QID, "default");
        await mkdir(path.dirname(p), { recursive: true });
        await writeFile(p, JSON.stringify({ qid: QID, nodes: {} }), "utf8");
      }
      return JSON.stringify({ status: "completed", artifacts: [] });
    },
    runCodex: async () => { throw new Error("runCodex should not be called by Stage 1"); },
    lean: undefined as never,
  };
  return { deps, prompt: () => prompt };
}

describe("F1 — f1_plan_retired forces a cold start and is consumed by the first valid new plan", () => {
  it("control: with history and a prior plan (no marker), F1 patches in place", async () => {
    const existingPlan = planPath(repoRoot, QID, "default");
    await mkdir(path.dirname(existingPlan), { recursive: true });
    await writeFile(existingPlan, '{"dead":"angle plan"}');
    const { deps, prompt } = stage1Deps();
    await runStage1({ ctx: makeCtx(), state: makeState(), deps });
    expect(prompt()).toContain("REVISION HEAD");
    expect(prompt()).toContain("Prior plan to patch");
  });

  it("with the marker, F1 cold-starts (the dead angle's plan is NOT offered for patching)", async () => {
    const existingPlan = planPath(repoRoot, QID, "default");
    await mkdir(path.dirname(existingPlan), { recursive: true });
    await writeFile(existingPlan, '{"dead":"angle plan"}');
    const { deps, prompt } = stage1Deps();
    const state = makeState({ f1_plan_retired: true });
    await runStage1({ ctx: makeCtx(), state, deps });
    expect(prompt()).not.toContain("REVISION HEAD");
    expect(prompt()).not.toContain("Prior plan to patch");
  });

  it("the marker is consumed once a schema-valid plan for the new angle is on disk", async () => {
    const { deps } = stage1Deps({ writePlan: true });
    const state = makeState({ f1_plan_retired: true });
    await runStage1({ ctx: makeCtx(), state, deps });
    expect(state.flags.f1_plan_retired).toBeUndefined();
  });

  it("the marker SURVIVES a pass that leaves no parseable plan (disk still holds the dead angle's plan)", async () => {
    const { deps } = stage1Deps(); // writes no plan
    const state = makeState({ f1_plan_retired: true });
    await runStage1({ ctx: makeCtx(), state, deps });
    expect(state.flags.f1_plan_retired).toBe(true);
  });
});

// ── F2 ──────────────────────────────────────────────────────────────────────────────

function stage2Deps(leanDir: string): { deps: StageDeps; prompt: () => string } {
  let prompt = "";
  const leanFilePath = path.join(leanDir, "Manski1990Test.lean");
  const responseJson = JSON.stringify({ status: "completed", message: "scaffold done", artifacts: [leanFilePath] });
  const write = async () => {
    await mkdir(leanDir, { recursive: true });
    await writeFile(leanFilePath, "theorem fresh_scaffold : True := by\n  sorry\n");
  };
  const deps: StageDeps = {
    runClaude: async (o: unknown) => { prompt = (o as { prompt: string }).prompt; await write(); return responseJson; },
    runCodex: async (o: unknown) => { prompt = (o as { prompt: string }).prompt; await write(); return { stdout: responseJson, stderr: "" }; },
    lean: undefined as never,
  };
  return { deps, prompt: () => prompt };
}

describe("F2 — f2_scaffold_retired forces a cold scaffold and is consumed on completion", () => {
  const deadLean = "theorem dead_angle_thm : True := by trivial\n";

  beforeEach(async () => {
    // F2's post-sync structural gate requires plan.json alongside core.json.
    const p = planPath(repoRoot, QID, "default");
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, JSON.stringify({ qid: QID, nodes: {} }), "utf8");
  });

  it("control: with history and an on-disk scaffold (no marker), F2 patches in place", async () => {
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    await mkdir(leanDir, { recursive: true });
    await writeFile(path.join(leanDir, "Manski1990Test.lean"), deadLean);
    const { deps, prompt } = stage2Deps(leanDir);
    await runStage2({ ctx: makeCtx(), state: makeState(), deps });
    expect(prompt()).toContain("=== REVISE MODE ===");
    expect(prompt()).toContain("On-disk files to patch");
  });

  it("with the marker, F2 cold-scaffolds (the dead angle's .lean tree is NOT offered for patching) and clears it on completion", async () => {
    const leanDir = path.join(repoRoot, "CausalSmith", "PartialID", "Manski1990Test");
    await mkdir(leanDir, { recursive: true });
    await writeFile(path.join(leanDir, "Manski1990Test.lean"), deadLean);
    const { deps, prompt } = stage2Deps(leanDir);
    const state = makeState({ f2_scaffold_retired: true });
    const result = await runStage2({ ctx: makeCtx(), state, deps });
    expect(result.status).toBe("completed");
    expect(prompt()).not.toContain("=== REVISE MODE ===");
    expect(prompt()).not.toContain("On-disk files to patch");
    // Consumed: the on-disk scaffold is now the NEW angle's, so later revise rounds patch it.
    expect(state.flags.f2_scaffold_retired).toBeUndefined();
    expect(await readFile(path.join(leanDir, "Manski1990Test.lean"), "utf8")).toContain("fresh_scaffold");
  });
});
