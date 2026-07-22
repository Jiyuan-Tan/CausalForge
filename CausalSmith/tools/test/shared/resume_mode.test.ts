import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { laterStageEverRan } from "../../src/shared/resume_mode.js";
import { pipelineLogPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

const roots: string[] = [];

async function fixture(stage_completed: StateJson["stage_completed"] = "1.5") {
  const repoRoot = await mkdtemp(path.join(tmpdir(), "resume-mode-"));
  roots.push(repoRoot);
  const ctx = {
    repoRoot,
    qid: "stat_resume_mode",
    specialization: "v1",
    dryRun: false,
    resume: true,
  } as PipelineContext;
  const state = {
    stage_completed,
    lean_subdir: "CausalSmith/Stat/ResumeMode",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    flags: {},
  } as unknown as StateJson;
  return { ctx, state };
}

afterEach(async () => {
  await Promise.all(roots.splice(0).map((root) => rm(root, { recursive: true, force: true })));
});

describe("laterStageEverRan", () => {
  it("uses the pre-reentry state cursor when --from-stage rewinds a completed run", async () => {
    const { ctx, state } = await fixture("5");
    await expect(laterStageEverRan(ctx, state, "2")).resolves.toBe(true);
  });

  it("uses append-only pipeline history after the mutable cursor was lowered", async () => {
    const { ctx, state } = await fixture("2");
    const log = pipelineLogPath(ctx.repoRoot, ctx.qid, ctx.specialization);
    await mkdir(path.dirname(log), { recursive: true });
    await writeFile(log, [
      JSON.stringify({ stage: "2", status: "completed" }),
      "not-json-from-an-interrupted-write",
      JSON.stringify({ stage: "4", status: "skipped" }),
    ].join("\n"));
    await expect(laterStageEverRan(ctx, state, "2")).resolves.toBe(true);
  });

  it("does not label a true first pass as revise", async () => {
    const { ctx, state } = await fixture("1.5");
    await expect(laterStageEverRan(ctx, state, "2")).resolves.toBe(false);
  });

  it("recognizes per-theorem progress when the paper cursor is behind", async () => {
    const { ctx, state } = await fixture("1");
    state.theorems = [{ stage_completed: "3" }] as StateJson["theorems"];
    await expect(laterStageEverRan(ctx, state, "2")).resolves.toBe(true);
  });
});
