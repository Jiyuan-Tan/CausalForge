import { describe, expect, it } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStageNeg1_1 } from "../../src/discovery/stages/neg1_1.js";
import { MODELS } from "../../src/models.js";
import { promptPath } from "../../src/paths.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

function makeCtx(repoRoot: string): PipelineContext {
  return {
    repoRoot,
    qid: "thin_lit_review",
    specialization: "v1",
    dryRun: false,
    resume: false,
    proposeTopic: "thin topic",
  };
}

function makeState(): StateJson {
  return {
    stage_completed: "-1.1",
    lean_subdir: "CausalSmith/Stat/ThinLitReview",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: { local_fix_from_4d: false, missing_architecture: false },
  } as unknown as StateJson;
}

describe("runStageNeg1_1", () => {
  it("uses the Codex kernel tier for the literature scout", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      let model: string | undefined;
      const deps = {
        runCodex: async (args: { model?: string }) => {
          model = args.model;
          return { stdout: JSON.stringify({ status: "completed", n_open_problems: 3 }), stderr: "" };
        },
        runClaude: async () => {
          throw new Error("unused");
        },
        lean: undefined as never,
      } as unknown as StageDeps;

      await runStageNeg1_1({ ctx: makeCtx(repoRoot), state: makeState(), deps });

      expect(model).toBe(MODELS.codexKernel);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });

  it("routes structure and mechanism recovery to exactid", async () => {
    const prompt = await readFile(
      path.join(process.cwd(), "src/discovery/prompts/D-1/stage_neg1_1_lit_review.txt"),
      "utf8",
    );
    expect(prompt).toMatch(/Use `exactid`[\s\S]*structure\/mechanism recovery map/);
    expect(prompt).toMatch(/structure-identification kernel in `exactid`/);
  });

  it("checkpoints instead of completing when fewer than three open problems are emitted", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "stage-neg11-"));
    try {
      const p = promptPath(repoRoot, "stage_neg1_1_lit_review.txt");
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, "stub lit review prompt", "utf8");
      const state = makeState();
      const deps = {
        runCodex: async () => ({
          stdout: JSON.stringify({ status: "completed", n_open_problems: 1, open_problems: [{ id: "gap1" }] }),
          stderr: "",
        }),
        runClaude: async () => {
          throw new Error("unused");
        },
        lean: undefined as never,
      } as unknown as StageDeps;

      const result = await runStageNeg1_1({ ctx: makeCtx(repoRoot), state, deps });

      expect(result.status).toBe("checkpoint");
      expect(result.advance).toBe(false);
      expect(result.message).toMatch(/needs-pivot/);
      expect(state.gaps?.status).toBe("needs-pivot");
      expect(state.gaps?.n_open_problems).toBe(1);
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });
});
