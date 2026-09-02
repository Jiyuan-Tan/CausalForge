import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { runStage2 } from "../../src/formalization/stage2.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

let repoRoot = "";

function state(redirect: boolean): StateJson {
  return {
    stage_completed: "2",
    lean_subdir: "CausalSmith/Stat/LocalContextTest",
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
      scaffold_redirect: redirect
        ? "Fix target.\n\nDeclarations to edit (one obj_id per line, verbatim):\n- thm:target"
        : null,
    },
  } as unknown as StateJson;
}

async function arrange(redirect: boolean) {
  const ctx: PipelineContext = {
    repoRoot,
    qid: "stat_local_context_test",
    specialization: "default",
    dryRun: false,
    resume: redirect,
  };
  const runState = state(redirect);
  const paths = artifactPaths(ctx, runState);
  const core = {
    qid: ctx.qid,
    symbols: [{ name: "x", type: "real" }, { name: "z", type: "real" }],
    assumptions: [
      { id: "ass:shared", condition: "x positive", free_symbols: ["x"], standard: { name: "positive", cite: "fixture" } },
      { id: "ass:unrelated", condition: "UNRELATED_CORE_SENTINEL", free_symbols: ["z"], standard: { name: "bounded", cite: "fixture" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:target", kind: "theorem", statement: "target x", free_symbols: ["x"], depends_on: ["ass:shared"], status: "to-prove" },
      { id: "lem:unrelated", kind: "lemma", statement: "unrelated z", free_symbols: ["z"], depends_on: ["ass:unrelated"], status: "to-prove" },
    ],
    sampling_model: { observed: "x" },
    target_estimand: "x",
    bibliography: [],
  };
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({
    lean_kind,
    lean_name,
    disposition: "define-local",
    reuse: null,
    modules: [],
    ...extra,
  });
  const plan = {
    qid: ctx.qid,
    env: [{ id: "S1", world: "local", binds_symbols: ["x"], binds_sampling_model: true, disposition: "define-local" }],
    nodes: {
      "ass:shared": node("assumption", "Shared"),
      "ass:unrelated": node("assumption", "UNRELATED_PLAN_SENTINEL"),
      "thm:target": node("theorem", "target", { hyps: ["ass:shared"] }),
      "lem:unrelated": node("lemma", "unrelated", { hyps: ["ass:unrelated"] }),
    },
    citations: [],
  };
  await mkdir(path.dirname(coreJsonPath(ctx)), { recursive: true });
  await mkdir(path.dirname(paths.plan), { recursive: true });
  await mkdir(paths.leanDir, { recursive: true });
  await writeFile(coreJsonPath(ctx), JSON.stringify(core));
  await writeFile(paths.plan, JSON.stringify(plan));
  await writeFile(
    path.join(paths.leanDir, "Main.lean"),
    [
      "-- @env: S1",
      "-- @node: ass:shared",
      "-- @node: ass:unrelated",
      "-- @node: thm:target",
      "-- @node: lem:unrelated",
      "theorem target : True := by trivial",
      "",
    ].join("\n"),
  );
  return { ctx, runState };
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "f2-local-prompt-"));
  await mkdir(path.dirname(promptPath(repoRoot, "stage2_scaffold.txt")), { recursive: true });
  await writeFile(promptPath(repoRoot, "stage2_scaffold.txt"), "scaffold instructions");
  await writeFile(promptPath(repoRoot, "stage2_head_revise.txt"), "revise instructions");
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("F2 revision prompt localization", () => {
  it("sends a local packet on a targeted redirect", async () => {
    const { ctx, runState } = await arrange(true);
    let prompt = "";
    const blocked = JSON.stringify({
      status: "blocked-missing-architecture",
      message: "stop after prompt capture",
      missing_items: [{ kind: "definition", name_suggestion: "Fixture", purpose: "test", why_substantial: "test" }],
    });
    const deps = {
      runCodex: async (opts: { prompt: string }) => {
        prompt = opts.prompt;
        return { stdout: blocked, stderr: "" };
      },
      runClaude: async () => blocked,
      lean: undefined,
    } as unknown as StageDeps;
    await runStage2({ ctx, state: runState, deps });
    expect(prompt).toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain('"thm:target"');
    expect(prompt).toContain('"ass:shared"');
    expect(prompt).not.toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).not.toContain("UNRELATED_PLAN_SENTINEL");
  });

  it("keeps the complete plan/core on a cold scaffold", async () => {
    const { ctx, runState } = await arrange(false);
    let prompt = "";
    const blocked = JSON.stringify({
      status: "blocked-missing-architecture",
      message: "stop after prompt capture",
      missing_items: [{ kind: "definition", name_suggestion: "Fixture", purpose: "test", why_substantial: "test" }],
    });
    const deps = {
      runCodex: async (opts: { prompt: string }) => {
        prompt = opts.prompt;
        return { stdout: blocked, stderr: "" };
      },
      runClaude: async () => blocked,
      lean: undefined,
    } as unknown as StageDeps;
    await runStage2({ ctx, state: runState, deps });
    expect(prompt).not.toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).toContain("UNRELATED_PLAN_SENTINEL");
  });

  it("falls back to full context when a prior scaffold is incomplete", async () => {
    const { ctx, runState } = await arrange(true);
    const paths = artifactPaths(ctx, runState);
    await writeFile(
      path.join(paths.leanDir, "Main.lean"),
      "-- @node: thm:target\ntheorem target : True := by trivial\n",
    );
    let prompt = "";
    const blocked = JSON.stringify({
      status: "blocked-missing-architecture",
      message: "stop after prompt capture",
      missing_items: [{ kind: "definition", name_suggestion: "Fixture", purpose: "test", why_substantial: "test" }],
    });
    const deps = {
      runCodex: async (opts: { prompt: string }) => {
        prompt = opts.prompt;
        return { stdout: blocked, stderr: "" };
      },
      runClaude: async () => blocked,
      lean: undefined,
    } as unknown as StageDeps;
    await runStage2({ ctx, state: runState, deps });
    expect(prompt).not.toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).toContain("UNRELATED_PLAN_SENTINEL");
  });
});
