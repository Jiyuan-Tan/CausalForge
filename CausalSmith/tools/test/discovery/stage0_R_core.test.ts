import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { runStage0RCore } from "../../src/discovery/stages/d0_r_core.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { promptPath } from "../../src/paths.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { Stage0_5CoreResult } from "../../src/discovery/stages/d0_5_core.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

const QID = "stat_ate_overlap_decay";
const SPEC = "v1";

let repoRoot: string;
let goldenCore: string;

async function stubPrompts(root: string): Promise<void> {
  const target = promptPath(root, "stage0_R_core.txt");
  await mkdir(path.dirname(target), { recursive: true });
  await writeFile(target, "stub stage0_R_core", "utf8");
}

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}

function makeState(): StateJson {
  return {
    stage_completed: "0",
    lean_subdir: `CausalSmith/Stat/${QID}`,
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
    proposed_from: { chosen_qid: QID, chosen_specialization: SPEC, cluster: "stat" },
  } as unknown as StateJson;
}

const review: Stage0_5CoreResult = {
  overall: "revise",
  verdicts: [
    { referee: "math", verdict: "revise", findings: [{ node_id: "thm:lower", code: "omission", one_line: "tighten the TV bound" }], cited_checks: [] },
    { referee: "general", verdict: "pass", findings: [], cited_checks: [] },
    { referee: "decision", verdict: "revise", findings: [], cited_checks: [] },
  ],
  cited_checks: [],
  citation_verification_required: [],
};

/** Mock editor: overwrites CORE_FILE with `coreBody` (the .tex is re-rendered by the stage). */
function makeDeps(coreBody: string): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const cm = prompt.match(/CORE_FILE: (.+)/);
      if (!cm) throw new Error("mock: missing CORE_FILE");
      await writeFile(cm[1].trim(), coreBody, "utf8");
      return {
        stdout: JSON.stringify({ status: "completed", message: "stub revise", artifacts: [cm[1].trim()] }),
        stderr: "",
      };
    },
    runClaude: async () => {
      throw new Error("runClaude not expected at Stage 0.R");
    },
    lean: undefined as never,
  };
}

async function seed(ctx: PipelineContext): Promise<void> {
  const cp = coreJsonPath(ctx);
  await mkdir(path.dirname(cp), { recursive: true });
  await writeFile(cp, goldenCore, "utf8");
}

describe("runStage0RCore (D0.R in-place core editor; .tex re-rendered deterministically)", () => {
  beforeAll(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "stage0R-"));
    await stubPrompts(repoRoot);
    goldenCore = await readFile(
      new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url),
      "utf8",
    );
  });

  afterAll(async () => {
    await rm(repoRoot, { recursive: true, force: true });
  });

  it("accepts a revise that keeps the core gate-clean, and re-renders the .tex from it", async () => {
    const ctx = makeCtx(repoRoot);
    await seed(ctx);
    const res = await runStage0RCore({ ctx, state: makeState(), deps: makeDeps(goldenCore), review });
    expect(res.coreJsonPath).toBe(coreJsonPath(ctx));
    expect(res.texPath).toBe(artifactPaths(ctx, makeState()).tex);
    // the .tex is regenerated from the core (not hand-edited)
    expect(existsSync(res.texPath)).toBe(true);
    const tex = await readFile(res.texPath, "utf8");
    expect(tex).toContain("\\label{thm:lower}");
  });

  it("ESCALATES (no throw) when the revise leaves a gate violation (A6 membership)", async () => {
    const ctx = makeCtx(repoRoot);
    await seed(ctx);
    const broken = JSON.parse(goldenCore) as Core;
    broken.assumptions.push({
      id: "ass:lower-class",
      kind: "smoothness",
      condition: "the resulting law belongs to \\(\\mathcal{P}_{\\kappa,\\beta}\\)",
      free_symbols: [],
      standard: { name: "x", cite: "Tsybakov2009" },
    } as unknown as Core["assumptions"][number]);
    // An in-place edit that does not re-discharge the gate is escalated, not thrown —
    // the typed loop turns the escalate signal into an early checkpoint.
    const res = await runStage0RCore({ ctx, state: makeState(), deps: makeDeps(JSON.stringify(broken)), review });
    expect(res.escalate).toBeDefined();
    expect(res.escalate?.reason).toMatch(/undischarged|gate|G\d/i);
  });

  it("ESCALATES (no throw) when D0.R reports status 'failed' (un-fixable in place)", async () => {
    const ctx = makeCtx(repoRoot);
    await seed(ctx);
    const failDeps = {
      runCodex: async () => ({ stdout: JSON.stringify({ status: "failed", message: "open converse needs real math, cannot edit in place" }), stderr: "" }),
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const res = await runStage0RCore({ ctx, state: makeState(), deps: failDeps, review });
    expect(res.escalate).toBeDefined();
    expect(res.escalate?.reason).toMatch(/open converse/i);
  });

  it("restores the whole core when D0.R edits an orchestrator-maintained assumption", async () => {
    const ctx = makeCtx(repoRoot);
    const protectedCore = JSON.parse(goldenCore) as Core;
    const maintained = protectedCore.assumptions[0] as any;
    delete maintained.standard;
    delete maintained.novel;
    maintained.maintained = {
      flag: true,
      reason: "A disclosed conditional nuisance premise.",
      open_object: "oeq:trainer remains open.",
      separate_object: "It constrains a separate nuisance object.",
      sanctioned_by: "orchestrator",
    };
    await writeFile(coreJsonPath(ctx), JSON.stringify(protectedCore), "utf8");

    const unauthorized = structuredClone(protectedCore) as any;
    unauthorized.assumptions[0].maintained.reason = "Invented trainer witness.";
    unauthorized.definitions.push({
      id: "def:invented-trainer",
      name: "invented trainer",
      construction: "an orientation-aware oracle",
      inputs: [],
    });
    const res = await runStage0RCore({
      ctx,
      state: makeState(),
      deps: makeDeps(JSON.stringify(unauthorized)),
      review,
    });

    expect(res.escalate?.reason).toMatch(/protected maintained assumption/i);
    const restored = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(restored.assumptions[0].maintained.reason).toBe("A disclosed conditional nuisance premise.");
    expect(restored.definitions.some((d: any) => d.id === "def:invented-trainer")).toBe(false);
  });

  it("repairs an under-escaped TeX backslash in the edited core and persists the canonical form", async () => {
    const ctx = makeCtx(repoRoot);
    await seed(ctx);
    // The worker re-serializes `\\text{observation}` with a single backslash — valid
    // JSON whose `\t` decodes to a tab, the silent-corruption class.
    const underEscaped = goldenCore.replace(String.raw`\\text{observation}`, String.raw`\text{observation}`);
    expect(underEscaped).not.toBe(goldenCore);
    const res = await runStage0RCore({ ctx, state: makeState(), deps: makeDeps(underEscaped), review });
    expect(res.escalate).toBeUndefined();
    // The persisted core.json is the canonical form: identical content to the golden core.
    const persisted = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(persisted).toEqual(JSON.parse(goldenCore));
  });

  it("ESCALATES and restores the core when the edit carries an unrecoverable control character", async () => {
    const ctx = makeCtx(repoRoot);
    await seed(ctx);
    const corrupted = JSON.parse(goldenCore) as Core;
    const originalEstimand = corrupted.target_estimand;
    corrupted.target_estimand = `${originalEstimand}\t 1`;
    const res = await runStage0RCore({ ctx, state: makeState(), deps: makeDeps(JSON.stringify(corrupted)), review });
    expect(res.escalate).toBeDefined();
    expect(res.escalate?.reason).toMatch(/U\+0009|control character/i);
    const restored = JSON.parse(await readFile(coreJsonPath(ctx), "utf8")) as Core;
    expect(restored.target_estimand).toBe(originalEstimand);
  });

  it("restores the whole core when D0.R deletes an assumption not targeted by a finding", async () => {
    const ctx = makeCtx(repoRoot);
    await seed(ctx);
    const unauthorized = JSON.parse(goldenCore) as Core;
    const deletedId = unauthorized.assumptions[0].id;
    unauthorized.assumptions = unauthorized.assumptions.slice(1);

    const res = await runStage0RCore({
      ctx,
      state: makeState(),
      deps: makeDeps(JSON.stringify(unauthorized)),
      review,
    });

    expect(res.escalate?.reason).toMatch(/deleted unflagged assumption/i);
    const restored = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    expect(restored.assumptions.some((a: any) => a.id === deletedId)).toBe(true);
  });
});
