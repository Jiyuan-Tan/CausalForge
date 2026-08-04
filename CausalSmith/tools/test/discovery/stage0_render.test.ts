import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { runStage0Render } from "../../src/discovery/stages/d0_render.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { artifactPaths } from "../../src/pipeline_support.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { PipelineContext, StateJson } from "../../src/types.js";

const QID = "stat_ate_overlap_decay";
const SPEC = "v1";

let repoRoot: string;
let core: Core;

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

describe("runStage0Render (D0-RENDER — deterministic core → .tex)", () => {
  beforeAll(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "stage0render-"));
    core = {
      qid: QID,
      specialization: SPEC,
      cluster: "stat",
      target_estimand: "\\(\\theta\\)",
      estimand_functional: "\\(\\widehat\\theta\\)",
      symbols: [{ name: "theta", type: "scalar", space: "R", role: "target" }],
      assumptions: [{
        id: "ass:tail", condition: "\\(0<\\kappa<\\infty\\)", free_symbols: [],
        standard: { name: "tail regularity", cite: "RefA" }, used_by: ["thm:lower"],
      }],
      definitions: [],
      statements: [{
        id: "thm:lower", kind: "theorem", statement: "\\(\\theta=\\theta\\).",
        depends_on: ["ass:tail"], status: "proved", proof_tex: "Immediate.",
      }],
      bibliography: [{ key: "RefA", citation: "Author (2026). \\emph{Reference}." }],
      tldr: "A deterministic render fixture.",
      project_justification: { gap: "Test gap.", niche: "Test niche.", fill: "Test fill." },
    } as Core;
    await mkdir(path.dirname(coreJsonPath(makeCtx(repoRoot))), { recursive: true });
    await writeFile(coreJsonPath(makeCtx(repoRoot)), JSON.stringify(core), "utf8");
  });

  afterAll(async () => {
    await rm(repoRoot, { recursive: true, force: true });
  });

  it("renders the .tex deterministically from the frozen core (no LLM)", async () => {
    const ctx = makeCtx(repoRoot);
    const res = await runStage0Render({ ctx, state: makeState() });
    expect(existsSync(res.texPath)).toBe(true);
    expect(res.texPath).toBe(artifactPaths(ctx, makeState()).tex);
    const tex = await readFile(res.texPath, "utf8");
    // formal nodes emitted verbatim with labels; proofs included (discharged core)
    expect(tex).toContain("\\label{thm:lower}");
    expect(tex).toContain("\\label{ass:tail}");
    expect(tex).toContain("\\begin{document}");
    expect(res.message).toMatch(/no compilation in D/i);
  });

  it("is a pure re-render — running twice yields byte-identical .tex", async () => {
    const ctx = makeCtx(repoRoot);
    const a = await runStage0Render({ ctx, state: makeState() });
    const first = await readFile(a.texPath, "utf8");
    await runStage0Render({ ctx, state: makeState() });
    const second = await readFile(a.texPath, "utf8");
    expect(second).toBe(first);
  });

  it("THROWS when no core exists yet", async () => {
    const empty = await mkdtemp(path.join(os.tmpdir(), "stage0render-empty-"));
    await expect(runStage0Render({ ctx: makeCtx(empty), state: makeState() })).rejects.toThrow(
      /requires a core/,
    );
    await rm(empty, { recursive: true, force: true });
  });

});
