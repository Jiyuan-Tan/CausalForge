// CausalSmith/tools/test/substrate/smoke.test.ts
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, mkdir, writeFile, readFile, readdir } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { runSubstratePipeline } from "../../src/substrate/pipeline.js";
import { requirementPath, substrateRunDir } from "../../src/substrate/paths.js";

let root: string;
const FULL = `# r
## Goal
g
## Provides (API contract)
p
## Statement / milestones
s
## Standard reference
ref
## Intended reuse
reuse
## May assume / must derive
assume
`;
beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "subsmoke-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("substrate smoke (faked workers, real fs)", () => {
  it("reaches done and writes artifacts", async () => {
    await mkdir(path.dirname(requirementPath(root, "x")), { recursive: true });
    await writeFile(requirementPath(root, "x"), FULL, "utf8");
    let n = 0;
    const s = await runSubstratePipeline(
      { repoRoot: root, slug: "x", resume: false },
      {
        runScaffolder: async () => (++n === 1
          ? { decision: "build", plan_markdown: "PLAN", codex_prompts: [{ id: "a", target_decls: ["t"], prompt: "go" }] }
          : { decision: "review", plan_markdown: "PLAN", codex_prompts: [] }),
        runFillers: async () => [{ id: "a", ok: true, summary: "closed t" }],
        buildTargets: async () => ({ ok: true, errors: [], sorryCount: 0, perFile: {} }),
        runReviewer: async () => ({ pass: true, findings: "", checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true } }),
        coordinate: async () => ({ ok: true, log: "coordinated" }),
      } as any,
    );
    expect(s.phase).toBe("done");
    const runDir = substrateRunDir(root, "x");
    expect(await readFile(path.join(runDir, "plan.md"), "utf8")).toBe("PLAN");
    const files = await readdir(runDir);
    expect(files).toContain("round_1.json");
    expect(files).toContain("state.json");
  });
});
