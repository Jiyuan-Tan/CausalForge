// CausalSmith/tools/test/substrate/pipeline.test.ts
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, mkdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { existsSync } from "node:fs";
import { runSubstratePipeline, BUILD_CAP } from "../../src/substrate/pipeline.js";
import { requirementPath, causaleanRoot, slugToPascal } from "../../src/substrate/paths.js";

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
async function seedReq(slug: string) {
  await mkdir(path.dirname(requirementPath(root, slug)), { recursive: true });
  await writeFile(requirementPath(root, slug), FULL, "utf8");
}
beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "subpipe-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

const okBuild = async () => ({ ok: true, errors: [], sorryCount: 0, perFile: {} });

describe("runSubstratePipeline (fakes)", () => {
  it("halts with bootstrap message when requirement is absent", async () => {
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false }, {} as any);
    expect(s.phase).toBe("halted");
    expect(s.terminalMessage).toMatch(/requirement\.md/);
  });

  it("runs build → review(pass) → coordinate → done", async () => {
    await seedReq("x");
    let scaffoldCalls = 0;
    const deps = {
      runScaffolder: async () => {
        scaffoldCalls++;
        return scaffoldCalls === 1
          ? { decision: "build", plan_markdown: "P", codex_prompts: [{ id: "a", target_decls: [], prompt: "go" }] }
          : { decision: "review", plan_markdown: "P", codex_prompts: [] };
      },
      runFillers: async () => [{ id: "a", ok: true, summary: "done" }],
      buildTargets: okBuild,
      runReviewer: async () => ({ pass: true, findings: "", checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true } }),
      coordinate: async () => ({ ok: true, log: "coordinated" }),
    };
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false }, deps as any);
    expect(s.phase).toBe("done");
  });

  it("escalates when the scaffolder says so", async () => {
    await seedReq("x");
    const deps = {
      runScaffolder: async () => ({ decision: "escalate", plan_markdown: "P", codex_prompts: [], escalation: { reason: "goal impossible" } }),
      runFillers: async () => [], buildTargets: okBuild, runReviewer: async () => ({}), coordinate: async () => ({ ok: true, log: "" }),
    };
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false }, deps as any);
    expect(s.phase).toBe("escalated");
    expect(s.terminalMessage).toMatch(/goal impossible/);
  });

  it("halts after BUILD_CAP build rounds", async () => {
    await seedReq("x");
    const deps = {
      runScaffolder: async () => ({ decision: "build", plan_markdown: "P", codex_prompts: [{ id: "a", target_decls: [], prompt: "go" }] }),
      runFillers: async () => [{ id: "a", ok: true, summary: "" }],
      buildTargets: okBuild, runReviewer: async () => ({}), coordinate: async () => ({ ok: true, log: "" }),
    };
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false }, deps as any);
    expect(s.phase).toBe("halted");
    expect(s.buildRounds).toBe(BUILD_CAP);
  });

  it("dry-run reaches done with NO deps, never touching real promotion", async () => {
    await seedReq("x");
    // No deps passed: the pipeline must select canned dry-run deps, not realDeps.
    // If realDeps.coordinate ran it would invoke codex / read a non-existent Causalean.lean and throw.
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false, dryRun: true });
    expect(s.phase).toBe("done");
    // No real promotion side effects: no Causalean substrate target was created.
    const target = path.join(causaleanRoot(root), "Causalean", "Substrate", slugToPascal("x"));
    expect(existsSync(target)).toBe(false);
  });

  it("escalates (no retry, no rollback) when coordinate times out after promotion", async () => {
    await seedReq("x");
    let coordinateCalls = 0;
    const deps = {
      runScaffolder: async () => ({ decision: "review", plan_markdown: "P", codex_prompts: [] }),
      runFillers: async () => [], buildTargets: okBuild,
      runReviewer: async () => ({ pass: true, findings: "", checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true } }),
      coordinate: async () => { coordinateCalls++; return { ok: false, timedOut: true, log: "verify step timed out; files left in place" }; },
    };
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false }, deps as any);
    expect(s.phase).toBe("escalated");
    // A timeout is terminal-escalate, NOT a retryable coordinate failure: called once.
    expect(coordinateCalls).toBe(1);
    expect(s.coordinateRounds).toBe(0);
    expect(s.terminalMessage).toMatch(/timed out|human/i);
  });

  it("loops review-fail back to build, halting after REVIEW_CAP", async () => {
    await seedReq("x");
    const deps = {
      runScaffolder: async () => ({ decision: "review", plan_markdown: "P", codex_prompts: [] }),
      runFillers: async () => [], buildTargets: okBuild,
      runReviewer: async () => ({ pass: false, findings: "too specific", checks: { generic: false, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true } }),
      coordinate: async () => ({ ok: true, log: "" }),
    };
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false }, deps as any);
    expect(s.phase).toBe("halted");
    expect(s.reviewRounds).toBe(3);
  });

  it("saves deterministic build-gate rejection with sorry_free=false", async () => {
    await seedReq("x");
    const deps = {
      runScaffolder: async () => ({ decision: "review", plan_markdown: "P", codex_prompts: [] }),
      runFillers: async () => [],
      buildTargets: async () => ({ ok: false, errors: ["boom"], sorryCount: 0, perFile: {} }),
      runReviewer: async () => ({ pass: true, findings: "", checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true } }),
      coordinate: async () => ({ ok: true, log: "" }),
    };
    const s = await runSubstratePipeline({ repoRoot: root, slug: "x", resume: false }, deps as any);
    expect(s.phase).toBe("halted");
    expect(s.lastReview?.pass).toBe(false);
    expect(s.lastReview?.checks.sorry_free).toBe(false);
  });
});
