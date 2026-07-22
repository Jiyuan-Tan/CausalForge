import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, beforeEach, describe, expect, it } from "vitest";
import { runStage0_5Core } from "../../src/discovery/stages/d0_5_core.js";
import { citationVerificationCheckpoint, runStage0_5Typed } from "../../src/discovery/stages/d0.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { promptPath } from "../../src/paths.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import { readEscalationLog } from "../../src/discovery/stages/d0_working.js";

const QID = "stat_ate_overlap_decay";
const SPEC = "v1";

describe("D0.5 ExactID reviewer contract", () => {
  it("routes structure/mechanism recovery by causal target rather than testing proof technique", async () => {
    const prompt = await readFile(
      new URL("../../src/discovery/prompts/D0.5/stage0_5_review.txt", import.meta.url),
      "utf8",
    );

    expect(prompt).toContain("causal target [effect OR graph/order/mechanism]");
    expect(prompt).toContain("Cluster by the CAUSAL TARGET, not by the proof technique");
    expect(prompt).toContain("Do NOT re-anchor such a note to Stat merely because it proves a recovery-risk limit");
    expect(prompt).toContain("local information boundary for graph/order/mechanism recovery");
    expect(prompt).toContain("Generic testing, LAN, concentration, or algebra used as the **proof engine** does not by itself demote");
  });

  it("does not force optional envelope optimization or construct an open maintained trainer", async () => {
    const prompt = await readFile(
      new URL("../../src/discovery/prompts/D0.5/stage0_5_math_review.txt", import.meta.url),
      "utf8",
    );
    const normalized = prompt.replace(/\s+/g, " ");

    expect(prompt).toContain("is not redundant merely");
    expect(normalized).toContain("it is not a mandate to optimize every sufficient regularity regime");
    expect(normalized).toContain("do NOT demand or invent a concrete common learner");
    expect(normalized).toContain("mere absence of a constructed trainer does not");
  });
});

let repoRoot: string;
let baseCore: Core;

async function stubPrompts(root: string): Promise<void> {
  for (const name of [
    "stage0_5_math_review.txt",
    "stage0_5_general_review.txt",
    "stage0_5_review.txt",
    "stage0_5_core_adapter.txt",
    "stage0_R_core.txt",
  ]) {
    const target = promptPath(root, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, `stub ${name}`, "utf8");
  }
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

type RoleVerdict = {
  verdict: "pass" | "revise" | "fail";
  badNode?: boolean;
  citedChecks?: Array<{
    node_id: string;
    check_status: "cited-verified" | "cited-verified-attested" | "cited-mismatch" |
      "cited-underspecified" | "cited-source-unverifiable";
    note: string;
  }>;
};

/** Mock: per referee role, write the verdict the scenario dictates. */
function makeDeps(byRole: Record<string, RoleVerdict>): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const m = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
      if (!m) throw new Error("mock: no VERDICT_OUTPUT_PATH");
      const outPath = m[1].trim();
      const pathRole = (outPath.match(/review_(math|general|rubric)\.json$/) ?? [])[1] ?? "math";
      const role = pathRole === "rubric" ? "decision" : pathRole; // why: production names the decision referee's artifact review_rubric.json.
      const spec = byRole[role] ?? { verdict: "pass" };
      const verdict = {
        referee: role,
        verdict: spec.verdict,
        findings:
          spec.verdict === "pass"
            ? []
            : [
                {
                  node_id: spec.badNode ? "thm:made-up" : "thm:lower",
                  code: "omission",
                  one_line: "mock finding",
                },
              ],
        cited_checks: spec.citedChecks ?? [],
      };
      await writeFile(outPath, JSON.stringify(verdict), "utf8");
      return {
        stdout: JSON.stringify({ status: "completed", message: "stub", artifacts: [outPath] }),
        stderr: "",
      };
    },
    runClaude: async () => {
      throw new Error("runClaude not expected at Stage 0.5 core");
    },
    lean: undefined as never,
  };
}

describe("runStage0_5Core (D0.5 math+decision core review)", () => {
  beforeAll(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "stage05core-"));
    await stubPrompts(repoRoot);
    baseCore = JSON.parse(
      await readFile(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8"),
    ) as Core;
    const p = coreJsonPath(makeCtx(repoRoot));
    await mkdir(path.dirname(p), { recursive: true });
  });

  beforeEach(async () => {
    await writeFile(coreJsonPath(makeCtx(repoRoot)), JSON.stringify(baseCore), "utf8");
  });

  afterAll(async () => {
    await rm(repoRoot, { recursive: true, force: true });
  });

  it("combines to pass when every referee passes", async () => {
    const res = await runStage0_5Core({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      deps: makeDeps({ math: { verdict: "pass" }, general: { verdict: "pass" }, decision: { verdict: "pass" } }),
    });
    expect(res.overall).toBe("pass");
    expect(res.verdicts).toHaveLength(2); // why: the cold general referee runs separately after this core panel.
  });

  it("gives every panel referee the full paper rendered from the exact current core", async () => {
    const current = structuredClone(baseCore);
    current.tldr = "CURRENT WHOLE PAPER MARKER";
    await writeFile(coreJsonPath(makeCtx(repoRoot)), JSON.stringify(current), "utf8");
    const prompts: string[] = [];
    const base = makeDeps({ math: { verdict: "pass" }, decision: { verdict: "pass" } });
    const deps: StageDeps = {
      ...base,
      runCodex: async (args: any) => {
        prompts.push(args.prompt);
        return base.runCodex(args);
      },
    };

    await runStage0_5Core({ ctx: makeCtx(repoRoot), state: makeState(), deps });

    expect(prompts).toHaveLength(2);
    for (const prompt of prompts) {
      expect(prompt).toContain("=== FULL CURRENT PAPER UNDER REVIEW ===");
      expect(prompt).toContain("CURRENT WHOLE PAPER MARKER");
      expect(prompt).toContain("=== CORE UNDER REVIEW ===");
    }
  });

  it("combines to revise when the decision referee asks for a revise", async () => {
    const res = await runStage0_5Core({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      deps: makeDeps({ math: { verdict: "pass" }, general: { verdict: "pass" }, decision: { verdict: "revise" } }),
    });
    expect(res.overall).toBe("revise");
  });

  it("combines to fail when the math referee fails (correctness is load-bearing)", async () => {
    const res = await runStage0_5Core({
      ctx: makeCtx(repoRoot),
      state: makeState(),
      deps: makeDeps({ math: { verdict: "fail" }, general: { verdict: "pass" }, decision: { verdict: "revise" } }),
    });
    expect(res.overall).toBe("fail");
  });

  it("THROWS when a referee cites a nonexistent core node", async () => {
    await expect(
      runStage0_5Core({
        ctx: makeCtx(repoRoot),
        state: makeState(),
        deps: makeDeps({ math: { verdict: "revise", badNode: true }, general: { verdict: "pass" }, decision: { verdict: "pass" } }),
      }),
    ).rejects.toThrow(/nonexistent core node/);
  });

  it("requires exactly one math-owned source-match row for each cited node", async () => {
    const cited = structuredClone(baseCore);
    cited.statements.push({
      id: "lem:external-rate",
      kind: "lemma",
      statement: "Published external rate under condition H.",
      depends_on: [],
      status: "cited",
      source: {
        cite: cited.bibliography[0]!.key,
        locator: "Theorem 3.1",
        verbatim_statement: "If H holds, then the risk is at most r_n.",
      },
    });
    await writeFile(coreJsonPath(makeCtx(repoRoot)), JSON.stringify(cited), "utf8");

    const deps = makeDeps({
      math: {
        verdict: "pass",
        citedChecks: [{
          node_id: "lem:external-rate",
          check_status: "cited-verified-attested",
          note: "quantifiers, H, and conclusion match",
        }],
      },
      decision: { verdict: "pass" },
    });
    const res = await runStage0_5Core({
      ctx: makeCtx(repoRoot), state: makeState(), deps,
      citedResolver: async () => ({ text: "If H holds, then the risk is at most r_n.", mode: "attested", detail: "test" }),
    });
    expect(res.overall).toBe("pass");
    expect(res.cited_checks).toHaveLength(1);

    await expect(runStage0_5Core({
      ctx: makeCtx(repoRoot), state: makeState(),
      deps: makeDeps({ math: { verdict: "pass" }, decision: { verdict: "pass" } }),
      citedResolver: async () => ({ text: "source", mode: "attested", detail: "test" }),
    })).rejects.toThrow(/omitted cited check/);

    await expect(runStage0_5Core({
      ctx: makeCtx(repoRoot), state: makeState(),
      deps: makeDeps({
        math: {
          verdict: "pass",
          citedChecks: [{
            node_id: "lem:external-rate",
            check_status: "cited-verified-attested",
            note: "math-owned match",
          }],
        },
        decision: {
          verdict: "pass",
          citedChecks: [{
            node_id: "lem:external-rate",
            check_status: "cited-verified-attested",
            note: "decision must not duplicate the match",
          }],
        },
      }),
      citedResolver: async () => ({ text: "source", mode: "attested", detail: "test" }),
    })).rejects.toThrow(/only the math referee/);
  });

  it("routes an unavailable source to external verification without calling it revise/fail", async () => {
    const cited = structuredClone(baseCore);
    cited.statements.push({
      id: "lem:paywalled-result",
      kind: "lemma",
      statement: "Published result behind an unavailable source.",
      depends_on: [],
      status: "cited",
      source: { cite: cited.bibliography[0]!.key, locator: "Theorem 2", doi: "10.1/example" },
    });
    await writeFile(coreJsonPath(makeCtx(repoRoot)), JSON.stringify(cited), "utf8");
    const res = await runStage0_5Core({
      ctx: makeCtx(repoRoot), state: makeState(),
      deps: makeDeps({
        math: {
          verdict: "pass",
          citedChecks: [{
            node_id: "lem:paywalled-result",
            check_status: "cited-source-unverifiable",
            note: "DOI source unavailable",
          }],
        },
        decision: { verdict: "pass" },
      }),
      citedResolver: async () => ({ text: "", mode: "unverifiable", detail: "paywalled" }),
    });
    expect(res.overall).toBe("pass");
    expect(res.citation_verification_required.map((c) => c.node_id)).toEqual(["lem:paywalled-result"]);
    expect(citationVerificationCheckpoint(res)).toMatchObject({
      stage: "0.5",
      status: "checkpoint",
      advance: false,
    });
    expect(citationVerificationCheckpoint(res)?.message).toMatch(/ask the user/);
  });

  it("deterministically turns cited mismatch into revise even if the broad verdict says pass", async () => {
    const cited = structuredClone(baseCore);
    cited.statements.push({
      id: "lem:misquoted-result",
      kind: "lemma",
      statement: "Claim stronger than the source.",
      depends_on: [],
      status: "cited",
      source: { cite: cited.bibliography[0]!.key, locator: "Theorem 4", verbatim_statement: "Weaker source claim." },
    });
    await writeFile(coreJsonPath(makeCtx(repoRoot)), JSON.stringify(cited), "utf8");
    const res = await runStage0_5Core({
      ctx: makeCtx(repoRoot), state: makeState(),
      deps: makeDeps({
        math: {
          verdict: "pass",
          citedChecks: [{ node_id: "lem:misquoted-result", check_status: "cited-mismatch", note: "source is weaker" }],
        },
        decision: { verdict: "pass" },
      }),
      citedResolver: async () => ({ text: "Weaker source claim.", mode: "attested", detail: "test" }),
    });
    expect(res.overall).toBe("revise");
  });
});

describe("runStage0_5Typed provisional D0.R transaction", () => {
  beforeAll(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "stage05txn-"));
    await stubPrompts(repoRoot);
    baseCore = JSON.parse(
      await readFile(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8"),
    ) as Core;
    await mkdir(path.dirname(coreJsonPath(makeCtx(repoRoot))), { recursive: true });
  });

  afterAll(async () => {
    await rm(repoRoot, { recursive: true, force: true });
  });

  it("rolls back core, tex, pending changes, and state metadata when the follow-up panel does not converge", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.design_decisions = { keep: "authoritative" };
    state.added_assumptions = [{
      label: "ass:existing",
      statement: "existing approved metadata",
      user_approved: true,
      source: "test",
      classification: "faithful-refinement",
    }];
    const cp = coreJsonPath(ctx);
    const initialCore = JSON.stringify(baseCore, null, 2);
    await writeFile(cp, initialCore, "utf8");
    const texPath = artifactPaths(ctx, state).tex;
    await mkdir(path.dirname(texPath), { recursive: true });
    await writeFile(texPath, "authoritative tex", "utf8");
    const pendingPath = path.join(path.dirname(cp), "d0r_pending_changes.json");
    const initialPending = JSON.stringify({ changes: [{ id: "authoritative-prior" }] }, null, 2);
    await writeFile(pendingPath, initialPending, "utf8");

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          const role = outPath.endsWith("review_rubric.json") ? "decision" : "math";
          await writeFile(outPath, JSON.stringify({
            referee: role,
            verdict: "revise",
            findings: [{ node_id: "thm:lower", code: "omission", one_line: "persistent mock finding" }],
            cited_checks: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        const coreMatch = prompt.match(/CORE_FILE: (.+)/);
        if (!coreMatch) throw new Error("mock: expected reviewer or D0.R prompt");
        const editedPath = coreMatch[1].trim();
        const edited = JSON.parse(await readFile(editedPath, "utf8")) as Core;
        edited.assumptions[0]!.condition += " (provisional D0.R edit)";
        await writeFile(editedPath, JSON.stringify(edited, null, 2), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [editedPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });

    expect(result.message).toMatch(/non-converging/i);
    expect(await readFile(cp, "utf8")).toBe(initialCore);
    expect(await readFile(texPath, "utf8")).toBe("authoritative tex");
    expect(await readFile(pendingPath, "utf8")).toBe(initialPending);
    expect(state.design_decisions).toEqual({ keep: "authoritative" });
    expect(state.added_assumptions).toEqual([expect.objectContaining({ label: "ass:existing" })]);
    const injected = (await readEscalationLog(ctx)).at(-1)!;
    expect(injected.directive).toContain("persistent mock finding");
    expect(injected.directive).toContain("complete current reviewer payload");
    expect(injected.required_core_targets).toContain("thm:lower");
  });

  it("rolls back provisional D0.R edits when math passes but the cold tier is below the target floor", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.design_decisions = { keep: "authoritative" };
    const cp = coreJsonPath(ctx);
    const initialCore = JSON.stringify(baseCore, null, 2);
    await writeFile(cp, initialCore, "utf8");
    const texPath = artifactPaths(ctx, state).tex;
    await mkdir(path.dirname(texPath), { recursive: true });
    await writeFile(texPath, "authoritative tex", "utf8");
    const pendingPath = path.join(path.dirname(cp), "d0r_pending_changes.json");
    await rm(pendingPath, { force: true });
    let panelCalls = 0;

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          const role = outPath.endsWith("review_rubric.json") ? "decision" : "math";
          const firstPanel = panelCalls++ < 2;
          await writeFile(outPath, JSON.stringify({
            referee: role,
            verdict: firstPanel ? "revise" : "pass",
            findings: firstPanel
              ? [{ node_id: "thm:lower", code: "omission", one_line: "repair once" }]
              : [],
            cited_checks: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        const coreMatch = prompt.match(/CORE_FILE: (.+)/);
        if (coreMatch) {
          const editedPath = coreMatch[1].trim();
          const edited = JSON.parse(await readFile(editedPath, "utf8")) as Core;
          edited.assumptions[0]!.condition += " (provisional D0.R edit)";
          await writeFile(editedPath, JSON.stringify(edited, null, 2), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [editedPath] }), stderr: "" };
        }
        return {
          stdout: JSON.stringify({
            tier: "subfield",
            salvageable: false,
            flagged_conjecture_labels: [],
            critique: "valid mathematics, below the requested field floor",
            flagship_potential: false,
          }),
          stderr: "",
        };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });

    expect(result.message).toMatch(/below novelty floor/i);
    expect(await readFile(cp, "utf8")).toBe(initialCore);
    expect(await readFile(texPath, "utf8")).toBe("authoritative tex");
    expect(existsSync(pendingPath)).toBe(false);
    expect(state.design_decisions).toEqual({ keep: "authoritative" });
    expect(state.added_assumptions).toEqual([]);
  });

  it("rolls back a worker write when D0.R fails after touching core.json", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.design_decisions = { keep: "authoritative" };
    const cp = coreJsonPath(ctx);
    const initialCore = JSON.stringify(baseCore, null, 2);
    await writeFile(cp, initialCore, "utf8");
    const texPath = artifactPaths(ctx, state).tex;
    await mkdir(path.dirname(texPath), { recursive: true });
    await writeFile(texPath, "authoritative tex", "utf8");

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          const role = outPath.endsWith("review_rubric.json") ? "decision" : "math";
          await writeFile(outPath, JSON.stringify({
            referee: role,
            verdict: "revise",
            findings: [{ node_id: "thm:lower", code: "omission", one_line: "repair once" }],
            cited_checks: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        const coreMatch = prompt.match(/CORE_FILE: (.+)/);
        if (!coreMatch) throw new Error("mock: expected reviewer or D0.R prompt");
        // Simulate a worker that mutates the shared file and then returns a
        // nominal completion whose artifact is not schema-valid.
        await writeFile(coreMatch[1].trim(), "{truncated", "utf8");
        return {
          stdout: JSON.stringify({ status: "completed", artifacts: [coreMatch[1].trim()] }),
          stderr: "",
        };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    // A corrupt worker write is contained gracefully: the stage checkpoints to the
    // orchestrator (no throw) and the transaction restores the pre-stage core
    // and .tex, so no worker garbage survives.
    const res = await runStage0_5Typed({ ctx, state, deps });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toMatch(/corrupt or unparseable/i);
    expect(JSON.parse(await readFile(cp, "utf8"))).toEqual(baseCore);
    expect(await readFile(texPath, "utf8")).toBe("authoritative tex");
    expect(state.design_decisions).toEqual({ keep: "authoritative" });
  });

  it("rebuilds the verified render bundle before committing a passing D0.R edit", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const cp = coreJsonPath(ctx);
    await writeFile(cp, JSON.stringify(baseCore, null, 2), "utf8");
    const texPath = artifactPaths(ctx, state).tex;
    await mkdir(path.dirname(texPath), { recursive: true });
    await writeFile(texPath, "pre-revision tex", "utf8");
    let panelCalls = 0;

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          const role = outPath.endsWith("review_rubric.json") ? "decision" : "math";
          const firstPanel = panelCalls++ < 2;
          await writeFile(outPath, JSON.stringify({
            referee: role,
            verdict: firstPanel ? "revise" : "pass",
            findings: firstPanel
              ? [{ node_id: "thm:lower", code: "positioning", one_line: "sync the note" }]
              : [],
            cited_checks: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        const coreMatch = prompt.match(/CORE_FILE: (.+)/);
        if (coreMatch) {
          const editedPath = coreMatch[1].trim();
          const edited = JSON.parse(await readFile(editedPath, "utf8")) as Core;
          edited.tldr = "A passing D0.R render-bundle revision.";
          await writeFile(editedPath, JSON.stringify(edited, null, 2), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [editedPath] }), stderr: "" };
        }
        return {
          stdout: JSON.stringify({
            tier: "field",
            salvageable: false,
            flagged_conjecture_labels: [],
            critique: "field-tier pass",
            flagship_potential: false,
          }),
          stderr: "",
        };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });
    expect(result.message).toMatch(/PASS/i);
    const tex = await readFile(texPath, "utf8");
    expect(tex).toContain("A passing D0.R render-bundle revision.");
    const stem = path.basename(texPath, path.extname(texPath));
    const pdf = await readFile(path.join(path.dirname(texPath), `${stem}.pdf`));
    const log = await readFile(path.join(path.dirname(texPath), `${stem}.log`), "utf8");
    expect(pdf.subarray(0, 5).toString("ascii")).toBe("%PDF-");
    expect(log).toContain("Output written on");
  });
});
