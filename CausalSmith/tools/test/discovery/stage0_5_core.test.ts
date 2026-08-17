import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, beforeEach, describe, expect, it } from "vitest";
import { compactD05DecisionAdapter, compactD05DecisionPrompt, runStage0_5Core } from "../../src/discovery/stages/d0_5_core.js";
import { citationVerificationCheckpoint, runStage0_5Typed } from "../../src/discovery/stages/d0.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import {
  hasValidD05AcceptanceReceipt,
  writeD05AcceptanceReceipt,
} from "../../src/discovery/stages/d0_acceptance.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { promptPath, statePath } from "../../src/paths.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import {
  readEscalationLog,
  saveWorkingState,
  workingPath,
  WORKING_STORE_FORMAT,
} from "../../src/discovery/stages/d0_working.js";

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
    const effective = compactD05DecisionPrompt(prompt);
    expect(effective).not.toContain("=== TIER-AWARENESS REASONING");
    expect(effective).toContain("=== PROPOSAL_PROMISE_GAP");
    expect(effective).toContain("Proof correctness belongs to the math referee");
    const adapter = await readFile(
      new URL("../../src/discovery/prompts/D0.5/stage0_5_core_adapter.txt", import.meta.url),
      "utf8",
    );
    const decisionAdapter = compactD05DecisionAdapter(adapter);
    expect(decisionAdapter).not.toContain("REPRODUCE its `proof_tex`");
    expect(decisionAdapter).not.toContain("math CLAIM itself is wrong");
    expect(decisionAdapter).not.toContain("Tiering still informs");
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
    await writeFile(
      target,
      name === "stage0_5_core_adapter.txt"
        ? `stub ${name}\n=== VERDICT OUTPUT ===\nUse \`revise\` for fixable defects,\n\`fail\` only if the math CLAIM itself is wrong, \`pass\` if the core is sound at your role's\nstandard.\n`
        : `stub ${name}`,
      "utf8",
    );
  }
}

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, qid: QID, specialization: SPEC, dryRun: false, resume: false };
}

function makeState(): StateJson {
  return {
    stage_completed: "0",
    lean_subdir: "CausalSmith/Stat/STAT_AteOverlapDecay_Research",
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

  it("gives every panel referee one authoritative core without a duplicate TeX render", async () => {
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
      expect(prompt).toContain("CURRENT WHOLE PAPER MARKER");
      expect(prompt).toContain("=== CORE UNDER REVIEW ===");
      expect(prompt).not.toContain("=== FULL CURRENT PAPER UNDER REVIEW ===");
      expect(prompt).not.toContain("Substrate-survey rule:");
      expect(prompt).not.toContain("Lean artifact directory:");
    }
    const decisionPrompt = prompts.find((prompt) => prompt.includes("stub stage0_5_review.txt"))!;
    expect(decisionPrompt).toContain("Do not reproduce proofs or assess tier");
    expect(decisionPrompt).not.toContain("REPRODUCE its `proof_tex`");
    expect(decisionPrompt).not.toContain("focus on the MATH");
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

  it("rolls back core, pending changes, and state metadata when the follow-up panel does not converge", async () => {
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
    Object.assign(state.proposed_from!, { current_angle_index: 0, current_version: 8 });
    await writeFile(protoCoreJsonPath(ctx), initialCore, "utf8");
    await saveWorkingState(ctx, {
      round: 40,
      proposal_revision: "angle:0/version:8",
      solved: {},
      store_format: WORKING_STORE_FORMAT,
    });
    await writeD05AcceptanceReceipt(ctx, state);
    expect(await hasValidD05AcceptanceReceipt(ctx, state)).toBe(true);
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
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });

    expect(result.message).toMatch(/non-converging/i);
    expect(await readFile(cp, "utf8")).toBe(initialCore);
    expect(await readFile(pendingPath, "utf8")).toBe(initialPending);
    expect(state.design_decisions).toEqual({ keep: "authoritative" });
    expect(state.added_assumptions).toEqual([expect.objectContaining({ label: "ass:existing" })]);
    expect(await hasValidD05AcceptanceReceipt(ctx, state)).toBe(false);
    const injected = (await readEscalationLog(ctx)).at(-1)!;
    expect(injected.directive).toContain("persistent mock finding");
    expect(injected.directive).toContain("complete current reviewer payload");
    expect(injected.required_core_targets).toContain("thm:lower");
  });

  it("banks panel-cleared D0.R prose before a later different-finding fail rollback", async () => {
    const localRoot = await mkdtemp(path.join(os.tmpdir(), "stage05prose-"));
    try {
      await stubPrompts(localRoot);
      const ctx = makeCtx(localRoot);
      const state = makeState();
      const cp = coreJsonPath(ctx);
      await mkdir(path.dirname(cp), { recursive: true });
      await writeFile(cp, JSON.stringify(baseCore, null, 2), "utf8");
      await writeFile(protoCoreJsonPath(ctx), JSON.stringify(baseCore, null, 2), "utf8");
      await saveWorkingState(ctx, {
        round: 0,
        solved: {},
        store_format: WORKING_STORE_FORMAT,
      });
      const originalLower = baseCore.statements.find((statement) => statement.id === "thm:lower")!;
      let panelRound = 0;
      let panelCalls = 0;

      const deps: StageDeps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
          if (verdictMatch) {
            const outPath = verdictMatch[1].trim();
            const finding = panelRound === 0
              ? { node_id: "thm:lower", code: "accepted-bank-omitted", one_line: "add the accepted comparison" }
              : { node_id: "thm:lower", code: "new-comparator-omitted", one_line: "different later issue" };
            const role = outPath.endsWith("review_rubric.json") ? "decision" : "math";
            await writeFile(outPath, JSON.stringify({
              referee: role,
              verdict: panelRound > 0 && role === "math" ? "fail" : "revise",
              findings: [finding],
              cited_checks: [],
            }), "utf8");
            panelCalls += 1;
            if (panelCalls === 2) {
              panelCalls = 0;
              panelRound += 1;
            }
            return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
          }
          const coreMatch = prompt.match(/CORE_FILE: (.+)/);
          if (coreMatch) {
            const editedPath = coreMatch[1].trim();
            const edited = JSON.parse(await readFile(editedPath, "utf8")) as Core;
            edited.related_work = "Panel-cleared accepted-bank comparison.";
            const lower = edited.statements.find((statement) => statement.id === "thm:lower")!;
            lower.gap = "Panel-cleared exact comparison gap.";
            lower.proof_tex = "PROVISIONAL FORMAL BYTES MUST ROLL BACK";
            await writeFile(editedPath, JSON.stringify(edited, null, 2), "utf8");
            return { stdout: JSON.stringify({ status: "completed", artifacts: [editedPath] }), stderr: "" };
          }
          return { stdout: JSON.stringify({
            tier: "field", salvageable: false, improvement_directive: "",
            flagged_conjecture_labels: [], critique: "field-tier triage",
            flagship_potential: false, flagship_directive: "",
          }), stderr: "" };
        },
        runClaude: async ({ prompt }: { prompt: string }) =>
          (await deps.runCodex({ prompt } as never)).stdout,
        lean: undefined as never,
      };

      const result = await runStage0_5Typed({ ctx, state, deps });
      expect(result.message).toMatch(/FAIL/i);
      const persisted = JSON.parse(await readFile(cp, "utf8")) as Core;
      const persistedLower = persisted.statements.find((statement) => statement.id === "thm:lower")!;
      expect(persisted.related_work).toBe("Panel-cleared accepted-bank comparison.");
      expect(persistedLower.gap).toBe("Panel-cleared exact comparison gap.");
      expect(persistedLower.proof_tex).toBe(originalLower.proof_tex);
      const working = JSON.parse(await readFile(workingPath(ctx), "utf8"));
      expect(working.prose_overlay.related_work).toBe("Panel-cleared accepted-bank comparison.");
      expect((JSON.parse(await readFile(protoCoreJsonPath(ctx), "utf8")) as Core).related_work)
        .toBe(baseCore.related_work);
      const rendered = await readFile(artifactPaths(ctx, state).tex, "utf8");
      expect(rendered).toContain("Panel-cleared accepted-bank comparison.");
      expect(rendered).not.toContain("PROVISIONAL FORMAL BYTES MUST ROLL BACK");
    } finally {
      await rm(localRoot, { recursive: true, force: true });
    }
  });

  it("rolls back provisional D0.R edits when math passes but the cold tier is below the target floor", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.design_decisions = { keep: "authoritative" };
    const cp = coreJsonPath(ctx);
    const initialCore = JSON.stringify(baseCore, null, 2);
    await writeFile(cp, initialCore, "utf8");
    const pendingPath = path.join(path.dirname(cp), "d0r_pending_changes.json");
    await rm(pendingPath, { force: true });
    let panelCalls = 0;
    let d0rCalls = 0;

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
          d0rCalls++;
          const editedPath = coreMatch[1].trim();
          const edited = JSON.parse(await readFile(editedPath, "utf8")) as Core;
          edited.assumptions[0]!.condition += " (provisional D0.R edit)";
          await writeFile(editedPath, JSON.stringify(edited, null, 2), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [editedPath] }), stderr: "" };
        }
        return {
          stdout: JSON.stringify({
            tier: "subfield",
            // SALVAGEABLE, deliberately. The D0.5.G triage read now runs concurrently with
            // round 0's panel, and `decideTriageKill` halts the run outright on
            // below-floor + NOT salvageable — which would return before D0.R ever runs and
            // leave every rollback assertion below vacuously true. Keeping it salvageable
            // holds this test on the path it exists to cover: revise → D0.R edit → panel
            // pass → authoritative below-floor tier → rollback. The kill path is covered by
            // the next test.
            salvageable: true,
            improvement_directive: "derive the constant from primitive rate conditions",
            flagged_conjecture_labels: [],
            critique: "valid mathematics, below the requested field floor",
            flagship_potential: false,
            flagship_directive: "",
          }),
          stderr: "",
        };
      },
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });

    expect(result.message).toMatch(/below novelty floor/i);
    // The point of the test: D0.R DID run and its provisional edit was rolled back.
    expect(d0rCalls).toBeGreaterThan(0);
    expect(await readFile(cp, "utf8")).toBe(initialCore);
    expect(existsSync(pendingPath)).toBe(false);
    expect(state.design_decisions).toEqual({ keep: "authoritative" });
    expect(state.added_assumptions).toEqual([]);
  });

  it("halts at the D0.5.G triage kill before D0.R spends the revise budget", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const cp = coreJsonPath(ctx);
    const initialCore = JSON.stringify(baseCore, null, 2);
    await writeFile(cp, initialCore, "utf8");
    let d0rCalls = 0;

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          await writeFile(outPath, JSON.stringify({
            referee: outPath.endsWith("review_rubric.json") ? "decision" : "math",
            verdict: "revise",
            findings: [{ node_id: "thm:lower", code: "omission", one_line: "repair once" }],
            cited_checks: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        if (prompt.match(/CORE_FILE: (.+)/)) {
          d0rCalls++;
          throw new Error("D0.R must not run: the triage kill returns first");
        }
        return {
          stdout: JSON.stringify({
            tier: "subfield",
            salvageable: false,
            improvement_directive: "",
            flagged_conjecture_labels: [],
            critique: "the kernel is a relabelling of a known result",
            flagship_potential: false,
            flagship_directive: "",
          }),
          stderr: "",
        };
      },
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });

    expect(result.message).toMatch(/below novelty floor \(triage/i);
    expect(d0rCalls).toBe(0);
    expect(await readFile(cp, "utf8")).toBe(initialCore);
    // The halt must still say the math was never cleared, so the note is not banked as
    // merely under-novel.
    expect(result.message).toMatch(/unrepaired/i);
  });

  it("rolls back a worker write when D0.R fails after touching core.json", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.design_decisions = { keep: "authoritative" };
    const cp = coreJsonPath(ctx);
    const initialCore = JSON.stringify(baseCore, null, 2);
    await writeFile(cp, initialCore, "utf8");

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
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    // A corrupt worker write is contained gracefully: the stage checkpoints to the
    // orchestrator (no throw) and the transaction restores the pre-stage core
    // so no worker garbage survives.
    const res = await runStage0_5Typed({ ctx, state, deps });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toMatch(/corrupt or unparseable/i);
    expect(JSON.parse(await readFile(cp, "utf8"))).toEqual(baseCore);
    expect(state.design_decisions).toEqual({ keep: "authoritative" });
    const persistedState = JSON.parse(await readFile(
      statePath(ctx.repoRoot, ctx.qid, ctx.specialization),
      "utf8",
    )) as StateJson;
    expect(persistedState.flags.d0_loop_counters?.revise_rounds).toBe(1);
  });

  it("publishes the updated TeX source only after a passing D0.R transaction", async () => {
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
            improvement_directive: "",
            flagged_conjecture_labels: [],
            critique: "field-tier pass",
            flagship_potential: false,
            flagship_directive: "",
          }),
          stderr: "",
        };
      },
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });
    expect(result.message).toMatch(/PASS/i);
    const tex = await readFile(texPath, "utf8");
    expect(tex).toContain("A passing D0.R render-bundle revision.");
  });

  it("reviews and commits the third allowed D0.R edit instead of rolling it back at the cap", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    const cp = coreJsonPath(ctx);
    await writeFile(cp, JSON.stringify(baseCore, null, 2), "utf8");
    let panelRound = 0;
    let panelCallsInRound = 0;
    let d0rCalls = 0;

    const findingsByRound = [
      [
        { node_id: "thm:lower", code: "first-a", one_line: "first repair" },
        { node_id: "thm:lower", code: "first-b", one_line: "first repair" },
        { node_id: "thm:lower", code: "first-c", one_line: "first repair" },
      ],
      [
        { node_id: "thm:lower", code: "second-a", one_line: "second repair" },
        { node_id: "thm:lower", code: "second-b", one_line: "second repair" },
      ],
      [{ node_id: "thm:lower", code: "third", one_line: "third repair" }],
      [],
    ];

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          const role = outPath.endsWith("review_rubric.json") ? "decision" : "math";
          const findings = findingsByRound[panelRound]!;
          await writeFile(outPath, JSON.stringify({
            referee: role,
            verdict: findings.length === 0 ? "pass" : "revise",
            findings,
            cited_checks: [],
          }), "utf8");
          panelCallsInRound++;
          if (panelCallsInRound === 2) {
            panelCallsInRound = 0;
            panelRound++;
          }
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        const coreMatch = prompt.match(/CORE_FILE: (.+)/);
        if (coreMatch) {
          d0rCalls++;
          const editedPath = coreMatch[1].trim();
          const edited = JSON.parse(await readFile(editedPath, "utf8")) as Core;
          edited.tldr = `D0.R repair ${d0rCalls}`;
          await writeFile(editedPath, JSON.stringify(edited, null, 2), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [editedPath] }), stderr: "" };
        }
        return {
          stdout: JSON.stringify({
            tier: "field",
            salvageable: false,
            improvement_directive: "",
            flagged_conjecture_labels: [],
            critique: "field-tier pass",
            flagship_potential: false,
            flagship_directive: "",
          }),
          stderr: "",
        };
      },
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });
    expect(result.message).toMatch(/PASS/i);
    expect(d0rCalls).toBe(3);
    expect(panelRound).toBe(4);
    expect((JSON.parse(await readFile(cp, "utf8")) as Core).tldr).toBe("D0.R repair 3");
    expect(state.flags.d0_loop_counters?.revise_rounds).toBe(3);
  });

  it("does not consume another D0.R edit when a resumed panel passes", async () => {
    const ctx = makeCtx(repoRoot);
    const state = makeState();
    state.flags.d0_loop_counters = { solve_rounds: 2, revise_rounds: 2, consistency_heals: 0 };
    Object.assign(state.proposed_from!, {
      current_angle_index: 0,
      current_version: 8,
    });
    await writeFile(protoCoreJsonPath(ctx), JSON.stringify(baseCore, null, 2), "utf8");
    await saveWorkingState(ctx, {
      round: 40,
      proposal_revision: "angle:0/version:8",
      solved: {},
      store_format: WORKING_STORE_FORMAT,
    });
    await writeFile(coreJsonPath(ctx), JSON.stringify(baseCore, null, 2), "utf8");

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          await writeFile(outPath, JSON.stringify({
            referee: outPath.endsWith("review_rubric.json") ? "decision" : "math",
            verdict: "pass",
            findings: [],
            cited_checks: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        return {
          stdout: JSON.stringify({
            tier: "field",
            salvageable: false,
            improvement_directive: "",
            flagged_conjecture_labels: [],
            critique: "field-tier pass",
            flagship_potential: false,
            flagship_directive: "",
          }),
          stderr: "",
        };
      },
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });
    expect(result.message).toMatch(/PASS/i);
    expect(state.flags.d0_loop_counters).toEqual({
      solve_rounds: 2,
      revise_rounds: 2,
      consistency_heals: 0,
    });
    expect(await hasValidD05AcceptanceReceipt(ctx, state)).toBe(true);
  });

  it("routes a proposal-topic mismatch before dispatching or charging D0.R", async () => {
    const ctx = { ...makeCtx(repoRoot), noveltyTarget: "incremental" as const };
    const state = makeState();
    state.flags.d0_loop_counters = { solve_rounds: 2, revise_rounds: 1, consistency_heals: 0 };
    await writeFile(coreJsonPath(ctx), JSON.stringify(baseCore, null, 2), "utf8");
    let d0rCalls = 0;

    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const verdictMatch = prompt.match(/VERDICT_OUTPUT_PATH: (.+)/);
        if (verdictMatch) {
          const outPath = verdictMatch[1].trim();
          const decision = outPath.endsWith("review_rubric.json");
          await writeFile(outPath, JSON.stringify({
            referee: decision ? "decision" : "math",
            verdict: decision ? "revise" : "pass",
            findings: decision ? [{
              node_id: "thm:lower",
              code: "novelty-kernel-substituted",
              one_line: "delivered kernel is narrower than the durable topic",
            }] : [],
            cited_checks: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        }
        if (prompt.includes("CORE_FILE:")) {
          d0rCalls++;
          throw new Error("D0.R must not run for a durable topic mismatch");
        }
        return {
          stdout: JSON.stringify({
            tier: "incremental",
            salvageable: false,
            improvement_directive: "",
            flagged_conjecture_labels: [],
            critique: "incremental scope",
            flagship_potential: false,
            flagship_directive: "",
          }),
          stderr: "",
        };
      },
      // D0.5.G moved to the claude runner (constants.ts::MODEL_PLAN.stage0_5_general),
      // so a D0.5 fixture has to answer BOTH runners. Delegating to this mock's own
      // runCodex keeps the fixture modelling ONE referee panel, and keeps these
      // scenarios byte-identical to what they asserted while D0.5.G was a codex call.
      runClaude: async ({ prompt }: { prompt: string }) =>
        (await deps.runCodex({ prompt } as never)).stdout,
      lean: undefined as never,
    };

    const result = await runStage0_5Typed({ ctx, state, deps });
    expect(result.message).toMatch(/state\.proposed_from\.topic|proposed-topic update/i);
    expect(d0rCalls).toBe(0);
    expect(state.flags.d0_loop_counters?.revise_rounds).toBe(1);
    const entries = await readEscalationLog(ctx);
    expect(entries.at(-1)?.provenance_only).toBe(true);
    expect(entries.at(-1)?.required_core_targets ?? []).toEqual([]);
  });
});
