// CausalSmith/tools/test/substrate/types.test.ts
import { describe, it, expect } from "vitest";
import { parseScaffolderOutput, parseReviewVerdict, substrateStateSchema } from "../../src/substrate/types.js";

describe("substrate types", () => {
  it("parses a valid scaffolder build output", () => {
    const out = parseScaffolderOutput({
      decision: "build",
      plan_markdown: "## Plan\n- step",
      codex_prompts: [{ id: "p1", target_decls: ["foo"], prompt: "prove foo" }],
    });
    expect(out.decision).toBe("build");
    expect(out.codex_prompts).toHaveLength(1);
  });

  it("defaults codex_prompts to [] when omitted (review/escalate)", () => {
    const out = parseScaffolderOutput({ decision: "review", plan_markdown: "done" });
    expect(out.codex_prompts).toEqual([]);
  });

  it("rejects an unknown decision", () => {
    expect(() => parseScaffolderOutput({ decision: "ship", plan_markdown: "x" })).toThrow();
  });

  it("parses a review verdict with all checks", () => {
    const v = parseReviewVerdict({
      pass: false,
      findings: "too specific",
      checks: { generic: false, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true },
    });
    expect(v.pass).toBe(false);
    expect(v.checks.generic).toBe(false);
  });

  it("rejects new reviewer output that omits the layering check", () => {
    expect(() => parseReviewVerdict({
      pass: true,
      findings: "",
      checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true },
    })).toThrow(/layered/);
  });

  it("round-trips a substrate state", () => {
    const s = substrateStateSchema.parse({
      slug: "bh_affinity", phase: "build", buildRounds: 0, reviewRounds: 0,
      moduleFiles: [], lastReport: null, lastReview: null, terminalMessage: null,
    });
    expect(s.slug).toBe("bh_affinity");
    expect(s.phase).toBe("build");
  });
});
