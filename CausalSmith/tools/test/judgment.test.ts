import { describe, expect, it } from "vitest";
import { extractJsonObject, interventionSchema, reviewResultSchema } from "../src/judgment.js";

describe("reviewResultSchema", () => {
  it("accepts Stage 0.5 journal-review accept results", () => {
    const parsed = reviewResultSchema.parse({
      status: "accept",
      notes: "passes structure, novelty, and correctness",
      dimension_findings: {
        structure: { verdict: "pass", notes: "all required sections are present" },
        novelty: { verdict: "pass", notes: "positioned against closest work" },
        correctness: { verdict: "pass", notes: "proof checks out" },
      },
      journal_recommendations: [
        {
          journal: "Journal of Econometrics",
          tier: "high",
          fit_reasoning: "technical econometric formula with methodological audience",
        },
        {
          journal: "Econometric Theory",
          tier: "high",
          fit_reasoning: "formal theorem note with a theory-facing econometrics audience",
        },
      ],
    });

    expect(parsed.status).toBe("accept");
  });

  it("accepts Stage 0.5 journal-review revise results", () => {
    const parsed = reviewResultSchema.parse({
      status: "revise",
      classification: "correctness",
      dimension_findings: {
        structure: { verdict: "pass", notes: "structure is usable" },
        novelty: { verdict: "pass", notes: "novelty is plausible" },
        correctness: { verdict: "revise", notes: "one support condition is missing" },
      },
      perItemFindings: [
        {
          label: "Theorem 1",
          verdict: "correctness",
          one_line: "inverse step needs a rank hypothesis",
        },
      ],
      verbatim_critique: "Add the missing rank hypothesis and cite it in the proof.",
      journal_recommendations: [],
    });

    expect(parsed.status).toBe("revise");
  });
});

describe("interventionSchema (auto-Bucket-A)", () => {
  it("accepts an Opus-authored Bucket A assumption with route=stage_0", () => {
    const parsed = interventionSchema.parse({
      route: "stage_0",
      reason:
        "case (2b) auto-Bucket-A — Theorem 1 step 4 requires a rank condition on Z; re-derivation infeasible.",
      proposed_action:
        "integrate `A-rank-Z` verbatim under §7 of the .tex; do not introduce any OTHER unstated premise",
      cite: "§7 Assumptions",
      proposed_assumption: {
        label: "A-rank-Z",
        statement: "E[Z Z^\\top] is positive definite.",
        source: "generic rank/regularity condition; not the kernel claim",
      },
    });
    expect(parsed.proposed_assumption?.label).toBe("A-rank-Z");
    expect(parsed.route).toBe("stage_0");
  });

  it("rejects a proposed_assumption paired with route=user", () => {
    expect(() =>
      interventionSchema.parse({
        route: "user",
        reason: "auto-Bucket-A misroute",
        proposed_assumption: {
          label: "A-rank-Z",
          statement: "E[Z Z^\\top] is positive definite.",
        },
      }),
    ).toThrow();
  });

  it("still requires proposed_action when route!=user (auto-Bucket-A path)", () => {
    expect(() =>
      interventionSchema.parse({
        route: "stage_0",
        reason: "missing proposed_action",
        proposed_assumption: {
          label: "A-rank-Z",
          statement: "E[Z Z^\\top] is positive definite.",
        },
      }),
    ).toThrow();
  });
});

describe("interventionSchema (stage_neg1 conjecture-pivot)", () => {
  it("accepts a stage_neg1 pivot with proposed_action", () => {
    const parsed = interventionSchema.parse({
      route: "stage_neg1",
      reason:
        "case 6b — Theorem 1 admits a 2-line counterexample at X=0; conjecture is unsalvageable.",
      proposed_action:
        "abandon angle 0 and draft a different angle from the seed_list",
    });
    expect(parsed.route).toBe("stage_neg1");
  });

  it("rejects a stage_neg1 paired with proposed_assumption", () => {
    expect(() =>
      interventionSchema.parse({
        route: "stage_neg1",
        reason: "conjecture-level reject",
        proposed_action: "pivot",
        proposed_assumption: {
          label: "A-rank-Z",
          statement: "E[Z Z^\\top] is positive definite.",
        },
      }),
    ).toThrow();
  });
});

describe("extractJsonObject", () => {
  it("parses a pure JSON object", () => {
    const out = extractJsonObject('{"route":"stage_2","reason":"ok"}');
    expect(out).toEqual({ route: "stage_2", reason: "ok" });
  });

  it("parses JSON preceded by prose", () => {
    const text = 'Some preamble explaining the diagnosis.\n\n{"route":"stage_0","reason":"x"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_0", reason: "x" });
  });

  it("skips accidentally balanced braces in prose (the {Z=z_l} regression)", () => {
    // Reproduces the production failure: codex's prose contained a backticked
    // Lean set `{Z=z_l}` BEFORE the real JSON. The legacy extractor latched
    // onto the first balanced pair and failed JSON.parse at position 1 (Z
    // is not a quoted key). The fix tries successive `{` positions until one
    // parses successfully.
    const text =
      "L-8 cites P-9 (partition by `{Z=z_l}` and integrability) which the Lean signature dropped.\n\n" +
      '{"route":"stage_2","reason":"Case 4b (encoding drift)","proposed_action":"Re-scaffold."}';
    expect(extractJsonObject(text)).toEqual({
      route: "stage_2",
      reason: "Case 4b (encoding drift)",
      proposed_action: "Re-scaffold.",
    });
  });

  it("skips multiple accidental balanced-brace prose runs before the real JSON", () => {
    const text =
      "Prose with `{a}` and another `{b=c}` and `{x | P x}` ahead.\n" +
      '{"route":"stage_1","reason":"r"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_1", reason: "r" });
  });

  it("parses JSON inside a fenced code block", () => {
    const text = "Here is the verdict:\n```json\n{\"route\":\"user\"}\n```\nDone.";
    expect(extractJsonObject(text)).toEqual({ route: "user" });
  });

  it("returns the first valid JSON when multiple JSON objects are present", () => {
    const text = '{"route":"stage_0"}\n\nlater: {"route":"stage_2"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_0" });
  });

  it("throws when no JSON object is present", () => {
    expect(() => extractJsonObject("plain prose, no braces")).toThrow();
  });

  it("surfaces the underlying JSON.parse error when all candidates fail", () => {
    // No balanced `{...}` parses; legacy first-to-last fallback also fails.
    expect(() => extractJsonObject("foo {bar} baz")).toThrow();
  });
});
