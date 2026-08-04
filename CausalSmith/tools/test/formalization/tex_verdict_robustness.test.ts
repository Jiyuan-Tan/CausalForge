import { describe, expect, it } from "vitest";
import { parseJsonObject, verdictClass } from "../../src/formalization/reviewer_verdicts.js";
import { containsLikelyDecodedTexNewlines } from "../../src/discovery/core/latex_serialization.js";

describe("verdictClass — TeX commands are not verdict tokens (2026-08-01 audit)", () => {
  it("a matched note mentioning \\partial does not grade as drift", () => {
    expect(verdictClass("matched; uses \\partial_x f throughout")).toBe("pass");
    expect(verdictClass("matched, but note \\partial is used in the operator")).toBe("pass");
  });

  it("\\begin{aligned} does not grade junk as pass, and a real verdict word inside a TeX group still fails", () => {
    expect(verdictClass("\\begin{aligned} rows \\end{aligned}")).toBe("unknown");
    // A `{`-boundary exclusion would hide this genuine contrast verdict — the
    // env-name STRIP handles `aligned` instead, so \emph{drifts} stays visible.
    expect(verdictClass("matched, but \\emph{drifts} in the constant")).toBe("fail");
  });

  it("plain verdicts are unchanged", () => {
    expect(verdictClass("faithful")).toBe("pass");
    expect(verdictClass("drift")).toBe("fail");
    expect(verdictClass("mostly faithful with a caveat")).toBe("unknown");
  });
});

describe("parseJsonObject — LaTeX in a reviewer note does not kill the verdict", () => {
  it("parses a verdict whose note carries under-escaped TeX", () => {
    const stdout =
      'Verdict follows.\n{"statement_verdicts":[{"obj_id":"T-1","verdict":"drift","note":"should be \\(\\forall n\\) eventually"}]}';
    const out = parseJsonObject(stdout);
    expect(Array.isArray(out.statement_verdicts)).toBe(true);
  });
});

describe("containsLikelyDecodedTexNewlines — raw-fallback fail-closed detector", () => {
  it("flags the \\n-family decode signature and passes ordinary newlines", () => {
    expect(containsLikelyDecodedTexNewlines({ note: "x \neq 0 holds" })).toBe(true);
    expect(containsLikelyDecodedTexNewlines({ note: "x \nabla-free" })).toBe(true);
    expect(containsLikelyDecodedTexNewlines({ note: "line one\nand line two" })).toBe(false);
    expect(containsLikelyDecodedTexNewlines({ note: "correctly escaped \\neq stays" })).toBe(false);
  });
});
