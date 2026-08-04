import { describe, expect, it } from "vitest";
import { isAssumeTheCruxNarrowing, isResultClassDegradation } from "../../src/discovery/stages/d0.js";

// 2026-08-01 TeX audit: these heuristics run on LaTeX-bearing statement text.
// Abbreviation/decimal periods must not truncate the clause scan, the regime
// whitelist must apply to BOTH premise branches, and a crux word anywhere in a
// premise clause vetoes the regime suppression (false negatives launder the
// crux; false positives merely route to review).
describe("isAssumeTheCruxNarrowing — TeX-aware clause scanning", () => {
  const change = (current: string, proposed: string) => ({ id: "thm:x", direction: "narrow", current, proposed });

  it("does not gate a whitelisted regime restriction carrying a decimal", () => {
    expect(
      isAssumeTheCruxNarrowing(
        change("The rate holds under overlap.", "Assume overlap at level 0.05 with margin \\(\\delta\\). The rate holds."),
      ),
    ).toBe(false);
  });

  it("does not gate an i.i.d. regime premise (masked abbreviation reaches the whitelist)", () => {
    expect(
      isAssumeTheCruxNarrowing(
        change("The CLT applies.", "Assume the errors are i.i.d. with mean zero. The CLT applies."),
      ),
    ).toBe(false);
  });

  it("gates a crux premise even when it contains a regime word", () => {
    expect(
      isAssumeTheCruxNarrowing(
        change(
          "The lower bound holds for the class.",
          "The lower bound holds. Suppose the least-favorable family with bounded variance satisfies the packing bound.",
        ),
      ),
    ).toBe(true);
  });

  it("gates a crux hidden in a SECOND premise behind a regime-only first one", () => {
    expect(
      isAssumeTheCruxNarrowing(
        change(
          "The bound holds.",
          "Assume the finite regime. Now suppose a least-favourable witness family with separation one such that testing fails.",
        ),
      ),
    ).toBe(true);
  });

  it("gates a leading crux premise", () => {
    expect(
      isAssumeTheCruxNarrowing(
        change("The bound holds.", "Assume there exists a two-point packing family with separation \\(\\delta_n\\). Then the bound holds."),
      ),
    ).toBe(true);
  });
});

describe("isResultClassDegradation — TeX comparators and multi-line assertions", () => {
  const change = (current: string, proposed: string) => ({ id: "thm:x", direction: "narrow", current, proposed });

  it("detects dropping a TeX-spelled lower-bound assertion (\\ge, not ASCII >=)", () => {
    expect(
      isResultClassDegradation(
        change("The risk satisfies \\(\\mathrm{risk} \\ge c R_n^*\\).", "The risk is finite."),
      ),
    ).toBe(true);
  });

  it("detects dropping a MULTI-LINE minimax assertion", () => {
    expect(
      isResultClassDegradation(
        change(
          "\\begin{aligned} \\inf_{\\hat\\theta} \\sup_{P} \\\\ \\mathbb{E}_P[\\ell] \\ge c \\end{aligned}",
          "The estimator is consistent.",
        ),
      ),
    ).toBe(true);
  });

  it("does not flag a pure notation swap between equivalence spellings", () => {
    expect(
      isResultClassDegradation(change("\\(A \\iff B\\) holds.", "\\(A \\Leftrightarrow B\\) holds.")),
    ).toBe(false);
  });
});
