import { describe, it, expect } from "vitest";
import { conceptKey, matchSynthDecl } from "../src/presentation/synth_lean_match.js";

const decls = new Map([
  ["CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredEstimator", { file: "Helpers/Estimator.lean", line: 344, kind: "def" }],
  ["CausalSmith.Stat.DiscreteAteMinimaxLoggap.selectedEstimator", { file: "Helpers/CombinedEnvelope.lean", line: 7, kind: "def" }],
  ["CausalSmith.Stat.DiscreteAteMinimaxLoggap.fallingFactorial", { file: "Helpers/Estimator.lean", line: 39, kind: "def" }],
  ["CausalSmith.Stat.DiscreteAteMinimaxLoggap.splitCellCount", { file: "Helpers/Estimator.lean", line: 22, kind: "def" }],
  // a lemma ABOUT the estimator — must never be matched as the definition's home
  ["CausalSmith.Stat.DiscreteAteMinimaxLoggap.centeredEstimator_mean", { file: "Helpers/Endpoint.lean", line: 189, kind: "theorem" }],
  ["CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse", { file: "Basic.lean", line: 10, kind: "def" }],
]);

describe("conceptKey", () => {
  it("strips LaTeX math and commands to a prose key", () => {
    expect(conceptKey("Centered estimator \\(\\widehat\\tau_{\\mathrm{ctr}}\\)")).toBe("centeredestimator");
    expect(conceptKey("Selected estimator \\(\\widehat\\tau^{\\mathrm{sel}}_{C_\\epsilon,\\epsilon}\\)")).toBe("selectedestimator");
    expect(conceptKey("Falling factorial \\((x)_r\\)")).toBe("fallingfactorial");
    expect(conceptKey("Split cell counts $N^{(0)}_{aky}$ and $N^{(1)}_{aky}$")).toBe("splitcellcountsand");
    expect(conceptKey("centeredEstimator")).toBe("centeredestimator");
  });
});

describe("matchSynthDecl", () => {
  it("matches a synthesized definition to its unique def-like decl by title prose", () => {
    expect(matchSynthDecl("Centered estimator \\(\\widehat\\tau_{\\mathrm{ctr}}\\)", "def:centered-estimator", decls))
      .toEqual({ decl: "centeredEstimator", file: "Helpers/Estimator.lean", line: 344, decl_kind: "def" });
    expect(matchSynthDecl("Selected estimator \\(\\widehat\\tau^{\\mathrm{sel}}\\)", "def:selected-estimator", decls)?.decl)
      .toBe("selectedEstimator");
    expect(matchSynthDecl("Falling factorial \\((x)_r\\)", "def:falling-factorial", decls)?.decl)
      .toBe("fallingFactorial");
  });

  it("matches on the obj_id when the title is absent (synth_N era)", () => {
    expect(matchSynthDecl(null, "def:centered-estimator", decls)?.decl).toBe("centeredEstimator");
  });

  it("does NOT match a plural/singular gap (exact-key policy)", () => {
    // "Split cell counts" → splitcellcounts ≠ splitcellcount
    expect(matchSynthDecl("Split cell counts $N$", "def:split-cell-counts", decls)).toBeNull();
  });

  it("does NOT match when no decl shares the key", () => {
    expect(matchSynthDecl("Bernoulli law \\(\\mathsf{Bernoulli}(\\pi_k)\\)", "def:bernoulli-law", decls)).toBeNull();
    expect(matchSynthDecl("Chebyshev polynomial $T_M$", "def:chebyshev-polynomial", decls)).toBeNull();
  });

  it("does NOT match a proof lemma (theorem kind) even if the key collides", () => {
    // centeredEstimator_mean keys to "centeredestimatormean" — different key, and it is a theorem.
    // The def match for "Centered estimator" still resolves to the def, not the lemma.
    expect(matchSynthDecl("Centered estimator", "def:centered-estimator", decls)?.decl).toBe("centeredEstimator");
  });

  it("rejects sub-minimum-length keys to avoid trivial collisions", () => {
    // "mse" is 3 chars — below MIN_KEY_LEN, never matched.
    expect(matchSynthDecl("MSE $\\mathrm{mse}$", "def:mse", decls)).toBeNull();
  });
});
