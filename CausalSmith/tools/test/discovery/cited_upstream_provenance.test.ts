// Provenance of attested `cited` nodes — content match =/= attribution.
//
// Regression fixtures are the two real misattributions found in the 2026-07-25
// stat_reversekl_two_coverage citation audit. Both nodes were attested
// `cited-verified-attested` with byte-correct verbatim statements, and both credited
// the wrong authors: the located environments were RESTATEMENTS that named their own
// primary source. The old CLI could not catch this because it never asked.

import { describe, it, expect } from "vitest";
import { detectUpstreamMarkers, resolveUpstreamDecision } from "../../src/discovery/core/cited_provenance.js";

const BIBKEYS = new Set(["ZhaoJiZhaoZhangGu2026SharpFDivergence", "ZhaoYeGuZhang2024SharpKL"]);

// arXiv:2502.06051 Appendix D.1 — declared `\begin{lemma}[{\citealt[Lemma~C.1]{zhao2024sharp}}]`.
const ZHAO_RESTATEMENT =
  "\\begin{lemma}[{\\citealt[Lemma~C.1]{zhao2024sharp}}]\\label{lem:concen-behavior-bandit}\n" +
  "For any policy $\\pi$ and state-action pairs generated i.i.d. from $\\rho \\times \\pi$, " +
  "with probability at least $1-\\delta$, for any $g_1$ and $g_2$ we have " +
  "$\\E[(g_1-g_2)^2] \\leq \\frac{2}{n}\\sum_i (g_1-g_2)^2 + \\frac{32}{3n}\\log(2\\cN(\\epsilon_c)/\\delta) + 10\\epsilon_c$.";

// arXiv:2406.05376 Appendix E — "we refer to \cite[Thm. 18.19]{guide2006infinite} for the proof".
const WEIGAND_RESTATEMENT =
  "The next theorem is known as the measurable maximum theorem, where we refer to " +
  "\\cite[Thm. 18.19]{guide2006infinite} for the proof of this statement.";

const ORIGINAL = "Let $X$ be a separable metrizable space and suppose $f$ is continuous. Then $m$ is measurable.";

describe("detectUpstreamMarkers", () => {
  it("flags a restatement whose environment header carries an inner citation", () => {
    expect(detectUpstreamMarkers(ZHAO_RESTATEMENT)).toContain("LaTeX citation macro");
  });

  it("flags a restatement that names its primary in prose", () => {
    const markers = detectUpstreamMarkers(WEIGAND_RESTATEMENT);
    expect(markers).toContain("LaTeX citation macro");
    expect(markers).toContain('"we refer to … for the proof"');
  });

  it("stays quiet on an ordinary statement — a noisy detector gets bypassed reflexively", () => {
    expect(detectUpstreamMarkers(ORIGINAL)).toEqual([]);
  });

  // Regression: these fired on ordinary mathematical prose. Because a marker BLOCKS
  // --upstream-none, each false positive pushed the operator toward inventing a
  // citation, so precision here is a correctness property, not tidiness.
  it.each([
    "This quantity is known as the propensity score.",
    "The bound holds due to boundedness of the second moment.",
    "The result was first proved for the tabular case.",
  ])("does not fire on ordinary prose: %s", (text) => {
    expect(detectUpstreamMarkers(text)).toEqual([]);
  });
});

describe("resolveUpstreamDecision", () => {
  const base = { verbatim: ORIGINAL, bibkeys: BIBKEYS };

  it("refuses attestation when provenance was never decided", () => {
    expect(() => resolveUpstreamDecision({ ...base, upstreamNone: false })).toThrow(/provenance undecided/);
  });

  it("refuses a contradictory decision", () => {
    expect(() => resolveUpstreamDecision({ ...base, upstream: "someone", upstreamNone: true }))
      .toThrow(/contradictory/);
  });

  it("refuses --upstream-none when the source text credits an earlier work", () => {
    expect(() => resolveUpstreamDecision({
      verbatim: ZHAO_RESTATEMENT,
      bibkeys: BIBKEYS,
      upstreamNone: true,
    })).toThrow(/contradicts the source text/);
  });

  it("points the operator at the environment's optional argument", () => {
    expect(() => resolveUpstreamDecision({ ...base, upstreamNone: false })).toThrow(/OPTIONAL ARGUMENT/);
  });

  it("records the primary when one is supplied", () => {
    expect(resolveUpstreamDecision({
      verbatim: ZHAO_RESTATEMENT,
      bibkeys: BIBKEYS,
      upstreamNone: false,
      upstream: "H. Zhao, C. Ye, Q. Gu, T. Zhang. Sharp Analysis for KL-Regularized Contextual Bandits and RLHF. arXiv:2411.04625, 2024.",
      upstreamLocator: "Lemma C.1",
      upstreamCite: "ZhaoYeGuZhang2024SharpKL",
    })).toEqual({
      citation: "H. Zhao, C. Ye, Q. Gu, T. Zhang. Sharp Analysis for KL-Regularized Contextual Bandits and RLHF. arXiv:2411.04625, 2024.",
      locator: "Lemma C.1",
      cite: "ZhaoYeGuZhang2024SharpKL",
    });
  });

  it("accepts a free-text primary that is not itself in the bibliography", () => {
    const resolved = resolveUpstreamDecision({
      verbatim: WEIGAND_RESTATEMENT,
      bibkeys: BIBKEYS,
      upstreamNone: false,
      upstream: "C. Aliprantis and K. Border. Infinite Dimensional Analysis: A Hitchhiker's Guide, 3rd ed.",
      upstreamLocator: "Theorem 18.19",
    });
    expect(resolved?.locator).toBe("Theorem 18.19");
    expect(resolved?.cite).toBeUndefined();
  });

  it("refuses an --upstream-cite that does not resolve in the bibliography", () => {
    expect(() => resolveUpstreamDecision({
      ...base,
      upstreamNone: false,
      upstream: "some primary",
      upstreamCite: "NotInBibliography2024",
    })).toThrow(/does not resolve in the core bibliography/);
  });

  it("returns undefined when the statement is affirmed original", () => {
    expect(resolveUpstreamDecision({ ...base, upstreamNone: true })).toBeUndefined();
  });

  it("offers an auditable escape so a false-positive marker cannot force an invented citation", () => {
    const input = { verbatim: WEIGAND_RESTATEMENT, bibkeys: BIBKEYS, upstreamNone: true };
    expect(() => resolveUpstreamDecision(input)).toThrow(/do NOT invent a citation/);
    expect(resolveUpstreamDecision({ ...input, acknowledgeMarker: "quotes a citation it does not borrow from" }))
      .toBeUndefined();
  });

  it("refuses a bibkey or locator alongside --upstream-none", () => {
    expect(() => resolveUpstreamDecision({ ...base, upstreamNone: true, upstreamCite: "ZhaoYeGuZhang2024SharpKL" }))
      .toThrow(/cannot accompany --upstream-none/);
    expect(() => resolveUpstreamDecision({ ...base, upstreamNone: true, upstreamLocator: "Lemma C.1" }))
      .toThrow(/cannot accompany --upstream-none/);
  });
});
