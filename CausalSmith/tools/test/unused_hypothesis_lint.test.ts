import { describe, expect, it } from "vitest";
import { lintUnusedHypotheses } from "../src/formalization/unused_hypothesis_lint.js";

describe("lintUnusedHypotheses", () => {
  it("flags a hypothesis the proof body never names", () => {
    const src = `
theorem foo (a b : Nat) (ha : a = 0) (hb : b = 0) : a = 0 := by
  exact ha
`;
    const r = lintUnusedHypotheses(src);
    expect(r.theoremsInspected).toBe(1);
    expect(r.findings.map((f) => f.hypothesisName)).toEqual(["hb"]);
    expect(r.findings[0].severity).toBe("definite");
  });

  it("does not flag a binder name that appears in the result type", () => {
    // `a` is used only in the conclusion; nothing else cites it but it is
    // load-bearing for the statement and must not be flagged.
    const src = `
theorem foo (a : Nat) (ha : a = 0) : a + 0 = 0 := by
  rw [ha]
`;
    const r = lintUnusedHypotheses(src);
    expect(r.findings).toEqual([]);
  });

  it("does not flag a binder name that appears only in a sibling binder's type", () => {
    // `a` does not appear in the result type or proof body, but it IS used
    // inside `ha`'s type — dropping `a` would make `ha` ill-formed.
    const src = `
theorem foo (a : Nat) (ha : a = 0) (b : Nat) : b = b := by
  rfl
`;
    const r = lintUnusedHypotheses(src);
    expect(r.findings.map((f) => f.hypothesisName)).toEqual(["ha"]);
  });

  it("downgrades to advisory when the proof uses a wildcard tactic", () => {
    const src = `
theorem foo (h1 : True) (h2 : True) : True := by
  trivial
`;
    const r = lintUnusedHypotheses(src);
    // `trivial` is not in our wildcard list, so this is `definite`.
    expect(r.findings.every((f) => f.severity === "definite")).toBe(true);
    const advSrc = `
theorem foo (h1 : 0 ≤ 1) (h2 : 0 ≤ 2) : 0 ≤ 3 := by
  linarith
`;
    const adv = lintUnusedHypotheses(advSrc);
    expect(adv.findings.every((f) => f.severity === "advisory")).toBe(true);
    expect(adv.findings[0].note).toMatch(/linarith/);
  });

  it("skips theorems whose proof body is `sorry`", () => {
    const src = `
theorem foo (a : Nat) (ha : a = 0) : a = 0 := by
  sorry
`;
    const r = lintUnusedHypotheses(src);
    expect(r.findings).toEqual([]);
    expect(r.skipped).toEqual([
      expect.objectContaining({ theoremName: "foo", reason: "sorry-stub" }),
    ]);
  });

  it("flags a public theorem that only forwards a hypothesis into an unused bridge parameter", () => {
    const src = `
private lemma bridge (hMain : True) (hExtra : True) : True := by
  exact hMain

theorem top (hMain : True) (hExtra : True) : True := by
  exact bridge hMain hExtra
`;
    const r = lintUnusedHypotheses(src);
    expect(r.findings).toContainEqual(
      expect.objectContaining({
        theoremName: "top",
        hypothesisName: "hExtra",
        severity: "definite",
        transitive: true,
      }),
    );
  });

  it("preserves source line numbers across docstrings (no offset drift)", () => {
    const src = `/--
A long docstring
spanning multiple
lines.
-/
theorem foo (h : Nat) : True := by
  trivial
`;
    const r = lintUnusedHypotheses(src);
    // theorem header is on line 6 in the original source
    expect(r.findings[0]?.declLine).toBe(6);
  });
});
