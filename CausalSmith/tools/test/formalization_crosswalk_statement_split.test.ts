import { describe, it, expect } from "vitest";
import { statementText, splitStatement } from "../src/formalization/crosswalk.js";

/** The real shape that exposed the bug: `Causalean.Stat`'s
 *  `finitePoissonObjective_snd_sign_of_nuisance_score` binds its conclusion
 *  through `let`s, so the first depth-0 `:=` belongs to a `let` binder rather
 *  than to the proof. */
const LET_CONCLUSION_DECL = `lemma finitePoissonObjective_snd_sign_of_nuisance_score
    {U I : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (q m : I → ℝ) (A : (U × ℝ) →ₗ[ℝ] (I → ℝ)) (u₀ : U)
    (hq : ∀ i, 0 < q i)
    (hNuisance : ∀ u : U,
      ∑ i, q i * A (u, 0) i * (m i - Real.exp (A (u₀, 0) i)) = 0) :
    let beta :=
      (maximizerOrZero (finitePoissonObjective q m A)).2
    let scalarScore :=
      ∑ i, q i * A (0, 1) i * (m i - Real.exp (A (u₀, 0) i))
    (beta < 0 ↔ scalarScore < 0) ∧
    (beta = 0 ↔ scalarScore = 0) ∧
    (0 < beta ↔ 0 < scalarScore) := by
  dsimp only`;

describe("statementText (proof-delimiter detection)", () => {
  it("keeps a let-bound conclusion instead of truncating at the let binder's :=", () => {
    const stmt = statementText(LET_CONCLUSION_DECL);
    // The conclusion is the point — it must survive.
    expect(stmt).toContain("0 < beta ↔ 0 < scalarScore");
    // ...and the proof must not.
    expect(stmt).not.toContain("dsimp only");
    expect(stmt.trimEnd().endsWith("(0 < beta ↔ 0 < scalarScore)")).toBe(true);
  });

  it("surfaces the decls that define what is proved", () => {
    const stmt = statementText(LET_CONCLUSION_DECL);
    // These are reached ONLY through the conclusion; truncation hid them from
    // the crosswalk BFS (and so from the reviewer).
    expect(stmt).toContain("maximizerOrZero");
    expect(stmt).toContain("finitePoissonObjective q m A");
  });

  it("still cuts at the proof := for an ordinary decl", () => {
    expect(statementText("theorem foo (h : P) : Q := by simp")).toBe("theorem foo (h : P) : Q ");
  });

  it("still ignores a named argument (x := y) inside a binder", () => {
    const decl = "theorem foo (h : Bar (x := 1)) : Q := by simp";
    expect(statementText(decl)).toBe("theorem foo (h : Bar (x := 1)) : Q ");
  });

  it("handles a have-bound conclusion the same way", () => {
    const decl = "theorem foo (h : P) :\n    have n := 3\n    n = 3 := by rfl";
    expect(statementText(decl).trimEnd().endsWith("n = 3")).toBe(true);
  });

  it("does not treat the identifier letFun as a let binder", () => {
    const decl = "theorem foo (h : P) : letFun 1 (fun x => x = 1) := by rfl";
    expect(statementText(decl)).toBe("theorem foo (h : P) : letFun 1 (fun x => x = 1) ");
  });

  it("never truncates a line-initial |absolute value| in a conclusion", () => {
    // A line-initial `|` is an absolute value far more often than a match arm;
    // terminating there would truncate the conclusion.
    const decl = "lemma abs_le (a b : ℝ) :\n    |a / b - c / d| ≤ 1 := by simp";
    expect(statementText(decl).trimEnd().endsWith("|a / b - c / d| ≤ 1")).toBe(true);
  });

  it("returns the whole decl for an equation-compiler def (no proof :=)", () => {
    // Accepted, deliberate: such a decl has no proof delimiter, so the binder
    // skip runs to the end. Over-inclusion is the safe direction here and it
    // does not move isPropValued. Do NOT "fix" this by cutting at the first `|`
    // (see the |absolute value| case above).
    const decl = "def f : ℕ → ℕ\n  | 0 => 1\n  | n + 1 =>\n      let r := f n\n      r + 1";
    expect(statementText(decl)).toBe(decl);
  });

  it("ignores delimiter and binder tokens inside comments and strings", () => {
    expect(statementText("theorem foo : Q -- let prose := marker\n:= by exact q").trimEnd()).toBe(
      "theorem foo : Q -- let prose := marker",
    );
    expect(statementText('theorem foo : (\") := let\" = \"x\") := by exact q').trimEnd()).toBe(
      'theorem foo : (\") := let\" = \"x\")',
    );
    expect(statementText("theorem foo -- ) ] } := fake\n  : Q := by exact q")).not.toContain("by exact q");
  });
});

describe("splitStatement (hypothesis/conclusion split)", () => {
  it("reports the real conclusion, not the bare `let beta` binder head", () => {
    const { hyp, concl } = splitStatement(statementText(LET_CONCLUSION_DECL));
    expect(hyp).toContain("hNuisance");
    expect(concl).toContain("0 < beta ↔ 0 < scalarScore");
    expect(concl.trim()).not.toBe("let beta");
  });

  it("ignores colons and brackets in comments while finding the conclusion", () => {
    const split = splitStatement("theorem foo -- : ) ] }\n  (h : P) : Q");
    expect(split.hyp).toContain("(h : P)");
    expect(split.concl.trim()).toBe("Q");
  });
});
