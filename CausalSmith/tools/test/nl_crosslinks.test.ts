import { describe, expect, it } from "vitest";
import {
  parseNlCrosslinks,
  stripNlCrosslinks,
  crosslinkNames,
  linksGoal,
  sourceBinders,
  sourceFieldNames,
} from "../src/shared/nl_crosslinks.js";

describe("nl_crosslinks parsing", () => {
  it("parses hyp and goal links, splitting comma-separated names", () => {
    const segs = parseNlCrosslinks("Fix [Λ at least 1](hyp:Λ,hΛ), then [it holds](goal).");
    expect(segs).toEqual([
      { text: "Fix ", links: null },
      { text: "Λ at least 1", links: ["Λ", "hΛ"] },
      { text: ", then ", links: null },
      { text: "it holds", links: ["⊢"] },
      { text: ".", links: null },
    ]);
  });
  it("handles balanced brackets inside a phrase", () => {
    const segs = parseNlCrosslinks("then [equals E[A·Y·(wMax if Y ≥ 0 else wMin)]](goal).");
    expect(segs[1]).toEqual({ text: "equals E[A·Y·(wMax if Y ≥ 0 else wMin)]", links: ["⊢"] });
  });
  it("leaves ordinary markdown links untouched and stripping is lossless on plain prose", () => {
    const s = "see [the paper](https://x.y) for context";
    expect(stripNlCrosslinks(s)).toBe(s);
  });
  it("strip removes only the markup, keeping phrase text", () => {
    expect(stripNlCrosslinks("If [overlap holds](hyp:hov), then [done](goal).")).toBe(
      "If overlap holds, then done.",
    );
  });
  it("ignores unbalanced brackets inside code/math spans (interval notation)", () => {
    const s = "If [overlap holds at level `ε ∈ (0, 1/2]`](hyp:hov) and [$x \\in [0,1)$ shifts](hyp:hx), done.";
    const segs = parseNlCrosslinks(s).filter((g) => g.links);
    expect(segs.map((g) => g.links)).toEqual([["hov"], ["hx"]]);
    expect(segs[0].text).toBe("overlap holds at level `ε ∈ (0, 1/2]`");
  });
  it("crosslinkNames and linksGoal report what is referenced", () => {
    const s = "Fix [Λ ≥ 1](hyp:Λ,hΛ); then [ATE is identified](goal).";
    expect(crosslinkNames(s)).toEqual(["Λ", "hΛ"]);
    expect(linksGoal(s)).toBe(true);
    expect(linksGoal("no goal here")).toBe(false);
  });
});

describe("sourceBinders", () => {
  const src = `/-- doc with (parens) inside -/
theorem msmUpper_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω)
    {η : NuisanceVec γ} [inst : MeasurableSpace γ]
    (henv : Integrable (fun ω => S.wMax Λ ω) P.μ) :
    S.msmUpper Λ = S.msmUpperForm Λ := by
  sorry`;
  it("extracts binder names and hyp classification from authored source", () => {
    const binders = sourceBinders(src)!;
    expect(binders.map((b) => b.names.join(" "))).toEqual([
      "Λ",
      "hΛ",
      "hoverlap",
      "η",
      "inst",
      "henv",
    ]);
    const hyps = binders.filter((b) => b.isHyp).map((b) => b.names[0]);
    // implicit/instance binders are never hyp-classified; Λ is a plain decl.
    expect(hyps).toEqual(["hΛ", "hoverlap", "henv"]);
  });
  it("returns null on shapes it cannot confidently scan", () => {
    expect(sourceBinders("instance : Foo Bar := ⟨…⟩")).toBeNull();
  });
});

describe("sourceFieldNames", () => {
  it("extracts a structure's where-block field names (crosslink targets)", () => {
    const src = `/-- A bundle. -/
structure Assumptions (P : POSystem) : Prop where
  consistency : ∀ ω, P.Y ω = P.YofD (P.D ω) ω
  ignorability : CondIndep P.D P.Y0
  [decEq : DecidableEq V]
    -- continuation line at deeper indent is not a new field
  overlap : ∀ ω, 0 < P.e ω`;
    expect(sourceFieldNames(src)).toEqual(["consistency", "ignorability", "decEq", "overlap"]);
  });
  it("returns [] when there is no where block", () => {
    expect(sourceFieldNames("theorem t (h : A) : B := proof")).toEqual([]);
  });
});
