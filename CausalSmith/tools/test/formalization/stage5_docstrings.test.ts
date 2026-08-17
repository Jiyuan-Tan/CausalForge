import { describe, expect, it } from "vitest";
import { crosslinkDefect, declListFor, moduleNamesFor } from "../../src/formalization/stage5_docstrings.js";

describe("moduleNamesFor (F5 docstring coverage module derivation)", () => {
  it("maps run-dir .lean files to dotted module names under the lean_subdir prefix", () => {
    expect(
      moduleNamesFor("CausalSmith/Stat/X_Research", ["Basic.lean", "Helpers/Bound.lean"]),
    ).toEqual([
      "CausalSmith.Stat.X_Research.Basic",
      "CausalSmith.Stat.X_Research.Helpers.Bound",
    ]);
  });

  it("excludes non-Lean files and the disposable tmp/ agent workspace", () => {
    expect(
      moduleNamesFor("CausalSmith/Stat/X_Research", [
        "Basic.lean",
        "notes.md",
        "tmp/Scratch.lean",
        "Helpers/tmp/Probe.lean",
      ]),
    ).toEqual(["CausalSmith.Stat.X_Research.Basic"]);
  });
});

describe("declListFor (docstring prompt decl list)", () => {
  it("groups by file and sorts each file's declarations by line", () => {
    const list = declListFor([
      { name: "t1_thm", file: "A.lean", line: 30, kind: "theorem" },
      { name: "muDef", file: "A.lean", line: 10, kind: "def" },
      { name: "l2_lem", file: "B.lean", line: 5, kind: "lemma" },
    ]);
    expect(list).toBe(
      "A.lean\n  L10 def muDef\n  L30 theorem t1_thm\n\nB.lean\n  L5 lemma l2_lem",
    );
  });
});

describe("crosslinkDefect (F5 hard gate on theorem docstring crosslinks)", () => {
  const source = `theorem t (x : ℝ) (hx : 0 ≤ x) (hb : x ≤ 1) : x ^ 2 ≤ x := proof`;
  it("accepts a fully crosslinked docstring", () => {
    const doc = "If [x is nonnegative](hyp:hx) and [at most one](hyp:hb), then [x² ≤ x](goal).";
    expect(crosslinkDefect({ kind: "theorem", doc, source })).toBeNull();
  });
  it("flags uncovered hypotheses, a missing goal link, and unknown names", () => {
    expect(
      crosslinkDefect({ kind: "theorem", doc: "If [x ≥ 0](hyp:hx), then [done](goal).", source }),
    ).toContain("hb");
    expect(
      crosslinkDefect({ kind: "theorem", doc: "If [a](hyp:hx) and [b](hyp:hb), done.", source }),
    ).toContain("(goal)");
    expect(
      crosslinkDefect({ kind: "theorem", doc: "If [a](hyp:hOld) and [b](hyp:hb), [c](goal).", source }),
    ).toContain("hOld");
  });
  it("exempts hypothesis-free theorems and non-theorems", () => {
    expect(
      crosslinkDefect({ kind: "theorem", doc: "Plain NL.", source: "theorem s : 1 = 1 := rfl" }),
    ).toBeNull();
    expect(crosslinkDefect({ kind: "def", doc: "Plain NL.", source })).toBeNull();
  });
});
