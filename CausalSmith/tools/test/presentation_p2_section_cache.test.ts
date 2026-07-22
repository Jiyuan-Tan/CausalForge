import { describe, it, expect } from "vitest";
import { sectionCacheKey } from "../src/presentation/stages/p2_draft.js";

describe("sectionCacheKey (P2 content-keyed section cache)", () => {
  const base = () => sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", ["BODY_A", "BODY_B"], "(no review)");

  it("is stable for identical inputs; re-keys when the objs are reordered (safe re-draft)", () => {
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", ["BODY_A", "BODY_B"], "(no review)")).toBe(base());
    expect(sectionCacheKey("02_main.tex", ["thm:b", "def:a"], "brief", "k1", ["BODY_B", "BODY_A"], "(no review)")).not.toBe(base());
  });
  it("changes when an env is added to / removed from the section (the restructure case)", () => {
    // def:a moved away → this section now has only thm:b → must re-draft.
    expect(sectionCacheKey("02_main.tex", ["thm:b"], "brief", "k1", ["BODY_B"], "(no review)")).not.toBe(base());
  });
  it("changes when a placed env body, the brief, the cites, or the revision brief changes", () => {
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", ["BODY_A2", "BODY_B"], "(no review)")).not.toBe(base());
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "BRIEF2", "k1", ["BODY_A", "BODY_B"], "(no review)")).not.toBe(base());
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k2", ["BODY_A", "BODY_B"], "(no review)")).not.toBe(base());
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", ["BODY_A", "BODY_B"], "[major] fix wording")).not.toBe(base());
  });
});
