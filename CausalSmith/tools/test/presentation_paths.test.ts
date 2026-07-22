import { describe, it, expect } from "vitest";
import { presentationDir, bankAcceptedDir, assertRunSlug } from "../src/presentation/paths.js";

describe("run-slug validation (qid/spec must not escape their directories)", () => {
  it("accepts normal slugs", () => {
    expect(() => assertRunSlug("qid", "stat_policy_regret_margin_overlap")).not.toThrow();
    expect(() => assertRunSlug("spec", "v1")).not.toThrow();
    expect(presentationDir("/repo", "q1", "v1")).toContain("q1_v1");
  });
  it("rejects traversal and separator characters", () => {
    for (const bad of ["../evil", "a/b", "a\\b", "", ".", "a b", "a\nb"]) {
      expect(() => presentationDir("/repo", bad, "v1")).toThrow(/qid/);
      expect(() => bankAcceptedDir("/repo", "q1", bad)).toThrow(/spec/);
    }
  });
});
