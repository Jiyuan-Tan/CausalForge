import { describe, expect, it } from "vitest";
import { SYNTHETIC_COMPANION_RE } from "../src/presentation/paper_index_orphans.js";

// Mirrors `isSyntheticCompanionLeaf` in LibraryIndexCore.lean — the Lean
// extractor and the TS index checkers must agree on the synthetic class.
describe("SYNTHETIC_COMPANION_RE", () => {
  it("matches compiler-synthesized companion names", () => {
    for (const n of ["Foo.congr_simp", "A.B.eq_def", "Foo.eq_unfold", "Foo.eq_1", "Foo.eq_12"])
      expect(SYNTHETIC_COMPANION_RE.test(n)).toBe(true);
  });

  it("rejects ordinary names that merely resemble the reserved leaves", () => {
    for (const n of ["Foo.eq_", "Foo.eq_x", "Foo.eq_1x", "Foo.some_eq_def", "Foo.npow", "eq_def", "Foo.eq_def.lem"])
      expect(SYNTHETIC_COMPANION_RE.test(n)).toBe(false);
  });
});
