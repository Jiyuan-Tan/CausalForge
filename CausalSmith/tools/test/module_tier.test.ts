import { describe, it, expect } from "vitest";
import { poolModules } from "../src/formalization/module_tier.js";

const c = (module: string, score: number, name = `${module}.d${score}`) => ({ module, name, score });

describe("poolModules (top-k pooled member scores → ranked modules)", () => {
  it("scores a module by the MEAN of its top-k member scores, ignoring the diluting tail", () => {
    const cands = [
      c("M1", 9), c("M1", 7), c("M1", 5), c("M1", 1), // top-3 mean = 7 (the 1 is ignored)
      c("M2", 8), c("M2", 8),                          // only 2 members → mean = 8
    ];
    const out = poolModules(cands, 10, 3);
    expect(out.map((m) => m.module)).toEqual(["M2", "M1"]);
    expect(out.find((m) => m.module === "M1")!.score).toBeCloseTo(7, 5);
    expect(out.find((m) => m.module === "M2")!.score).toBeCloseTo(8, 5);
  });

  it("a single very-relevant member outranks three medium members (top-k mean, not centroid)", () => {
    const out = poolModules([c("Strong", 10), c("Medium", 6), c("Medium", 6), c("Medium", 6)], 10, 3);
    expect(out[0].module).toBe("Strong"); // mean([10]) = 10 > mean([6,6,6]) = 6
  });

  it("exposes up to 3 prototype member decl names (highest-scoring), for the 'e.g.' anchors", () => {
    const out = poolModules([c("M", 9, "M.a"), c("M", 7, "M.b"), c("M", 5, "M.c"), c("M", 3, "M.d")], 10, 3);
    expect(out[0].prototypes).toEqual(["M.a", "M.b", "M.c"]); // top-3 by score, in order
  });

  it("carries the member count and respects topN", () => {
    const out = poolModules([c("M1", 9), c("M1", 8), c("M2", 5), c("M3", 4)], 2, 3);
    expect(out).toHaveLength(2);
    expect(out.find((m) => m.module === "M1")!.memberCount).toBe(2);
  });

  it("breaks module-score ties deterministically by module name", () => {
    const out = poolModules([c("Zmod", 5), c("Amod", 5)], 10, 3);
    expect(out.map((m) => m.module)).toEqual(["Amod", "Zmod"]);
  });
});
