import { describe, it, expect } from "vitest";
import { applyRerank } from "../../src/formalization/reuse_retrieval.js";

const cand = (name: string, score: number) => ({
  name, statement: "", docFirstPara: "", module: "", file: "",
  tier1: false, usesSorry: false, score, matchedVia: "semantic" as const,
});

describe("applyRerank (cross-encoder reorder of the fused top-pool)", () => {
  it("reorders the top-pool by reranker score (descending), not fused order", () => {
    const fused = [cand("a", 9), cand("b", 8), cand("c", 7)];
    const scores = [0.1, 0.9, 0.4]; // b best, then c, then a
    const out = applyRerank(fused, scores, 3, 10);
    expect(out.map((c) => c.name)).toEqual(["b", "c", "a"]);
  });

  it("promotes a low-fused-rank candidate the reranker loves to the very top", () => {
    const fused = [cand("top", 9), cand("mid", 8), cand("buried", 1)];
    const scores = [0.2, 0.3, 0.95]; // reranker loves the buried one
    const out = applyRerank(fused, scores, 3, 10);
    expect(out[0].name).toBe("buried");
  });

  it("only reranks the top-`pool`; candidates below the pool keep their fused order and stay below", () => {
    const fused = [cand("a", 9), cand("b", 8), cand("tail1", 3), cand("tail2", 2)];
    const scores = [0.1, 0.9]; // only the first 2 are in the pool
    const out = applyRerank(fused, scores, 2, 10);
    expect(out.map((c) => c.name)).toEqual(["b", "a", "tail1", "tail2"]);
  });

  it("respects topK after reranking", () => {
    const fused = [cand("a", 9), cand("b", 8), cand("c", 7)];
    const out = applyRerank(fused, [0.1, 0.9, 0.4], 3, 2);
    expect(out.map((c) => c.name)).toEqual(["b", "c"]);
  });

  it("writes the reranker score onto each reranked candidate (raw material for the confidence gate)", () => {
    const fused = [cand("a", 9), cand("b", 8)];
    const out = applyRerank(fused, [0.25, 0.75], 2, 10);
    expect(out.find((c) => c.name === "b")!.score).toBe(0.75);
    expect(out.find((c) => c.name === "a")!.score).toBe(0.25);
  });

  it("breaks reranker-score ties deterministically by name", () => {
    const fused = [cand("z", 9), cand("a", 8)];
    const out = applyRerank(fused, [0.5, 0.5], 2, 10);
    expect(out.map((c) => c.name)).toEqual(["a", "z"]);
  });
});
