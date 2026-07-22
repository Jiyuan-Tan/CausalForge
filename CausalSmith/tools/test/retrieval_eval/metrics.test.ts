import { describe, it, expect } from "vitest";
import { scoreRanking, aggregate, type PerQuery } from "../../src/formalization/retrieval_eval/metrics.js";

describe("scoreRanking", () => {
  const equalIdf = new Map([["a", 5], ["b", 5], ["c", 5]]); // all discriminating
  it("IDF-weighted recall@k over equally-weighted gold reduces to plain recall", () => {
    const r = scoreRanking(["a", "x", "b", "y"], new Set(["a", "b", "c"]), equalIdf);
    expect(r.recallAt[3]).toBeCloseTo(2 / 3); // (5+5)/(5+5+5)
    expect(r.recallAt[1]).toBeCloseTo(1 / 3);
    expect(r.hitAt3).toBe(true);
    expect(r.rr).toBeCloseTo(1);              // first core gold at rank 1
  });
  it("rr is 0 and hit false when no gold appears", () => {
    const r = scoreRanking(["x", "y"], new Set(["a"]), new Map([["a", 5]]));
    expect(r.rr).toBe(0);
    expect(r.hitAt3).toBe(false);
  });
  it("a ubiquitous carrier (idf≈0) neither satisfies hit@3 nor inflates recall", () => {
    const idf = new Map([["carrier", 0.1], ["real", 5]]); // floor 2.3: carrier is not core
    const r = scoreRanking(["carrier", "z", "w"], new Set(["carrier", "real"]), idf);
    expect(r.hitAt3).toBe(false);                  // only the carrier was retrieved
    expect(r.recallAt[3]).toBeCloseTo(0.1 / 5.1);  // carrier contributes ~0 of the mass
  });
});

describe("aggregate", () => {
  it("means hit@3 and recall@k across queries", () => {
    const rows: PerQuery[] = [
      { qid: "1", theorem: "T", rendering: "doc", variant: 0, stratum: "bridgeable", cluster: "stat", recallAt: { 1: 1, 3: 1, 5: 1, 10: 1 }, hitAt3: true, rr: 1 },
      { qid: "2", theorem: "T", rendering: "para", variant: 1, stratum: "gap", cluster: "stat", recallAt: { 1: 0, 3: 0, 5: 0, 10: 0 }, hitAt3: false, rr: 0 },
    ];
    const agg = aggregate(rows);
    expect(agg.overall.hitAt3).toBeCloseTo(0.5);
    expect(agg.byStratum.gap.hitAt3).toBe(0);
    expect(agg.byRendering.doc.recallAt[3]).toBe(1);
  });
});
