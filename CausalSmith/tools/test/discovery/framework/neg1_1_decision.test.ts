import { describe, it, expect } from "vitest";
import { decideLitReviewOutcome } from "../../../src/discovery/stages/neg1_1.js";

describe("decideLitReviewOutcome", () => {
  it("completed with a healthy count", () => {
    expect(decideLitReviewOutcome({ status: "completed", n_open_problems: 5 })).toEqual({ kind: "completed", nOpen: 5 });
  });

  it("missing status defaults to completed (back-compat), thin count still pivots", () => {
    expect(decideLitReviewOutcome({ n_open_problems: 7 })).toEqual({ kind: "completed", nOpen: 7 });
    expect(decideLitReviewOutcome({ n_open_problems: 2 })).toEqual({ kind: "needs-pivot", nOpen: 2 });
  });

  it("an unrecognized PRESENT status halts as needs-pivot, never silently advances", () => {
    expect(decideLitReviewOutcome({ status: "wat", n_open_problems: 9 })).toEqual({ kind: "needs-pivot", nOpen: 9 });
  });

  it("counts fall back to open_problems.length when n_open_problems is absent", () => {
    expect(decideLitReviewOutcome({ open_problems: [1, 2, 3, 4] })).toEqual({ kind: "completed", nOpen: 4 });
  });

  it("NEITHER count NOR list present → malformed, not a pivot (a wrong-object parse must not discard a healthy angle)", () => {
    const d = decideLitReviewOutcome({ echo: "template" });
    expect(d.kind).toBe("malformed");
    if (d.kind === "malformed") expect(d.detail).toContain("echo");
  });

  it("non-finite and negative counts are clamped like the original (floor, min 0)", () => {
    expect(decideLitReviewOutcome({ n_open_problems: 3.9 })).toEqual({ kind: "completed", nOpen: 3 });
    expect(decideLitReviewOutcome({ n_open_problems: -2 })).toEqual({ kind: "needs-pivot", nOpen: 0 });
  });
});
