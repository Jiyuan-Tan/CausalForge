import { describe, it, expect } from "vitest";
import { PROMOTION_ESCALATION_MARKER } from "../src/presentation/promotion.js";
import { droppedLeanRoutes } from "../src/presentation/audit.js";

describe("promotion escalates to the orchestrator instead of guessing", () => {
  it("has a marker the orchestrator can recognize on the halt", () => {
    expect(PROMOTION_ESCALATION_MARKER).toContain("promotion");
  });
});

describe("refine guard: a refinement may reword an anchored step, never drop it", () => {
  const before = [
    "Step 6. The upper bound follows. % lean: abstractClassFrontierRisk_le",
    "Step 7. The matching lower bound. % lean: fixed_geometry_frontier, fixedGeometryValue_le_frontierRisk",
  ].join("\n");

  it("reports each declaration the refinement deleted", () => {
    const after = "Step 6. The upper bound follows. % lean: abstractClassFrontierRisk_le";
    expect(droppedLeanRoutes(before, after).sort()).toEqual(
      ["fixedGeometryValue_le_frontierRisk", "fixed_geometry_frontier"],
    );
  });

  it("accepts rewording around the anchors", () => {
    const after = [
      "Step 6. Taking suprema gives the bound. % lean: abstractClassFrontierRisk_le",
      "Step 7. Chaining at the chosen geometry. % lean: fixed_geometry_frontier, fixedGeometryValue_le_frontierRisk",
    ].join("\n");
    expect(droppedLeanRoutes(before, after)).toEqual([]);
  });

  it("accepts reformatting and reordering of a route list", () => {
    const after = [
      "Step 6. The upper bound follows. % lean: abstractClassFrontierRisk_le",
      "Step 7. The matching lower bound. % lean:fixedGeometryValue_le_frontierRisk,fixed_geometry_frontier",
    ].join("\n");
    expect(droppedLeanRoutes(before, after)).toEqual([]);
  });

  it("still catches deletion of one of two identically-anchored branches", () => {
    const twice = [
      "Step A. First branch. % lean: sharedLemma",
      "Step B. Second branch. % lean: sharedLemma",
    ].join("\n");
    expect(droppedLeanRoutes(twice, "Step A. First branch. % lean: sharedLemma")).toEqual(["sharedLemma"]);
  });

  it("accepts an added anchor", () => {
    expect(droppedLeanRoutes(before, before + "\nStep 8. More. % lean: anotherLemma")).toEqual([]);
  });

  it("ignores an escaped percent, so prose mentioning the annotation is not a route", () => {
    const withProse = before + "\nA literal \\% lean: notARoute in the text.";
    expect(droppedLeanRoutes(withProse, before)).toEqual([]);
  });

  it("is inert on proofs carrying no anchors", () => {
    expect(droppedLeanRoutes("Step 1. Plain prose.", "Step 1. Rewritten prose.")).toEqual([]);
  });
});
