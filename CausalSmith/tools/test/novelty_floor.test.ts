import { describe, expect, it } from "vitest";
import { meetsNoveltyFloor } from "../src/pipeline_stages.js";

// The Stage -0.5 angle/revise loop gates BOTH the tier-saturation auto-promote
// and the early angle-kill on `meetsNoveltyFloor(tier, novelty_target)`. These
// tests pin the floor semantics and, through them, the two loop behaviors the
// predicate drives:
//   - early-kill fires only when NO iteration of the angle met the floor;
//   - auto-promote fires only when the recent REVISEs all met the floor.

describe("meetsNoveltyFloor", () => {
  it("enforces the flagship floor strictly (regression guard)", () => {
    expect(meetsNoveltyFloor("flagship", "flagship")).toBe(true);
    expect(meetsNoveltyFloor("field", "flagship")).toBe(false);
    expect(meetsNoveltyFloor("subfield", "flagship")).toBe(false);
    expect(meetsNoveltyFloor(undefined, "flagship")).toBe(false);
  });

  it("lets a field-tier proposal meet a field target", () => {
    expect(meetsNoveltyFloor("flagship", "field")).toBe(true);
    expect(meetsNoveltyFloor("field", "field")).toBe(true);
    expect(meetsNoveltyFloor("subfield", "field")).toBe(false);
    expect(meetsNoveltyFloor(undefined, "field")).toBe(false);
  });

  it("treats subfield as the floor for relative-to-literature", () => {
    expect(meetsNoveltyFloor("field", "relative-to-literature")).toBe(true);
    expect(meetsNoveltyFloor("subfield", "relative-to-literature")).toBe(true);
    expect(meetsNoveltyFloor("incremental", "relative-to-literature")).toBe(false);
    expect(meetsNoveltyFloor(undefined, "relative-to-literature")).toBe(false);
  });

  it("imposes no floor for relative-to-repo (any/missing tier passes)", () => {
    expect(meetsNoveltyFloor("incremental", "relative-to-repo")).toBe(true);
    expect(meetsNoveltyFloor("subfield", "relative-to-repo")).toBe(true);
    expect(meetsNoveltyFloor(undefined, "relative-to-repo")).toBe(true);
  });
});

describe("Stage -0.5 loop gating (via meetsNoveltyFloor)", () => {
  type Iter = { angle: number; version: number; verdict: string; tier?: string; clean_substance?: boolean };

  // Mirror of the loop's early-kill predicate: kill iff no iteration of the
  // angle ever met the floor.
  const wouldKill = (iters: Iter[], angle: number, target: Parameters<typeof meetsNoveltyFloor>[1]) =>
    !iters.some((it) => it.angle === angle && meetsNoveltyFloor(it.tier, target));

  // Mirror of the loop's auto-promote predicate over the last 3 same-angle iters.
  const wouldAutoPromote = (iters: Iter[], angle: number, target: Parameters<typeof meetsNoveltyFloor>[1]) => {
    const recent = iters.filter((it) => it.angle === angle).slice(-3);
    return (
      recent.length >= 3 &&
      recent.every(
        (it) => it.verdict === "REVISE" && meetsNoveltyFloor(it.tier, target) && it.clean_substance === true,
      )
    );
  };

  const fieldAngle: Iter[] = [
    { angle: 0, version: 1, verdict: "REVISE", tier: "field", clean_substance: true },
    { angle: 0, version: 2, verdict: "REVISE", tier: "field", clean_substance: true },
    { angle: 0, version: 3, verdict: "REVISE", tier: "field", clean_substance: true },
  ];

  it("does NOT early-kill a field-tier angle under a field target (gets full revise cap)", () => {
    expect(wouldKill(fieldAngle, 0, "field")).toBe(false);
  });

  it("auto-promotes a field-tier angle after 3 clean REVISEs under a field target", () => {
    expect(wouldAutoPromote(fieldAngle, 0, "field")).toBe(true);
  });

  it("still early-kills a field-only angle under a flagship target", () => {
    expect(wouldKill(fieldAngle, 0, "flagship")).toBe(true);
    expect(wouldAutoPromote(fieldAngle, 0, "flagship")).toBe(false);
  });

  it("does not auto-promote when a substantive flag remains (clean_substance false)", () => {
    const dirty = fieldAngle.map((it) => ({ ...it, clean_substance: false }));
    expect(wouldAutoPromote(dirty, 0, "field")).toBe(false);
  });
});
