// D0.5.G paper-score ceiling gate. The tier ladder does not predict paper quality (every
// `_bank/accepted/` entry ran at `novelty_target: field` and scored 4.0–8.2), so the ceiling
// caps the tier independently. These tests pin the ladder, the routing the cap implies, and
// the fail-OPEN behaviour on an omitted ceiling.
import { describe, expect, it } from "vitest";
import {
  CEILING_FOR_FIELD,
  CEILING_FOR_SUBFIELD,
  ceilingTierCap,
  decideGeneralReroute,
  normalizeGeneralReview,
} from "../../src/discovery/stages/d0_5_general.js";

const base = {
  tier: "field",
  salvageable: false,
  flagged_conjecture_labels: [],
  critique: "delivered kernel is a one-estimator analogue",
  flagship_potential: false,
};

describe("ceilingTierCap", () => {
  it("maps the ceiling ladder to the highest permitted tier", () => {
    expect(ceilingTierCap(9.4)).toBe("flagship");
    expect(ceilingTierCap(9.0)).toBe("flagship");
    expect(ceilingTierCap(8.9)).toBe("field");
    expect(ceilingTierCap(CEILING_FOR_FIELD)).toBe("field");
    expect(ceilingTierCap(7.4)).toBe("field");
    expect(ceilingTierCap(6.9)).toBe("subfield");
    expect(ceilingTierCap(CEILING_FOR_SUBFIELD)).toBe("subfield");
    expect(ceilingTierCap(6.4)).toBe("incremental");
  });

  it("fails OPEN on an absent or unusable ceiling so a paid call is never discarded", () => {
    expect(ceilingTierCap(undefined)).toBe("flagship");
    expect(ceilingTierCap(Number.NaN)).toBe("flagship");
  });
});

describe("normalizeGeneralReview ceiling cap", () => {
  it("leaves the graded tier and routing untouched at or above the field ceiling", () => {
    const gen = normalizeGeneralReview({ ...base, paper_score_ceiling: 7.8 }, "raw");
    expect(gen.tier).toBe("field");
    expect(gen.salvageable).toBe(false);
    expect(gen.critique).not.toMatch(/ceiling gate/);
    expect(gen.paper_score_ceiling).toBe(7.8);
  });

  it("caps to subfield and routes to REVISE on the ceiling directive in [6.5, 7.0)", () => {
    const gen = normalizeGeneralReview(
      {
        ...base,
        paper_score_ceiling: 6.8,
        ceiling_directive: "restate the converse over the published class",
      },
      "raw",
    );
    expect(gen.tier).toBe("subfield");
    // Below a `field` floor + salvageable → the existing D0.5 boundary reroutes to D0.
    expect(gen.salvageable).toBe(true);
    expect(gen.improvement_directive).toBe("restate the converse over the published class");
    expect(gen.critique).toMatch(/ceiling gate/);
  });

  it("caps to incremental and routes to REJECT below the subfield ceiling", () => {
    const gen = normalizeGeneralReview(
      { ...base, salvageable: true, paper_score_ceiling: 5.2, ceiling_directive: "widen it" },
      "raw",
    );
    expect(gen.tier).toBe("incremental");
    // Overrides the referee's own `salvageable: true` — no rewrite lifts this to the bar.
    expect(gen.salvageable).toBe(false);
  });

  it("never promotes: a low graded tier is not raised by a high ceiling", () => {
    const gen = normalizeGeneralReview(
      { ...base, tier: "subfield", paper_score_ceiling: 9.5 },
      "raw",
    );
    expect(gen.tier).toBe("subfield");
  });

  it("forecloses flagship_potential below the flagship ceiling", () => {
    const gen = normalizeGeneralReview(
      {
        ...base,
        paper_score_ceiling: 8.0,
        flagship_potential: true,
        flagship_directive: "prove the matching converse",
      },
      "raw",
    );
    expect(gen.flagship_potential).toBe(false);
  });

  it("degrades to tier-only routing when the referee omits the ceiling", () => {
    const gen = normalizeGeneralReview({ ...base, tier: "field" }, "raw");
    expect(gen.tier).toBe("field");
    expect(gen.paper_score_ceiling).toBeUndefined();
    expect(gen.critique).not.toMatch(/ceiling gate/);
  });
});

// The reroute budget. Each grant halts at an operator checkpoint and the next `--resume`
// pays for a full D0, so the counter is persisted and MUST bind across resumes.
describe("decideGeneralReroute", () => {
  const fix = { salvageable: true, improvement_directive: "widen the estimator class" };

  it("offers the reroute while budget remains and withdraws it at the cap", () => {
    expect(decideGeneralReroute({ gen: fix, reroutesUsed: 0, cap: 2 })).toEqual({
      canReroute: true,
      capExhausted: false,
    });
    expect(decideGeneralReroute({ gen: fix, reroutesUsed: 1, cap: 2 }).canReroute).toBe(true);
    expect(decideGeneralReroute({ gen: fix, reroutesUsed: 2, cap: 2 })).toEqual({
      canReroute: false,
      capExhausted: true,
    });
  });

  it("distinguishes a spent budget from a dead object, so exhaustion is not banked as refuted", () => {
    // No bounded fix → halt, but NOT `capExhausted`: the halt reason is the object, not the
    // budget, and the two route to different operator actions.
    expect(decideGeneralReroute({ gen: { salvageable: false }, reroutesUsed: 9, cap: 2 })).toEqual({
      canReroute: false,
      capExhausted: false,
    });
    expect(
      decideGeneralReroute({
        gen: { salvageable: true, improvement_directive: "   " },
        reroutesUsed: 0,
        cap: 2,
      }),
    ).toEqual({ canReroute: false, capExhausted: false });
  });
});
