import { describe, it, expect } from "vitest";
import {
  collectFlagCodes,
  decideRejectEscape,
  decideReviseOutcome,
  decideTierSaturationPromote,
  normalizeReviewVerdict,
} from "../../../src/discovery/stages/neg0_5_decision.js";

const flag = (code: string) => ({ code, note: "x" });

describe("collectFlagCodes", () => {
  it("collects codes across the three flag arrays, ignoring malformed entries", () => {
    expect(
      collectFlagCodes({
        structure_flags: [flag("S-1")],
        novelty_flags: [flag("N-mischar"), "junk", null],
        soundness_flags: [flag("C-sanity")],
      }),
    ).toEqual(["S-1", "N-mischar", "C-sanity"]);
  });
});

describe("normalizeReviewVerdict", () => {
  it("normalizes the three legal verdicts case-insensitively", () => {
    expect(normalizeReviewVerdict("accept")).toBe("ACCEPT");
    expect(normalizeReviewVerdict("REJECT")).toBe("REJECT");
    expect(normalizeReviewVerdict(" Revise ")).toBe("REVISE");
  });

  it("returns null for a missing or junk verdict instead of defaulting to REVISE", () => {
    // A reviewer emitting parseable JSON with no usable `verdict` has NOT reviewed
    // anything: defaulting to REVISE burned one of five revise rounds plus a full
    // producer re-author on a shape fault, and poisoned the tier-promote history.
    expect(normalizeReviewVerdict(null)).toBeNull();
    expect(normalizeReviewVerdict("")).toBeNull();
    expect(normalizeReviewVerdict("TODO: fill in")).toBeNull();
  });
});

describe("decideRejectEscape", () => {
  it("kernel flag → kernel-replace, once per angle", () => {
    const base = { codes: ["C-definitional-unfold"], angle: 2, draftRebuildUsedAngles: [] as number[] };
    expect(decideRejectEscape({ ...base, kernelReplaceUsedAngles: [] })).toBe("kernel-replace");
    expect(decideRejectEscape({ ...base, kernelReplaceUsedAngles: [2] })).toBeNull();
  });

  it("kernel-replace takes priority over draft-rebuild when both patterns present", () => {
    expect(
      decideRejectEscape({
        codes: ["C-tautological-iff", "C-sanity", "C-coherence"],
        angle: 0,
        kernelReplaceUsedAngles: [],
        draftRebuildUsedAngles: [],
      }),
    ).toBe("kernel-replace");
  });

  it("draft-rebuild needs >= 2 draft-broken codes and fires once per angle", () => {
    const two = { codes: ["C-sanity", "N-witness-trivial"], angle: 1, kernelReplaceUsedAngles: [] as number[] };
    expect(decideRejectEscape({ ...two, draftRebuildUsedAngles: [] })).toBe("draft-rebuild");
    expect(decideRejectEscape({ ...two, draftRebuildUsedAngles: [1] })).toBeNull();
    expect(
      decideRejectEscape({ codes: ["C-sanity"], angle: 1, kernelReplaceUsedAngles: [], draftRebuildUsedAngles: [] }),
    ).toBeNull();
  });
});

describe("decideTierSaturationPromote", () => {
  const row = (verdict: string, tier?: string, clean?: boolean) => ({
    angle: 0,
    version: 1,
    mode: "revise",
    verdict,
    tier,
    clean_substance: clean,
  });

  it("promotes after 3 consecutive clean at-floor REVISEs on the same angle", () => {
    const iterations = [row("REVISE", "flagship", true), row("REVISE", "flagship", true), row("REVISE", "flagship", true)];
    expect(
      decideTierSaturationPromote({
        verdict: "REVISE",
        tier: "flagship",
        cleanSubstance: true,
        iterations,
        angle: 0,
        noveltyTarget: "field",
      }),
    ).toBe(true);
  });

  it("does not promote with only 2 rows, a dirty row, or a below-floor tier", () => {
    const clean = row("REVISE", "flagship", true);
    expect(
      decideTierSaturationPromote({
        verdict: "REVISE", tier: "flagship", cleanSubstance: true,
        iterations: [clean, clean], angle: 0, noveltyTarget: "field",
      }),
    ).toBe(false);
    expect(
      decideTierSaturationPromote({
        verdict: "REVISE", tier: "flagship", cleanSubstance: true,
        iterations: [clean, row("REVISE", "flagship", false), clean], angle: 0, noveltyTarget: "field",
      }),
    ).toBe(false);
    expect(
      decideTierSaturationPromote({
        verdict: "REVISE", tier: "not-publishable", cleanSubstance: true,
        iterations: [clean, clean, clean], angle: 0, noveltyTarget: "field",
      }),
    ).toBe(false);
  });

  it("never promotes a non-REVISE verdict", () => {
    expect(
      decideTierSaturationPromote({
        verdict: "REJECT", tier: "flagship", cleanSubstance: true,
        iterations: [row("REVISE", "flagship", true), row("REVISE", "flagship", true), row("REVISE", "flagship", true)],
        angle: 0, noveltyTarget: "field",
      }),
    ).toBe(false);
  });
});

describe("decideReviseOutcome", () => {
  const floorRow = { angle: 0, version: 1, mode: "revise", verdict: "REVISE", tier: "flagship" };

  it("kills a below-floor angle at the kill version", () => {
    expect(
      decideReviseOutcome({
        version: 3,
        iterations: [{ ...floorRow, tier: "letter" }],
        angle: 0,
        noveltyTarget: "field",
        reviseCap: 5,
        killVersion: 3,
      }),
    ).toBe("below-floor-kill");
  });

  it("an angle that reached the floor gets the full cap runway, then exhausts", () => {
    const args = { iterations: [floorRow], angle: 0, noveltyTarget: "field" as const, reviseCap: 5, killVersion: 3 };
    expect(decideReviseOutcome({ ...args, version: 3 })).toBe("revise");
    expect(decideReviseOutcome({ ...args, version: 5 })).toBe("revise-cap-exhausted");
  });
});
