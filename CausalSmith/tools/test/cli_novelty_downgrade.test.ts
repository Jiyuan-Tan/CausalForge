import { describe, it, expect } from "vitest";
import { parseArgsForTest } from "../src/cli.js";
import { normalizeNoveltyTarget, NOVELTY_TARGETS } from "../src/novelty.js";

describe("normalizeNoveltyTarget", () => {
  it("passes through the canonical tier vocabulary", () => {
    for (const t of NOVELTY_TARGETS) expect(normalizeNoveltyTarget(t)).toBe(t);
  });

  it("maps the two legacy spellings onto the tier ladder", () => {
    expect(normalizeNoveltyTarget("relative-to-repo")).toBe("incremental");
    expect(normalizeNoveltyTarget("relative-to-literature")).toBe("subfield");
  });

  it("returns undefined for an unknown value", () => {
    expect(normalizeNoveltyTarget("bogus")).toBeUndefined();
    expect(normalizeNoveltyTarget(undefined)).toBeUndefined();
  });
});

describe("cli --novelty (unified tier vocabulary)", () => {
  it("accepts the tier names directly", () => {
    for (const t of ["incremental", "subfield", "field", "flagship"] as const) {
      const a = parseArgsForTest(["--novelty", t, "stat_x_v1", "v1"]);
      expect(a.noveltyTarget).toBe(t);
    }
  });

  it("normalizes legacy spellings to the tier vocabulary", () => {
    expect(parseArgsForTest(["--novelty", "relative-to-repo", "stat_x_v1", "v1"]).noveltyTarget).toBe(
      "incremental",
    );
    expect(
      parseArgsForTest(["--novelty", "relative-to-literature", "stat_x_v1", "v1"]).noveltyTarget,
    ).toBe("subfield");
  });

  it("rejects an unknown novelty value", () => {
    expect(() => parseArgsForTest(["--novelty", "subfeld", "stat_x_v1", "v1"])).toThrow();
  });
});

describe("cli --downgrade-tier parsing", () => {
  it("parses --downgrade-tier <tier> <qid> <spec> as a resume-mode operation", () => {
    const a = parseArgsForTest(["--downgrade-tier", "subfield", "stat_dp_cate_minimax_v1", "v1"]);
    expect(a.downgradeTierMode).toBe(true);
    expect(a.downgradeTier).toBe("subfield");
    expect(a.qid).toBe("stat_dp_cate_minimax_v1");
    expect(a.specialization).toBe("v1");
    expect(a.resume).toBe(true);
  });

  it("normalizes a legacy tier spelling", () => {
    const a = parseArgsForTest(["--downgrade-tier", "relative-to-literature", "stat_x_v1", "v1"]);
    expect(a.downgradeTier).toBe("subfield");
  });

  it("carries --auto and --stop-after through parse", () => {
    const a = parseArgsForTest([
      "--downgrade-tier", "incremental", "stat_x_v1", "v1", "--auto", "--stop-after", "D0.5",
    ]);
    expect(a.downgradeTierMode).toBe(true);
    expect(a.auto).toBe(true);
    expect(a.stopAfter).toBe("D0.5");
  });

  it("rejects an unknown tier", () => {
    expect(() => parseArgsForTest(["--downgrade-tier", "bogus", "stat_x_v1", "v1"])).toThrow();
  });

  it("rejects a missing spec", () => {
    expect(() => parseArgsForTest(["--downgrade-tier", "subfield", "stat_x_v1"])).toThrow();
  });

  it("rejects extra positionals", () => {
    expect(() =>
      parseArgsForTest(["--downgrade-tier", "subfield", "stat_x_v1", "v1", "extra"]),
    ).toThrow();
  });
});
