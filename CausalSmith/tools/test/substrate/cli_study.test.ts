import { describe, it, expect } from "vitest";
import { parseArgs, parseStudyArgsForTest, runCli } from "../../src/cli.js";

describe("causalsmith study parsing", () => {
  it("parses <slug>", () => {
    const a = parseStudyArgsForTest(["bh_affinity"]);
    expect(a.slug).toBe("bh_affinity");
  });
  it("parses --resume <slug> --dry-run", () => {
    const a = parseStudyArgsForTest(["--resume", "bh_affinity", "--dry-run"]);
    expect(a.resume).toBe(true);
    expect(a.dryRun).toBe(true);
    expect(a.slug).toBe("bh_affinity");
  });
  it("parses --resume after the slug (position-independent)", () => {
    const a = parseStudyArgsForTest(["bh_affinity", "--resume"]);
    expect(a.resume).toBe(true);
    expect(a.slug).toBe("bh_affinity");
  });
  it("parses a main-authority coordinate-cap reset on resume", () => {
    const a = parseStudyArgsForTest(["bh_affinity", "--resume", "--clear-coordinate-cap"]);
    expect(a.resume).toBe(true);
    expect(a.clearCoordinateCap).toBe(true);
  });
  it("rejects a coordinate-cap reset without resume", () => {
    expect(() => parseStudyArgsForTest(["bh_affinity", "--clear-coordinate-cap"])).toThrow(/requires --resume/);
  });
  it("parses explicit legacy requirement-change recovery only on resume", () => {
    expect(parseStudyArgsForTest(["x", "--resume", "--accept-requirement-change"]).acceptRequirementChange).toBe(true);
    expect(() => parseStudyArgsForTest(["x", "--accept-requirement-change"])).toThrow(/requires --resume/);
  });
  it("rejects extra positionals", () => {
    expect(() => parseStudyArgsForTest(["a", "b"])).toThrow();
  });

  it("rejects the retired research --study flag before a run can start", () => {
    expect(() => parseArgs(["--study", "slug"])).toThrow(/causalsmith study/);
  });

  it("keeps retired study-run ids out of the live research pipeline", async () => {
    await expect(runCli(["insight_legacy", "v1", "--dry-run"])).rejects.toThrow(
      /doc\/study\/runs is reserved for retired study-run compatibility/,
    );
  });
});
