import { describe, it, expect } from "vitest";
import {
  crosswalkAnchorIntegrity,
  type LiveDeclIndex,
} from "../src/formalization/bank_crosswalk_lint.js";
import type { CrosswalkEntry, CrosswalkVerdict } from "../src/types.js";

const anchor = (file: string, decl: string, line = 1) =>
  ({ file, decl, decl_kind: "def", line }) as const;

const entry = (
  obj_id: string,
  verdict: CrosswalkVerdict,
  lean: CrosswalkEntry["lean"],
): CrosswalkEntry => ({
  obj_id,
  kind: "definition",
  title: obj_id,
  tex: { label: obj_id, line_range: "1" },
  lean,
  verdict,
});

// A small live-source index: decl name → occurrences (file relative to leanDir, line).
const live: LiveDeclIndex = new Map([
  ["ConditionalExchangeability", [{ file: "Basic.lean", line: 418 }]],
  ["t1_thm", [{ file: "T1.lean", line: 903 }]],
  ["movedHelper", [{ file: "Helpers_Part2.lean", line: 12 }]],
]);

describe("crosswalkAnchorIntegrity (banked anchor → live source)", () => {
  it("passes a resolving anchor (file + decl present, line within tolerance)", () => {
    const f = crosswalkAnchorIntegrity(
      [entry("P-1b", "equivalent", anchor("Basic.lean", "ConditionalExchangeability", 411))],
      live,
    );
    expect(f).toEqual([]);
  });

  it("flags missing-decl when the decl no longer exists (renamed/removed)", () => {
    const f = crosswalkAnchorIntegrity(
      [entry("P-3", "equivalent", anchor("Basic.lean", "lamDagger", 520))],
      live,
    );
    expect(f.map((x) => [x.obj_id, x.severity])).toEqual([["P-3", "missing-decl"]]);
    expect(f[0].verdict).toBe("equivalent"); // carries verdict so a verified-match miss reads as laundering
  });

  it("flags moved-file when the decl now lives in a different file", () => {
    const f = crosswalkAnchorIntegrity(
      [entry("L-1", "exact", anchor("Helpers.lean", "movedHelper", 10))],
      live,
    );
    expect(f[0].severity).toBe("moved-file");
    expect(f[0].liveFile).toBe("Helpers_Part2.lean");
  });

  it("flags line-drift only beyond tolerance, not within", () => {
    const within = crosswalkAnchorIntegrity(
      [entry("T-1", "equivalent", anchor("T1.lean", "t1_thm", 900))],
      live,
      { lineTolerance: 50 },
    );
    expect(within).toEqual([]);
    const beyond = crosswalkAnchorIntegrity(
      [entry("T-1", "equivalent", anchor("T1.lean", "t1_thm", 10))],
      live,
      { lineTolerance: 50 },
    );
    expect(beyond[0].severity).toBe("line-drift");
    expect(beyond[0].liveLine).toBe(903);
  });

  it("matches the recorded file by basename (path-prefix insensitive)", () => {
    const f = crosswalkAnchorIntegrity(
      [entry("P-1b", "equivalent", anchor("sub/Basic.lean", "ConditionalExchangeability", 418))],
      live,
    );
    expect(f).toEqual([]);
  });

  it("skips lean:null rows (intentionally unanchored)", () => {
    const f = crosswalkAnchorIntegrity([entry("P-1", "equivalent", null)], live);
    expect(f).toEqual([]);
  });
});
