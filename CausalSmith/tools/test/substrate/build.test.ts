// CausalSmith/tools/test/substrate/build.test.ts
import { describe, it, expect } from "vitest";
import {
  parseBuildDiagnostics,
  scanSourceForNonProofDischarge,
  stripLeanComments,
} from "../../src/substrate/build.js";

const LOG = `
Building CausalSmith.Substrate.X.Basic
warning: ./CausalSmith/Substrate/X/Basic.lean:10:0: declaration uses 'sorry'
warning: ./CausalSmith/Substrate/X/Basic.lean:20:0: declaration uses 'sorry'
error: ./CausalSmith/Substrate/X/Helpers.lean:5:2: unknown identifier 'foo'
`;

describe("parseBuildDiagnostics", () => {
  it("counts sorries and errors per file", () => {
    const d = parseBuildDiagnostics(LOG, [
      "CausalSmith/Substrate/X/Basic.lean",
      "CausalSmith/Substrate/X/Helpers.lean",
    ]);
    expect(d.ok).toBe(false);
    expect(d.sorryCount).toBe(2);
    expect(d.errors).toHaveLength(1);
    expect(d.perFile["CausalSmith/Substrate/X/Basic.lean"].sorries).toBe(2);
    expect(d.perFile["CausalSmith/Substrate/X/Helpers.lean"].errors).toBe(1);
  });
  it("ignores a dependency-replay sorry that is not in a target file", () => {
    // `lake build <module>` replays the full dependency closure and re-emits
    // deps' cached warnings; a pre-existing sorry in a dependency must NOT fail
    // the substrate gate (regression: Clt/Prokhorov poisoned every ATE substrate).
    const log = [
      "⚠ [3022/3058] Replayed Clt.Prokhorov",
      "warning: Clt/Prokhorov.lean:15:8: declaration uses `sorry`",
      "Build completed successfully (3058 jobs).",
    ].join("\n");
    const d = parseBuildDiagnostics(log, [
      "CausalSmith/Substrate/AteEifInstance/ATEEfficientIF.lean",
    ]);
    expect(d.sorryCount).toBe(0);
    expect(d.ok).toBe(true);
  });
  it("still counts a sorry in a target file (gate not defeated)", () => {
    const log = "warning: CausalSmith/Substrate/AteEifInstance/ATEEfficientIF.lean:9:8: declaration uses 'sorry'\n";
    const d = parseBuildDiagnostics(log, [
      "CausalSmith/Substrate/AteEifInstance/ATEEfficientIF.lean",
    ]);
    expect(d.sorryCount).toBe(1);
  });
  it("ok=true when only sorries (no errors)", () => {
    const d = parseBuildDiagnostics(
      "warning: ./a/B.lean:1:0: declaration uses 'sorry'\n",
      ["a/B.lean"],
    );
    expect(d.ok).toBe(true);
    expect(d.sorryCount).toBe(1);
  });
});

describe("scanSourceForNonProofDischarge (axiom-laundering guard)", () => {
  it("flags a new axiom declaration", () => {
    const src = [
      "theorem foo : True := by exact hard_core",
      "private axiom hard_core : True",
    ].join("\n");
    const hits = scanSourceForNonProofDischarge("X.lean", src);
    expect(hits).toHaveLength(1);
    expect(hits[0]).toContain("axiom");
  });

  it("flags native_decide", () => {
    const hits = scanSourceForNonProofDischarge("X.lean", "theorem p : 2 = 2 := by native_decide");
    expect(hits).toHaveLength(1);
    expect(hits[0]).toContain("native_decide");
  });

  it("does NOT flag the word 'axiom' when it appears only in a comment/docstring", () => {
    const src = [
      "/-- This proof avoids any `axiom`; it is fully constructive. -/",
      "-- strategy: do not axiomatize the hard step; native_decide is banned",
      "/- nested /- axiom -/ still a comment -/",
      "theorem foo : True := trivial",
    ].join("\n");
    expect(scanSourceForNonProofDischarge("X.lean", src)).toEqual([]);
  });

  it("does not false-positive on identifiers containing the substring", () => {
    const src = "def myaxiomatic_helper : Nat := 0\ntheorem t : True := trivial";
    expect(scanSourceForNonProofDischarge("X.lean", src)).toEqual([]);
  });

  it("stripLeanComments removes line and nested block comments", () => {
    const out = stripLeanComments("a -- axiom\n/- b /- c -/ d -/ e");
    expect(out).not.toContain("axiom");
    expect(out).toContain("a");
    expect(out).toContain("e");
  });
});
