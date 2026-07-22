import { describe, it, expect } from "vitest";
import { decideReviseConvergence } from "../../../src/discovery/stages/d0.js";

const keys = (...ks: string[]) => new Set(ks);

describe("decideReviseConvergence (D0.5 review↔D0.R loop control)", () => {
  it("round 0 (no previous keys) always continues", () => {
    expect(decideReviseConvergence(null, keys("a@n1", "b@n2"))).toEqual({ kind: "continue" });
  });

  it("a finding surviving a D0.R edit escalates as persistent, even when the count shrank", () => {
    expect(decideReviseConvergence(keys("a@n1", "b@n2", "c@n3"), keys("a@n1"))).toEqual({
      kind: "persistent-findings",
      persistent: ["a@n1"],
    });
  });

  it("all-new findings with no count reduction escalate as whack-a-mole", () => {
    expect(decideReviseConvergence(keys("a@n1", "b@n2"), keys("c@n3", "d@n4"))).toEqual({
      kind: "no-net-progress",
      before: 2,
      after: 2,
    });
    expect(decideReviseConvergence(keys("a@n1"), keys("c@n3", "d@n4"))).toEqual({
      kind: "no-net-progress",
      before: 1,
      after: 2,
    });
  });

  it("a strictly shrinking, fully-fresh finding set continues", () => {
    expect(decideReviseConvergence(keys("a@n1", "b@n2"), keys("c@n3"))).toEqual({ kind: "continue" });
    expect(decideReviseConvergence(keys("a@n1"), new Set())).toEqual({ kind: "continue" });
  });
});
