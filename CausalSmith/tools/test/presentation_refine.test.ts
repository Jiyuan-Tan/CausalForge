import { describe, it, expect } from "vitest";
import { refineStatement, type StatementCheck } from "../src/presentation/gates.js";

const check: StatementCheck = {
  obj_id: "T-1",
  envBody: "the rate is n^{-1/2}",
  leanStatement: "theorem t1 : rate = n^{-1/2} under (h : Measurable f)",
  leanPointer: "file: X.lean decl: t1",
  isMainResult: true,
};

describe("refineStatement", () => {
  it("passes through unchanged when the first audit is faithful (0 rounds)", async () => {
    const r = await refineStatement({
      check,
      notation: "",
      maxRounds: 3,
      reaudit: async () => ({ verdict: "faithful" }),
      refine: async () => {
        throw new Error("refine must not be called when already faithful");
      },
    });
    expect(r).toMatchObject({ faithful: true, escalated: false, rounds: 0, body: check.envBody });
  });

  it("refines once and becomes faithful (not escalated, body updated)", async () => {
    let audits = 0;
    const r = await refineStatement({
      check,
      notation: "",
      maxRounds: 3,
      reaudit: async () => ({ verdict: audits++ === 0 ? "drift" : "faithful", detail: "missing measurability" }),
      refine: async () => ({ refinedBody: "the rate is n^{-1/2}, for measurable f", changed: true, note: "added measurability" }),
    });
    expect(r.faithful).toBe(true);
    expect(r.escalated).toBe(false);
    expect(r.rounds).toBe(1);
    expect(r.body).toContain("measurable f");
    expect(r.note).toBe("added measurability");
  });

  it("escalates when the refiner cannot tighten further (changed=false)", async () => {
    const r = await refineStatement({
      check,
      notation: "",
      maxRounds: 3,
      reaudit: async () => ({ verdict: "drift", detail: "still off" }),
      refine: async () => ({ refinedBody: check.envBody, changed: false, note: "cannot tighten" }),
    });
    expect(r.escalated).toBe(true);
    expect(r.faithful).toBe(false);
    expect(r.rounds).toBe(1);
  });

  it("escalates after exactly maxRounds (3) when drift persists", async () => {
    let refines = 0;
    const r = await refineStatement({
      check,
      notation: "",
      maxRounds: 3,
      reaudit: async () => ({ verdict: "drift", detail: "persistent" }),
      refine: async () => ({ refinedBody: `attempt ${++refines}`, changed: true }),
    });
    expect(r.escalated).toBe(true);
    expect(r.rounds).toBe(3);
    expect(refines).toBe(3);
  });
});
