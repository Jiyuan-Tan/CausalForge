import { describe, it, expect } from "vitest";
import { defineGate, runGates } from "../../../src/discovery/framework/gates.js";

describe("explicit gates", () => {
  it("defines an immutable gate with evidence", () => {
    const g = defineGate({
      id: "demo-nonempty",
      tier: "hard",
      stages: ["0"],
      evidence: "PIPELINE_NOTES 2026-07-20 (demo)",
      check: (input: { items: string[] }) =>
        input.items.length === 0 ? [{ gateId: "demo-nonempty", detail: "no items" }] : [],
    });
    expect(g.id).toBe("demo-nonempty");
    expect(Object.isFrozen(g)).toBe(true);
  });

  it("runGates partitions violations by tier and tags each with its gate id", () => {
    const hard = defineGate({
      id: "h",
      tier: "hard",
      stages: ["0"],
      evidence: "e",
      check: (_: { x: number }) => [{ gateId: "h", detail: "boom" }],
    });
    const warn = defineGate({
      id: "w",
      tier: "warn",
      stages: ["0"],
      evidence: "e",
      check: (_: { x: number }) => [{ gateId: "w", detail: "meh" }],
    });
    const out = runGates([hard, warn], { x: 1 });
    expect(out.hard).toEqual([{ gateId: "h", detail: "boom" }]);
    expect(out.warn).toEqual([{ gateId: "w", detail: "meh" }]);
  });

  it("rejects registration with empty evidence — every gate must cite its incident", () => {
    expect(() =>
      defineGate({ id: "no-evidence", tier: "warn", stages: ["0"], evidence: "  ", check: () => [] }),
    ).toThrow(/evidence/i);
  });
});
