import { describe, it, expect } from "vitest";
import { registerGate, allGates, runGates, _resetRegistryForTests } from "../../../src/discovery/framework/gates.js";

describe("gate registry", () => {
  it("registers a gate, lists it, and enforces unique ids", () => {
    _resetRegistryForTests();
    const g = registerGate({
      id: "demo-nonempty",
      tier: "hard",
      stages: ["0"],
      evidence: "PIPELINE_NOTES 2026-07-20 (demo)",
      check: (input: { items: string[] }) =>
        input.items.length === 0 ? [{ gateId: "demo-nonempty", detail: "no items" }] : [],
    });
    expect(allGates().map((x) => x.id)).toContain("demo-nonempty");
    expect(() => registerGate({ ...g })).toThrow(/duplicate gate id/i);
  });

  it("runGates partitions violations by tier and tags each with its gate id", () => {
    _resetRegistryForTests();
    const hard = registerGate({
      id: "h",
      tier: "hard",
      stages: ["0"],
      evidence: "e",
      check: (_: { x: number }) => [{ gateId: "h", detail: "boom" }],
    });
    const warn = registerGate({
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
    _resetRegistryForTests();
    expect(() =>
      registerGate({ id: "no-evidence", tier: "warn", stages: ["0"], evidence: "  ", check: () => [] }),
    ).toThrow(/evidence/i);
  });
});
