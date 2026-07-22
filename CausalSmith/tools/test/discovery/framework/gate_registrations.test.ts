import { describe, it, expect } from "vitest";
import {
  structuralGate,
  proposalGate,
  closureGate,
  symbolPreflightGate,
  roundInvariantsGate,
  proseConsistencyGate,
} from "../../../src/discovery/framework/gate_registrations.js";
import { allGates } from "../../../src/discovery/framework/gates.js";

describe("gate registrations", () => {
  it("registry lists every registered gate with non-empty evidence", () => {
    const ids = allGates().map((g) => g.id);
    expect(ids).toContain("structural-gate");
    expect(ids).toContain("proposal-gate");
    for (const g of allGates()) expect(g.evidence.trim().length).toBeGreaterThan(0);
  });

  it("structural-gate fires on a schema-invalid core (firing fixture)", () => {
    const violations = structuralGate.check({ core: { not: "a core" } });
    expect(violations.length).toBeGreaterThan(0);
    expect(violations[0].gateId).toBe("structural-gate");
  });

  it("proposal-gate fires on a schema-invalid core (firing fixture)", () => {
    const violations = proposalGate.check({ not: "a core" });
    expect(violations.length).toBeGreaterThan(0);
    expect(violations[0].gateId).toBe("proposal-gate");
  });

  it("proposal-closure fires on an uncarried core id (firing fixture)", () => {
    const node = (id: string) => ({ id });
    const violations = closureGate.check({
      core: { statements: [node("thm:orphan")], definitions: [], assumptions: [] },
      proto: { statements: [], definitions: [], assumptions: [] },
      proposalIds: new Set<string>(),
    });
    expect(violations.length).toBeGreaterThan(0);
    expect(violations[0].ids).toContain("thm:orphan");
  });

  it("symbol-preflight fires on an undeclared free symbol (firing fixture)", () => {
    const violations = symbolPreflightGate.check({
      symbols: [{ name: "tau" }],
      assumptions: [{ id: "ass:x", free_symbols: ["tau", "undeclared_sym"] }],
      definitions: [],
    });
    expect(violations.length).toBeGreaterThan(0);
    expect(violations[0].gateId).toBe("symbol-preflight");
  });

  it("warn-tier gates are registered with warn tier (policy: detect, not throw)", () => {
    expect(roundInvariantsGate.tier).toBe("warn");
    expect(proseConsistencyGate.tier).toBe("warn");
  });
});
