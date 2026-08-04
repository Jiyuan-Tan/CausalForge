import { describe, it, expect } from "vitest";
import {
  structuralGate,
  proposalGate,
  symbolPreflightGate,
  symbolDriftGate,
  roundInvariantsGate,
  proseConsistencyGate,
} from "../../../src/discovery/framework/gate_registrations.js";

describe("gate registrations", () => {
  it("every exported gate has a stable id and non-empty evidence", () => {
    const gates = [
      structuralGate,
      proposalGate,
      symbolPreflightGate,
      symbolDriftGate,
      roundInvariantsGate,
      proseConsistencyGate,
    ];
    const ids = gates.map((g) => g.id);
    expect(ids).toContain("structural-gate");
    expect(ids).toContain("proposal-gate");
    expect(new Set(ids).size).toBe(ids.length);
    for (const g of gates) expect(g.evidence.trim().length).toBeGreaterThan(0);
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

  // (Retired, Phase 1: the proposal-closure gate — closure holds by construction
  // of assembleCore; see test/discovery/assemble.test.ts.)

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
