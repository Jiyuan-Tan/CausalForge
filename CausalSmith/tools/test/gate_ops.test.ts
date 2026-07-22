import { describe, it, expect } from "vitest";
import {
  deriveGateConsumers,
  gateIdentityStrings,
  isGateDisclosure,
  isGateDebtBullet,
  withoutGateKeys,
} from "../src/formalization/gate_ops.js";

const NODE = "input:hetero-clt-denominator-tightness";
const LEAN = "HeteroDenominatorTightnessInput";

describe("deriveGateConsumers", () => {
  it("unions graph proof-uses consumers with plan-hyps consumers, de-duplicated", () => {
    const edges = [
      { kind: "proof-uses", from: "thm:hetero-clt", to: NODE },
      { kind: "proof-uses", from: "thm:postdesign-wald", to: NODE },
      { kind: "proof-uses", from: "thm:other", to: "input:unrelated" }, // different target
      { kind: "depends", from: "thm:x", to: NODE }, // not a proof-uses edge
    ];
    const planNodes = {
      "thm:hetero-clt": { hyps: [NODE, "input:hetero-clt-linscore-depgraph-clt"] },
      "thm:postdesign-wald": { hyps: [NODE] },
      "thm:unrelated": { hyps: ["input:something-else"] },
    };
    expect(deriveGateConsumers(edges, planNodes, NODE).sort()).toEqual(
      ["thm:hetero-clt", "thm:postdesign-wald"].sort(),
    );
  });

  it("returns [] when nothing threads the node", () => {
    expect(deriveGateConsumers([], { "thm:a": { hyps: [] } }, NODE)).toEqual([]);
  });
});

describe("gateIdentityStrings", () => {
  it("includes the node id plus distinct Lean names, dropping blanks/dupes", () => {
    expect(gateIdentityStrings(NODE, LEAN, undefined, NODE)).toEqual([NODE, LEAN]);
    expect(gateIdentityStrings(NODE, NODE, null)).toEqual([NODE]);
  });
});

describe("isGateDisclosure", () => {
  const ids = [NODE, LEAN];
  it("matches BOTH the node-id-keyed and the Lean-name-keyed disclosure of one gate", () => {
    expect(isGateDisclosure({ label: `thm:hetero-clt:${NODE}` }, ids)).toBe(true);
    expect(isGateDisclosure({ label: `thm:hetero-clt:${LEAN}` }, ids)).toBe(true);
    expect(isGateDisclosure({ label: NODE }, ids)).toBe(true); // bare label
  });
  it("does NOT match an unrelated gate that merely shares the anchor prefix", () => {
    expect(isGateDisclosure({ label: "thm:hetero-clt:HeteroLinScoreCLTInput" }, ids)).toBe(false);
    expect(isGateDisclosure({ label: "thm:hetero-clt:BudgetAdmissible" }, ids)).toBe(false);
  });
});

describe("withoutGateKeys", () => {
  it("DELETES gate + gate_class (never leaves gate_class: null, which trips the plan schema)", () => {
    const node = { lean_name: "X", gate: true, gate_class: "gated", disposition: "define-local" };
    const out = withoutGateKeys(node) as Record<string, unknown>;
    expect("gate" in out).toBe(false);
    expect("gate_class" in out).toBe(false);
    expect(out).toEqual({ lean_name: "X", disposition: "define-local" });
  });
  it("is a no-op on a node that has no gate keys", () => {
    expect(withoutGateKeys({ lean_name: "X" })).toEqual({ lean_name: "X" });
  });
});

describe("isGateDebtBullet", () => {
  const ids = [NODE, LEAN];
  it("matches a gate.ts-appended bullet `- **id** (class) — …`", () => {
    expect(isGateDebtBullet(`- **${NODE}** (gated) — gated substrate-debt on thm:hetero-clt`, ids)).toBe(true);
    expect(isGateDebtBullet(`  - **${LEAN}** (cited) — borrowed`, ids)).toBe(true);
  });
  it("does NOT match hand-authored prose (no ` (` after the bold id), preserving a RESOLVED note", () => {
    expect(isGateDebtBullet(`- **${NODE}** — **RESOLVED (2026-07-09).** delta-method discharged…`, ids)).toBe(false);
    expect(isGateDebtBullet(`- **thm:hetero-clt** — REGULARITY added: mentions ${LEAN} in prose`, ids)).toBe(false);
  });
});
