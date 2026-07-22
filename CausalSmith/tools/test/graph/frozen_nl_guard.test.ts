import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode } from "../../src/graph/mutate.js";
import { frozenNlFingerprint, frozenMutationReason, assertFrozenNlStable } from "../../src/graph/frozen_nl_guard.js";

function graphWith() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "a1", kind: "assumption", provenance: "from-note", nl_statement: "(Y(0),Y(1))⊥A∣X", tex_anchor: "" });
  g = addNode(g, { id: "h1", kind: "lemma", provenance: "agent-introduced", nl_statement: "helper", tex_anchor: "" });
  return g;
}

describe("frozen-note immutability guard", () => {
  it("passes when the frozen NL is unchanged", () => {
    const g = graphWith();
    const base = frozenNlFingerprint(g);
    expect(frozenMutationReason(base, g)).toBeNull();
    expect(() => assertFrozenNlStable(base, g)).not.toThrow();
  });

  it("flags a weakened frozen NL (the A-1/D1 laundering shape)", () => {
    const g = graphWith();
    const base = frozenNlFingerprint(g);
    const weakened = {
      ...g,
      nodes: g.nodes.map((n) => (n.id === "a1" ? { ...n, nl: { ...n.nl, statement: "only the 4 moment identities" } } : n)),
    };
    const reason = frozenMutationReason(base, weakened);
    expect(reason).toContain("a1");
    expect(() => assertFrozenNlStable(base, weakened)).toThrow(/frozen-note immutability violated/);
  });

  it("flags a deleted frozen node", () => {
    const g = graphWith();
    const base = frozenNlFingerprint(g);
    const dropped = { ...g, nodes: g.nodes.filter((n) => n.id !== "a1") };
    expect(frozenMutationReason(base, dropped)).toContain("deleted");
  });

  it("ignores edits to NON-frozen (agent-introduced) nodes", () => {
    const g = graphWith();
    const base = frozenNlFingerprint(g);
    const edited = {
      ...g,
      nodes: g.nodes.map((n) => (n.id === "h1" ? { ...n, nl: { ...n.nl, statement: "rewritten helper" } } : n)),
    };
    expect(frozenMutationReason(base, edited)).toBeNull();
  });
});
