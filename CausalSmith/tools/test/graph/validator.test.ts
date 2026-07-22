import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, setLean } from "../../src/graph/mutate.js";
import { validate } from "../../src/graph/validator.js";

function base() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "weak-overlap ATE under PO", tex_anchor: "" });
  g.nodes[0].setup = { required_modules: ["Causalean.PO"] };
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
  g = setLean(g, "t1", "t1_main", "T1.lean");
  g = setLean(g, "setup", "demoSetup", "T1.lean");
  g = addEdge(g, { kind: "setup-of", from: "setup", to: "t1", source: "declared" });
  return g;
}

describe("validate", () => {
  it("a well-formed graph produces no errors", () => {
    const r = validate(base());
    expect(r.findings.filter((f) => f.severity === "error")).toEqual([]);
    expect(r.ok).toBe(true);
  });

  it("INV-coverage: a from-note node with no Lean link errors", () => {
    let g = base();
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "helper", tex_anchor: "" });
    const r = validate(g);
    expect(r.findings.some((f) => f.invariant === "coverage" && f.node === "l1" && f.severity === "error")).toBe(true);
    expect(r.ok).toBe(false);
  });

  it("INV-coverage: an undelivered node must have no stale Lean anchor", () => {
    let g = base();
    g = addNode(g, { id: "t2", kind: "theorem", provenance: "from-note", nl_statement: "secondary claim", tex_anchor: "" });
    g = setLean(g, "t2", "staleSecondaryTheorem", "T2.lean");
    g.nodes.find((node) => node.id === "t2")!.delivery = {
      status: "undelivered", role: "secondary", reason: "secondary citation overflow",
    };
    const r = validate(g);
    expect(r.ok).toBe(false);
    expect(r.findings.some((finding) => finding.node === "t2" && /must not retain/.test(finding.message))).toBe(true);
  });

  it("INV-edge-integrity: a dangling edge endpoint errors", () => {
    const g = base();
    g.edges.push({ kind: "proof-uses", from: "t1", to: "missing", source: "declared" });
    const r = validate(g);
    expect(r.findings.some((f) => f.invariant === "edge-integrity" && f.severity === "error")).toBe(true);
  });

  it("INV-edge-integrity: a depends-on cycle errors", () => {
    let g = base();
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = setLean(g, "l1", "l1_h", "T1.lean");
    g.edges.push({ kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
    g.edges.push({ kind: "proof-uses", from: "l1", to: "t1", source: "declared" });
    const r = validate(g);
    expect(r.findings.some((f) => f.invariant === "edge-integrity" && /cycle/i.test(f.message))).toBe(true);
  });

  it("INV-setup-binding: a theorem with no setup-of edge errors", () => {
    let g = base();
    g.edges = g.edges.filter((e) => e.kind !== "setup-of");
    const r = validate(g);
    expect(r.findings.some((f) => f.invariant === "setup-binding" && f.node === "t1")).toBe(true);
  });
});
