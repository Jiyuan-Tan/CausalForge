import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, markPassed } from "../../src/graph/mutate.js";
import { dirtyFrontier } from "../../src/graph/diff.js";
import { statementHash } from "../../src/graph/hash.js";

// t1 PROOF-uses l1 (a proof lemma) and STATEMENT-uses d1 (a def its statement references).
function chain() {
  let g = createEmptyGraph("q", "v1");
  g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
  g = addNode(g, { id: "d1", kind: "definition", provenance: "from-note", nl_statement: "def", tex_anchor: "" });
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" }); // proof-level dep
  g = addEdge(g, { kind: "statement-uses", from: "t1", to: "d1", source: "extracted" }); // statement-level dep
  g = markPassed(g, "l1", "h_l1");
  g = markPassed(g, "d1", "h_d1");
  g = markPassed(g, "t1", "h_t1");
  return g;
}

describe("dirtyFrontier", () => {
  it("returns empty when all hashes match", () => {
    const g = chain();
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1" })).toEqual([]);
  });

  it("a changed PROOF-USES lemma marks ONLY itself — proof deps don't dirty the dependent's statement", () => {
    const g = chain();
    expect(dirtyFrontier(g, { l1: "h_l1_NEW", d1: "h_d1", t1: "h_t1" })).toEqual(["l1"]);
  });

  it("a changed STATEMENT-USES def marks itself AND the statement-dependent theorem", () => {
    const g = chain();
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1_NEW", t1: "h_t1" }).sort()).toEqual(["d1", "t1"]);
  });

  it("a from-note node never passed (no passed_hash) is dirty (needs first review)", () => {
    let g = chain();
    g = addNode(g, { id: "l2", kind: "lemma", provenance: "from-note", nl_statement: "x", tex_anchor: "" });
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1", l2: "h_l2" })).toEqual(["l2"]);
  });

  it("does not label setup containers dirty because symbol clusters own their review", () => {
    let g = chain();
    g = addNode(g, { id: "S1", kind: "setup", provenance: "from-note", nl_statement: "world", tex_anchor: "" });
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1", S1: "new" })).toEqual([]);
    g = markPassed(g, "S1", "old");
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1", S1: "new" })).toEqual([]);
  });

  it("a never-reviewed AGENT-INTRODUCED node is NOT a dirty source, and doesn't dirty a statement that uses it", () => {
    let g = chain();
    // an agent-introduced hidden-def t1's STATEMENT references but which is never a review target
    g = addNode(g, { id: "aux1", kind: "definition", provenance: "agent-introduced", nl_statement: "aux", tex_anchor: "" });
    g = addEdge(g, { kind: "statement-uses", from: "t1", to: "aux1", source: "extracted" });
    // aux1 has no passed_hash (null) but is agent-introduced → not a source → t1 stays clean
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1", aux1: "h_aux1" })).toEqual([]);
  });

  // ── Hypothesis-backed nodes (no standalone `@node:` decl → absent from freshHashes).
  // Their freshness falls back to the hash of their NL statement, so they are verifiable
  // rather than trusted forever behind a constant `passed_hash` sentinel.
  it("a reviewed hypothesis-backed node carrying a legacy sentinel hash is dirty (heals to its NL-statement hash)", () => {
    let g = chain();
    g = addNode(g, { id: "hyp1", kind: "assumption", provenance: "agent-introduced", nl_statement: "assume the L-11 budget", tex_anchor: "" });
    g = markPassed(g, "hyp1", "reviewed"); // the old constant sentinel — not a real hash
    // hyp1 absent from freshHashes (hypothesis lives inside a host theorem's signature)
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1" })).toEqual(["hyp1"]);
  });

  it("a reviewed hypothesis-backed node is stable once passed_hash IS its NL-statement hash", () => {
    let g = chain();
    const nl = "assume the L-11 budget";
    g = addNode(g, { id: "hyp1", kind: "assumption", provenance: "agent-introduced", nl_statement: nl, tex_anchor: "" });
    g = markPassed(g, "hyp1", statementHash(nl));
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1" })).toEqual([]);
  });

  it("a reviewed hypothesis-backed node re-dirties when its NL statement changes", () => {
    let g = chain();
    g = addNode(g, { id: "hyp1", kind: "assumption", provenance: "agent-introduced", nl_statement: "new spec", tex_anchor: "" });
    g = markPassed(g, "hyp1", statementHash("old spec")); // reviewed against the prior spec
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1" })).toEqual(["hyp1"]);
  });
});
