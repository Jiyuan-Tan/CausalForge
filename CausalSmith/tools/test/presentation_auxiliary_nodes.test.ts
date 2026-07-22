import { describe, it, expect } from "vitest";
import { auxiliaryNodes } from "../src/presentation/graph_view.js";
import type { FormalizationGraph } from "../src/graph/types.js";

const n = (
  id: string,
  kind: FormalizationGraph["nodes"][number]["kind"],
  provenance: FormalizationGraph["nodes"][number]["provenance"],
  decl: string | null,
  frozen: boolean,
): FormalizationGraph["nodes"][number] => ({
  id,
  kind,
  provenance,
  nl: { statement: id, tex_anchor: "", frozen },
  lean: { decl_name: decl, file: decl ? "Basic.lean" : null },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
});

const g: FormalizationGraph = {
  qid: "q",
  specialization: "s",
  nodes: [
    n("thm:main", "theorem", "from-note", "mainThm", true), // rendered
    n("aux:a", "lemma", "agent-introduced", "helperA", false), // proof-used by the theorem
    n("aux:b", "lemma", "agent-introduced", "helperB", false), // proof-used by aux:a (helper of helper)
    n("aux:nodecl", "lemma", "agent-introduced", null, false), // no decl → excluded
    n("lib:reuse", "lemma", "library", "reuseLemma", false), // library, not agent → excluded
    n("aux:disconnected", "lemma", "agent-introduced", "disconnected", false), // NO edge to the theorem
  ],
  edges: [
    { kind: "proof-uses", from: "thm:main", to: "aux:a", source: "extracted" },
    { kind: "proof-uses", from: "thm:main", to: "aux:nodecl", source: "extracted" },
    { kind: "statement-uses", from: "thm:main", to: "lib:reuse", source: "declared" },
    { kind: "proof-uses", from: "aux:a", to: "aux:b", source: "extracted" },
  ],
};

describe("auxiliaryNodes", () => {
  const aux = auxiliaryNodes(g).map((x) => x.id);

  it("collects every agent-introduced decl-carrying helper", () => {
    expect(aux).toContain("aux:a");
    expect(aux).toContain("aux:b");
    // The graph's proof/statement edges are an incomplete dependency record, so a helper with no
    // edge to the theorem it supports MUST still appear — a reachability walk would silently drop
    // it (real runs lose ~half the helpers, e.g. the whole lower-bound machinery, to missing edges).
    expect(aux).toContain("aux:disconnected");
  });
  it("excludes decl-less and library nodes", () => {
    expect(aux).not.toContain("aux:nodecl");
    expect(aux).not.toContain("lib:reuse");
  });
  it("excludes the rendered (from-note) objects themselves", () => {
    expect(aux).not.toContain("thm:main");
  });
});
