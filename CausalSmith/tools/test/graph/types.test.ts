import { describe, it, expect } from "vitest";
import { GraphSchema, type FormalizationGraph } from "../../src/graph/types.js";

const minimal: FormalizationGraph = {
  qid: "stat_demo",
  specialization: "v1",
  nodes: [
    {
      id: "t1",
      kind: "theorem",
      provenance: "from-note",
      nl: { statement: "the estimand is root-n estimable", tex_anchor: "tex:L10-20", frozen: true },
      lean: { decl_name: null, file: null },
      review: { status: "unreviewed", passed_hash: null },
      proof: { state: "sorry", sorry_count: 1 },
    },
  ],
  edges: [],
};

describe("GraphSchema", () => {
  it("accepts a minimal valid graph", () => {
    expect(GraphSchema.parse(minimal)).toEqual(minimal);
  });

  it("rejects an unknown node kind", () => {
    const bad = { ...minimal, nodes: [{ ...minimal.nodes[0], kind: "widget" }] };
    expect(() => GraphSchema.parse(bad)).toThrow();
  });

  it("requires the assumption sub-object only for assumption nodes", () => {
    const asm = {
      ...minimal,
      nodes: [
        {
          id: "a1",
          kind: "assumption",
          provenance: "from-note",
          nl: { statement: "overlap holds", tex_anchor: "tex:L5", frozen: true },
          lean: { decl_name: null, file: null },
          review: { status: "unreviewed", passed_hash: null },
          proof: { state: "complete", sorry_count: 0 },
          assumption: { tier: 2, classification: "faithful-refinement" },
        },
      ],
    };
    expect(GraphSchema.parse(asm).nodes[0].assumption?.tier).toBe(2);
  });

  it("allows undelivered only for secondary theorems or cited gates", () => {
    const secondary = {
      ...minimal,
      nodes: [{
        ...minimal.nodes[0],
        delivery: { status: "undelivered", role: "secondary", reason: "non-headline citation overflow" },
      }],
    };
    expect(GraphSchema.parse(secondary).nodes[0].delivery?.status).toBe("undelivered");
    const headline = {
      ...minimal,
      nodes: [{
        ...minimal.nodes[0],
        delivery: { status: "undelivered", role: "headline", reason: "too hard" },
      }],
    };
    expect(() => GraphSchema.parse(headline)).toThrow(/secondary theorem or a cited gate/);
  });

  it("rejects a delivered result that depends on an undelivered node", () => {
    const bad = {
      ...minimal,
      nodes: [
        minimal.nodes[0],
        {
          ...minimal.nodes[0], id: "t2",
          delivery: { status: "undelivered", role: "secondary", reason: "secondary overflow" },
        },
      ],
      edges: [{ kind: "proof-uses", from: "t1", to: "t2", source: "declared" }],
    };
    expect(() => GraphSchema.parse(bad)).toThrow(/depends on undelivered/);
  });

  it("rejects a two-hop dependency on an undelivered node through a definition", () => {
    const bad = {
      ...minimal,
      nodes: [
        { ...minimal.nodes[0], delivery: { status: "deliver" as const, role: "headline" as const } },
        { ...minimal.nodes[0], id: "d1", kind: "definition" as const },
        { ...minimal.nodes[0], id: "t2", delivery: { status: "undelivered" as const, role: "secondary" as const, reason: "secondary overflow" } },
      ],
      edges: [
        { kind: "statement-uses" as const, from: "t1", to: "d1", source: "declared" as const },
        { kind: "proof-uses" as const, from: "d1", to: "t2", source: "declared" as const },
      ],
    };
    expect(() => GraphSchema.parse(bad)).toThrow(/transitively depends on undelivered/);
  });
});
