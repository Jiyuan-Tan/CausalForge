import { describe, it, expect } from "vitest";
import { proofContentClosureIntersects } from "../../src/discovery/solve/merge.js";

const theorem = {
  id: "thm:consumer", kind: "theorem", statement: "The consumer holds.",
  depends_on: ["def:outer"], status: "proved", proof_tex: "Apply the outer construction.",
};

const core = {
  qid: "stat_closure", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "tau" }],
  assumptions: [{
    id: "ass:outer", kind: "regularity", condition: "Use ass:inner.",
    free_symbols: [], novel: { flag: true, justification: "test" },
  }, {
    id: "ass:inner", kind: "regularity", condition: "Inner condition.",
    free_symbols: [], novel: { flag: true, justification: "test" },
  }],
  definitions: [{
    id: "def:outer", name: "outer", construction: "Build it using def:inner and ass:outer.",
    // The regression is specifically that these are symbols, while the real node refs
    // occur only in `construction`.
    inputs: ["x"],
  }, {
    id: "def:inner", name: "inner", construction: "Inner construction.", inputs: ["x"],
  }],
  statements: [theorem, {
    id: "thm:hidden-source", kind: "theorem", statement: "A hidden source theorem.",
    depends_on: [], status: "proved", proof_tex: "QED.",
  }],
  target_estimand: "tau", bibliography: [],
} as never;

describe("proposal proof-invalidation closure", () => {
  const touches = (id: string): boolean => proofContentClosureIntersects({
    core,
    node: theorem as never,
    proofText: theorem.proof_tex,
    changedIds: new Set([id]),
  });

  it("follows definition refs embedded in construction text", () => {
    expect(touches("def:inner")).toBe(true);
  });

  it("follows assumption refs embedded behind a definition and another assumption", () => {
    expect(touches("ass:inner")).toBe(true);
  });

  it("does not invalidate a genuinely unrelated closure", () => {
    expect(touches("thm:hidden-source")).toBe(false);
  });

  it("follows a transitive statement consumer edge", () => {
    const consumer = {
      ...theorem,
      id: "thm:downstream",
      depends_on: [theorem.id],
      proof_tex: "Apply thm:consumer.",
    };
    expect(proofContentClosureIntersects({
      core: { ...(core as never as Record<string, unknown>), statements: [...(core as any).statements, consumer] } as never,
      node: consumer as never,
      proofText: consumer.proof_tex,
      changedIds: new Set([theorem.id]),
    })).toBe(true);
  });
});
