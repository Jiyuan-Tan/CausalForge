import { describe, expect, it } from "vitest";
import { buildGraphFromCorePlan } from "../../src/graph/from_core.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { Plan } from "../../src/formalization/plan/schema.js";

function core(): Core {
  return {
    qid: "panel_demo",
    specialization: "v1",
    symbols: [{ name: "Y", type: "outcome" }],
    assumptions: [
      { id: "ass:overlap", condition: "0 < e(X) < 1", free_symbols: [], novel: { flag: true, justification: "x" } },
      { id: "ass:consistency", condition: "Y = Y(D)", free_symbols: [], novel: { flag: true, justification: "x" } },
    ],
    definitions: [
      { id: "def:class", name: "C", construction: "{P : satisfies ass:consistency}", by_member_properties: ["ass:consistency"] },
      { id: "def:est", name: "tauHat", construction: "tauHat = ...", inputs: ["O"] },
    ],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "tauHat → tau", depends_on: ["ass:overlap", "def:class", "def:est"], status: "proved" },
      { id: "oeq:tight", kind: "openendedquestion", statement: "is the feasible rate tight?", depends_on: ["thm:main"], status: "to-prove" },
    ],
    target_estimand: "tau",
    bibliography: [],
  } as Core;
}

function plan(): Plan {
  return {
    qid: "panel_demo",
    specialization: "v1",
    env: [
      { id: "S1", world: "po-system", binds_symbols: ["Y"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] },
    ],
    nodes: {
      "ass:overlap": { lean_kind: "assumption", lean_name: "assOverlap", disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "ass:consistency": { lean_kind: "assumption", lean_name: "assConsistency", disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "def:class": { lean_kind: "structure", lean_name: "C", members: ["ass:consistency"], disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "def:est": { lean_kind: "def", lean_name: "tauHat", disposition: "reuse", reuse: "Causalean.Estimation.AIPW", modules: [], defer_tier: false },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["ass:overlap", "def:class"], disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "oeq:tight": { lean_kind: "def", lean_name: "tightOpenQuestion", disposition: "define-local", reuse: null, modules: [], defer_tier: false },
    },
    citations: [],
  } as Plan;
}

describe("buildGraphFromCorePlan", () => {
  const g = buildGraphFromCorePlan(core(), "v1", plan());
  const ids = new Set(g.nodes.map((n) => n.id));

  it("creates one node per core node id, keyed by the core id, plus the env S-block", () => {
    expect(ids).toEqual(new Set(["S1", "ass:overlap", "ass:consistency", "def:class", "def:est", "thm:main", "oeq:tight"]));
  });

  it("maps node kinds from the plan's lean_kind / core kind", () => {
    const kind = (id: string) => g.nodes.find((n) => n.id === id)!.kind;
    expect(kind("S1")).toBe("setup");
    expect(kind("ass:overlap")).toBe("assumption");
    expect(kind("def:class")).toBe("definition");
    expect(kind("def:est")).toBe("definition");
    expect(kind("thm:main")).toBe("theorem");
    expect(kind("oeq:tight")).toBe("definition");
  });

  it("fails closed if a proved OEQ was not replaced at the D0 boundary", () => {
    const malformed = core();
    malformed.statements.find((s) => s.id === "oeq:tight")!.status = "proved";
    expect(() => buildGraphFromCorePlan(malformed, "v1", plan())).toThrow(/not normalized to a thm:/);
  });

  it("carries the core NL as the node statement", () => {
    expect(g.nodes.find((n) => n.id === "ass:overlap")!.nl.statement).toContain("0 < e(X)");
  });

  it("marks a reuse node as library-backed (decl_name set)", () => {
    expect(g.nodes.find((n) => n.id === "def:est")!.lean.decl_name).toBe("Causalean.Estimation.AIPW");
    expect(g.nodes.find((n) => n.id === "S1")!.lean.decl_name).toBe("Causalean.PO.System.POStructure");
  });

  it("stamps a causalsmith-compatible obj_id alias on every node (by kind)", () => {
    const objId = (id: string) => g.nodes.find((n) => n.id === id)!.obj_id;
    expect(objId("S1")).toBe("S-1");
    expect(objId("ass:overlap")).toBe("A-1");
    expect(objId("ass:consistency")).toBe("A-2");
    expect(objId("def:class")).toBe("P-1");
    expect(objId("def:est")).toBe("P-2");
    expect(objId("oeq:tight")).toBe("P-3");
    expect(objId("thm:main")).toBe("T-1");
  });

  it("emits proof-uses edges from depends_on and setup-of edges to the theorem", () => {
    const proofUses = g.edges.filter((e) => e.kind === "proof-uses" && e.from === "thm:main").map((e) => e.to);
    expect(new Set(proofUses)).toEqual(new Set(["ass:overlap", "def:class", "def:est"]));
    expect(g.edges.some((e) => e.kind === "setup-of" && e.from === "S1" && e.to === "thm:main")).toBe(true);
  });
});

describe("buildGraphFromCorePlan — assumption citation provenance", () => {
  function coreWithStandard(): Core {
    return {
      qid: "panel_std",
      specialization: "v1",
      symbols: [{ name: "Y", type: "outcome" }],
      assumptions: [
        { id: "ass:margin", condition: "P(0<|tau|<=u)<=Cm u^a", free_symbols: [], standard: { name: "Tsybakov decision margin", cite: "Tsybakov2004" } },
        { id: "ass:novelone", condition: "some new condition", free_symbols: [], novel: { flag: true, justification: "new" } },
      ],
      definitions: [],
      statements: [{ id: "thm:main", kind: "theorem", statement: "S", depends_on: ["ass:margin", "ass:novelone"], status: "proved" }],
      target_estimand: "tau",
      bibliography: [{ key: "Tsybakov2004", citation: "Tsybakov, A. B. (2004). Optimal aggregation of classifiers in statistical learning. Ann. Statist." }],
    } as Core;
  }

  const g = buildGraphFromCorePlan(coreWithStandard(), "v1", null);

  it("carries standard {name, cite, citation} onto a standard assumption node", () => {
    expect(g.nodes.find((n) => n.id === "ass:margin")!.standard).toEqual({
      name: "Tsybakov decision margin",
      cite: "Tsybakov2004",
      citation: "Tsybakov, A. B. (2004). Optimal aggregation of classifiers in statistical learning. Ann. Statist.",
    });
  });

  it("leaves a novel assumption with no standard (absent ⇒ novel-to-this-work)", () => {
    expect(g.nodes.find((n) => n.id === "ass:novelone")!.standard).toBeUndefined();
  });
});
