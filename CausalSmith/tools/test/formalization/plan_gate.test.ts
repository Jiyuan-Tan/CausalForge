import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { runPlanGate, type PlanGateViolation } from "../../src/formalization/plan/plan_gate.js";
import type { Core } from "../../src/discovery/core/schema.js";

// A small, schema-valid core exercising every node kind: a standalone atom, two
// shared member atoms, a class, a construction, and a theorem.
function makeCore(): Core {
  return {
    qid: "panel_demo",
    specialization: "v1",
    cluster: "stat",
    symbols: [
      { name: "X", type: "covariate" },
      { name: "Y", type: "outcome" },
      { name: "e", type: "propensity" },
    ],
    assumptions: [
      { id: "ass:overlap", condition: "0 < e(X) < 1", free_symbols: ["e", "X"], novel: { flag: true, justification: "weak overlap regime" } },
      { id: "ass:consistency", condition: "Y = Y(D)", free_symbols: ["Y"], novel: { flag: true, justification: "PO consistency" } },
      { id: "ass:ignorability", condition: "(Y(1),Y(0)) ⫫ D | X", free_symbols: ["Y", "X"], novel: { flag: true, justification: "unconfoundedness" } },
    ],
    definitions: [
      { id: "def:overlap-class", name: "OverlapClass", construction: "{ P : P satisfies ass:consistency, ass:ignorability }", by_member_properties: ["ass:consistency", "ass:ignorability"] },
      { id: "def:estimator", name: "tauHat", construction: "tauHat = average of psi", inputs: ["O"] },
    ],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "tauHat → tau", depends_on: ["ass:overlap", "ass:consistency", "ass:ignorability", "def:overlap-class", "def:estimator"], status: "proved" },
      { id: "oeq:tight", kind: "openendedquestion", statement: "is the feasible rate tight?", depends_on: ["thm:main"], status: "to-prove" },
    ],
    target_estimand: "tau = E[Y(1) - Y(0)]",
    bibliography: [],
  } as Core;
}

// A plan that maps makeCore() one-to-one. `consistency`/`ignorability` are reached
// by `thm:main` through the bundled class, so they need not be re-listed in hyps.
function makePlan() {
  return {
    qid: "panel_demo",
    specialization: "v1",
    cluster: "stat",
    lean_subdir: "Stat/Demo",
    env: [
      { id: "S1", world: "po-system", binds_symbols: ["X", "Y", "e"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] },
    ],
    nodes: {
      "ass:overlap": { lean_kind: "assumption", lean_name: "assOverlap", disposition: "define-local", modules: ["Causalean.PO.Overlap"] },
      "ass:consistency": { lean_kind: "assumption", lean_name: "assConsistency", disposition: "define-local" },
      "ass:ignorability": { lean_kind: "assumption", lean_name: "assIgnorability", disposition: "define-local" },
      "def:overlap-class": { lean_kind: "structure", lean_name: "OverlapClass", members: ["ass:consistency", "ass:ignorability"], disposition: "define-local" },
      "def:estimator": { lean_kind: "def", lean_name: "tauHat", disposition: "define-local" },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["ass:overlap", "def:overlap-class"], disposition: "define-local" },
      "oeq:tight": { lean_kind: "def", lean_name: "tightOpenQuestion", disposition: "define-local" },
    },
    feasibility: "formalizable-now",
  };
}

function codes(vs: PlanGateViolation[]): string[] {
  return vs.map((v) => v.code);
}

describe("F1 plan gate — golden minimal plan", () => {
  it("a one-to-one plan over the demo core passes every check", () => {
    const res = runPlanGate(makePlan(), makeCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });
});

describe("F1 plan gate — P1 coverage", () => {
  it("flags a missing node entry", () => {
    const plan = makePlan();
    delete (plan.nodes as Record<string, unknown>)["ass:overlap"];
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P1");
  });
  it("flags an extra node entry that is not a core node", () => {
    const plan = makePlan();
    (plan.nodes as Record<string, unknown>)["ass:bogus"] = { lean_kind: "assumption", lean_name: "x", disposition: "define-local" };
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P1");
  });
  it("flags an unbound symbol", () => {
    const plan = makePlan();
    plan.env[0].binds_symbols = ["X", "Y"]; // drops 'e'
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P1");
  });
});

describe("F1 plan gate — P2/P3 structure", () => {
  it("flags a class whose members disagree with by_member_properties", () => {
    const plan = makePlan();
    plan.nodes["def:overlap-class"].members = ["ass:consistency"]; // drops ignorability
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P2");
  });
  it("flags a wrong lean_kind for a core kind", () => {
    const plan = makePlan();
    plan.nodes["def:overlap-class"].lean_kind = "def"; // class must be structure
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P3");
  });
  it("allows an open-ended question to be realized as a non-theorem Prop def", () => {
    const res = runPlanGate(makePlan(), makeCore());
    expect(res.violations.filter((v) => v.where === "oeq:tight")).toEqual([]);
  });
  it("rejects theorem/lemma dispositions for unresolved open-ended questions", () => {
    const plan = makePlan();
    plan.nodes["oeq:tight"].lean_kind = "theorem";
    const res = runPlanGate(plan, makeCore());
    expect(res.violations.some((v) => v.code === "P3" && v.where === "oeq:tight")).toBe(true);
  });
  it("rejects legacy proved open-ended questions as theorem dispositions (D0 must replace them)", () => {
    const core = makeCore();
    core.statements.find((s) => s.id === "oeq:tight")!.status = "proved";
    const plan = makePlan();
    plan.nodes["oeq:tight"].lean_kind = "lemma";
    expect(runPlanGate(plan, core).violations.some((v) => v.code === "P3" && v.where === "oeq:tight")).toBe(true);
  });
});

describe("F1 plan gate — P4 hyp closure", () => {
  it("flags a hyp not in depends_on", () => {
    const plan = makePlan();
    plan.nodes["thm:main"].hyps = ["ass:overlap", "def:overlap-class", "ass:phantom"];
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P4");
  });
  it("flags an assumption dependency reachable through no hyp or bundled class", () => {
    const plan = makePlan();
    plan.nodes["thm:main"].hyps = ["ass:overlap"]; // drops the class → consistency/ignorability uncovered
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P4");
  });
});

describe("F1 plan gate — P5/P6/P7/P8 optional + derived", () => {
  it("flags a reuse decl absent from the library index (P5)", () => {
    const plan = makePlan();
    const res = runPlanGate(plan, makeCore(), { knownDecls: new Set(["SomethingElse"]) });
    expect(codes(res.violations)).toContain("P5");
  });
  it("passes P5 when the reuse decl is in the index", () => {
    const plan = makePlan();
    const res = runPlanGate(plan, makeCore(), { knownDecls: new Set(["Causalean.PO.System.POStructure"]) });
    expect(res.ok).toBe(true);
  });
  it("flags a malformed module path (P6)", () => {
    const plan = makePlan();
    plan.nodes["ass:overlap"].modules = ["not a module"];
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P6");
  });
  it("flags emitted-tag drift against the plan (P7)", () => {
    const plan = makePlan();
    const leanTags = { nodes: new Set(["thm:main"]), envs: new Set(["S1"]) }; // missing the other 5 nodes
    expect(codes(runPlanGate(plan, makeCore(), { leanTags }).violations)).toContain("P7");
  });
  it("passes P7 when every node is tagged", () => {
    const plan = makePlan();
    const leanTags = { nodes: new Set(Object.keys(plan.nodes)), envs: new Set(["S1"]) };
    expect(runPlanGate(plan, makeCore(), { leanTags }).ok).toBe(true);
  });
  it("flags stored feasibility disagreeing with the derived value (P8)", () => {
    const plan = makePlan();
    (plan.nodes["def:estimator"] as Record<string, unknown>).defer_tier = true; // derived ⇒ needs-new-infrastructure
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P8");
  });
});

// A minimal core+plan exercising a CITED node: `lem:borrowed-upper` is borrowed
// (D0 status:"cited", a leaf with its own source), consumed by `thm:main`.
function makeCitedCore(): Core {
  return {
    qid: "panel_cite",
    specialization: "v1",
    cluster: "stat",
    symbols: [{ name: "Y", type: "outcome" }],
    assumptions: [
      { id: "ass:reg", condition: "Y bounded", free_symbols: ["Y"], novel: { flag: true, justification: "regularity" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "rate holds", depends_on: ["ass:reg", "lem:borrowed-upper"], status: "proved" },
      { id: "lem:borrowed-upper", kind: "lemma", statement: "published upper bound", depends_on: [], status: "cited", source: { cite: "BK2022", locator: "Theorem 3" } },
    ],
    target_estimand: "theta",
    bibliography: [{ key: "BK2022", citation: "Bonvini, Kennedy (2022)" }],
  } as Core;
}

function makeCitedPlan() {
  return {
    qid: "panel_cite",
    specialization: "v1",
    cluster: "stat",
    lean_subdir: "Stat/Cite",
    env: [
      { id: "S1", world: "po-system", binds_symbols: ["Y"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] },
    ],
    nodes: {
      "ass:reg": { lean_kind: "assumption", lean_name: "assReg", disposition: "define-local" },
      "lem:borrowed-upper": { lean_kind: "assumption", lean_name: "borrowedUpper", disposition: "define-local", gate: true, gate_class: "cited", source: "cite:bk2022" },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["ass:reg", "lem:borrowed-upper"], disposition: "define-local" },
    },
    citations: [{ id: "cite:bk2022", title: "Fast rates", authors: "Bonvini, Kennedy", year: 2022, arxiv: "2207.11825", locator: "Theorem 3" }],
    feasibility: "formalizable-now",
  };
}

describe("F1 plan gate — P9 cited mapping", () => {
  it("the F1 prompt preserves cited provenance even on a headline dependency", () => {
    const prompt = readFileSync(
      new URL("../../src/formalization/prompts/F1/stage1_template.txt", import.meta.url),
      "utf8",
    );
    expect(prompt).toMatch(/If it is load-bearing for a headline, the delivered headline is honestly CONDITIONAL/);
    expect(prompt).toMatch(/importance does not change provenance/);
    expect(prompt).not.toMatch(/Headline carve-out/);
  });

  it("a faithful cited mapping passes every check", () => {
    const res = runPlanGate(makeCitedPlan(), makeCitedCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });

  it("flags re-laundering a cited statement as a non-cited gate", () => {
    const plan = makeCitedPlan();
    (plan.nodes["lem:borrowed-upper"] as Record<string, unknown>).gate_class = "gated";
    expect(codes(runPlanGate(plan, makeCitedCore()).violations)).toContain("P9");
  });

  it("flags a cited node whose source does not resolve", () => {
    const plan = makeCitedPlan();
    (plan.nodes["lem:borrowed-upper"] as Record<string, unknown>).source = "cite:nonexistent";
    expect(codes(runPlanGate(plan, makeCitedCore()).violations)).toContain("P9");
  });

  it("flags F1 inventing a citation for a non-cited statement", () => {
    const plan = makeCitedPlan();
    (plan.nodes["thm:main"] as Record<string, unknown>).gate_class = "cited";
    expect(codes(runPlanGate(plan, makeCitedCore()).violations)).toContain("P9");
  });
});

describe("F1 plan gate — P10 undelivered guard", () => {
  it("allows an isolated secondary theorem and requires no emitted @node tag", () => {
    const core = makeCore();
    core.statements.find((s) => s.id === "oeq:tight")!.depends_on = [];
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], {
      delivery_role: "secondary",
      delivery_status: "undelivered",
      delivery_reason: "citation instantiation would require a substantial non-headline substrate",
    });
    const leanTags = {
      nodes: new Set(Object.keys(plan.nodes).filter((id) => id !== "thm:main")),
      envs: new Set(["S1"]),
    };
    expect(runPlanGate(plan, core, { leanTags }).violations).toEqual([]);
  });

  it("rejects undelivered headline/support roles and delivered consumers", () => {
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], {
      delivery_role: "headline",
      delivery_status: "undelivered",
      delivery_reason: "too hard",
    });
    const res = runPlanGate(plan, makeCore());
    expect(res.violations.some((v) => v.code === "P10" && v.where === "thm:main")).toBe(true);
    expect(res.violations.some((v) => v.code === "P10" && v.where === "oeq:tight")).toBe(true);
  });
});
