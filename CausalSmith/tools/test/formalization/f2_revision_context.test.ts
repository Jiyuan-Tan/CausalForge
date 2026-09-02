import { describe, expect, it } from "vitest";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import {
  buildF2RevisionContext,
  F2_REVISION_TARGETS_HEADER,
  hasCompleteScaffoldCoverage,
  revisionTargetsFromRedirect,
} from "../../src/formalization/f2_revision_context.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";

function fixture() {
  const core = CoreSchema.parse({
    qid: "local-context-test",
    symbols: [
      { name: "x", type: "real" },
      { name: "y", type: "real", refs: ["x"], ref: "def:derived" },
      { name: "z", type: "real" },
    ],
    assumptions: [
      {
        id: "ass:shared",
        condition: "x is positive",
        free_symbols: ["x"],
        standard: { name: "positivity", cite: "fixture" },
      },
      {
        id: "ass:unrelated",
        condition: "z is bounded",
        free_symbols: ["z"],
        standard: { name: "boundedness", cite: "fixture" },
      },
    ],
    definitions: [
      {
        id: "def:shared",
        name: "Shared",
        construction: "objects satisfying ass:shared",
        free_symbols: ["x"],
        by_member_properties: ["ass:shared"],
      },
      {
        id: "def:derived",
        name: "Derived",
        construction: "y computed from x",
        free_symbols: ["x", "y"],
        inputs: ["x"],
      },
    ],
    statements: [
      {
        id: "thm:target",
        kind: "theorem",
        statement: "target about x",
        free_symbols: ["x"],
        depends_on: ["def:shared"],
        route: "direct",
        status: "to-prove",
        proof_tex: "PROOF_SENTINEL",
        justification: "PROSE_SENTINEL",
      },
      {
        id: "lem:consumer",
        kind: "lemma",
        statement: "consumer of target",
        free_symbols: ["x"],
        depends_on: ["thm:target"],
        status: "to-prove",
      },
      {
        id: "lem:sibling",
        kind: "lemma",
        statement: "sibling using the same prerequisite",
        free_symbols: ["x"],
        depends_on: ["def:shared"],
        status: "to-prove",
      },
      {
        id: "lem:unrelated",
        kind: "lemma",
        statement: "unrelated z result",
        free_symbols: ["z"],
        depends_on: ["ass:unrelated"],
        status: "to-prove",
      },
    ],
    sampling_model: { observed: "x" },
    target_estimand: "x",
    bibliography: [],
  });
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({
    lean_kind,
    lean_name,
    disposition: "define-local",
    reuse: null,
    modules: [],
    ...extra,
  });
  const plan = PlanSchema.parse({
    qid: core.qid,
    env: [
      { id: "S1", world: "x-world", binds_symbols: ["x"], binds_sampling_model: true, disposition: "define-local" },
      { id: "S2", world: "z-world", binds_symbols: ["z"], binds_sampling_model: false, disposition: "define-local" },
    ],
    nodes: {
      "ass:shared": node("assumption", "SharedAssumption"),
      "ass:unrelated": node("assumption", "UnrelatedAssumption"),
      "def:shared": node("structure", "Shared", { members: ["ass:shared"] }),
      "def:derived": node("def", "Derived"),
      "thm:target": node("theorem", "targetTheorem", { hyps: ["def:shared"] }),
      "lem:consumer": node("lemma", "consumerLemma", { hyps: ["thm:target"] }),
      "lem:sibling": node("lemma", "siblingLemma", { hyps: ["def:shared"] }),
      "lem:unrelated": node("lemma", "unrelatedLemma", { hyps: ["ass:unrelated"] }),
    },
    citations: [],
  });
  return { core, plan };
}

describe("F2 local revision context", () => {
  it("keeps the target, prerequisites, and forced downstream consumers without sibling churn", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["thm:target"]);
    expect(packet).not.toBeNull();
    const ids = Object.keys(packet!.plan.nodes as Record<string, unknown>);
    expect(ids).toEqual(["ass:shared", "def:shared", "thm:target", "lem:consumer"]);
    expect(ids).not.toContain("lem:sibling");
    expect(ids).not.toContain("lem:unrelated");
    expect(packet!.plan.env).toEqual([expect.objectContaining({ id: "S1" })]);
    expect(JSON.stringify(packet!.core)).not.toContain("PROOF_SENTINEL");
    expect(JSON.stringify(packet!.core)).not.toContain("PROSE_SENTINEL");
  });

  it("expands a shared symbol target to every declaration that uses that symbol", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["sym:x"]);
    const ids = Object.keys(packet!.plan.nodes as Record<string, unknown>);
    expect(ids).toContain("lem:sibling");
    expect(ids).toContain("def:derived");
    expect(ids).not.toContain("lem:unrelated");
    expect(packet!.resolved_targets).toEqual(["sym:x"]);
    expect(packet!.core.symbols).toEqual(expect.arrayContaining([
      expect.objectContaining({ name: "x" }),
      expect.objectContaining({ name: "y" }),
    ]));
  });

  it("falls back to full context for a shared-symbol edit with undeclared symbol scope", () => {
    const { core, plan } = fixture();
    delete core.statements[0].free_symbols;
    expect(buildF2RevisionContext(core, plan, ["sym:x"])).toBeNull();
  });

  it("includes an ordinary target symbol's explicit ref definition as upstream context", () => {
    const { core, plan } = fixture();
    core.symbols.push({ name: "K", type: "Type", ref: "def:k" });
    core.definitions.push({
      id: "def:k",
      name: "KDefinition",
      construction: "the carrier realizing K",
      free_symbols: ["K"],
      inputs: ["K"],
    });
    plan.nodes["def:k"] = {
      lean_kind: "def",
      lean_name: "KDefinition",
      disposition: "define-local",
      reuse: null,
      modules: [],
      gate: false,
      defer_tier: false,
      delivery_status: "deliver",
    };
    core.statements[0].free_symbols!.push("K");
    const packet = buildF2RevisionContext(core, plan, ["thm:target"]);
    expect(Object.keys(packet!.plan.nodes as Record<string, unknown>)).toContain("def:k");
  });

  it("fails closed to full context when any requested target is unknown", () => {
    const { core, plan } = fixture();
    expect(buildF2RevisionContext(core, plan, ["thm:target", "missing:node"])).toBeNull();
  });

  it("recovers only the exact persisted dispatcher target block", () => {
    const redirect = `Fix the mismatch.\n\n${F2_REVISION_TARGETS_HEADER}\n- thm:target\n- sym:x`;
    expect(revisionTargetsFromRedirect(redirect)).toEqual(["thm:target", "sym:x"]);
    expect(revisionTargetsFromRedirect("Please edit thm:target")).toEqual([]);
  });

  it("requires complete delivered node and environment coverage before localization", () => {
    const { plan } = fixture();
    const delivered = new Set(Object.keys(plan.nodes));
    const envs = new Set(plan.env.map((env) => env.id));
    expect(hasCompleteScaffoldCoverage(plan, { nodes: delivered, envs })).toBe(true);
    delivered.delete("lem:unrelated");
    expect(hasCompleteScaffoldCoverage(plan, { nodes: delivered, envs })).toBe(false);
  });
});
