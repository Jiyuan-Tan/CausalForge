import { describe, expect, it } from "vitest";
import { buildGraphFromCorePlan } from "../../src/graph/from_core.js";
import { renderBridgeNote } from "../../src/graph/render_note.js";
import { parseNoteBlocks } from "../../src/presentation/note_parser.js";
import type { Core } from "../../src/discovery/core/schema.js";
import type { Plan } from "../../src/formalization/plan/schema.js";

function core(): Core {
  return {
    qid: "panel_demo",
    specialization: "v1",
    symbols: [{ name: "Y", type: "outcome" }],
    assumptions: [
      { id: "ass:overlap", condition: "0 < e(X) < 1 for all X", free_symbols: [], novel: { flag: true, justification: "x" } },
    ],
    definitions: [
      { id: "def:class", name: "C", construction: "the weak-overlap class of laws", by_member_properties: ["ass:overlap"] },
      { id: "def:est", name: "tauHat", construction: "the cross-fitted AIPW estimator", inputs: ["O"] },
    ],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "tauHat converges to tau at the minimax rate", depends_on: ["ass:overlap", "def:class", "def:est"], status: "proved" },
      { id: "lem:aux", kind: "lemma", statement: "the oracle score is unbiased", depends_on: ["ass:overlap"], status: "proved" },
      { id: "oeq:tight", kind: "openendedquestion", statement: "OPEN: determine whether the feasible rate is tight", depends_on: ["thm:main"], status: "to-prove" },
    ],
    target_estimand: "tau",
    bibliography: [],
  } as Core;
}

function plan(): Plan {
  return {
    qid: "panel_demo",
    specialization: "v1",
    env: [{ id: "S1", world: "po-system", binds_symbols: ["Y"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] }],
    nodes: {
      "ass:overlap": { lean_kind: "assumption", lean_name: "assOverlap", disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "def:class": { lean_kind: "structure", lean_name: "C", members: ["ass:overlap"], disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "def:est": { lean_kind: "def", lean_name: "tauHat", disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["def:class"], disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "lem:aux": { lean_kind: "lemma", lean_name: "aux", target_file: "Basic.lean", hyps: ["ass:overlap"], disposition: "define-local", reuse: null, modules: [], defer_tier: false },
      "oeq:tight": { lean_kind: "def", lean_name: "tightOpenQuestion", disposition: "define-local", reuse: null, modules: [], defer_tier: false },
    },
    citations: [],
  } as Plan;
}

describe("renderBridgeNote — round-trips through causalsmith parseNoteBlocks", () => {
  const md = renderBridgeNote(buildGraphFromCorePlan(core(), "v1", plan()));
  const blocks = parseNoteBlocks(md);
  const byId = new Map(blocks.map((b) => [b.obj_id, b]));

  it("emits P/L/T blocks parseNoteBlocks recovers, keyed by the graph obj_id alias", () => {
    // definitions → P-1, P-2, open OEQ def → P-3 ; lemma → L-1 ; theorem → T-1 (A-/S- are not [PLT], so ignored)
    expect(byId.has("P-1")).toBe(true);
    expect(byId.has("P-2")).toBe(true);
    expect(byId.has("P-3")).toBe(true);
    expect(byId.has("L-1")).toBe(true);
    expect(byId.has("T-1")).toBe(true);
  });

  it("the T-block carries a Statement field with the core statement", () => {
    const t = byId.get("T-1")!;
    expect(t.fields["Statement"] ?? t.body).toContain("minimax rate");
  });

  it("a P-block body carries the core construction text", () => {
    const p2 = byId.get("P-2")!;
    expect(`${p2.title} ${p2.body}`).toContain("AIPW");
  });

  it("renders an open-ended residual def as a P-block, not a T-block", () => {
    expect(`${byId.get("P-3")!.title} ${byId.get("P-3")!.body}`).toContain("OPEN");
    expect([...byId.keys()].filter((id) => id.startsWith("T-"))).toEqual(["T-1"]);
  });
});
