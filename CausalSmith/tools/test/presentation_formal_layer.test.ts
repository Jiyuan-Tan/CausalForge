import { describe, it, expect } from "vitest";
import { buildFormalLayer } from "../src/presentation/emit.js";
import type { CrosswalkEntry } from "../src/presentation/types.js";
import type { FormalizationGraph } from "../src/graph/types.js";

const n = (
  id: string,
  obj_id: string,
  kind: FormalizationGraph["nodes"][number]["kind"],
  decl: string | null,
  status: string,
  proof: FormalizationGraph["nodes"][number]["proof"],
  provenance: FormalizationGraph["nodes"][number]["provenance"] = "from-note",
  frozen = true,
): FormalizationGraph["nodes"][number] => ({
  id,
  obj_id,
  kind,
  provenance,
  nl: { statement: `NL of ${obj_id}`, tex_anchor: "", frozen },
  lean: { decl_name: decl, file: decl ? "Basic.lean" : null },
  review: { status: status as never, passed_hash: null },
  proof,
});

const cw = (obj_id: string, decl: string): CrosswalkEntry => ({
  obj_id,
  kind: "definition",
  title: obj_id,
  tex: null,
  lean: { file: "Basic.lean", decl, decl_kind: "def", line: 0 },
  verdict: "equivalent",
});

const graph: FormalizationGraph = {
  qid: "q",
  specialization: "s",
  nodes: [
    n("S-1", "S-1", "setup", null, "unreviewed", { state: "complete", sorry_count: 0 }),
    n("def:a", "P-1", "definition", "declA", "matched", { state: "complete", sorry_count: 0 }),
    n("ass:x", "A-1", "assumption", "AssX", "matched", { state: "complete", sorry_count: 0 }),
    n("thm:m", "T-1", "theorem", "mainThm", "matched", { state: "sorry", sorry_count: 1 }),
    // agent-introduced helper must NOT appear in the formal layer (from-note only)
    n("lem:helper", "L-1", "lemma", "helper", "matched", { state: "complete", sorry_count: 0 }, "agent-introduced"),
  ],
  edges: [],
};

describe("buildFormalLayer", () => {
  // Crosswalk + items join by NODE id (matching the paper's data-objid); the alias is display only.
  const fl = buildFormalLayer(graph, [cw("def:a", "declA"), cw("ass:x", "AssX"), cw("thm:m", "mainThm")], "deadbeef");

  it("groups every from-note object by kind in a stable order", () => {
    expect(fl.commit).toBe("deadbeef");
    expect(fl.groups.map((g) => g.kind)).toEqual(["setup", "definition", "assumption", "theorem"]);
  });

  it("excludes non-from-note nodes (the agent-introduced lemma)", () => {
    const all = fl.groups.flatMap((g) => g.items.map((i) => i.obj_id));
    expect(all).toEqual(["S-1", "def:a", "ass:x", "thm:m"]); // obj_id = node id
  });

  it("carries NL, Lean anchor, status, and sorry-free per item", () => {
    const def = fl.groups.find((g) => g.kind === "definition")!.items[0];
    // obj_id is the node id (the join key); the alias `P-1` survives only as the display label.
    expect(def).toMatchObject({ obj_id: "def:a", label: "Definition P-1", nl: "NL of P-1", status: "matched", sorry_free: true });
    expect(def.lean?.decl).toBe("declA");
    const setup = fl.groups.find((g) => g.kind === "setup")!.items[0];
    expect(setup).toMatchObject({ obj_id: "S-1", lean: null, status: "unreviewed" }); // decl-less setup
    const thm = fl.groups.find((g) => g.kind === "theorem")!.items[0];
    expect(thm.sorry_free).toBe(false); // proof.state === "sorry"
  });
});

describe("buildFormalLayer auxiliary group", () => {
  const withAux: FormalizationGraph = {
    qid: "q",
    specialization: "s",
    nodes: [
      n("thm:m", "T-1", "theorem", "mainThm", "matched", { state: "complete", sorry_count: 0 }),
      n("aux:h", "aux:h", "lemma", "helperH", "matched", { state: "complete", sorry_count: 0 }, "agent-introduced", false),
    ],
    edges: [{ kind: "proof-uses", from: "thm:m", to: "aux:h", source: "extracted" }],
  };
  const fl = buildFormalLayer(withAux, [cw("aux:h", "helperH")], "c");

  it("appends an auxiliary group with the agent-introduced proof helper (Lean-only)", () => {
    const aux = fl.groups.find((g) => g.kind === "auxiliary");
    expect(aux).toBeTruthy();
    expect(aux!.items.map((i) => i.obj_id)).toEqual(["aux:h"]);
    expect(aux!.items[0].nl).toBe(""); // Lean-only, no rendered NL
    expect(aux!.items[0].lean?.decl).toBe("helperH");
    expect(aux!.items[0].label).toContain("helperH");
  });

  it("places auxiliary last, after the from-note groups", () => {
    expect(fl.groups[fl.groups.length - 1].kind).toBe("auxiliary");
  });
});

describe("buildFormalLayer current equivalence status", () => {
  it("uses the successful P1 audit instead of a stale unreviewed graph stamp", () => {
    const g: FormalizationGraph = {
      qid: "q", specialization: "s", edges: [],
      nodes: [n("ass:x", "A-1", "assumption", "AssX", "unreviewed", { state: "complete", sorry_count: 0 })],
    };
    const fl = buildFormalLayer(g, [cw("ass:x", "AssX")], "c", new Map([["ass:x", "matched"]]));
    expect(fl.groups[0].items[0].status).toBe("matched");
  });
});

describe("buildFormalLayer undelivered remarks", () => {
  it("moves an undelivered secondary theorem to a remark group with no Lean/sorry claim", () => {
    const atlas = {
      ...n("thm:atlas", "T-5", "theorem", "atlasThm", "matched", { state: "sorry", sorry_count: 1 }),
      delivery: { status: "undelivered" as const, role: "secondary" as const, reason: "citation overflow" },
    };
    const fl = buildFormalLayer(
      { qid: "q", specialization: "s", nodes: [atlas], edges: [] },
      [cw("thm:atlas", "atlasThm")],
      "c",
    );
    expect(fl.groups.map((g) => g.kind)).toEqual(["remark"]);
    expect(fl.groups[0].items[0]).toMatchObject({
      obj_id: "thm:atlas", kind: "remark", lean: null, status: "undelivered", sorry_free: null,
    });
  });
});
