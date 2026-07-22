import { describe, it, expect } from "vitest";
import { renderMechanicalLayer, routeFinding } from "../src/presentation/p1_loop.js";
import { presentedBody, safelyFramesUndeliveredRemark, undeliveredRemarkBody } from "../src/presentation/stages/p1_plan.js";
import { topoOrder, renderedNodes } from "../src/presentation/graph_view.js";
import { parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";
import type { FormalizationGraph, GraphNode, GraphEdge } from "../src/graph/types.js";

const node = (id: string, kind: GraphNode["kind"], stmt = `stmt ${id}`): GraphNode => ({
  id, kind, provenance: "from-note",
  nl: { statement: stmt, tex_anchor: "", frozen: true },
  lean: { decl_name: `${id}_decl`, file: "F.lean" },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
});
const edge = (from: string, to: string): GraphEdge => ({ kind: "statement-uses", from, to, source: "extracted" });
const graph = (nodes: GraphNode[], edges: GraphEdge[] = []): FormalizationGraph =>
  ({ qid: "q", specialization: "v1", nodes, edges });

describe("renderMechanicalLayer", () => {
  it("renders topo-ordered envs by kind, skips setups, body = nl.statement", () => {
    const g = graph(
      [node("a1", "assumption"), node("p7", "definition"), node("s1", "setup"), node("t1", "theorem")],
      [edge("a1", "p7"), edge("t1", "a1")],
    );
    const ordered = topoOrder(g, renderedNodes(g));
    const layer = renderMechanicalLayer(ordered);
    const envs = parseAnchoredEnvs(layer);
    // p7 before a1 (a1 uses p7); a1 before t1 (t1 uses a1); s1 skipped (setup)
    expect(envs.map((e) => e.obj_id)).toEqual(["p7", "a1", "t1"]);
    expect(envs[0].env).toBe("definitionv");
    expect(envs[2].env).toBe("theoremv");
    expect(envs[1].body).toContain("stmt a1");
    expect(layer).not.toContain("{s1}");
  });
});

describe("undelivered presentation boundary", () => {
  it("uses a natural varied open-direction fallback rather than legalistic boilerplate", () => {
    const body = undeliveredRemarkBody("The exact atlas covers every real boundary branch", "the CAD substrate is secondary");
    expect(safelyFramesUndeliveredRemark(body)).toBe(true);
    expect(body).not.toContain("does not establish, prove, or deliver");
    expect(body).not.toContain("nevertheless");
    expect(body).not.toContain("Theorem");
  });

  it("keeps distinct safe agent paraphrases instead of replacing them with one template", () => {
    const a = "A natural next question is whether the exceptional locus admits a finite real stratification; resolving the boundary branches is left for future work.";
    const b = "It remains open whether every feasible fiber has the proposed atlas, and understanding the elimination boundary is a worthwhile direction for future research.";
    expect(undeliveredRemarkBody("claim A", "reason A", a)).toBe(a);
    expect(undeliveredRemarkBody("claim B", "reason B", b)).toBe(b);
  });

  it("rejects a disclaimer that later asserts the undelivered claim as a theorem", () => {
    const unsafe = "A natural open question is whether the atlas exists. Nevertheless, Theorem 7 proves that the atlas exists.";
    const framed = undeliveredRemarkBody("the atlas exists", "the boundary analysis is incomplete", unsafe);
    expect(framed).not.toBe(unsafe);
    expect(safelyFramesUndeliveredRemark(framed)).toBe(true);
  });

  it("rejects an open-question preface followed by an assertive reversal", () => {
    const unsafe = "It remains open whether the atlas exists. In fact, the atlas exists on every boundary branch.";
    expect(safelyFramesUndeliveredRemark(unsafe)).toBe(false);
  });

  it("final emission prefers the safe loop remark over a stale frozen theorem body", () => {
    expect(presentedBody("undelivered", "OLD THEOREM ASSERTION", "safe disclosed remark")).toBe("safe disclosed remark");
    expect(presentedBody("deliver", "validated theorem body", "new draft")).toBe("validated theorem body");
  });
});

describe("routeFinding (deterministic fix_locus)", () => {
  it("routes wording gates to the reviser", () => {
    for (const g of ["lean-identifier", "formalization-leak", "xref-dangling", "xref-missing", "xref-missing-assumption", "faithfulness", "objid-in-prose", "assumption-numbering", "bare-ref"]) {
      expect(routeFinding(g)).toBe("wording-revise");
    }
  });
  it("routes the statement-presentation floor gates to the reviser (re-render, not halt)", () => {
    // Regression: `lintHypothesisPresentation` emits these and its docstring promises a RE-RENDER,
    // but they were absent from WORDING_GATES, so the router halted P1 on the first hypothesis-heavy
    // theorem instead of itemizing it. (Real incident: thm:margin-localization et al.)
    expect(routeFinding("hypothesis-not-itemized")).toBe("wording-revise");
    expect(routeFinding("hypothesis-restated")).toBe("wording-revise");
  });
  it("routes missing class-definition to synthesis; undefined-assumption to wording", () => {
    expect(routeFinding("notation-undefined")).toBe("synthesize-def");
    expect(routeFinding("undefined-assumption")).toBe("wording-revise");
  });
  it("halts on structural / unrecognized gates", () => {
    for (const g of ["unknown-objid", "env-set-changed", "bare-env", "not-frozen", "mystery"]) {
      expect(routeFinding(g)).toBe("halt");
    }
  });
});

import { runP1Loop, P1_MODELS, type P1Env, type P1Finding, type P1LoopHooks } from "../src/presentation/p1_loop.js";

const env = (id: string, refSet: string[] = []): P1Env =>
  ({ id, env: "theoremv", statement: `stmt ${id}`, body: `stmt ${id}`, refSet });

// Build hooks whose `review` returns a scripted finding list per call.
const hooks = (reviews: P1Finding[][], extra: Partial<P1LoopHooks> = {}): P1LoopHooks => {
  let call = 0;
  return {
    render: async (reqs) => new Map(reqs.map((r) => [r.id, `rendered ${r.id}${r.defects ? " (fixed)" : ""}`])),
    review: async () => reviews[Math.min(call++, reviews.length - 1)] ?? [],
    synthesize: async (syms) => syms.map((s) => env(`def_${s}`)),
    assemble: (envs) => envs.map((e) => `\\begin{${e.env}}{${e.id}}\n${e.body}\n\\end{${e.env}}`).join("\n"),
    maxIterations: 4,
    ...extra,
  };
};

describe("runP1Loop (executor→reviewer→router control flow)", () => {
  it("P1_MODELS uses codex for both the executor and the (high-effort) reviewer", () => {
    expect(P1_MODELS.executor).toBe("codex");
    expect(P1_MODELS.reviewer).toBe("codex");
  });

  it("renders all then exits clean when the reviewer is happy", async () => {
    const r = await runP1Loop([env("t1"), env("a1")], hooks([[]]));
    expect(r.ok).toBe(true);
    expect(r.iterations).toBe(1);
    expect(r.envs.find((e) => e.id === "t1")?.body).toBe("rendered t1");
  });

  it("routes a wording finding to a re-render, then converges", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "lean-identifier", objId: "a1", detail: "raw decl name" }],
      [],
    ]));
    expect(r.ok).toBe(true);
    expect(r.envs[0].body).toContain("(fixed)"); // re-rendered with defects
  });

  it("places synthesized definitions before the statements that use them", async () => {
    const r = await runP1Loop([env("t1")], hooks([
      [{ gate: "notation-reviewer", symbol: "X", fixLocus: "synthesize-def", detail: "X undefined" }],
      [],
    ]));
    expect(r.ok).toBe(true);
    expect(r.envs.map((e) => e.id)).toEqual(["def_X", "t1"]);
  });

  it("treats notation-undefined as advisory (graph guarantees defs exist) — no synthesis, converges", async () => {
    let synthCalled = false;
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "notation-undefined", detail: "H undefined", symbol: "H" }],
    ], { synthesize: async () => { synthCalled = true; return []; } }));
    expect(r.ok).toBe(true);
    expect(synthCalled).toBe(false);
    expect(r.advisories.some((f) => f.gate === "notation-undefined")).toBe(true);
  });

  it("halts on a structural finding", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "unknown-objid", objId: "a1", detail: "not in graph" }],
    ]));
    expect(r.ok).toBe(false);
    expect(r.unresolved[0].gate).toBe("unknown-objid");
  });

  it("treats xref-missing as advisory (non-blocking)", async () => {
    const r = await runP1Loop([env("a1", ["p7"])], hooks([
      [{ gate: "xref-missing", objId: "a1", detail: "missing p7" }],
    ]));
    expect(r.ok).toBe(true);
    expect(r.advisories[0].gate).toBe("xref-missing");
  });

  it("halts on unresolved semantic notation-reviewer findings", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "notation-reviewer", symbol: "\\operatorname{Cum}", detail: "named operator is undefined" }],
    ]));
    expect(r.ok).toBe(false);
    expect(r.unresolved[0].gate).toBe("notation-reviewer");
    expect(r.advisories.some((a) => a.gate === "notation-reviewer")).toBe(false);
  });

  it("ENFORCES xref-missing-assumption (blocks → re-renders, not advisory)", async () => {
    // round 0 flags the unreferenced assumption hypothesis; the re-render clears it on round 1.
    const r = await runP1Loop([env("thm:a", ["ass:foo"])], hooks([
      [{ gate: "xref-missing-assumption", objId: "thm:a", detail: "depends on ass:foo, never \\ref'd" }],
      [],
    ]));
    expect(r.ok).toBe(true);
    // it went through the actionable (re-render) path, NOT collected as a non-blocking advisory.
    expect(r.advisories.some((a) => a.gate === "xref-missing-assumption")).toBe(false);
  });

  it("fails after the iteration cap on a persistent finding", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "lean-identifier", objId: "a1", detail: "persists" }],
    ]));
    expect(r.ok).toBe(false);
    expect(r.iterations).toBe(4);
  });
});
