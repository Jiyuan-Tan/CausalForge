import { describe, it, expect } from "vitest";
import { renderMechanicalLayer, routeFinding } from "../src/presentation/p1_loop.js";
import {
  placeSynthesizedDefinitions,
  presentedBody,
  routeNotationProblems,
  orderEnvsForLayer,
  synthLedgerKey,
  safelyFramesUndeliveredRemark,
  undeliveredRemarkBody,
} from "../src/presentation/stages/p1_plan.js";
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

describe("P1 synthesized-definition placement", () => {
  it("reconciles current and stale synthetic outline ids without moving graph objects", () => {
    const outline = `# Title\nT\n# Notation\n\n# Sections\n## section: setup\nbrief\nobjs: graph-a, synth_99\nbib: none\n## section: results\nkeep\nobjs: graph-b, synth_88\nbib: none`;
    const placed = placeSynthesizedDefinitions(outline, ["synth_2", "synth_1"]);
    expect(placed).toContain("objs: synth_2, synth_1,graph-a");
    expect(placed).toContain("objs: graph-b");
    expect(placed).not.toMatch(/synth_(?:88|99)/);
    expect(placeSynthesizedDefinitions(placed, ["synth_2", "synth_1"])).toBe(placed);
  });
  it("retains valid one-time synth placements across sections and places only missing ids at first use", () => {
    const outline = `# Title\nT\n# Notation\n\n# Sections\n## section: setup\nbrief\nobjs: graph-a, synth_99\nbib: none\n## section:   method  \nkeep\nobjs: synth_1, graph-b\nbib: none\n## section: results\nlast\nobjs: graph-c\nbib: none`;
    const preferred = new Map([["synth_1", "results"], ["synth_2", "method"]]);
    const placed = placeSynthesizedDefinitions(outline, ["synth_2", "synth_1"], preferred);
    expect(placed).toContain("objs: synth_2,synth_1, graph-b");
    expect(placed).not.toContain("synth_99");
    expect(placeSynthesizedDefinitions(placed, ["synth_2", "synth_1"], preferred)).toBe(placed);
  });
});

describe("orderEnvsForLayer (synth-before-first-use placement)", () => {
  const mkEnv = (id: string, body: string): { id: string; env: "definitionv"; statement: string; body: string; refSet: string[] } =>
    ({ id, env: "definitionv", statement: body, body, refSet: [] });
  it("inserts each synthesized definition immediately before its first user", () => {
    const graphEnvs = [
      mkEnv("d1", String.raw`Setup without the symbol.`),
      mkEnv("t1", String.raw`The theorem uses \(\mathcal H^\beta\).`),
      mkEnv("t2", String.raw`Also uses \(\mathcal H^\beta\).`),
    ];
    const synth = mkEnv("synth_1", String.raw`We define \(\mathcal H^\beta := \dots\).`);
    const ordered = orderEnvsForLayer(graphEnvs, [synth], new Map([["synth_1", [String.raw`\mathcal H^\beta`]]]), new Map());
    expect(ordered.map((e) => e.id)).toEqual(["d1", "synth_1", "t1", "t2"]);
  });
  it("chains synthesized prerequisites: a later synth lands before the earlier synth that uses it", () => {
    const graphEnvs = [mkEnv("t1", String.raw`Uses \(A(x)\).`)];
    const synthA = mkEnv("synth_1", String.raw`We define \(A(x) := B(x)+1\).`);
    const synthB = mkEnv("synth_2", String.raw`We define \(B(x) := x\).`);
    const symbols = new Map([["synth_1", ["A(x)"]], ["synth_2", ["B(x)"]]]);
    const ordered = orderEnvsForLayer(graphEnvs, [synthA, synthB], symbols, new Map());
    expect(ordered.map((e) => e.id)).toEqual(["synth_2", "synth_1", "t1"]);
  });
  it("places a CONSOLIDATED synth before the earliest first-use among ALL its symbols", () => {
    // A grouped definition covering {A, B}: B is used earlier than A — the env must
    // precede B's first use, not A's (splicing by one arbitrary sibling let siblings
    // be used before their definition; audit finding).
    const graphEnvs = [
      mkEnv("d1", "No symbols."),
      mkEnv("t1", String.raw`Uses \(B_n\).`),
      mkEnv("t2", String.raw`Uses \(A_n\) and \(B_n\).`),
    ];
    const synth = mkEnv("synth_1", String.raw`We define \(A_n\) and \(B_n\).`);
    const ordered = orderEnvsForLayer(graphEnvs, [synth], new Map([["synth_1", ["A_n", "B_n"]]]), new Map());
    expect(ordered.map((e) => e.id)).toEqual(["d1", "synth_1", "t1", "t2"]);
  });
  it("front-places a synth with no visible user and never drops an env", () => {
    const graphEnvs = [mkEnv("t1", "No symbols here.")];
    const synth = mkEnv("synth_1", String.raw`We define \(Z := 0\).`);
    const ordered = orderEnvsForLayer(graphEnvs, [synth], new Map([["synth_1", ["Z"]]]), new Map());
    expect(ordered.map((e) => e.id)).toEqual(["synth_1", "t1"]);
  });
  it("matches first use through the env title too", () => {
    const graphEnvs = [mkEnv("d1", "No use in body."), mkEnv("t1", "Body without symbol.")];
    const synth = mkEnv("synth_1", String.raw`We define \(Q_n\).`);
    const titles = new Map([["t1", String.raw`Rate for \(Q_n\)`]]);
    const ordered = orderEnvsForLayer(graphEnvs, [synth], new Map([["synth_1", ["Q_n"]]]), titles);
    expect(ordered.map((e) => e.id)).toEqual(["d1", "synth_1", "t1"]);
  });
});

describe("routeNotationProblems (single semantic notation authority)", () => {
  const base = {
    isLeanRealized: () => false,
    designatedHomeFor: () => undefined as string | undefined,
    ledgerHas: () => false,
    graphNodeIds: new Set<string>(["thm:a", "def:b"]),
    lockedIds: new Set<string>(),
  };
  it("routes undefined/no-anchor to synthesis for ordinary symbols", () => {
    const out = routeNotationProblems(
      [{ symbol: "\\mathcal H", case: "undefined", used_in: ["thm:a"], fix: "add a definition" }], base);
    expect(out).toMatchObject([{ gate: "notation-reviewer", fixLocus: "synthesize-def", symbol: "\\mathcal H" }]);
  });
  it("converts a re-flagged ledgered symbol into a non-blocking checkpoint advisory", () => {
    const out = routeNotationProblems(
      [{ symbol: "\\mathcal H", case: "undefined", used_in: ["thm:a"] }],
      { ...base, ledgerHas: (key) => key === synthLedgerKey("\\mathcal H") });
    expect(out).toMatchObject([{ gate: "notation-unresolved", symbol: "\\mathcal H" }]);
    expect(out[0].fixLocus).toBeUndefined();
  });
  it("converts a re-flagged COMPOUND symbol into an advisory when every atom is ledgered", () => {
    // The loop ledgers per atom; the reviewer may re-report the same compound string.
    // Without the atom-wise check this routed synthesize-def forever and idled the
    // loop to its iteration cap (audit finding, 2026-08-15).
    const compound = String.raw`\(m_1(h)\) and \(m_2(h)\)`;
    const ledgered = new Set([synthLedgerKey(String.raw`m_1(h)`), synthLedgerKey(String.raw`m_2(h)`)]);
    const out = routeNotationProblems(
      [{ symbol: compound, case: "undefined", used_in: ["thm:a"] }],
      { ...base, ledgerHas: (key) => ledgered.has(key) });
    expect(out).toMatchObject([{ gate: "notation-unresolved" }]);
  });
  it("halts loud on symbol-less problems and target-less wrong-refs instead of dropping them", () => {
    const out = routeNotationProblems(
      [{ case: "undefined", fix: "who knows" }, { symbol: "X", case: "wrong-ref", used_in: [] }], base);
    expect(out).toMatchObject([{ fixLocus: "halt" }, { fixLocus: "halt", symbol: "X" }]);
  });
  it("routes an ORDINARY symbol with an editable designated home to that home instead of synthesizing", () => {
    const out = routeNotationProblems(
      [{ symbol: "\\sigma_a", case: "undefined", used_in: ["thm:a"] }],
      { ...base, designatedHomeFor: () => "def:b" });
    expect(out).toMatchObject([{ gate: "notation-reviewer", objId: "def:b", fixLocus: "wording-revise" }]);
  });
  it("re-renders the designated home for a Lean-realized symbol instead of synthesizing", () => {
    const out = routeNotationProblems(
      [{ symbol: "\\theta_T", case: "undefined", used_in: ["thm:a"] }],
      { ...base, isLeanRealized: () => true, designatedHomeFor: () => "def:b" });
    expect(out).toMatchObject([{ gate: "notation-reviewer", objId: "def:b", fixLocus: "wording-revise" }]);
  });
  it("halts on a Lean-realized symbol whose designated home is locked or missing", () => {
    const locked = routeNotationProblems(
      [{ symbol: "\\theta_T", case: "undefined" }],
      { ...base, isLeanRealized: () => true, designatedHomeFor: () => "def:b", lockedIds: new Set(["def:b"]) });
    expect(locked).toMatchObject([{ fixLocus: "halt" }]);
    const homeless = routeNotationProblems(
      [{ symbol: "\\theta_T", case: "no-anchor" }],
      { ...base, isLeanRealized: () => true });
    expect(homeless).toMatchObject([{ fixLocus: "halt" }]);
  });
  it("routes wrong-ref/mismatch to a wording revise per using env", () => {
    const out = routeNotationProblems(
      [{ symbol: "\\mathcal H", case: "wrong-ref", used_in: ["thm:a", "def:b"] }], base);
    expect(out).toMatchObject([
      { objId: "thm:a", fixLocus: "wording-revise" },
      { objId: "def:b", fixLocus: "wording-revise" },
    ]);
  });
  it("halts on an unrecognized case", () => {
    const out = routeNotationProblems([{ symbol: "X", case: "surprise" }], base);
    expect(out).toMatchObject([{ fixLocus: "halt", symbol: "X" }]);
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
  it("routes undefined-assumption to wording; synthesis needs an explicit reviewer fix_locus", () => {
    expect(routeFinding("undefined-assumption")).toBe("wording-revise");
    // The deterministic orphan-class gate was retired: no gate name routes to
    // synthesize-def by itself any more.
    expect(routeFinding("notation-undefined")).toBe("halt");
  });
  it("halts on structural / unrecognized gates", () => {
    for (const g of ["unknown-objid", "env-set-changed", "bare-env", "not-frozen", "mystery"]) {
      expect(routeFinding(g)).toBe("halt");
    }
  });
});

import { atomicRequestedNotationSymbols, runP1Loop, type P1Env, type P1Finding, type P1LoopHooks } from "../src/presentation/p1_loop.js";

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

  it("splits combined reviewer symbols into atomic synthesis requests", async () => {
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\) and \(m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`K(x,z), L(x)`))
      .toEqual([String.raw`K(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n),m_2(h_n)\) and \(m_3(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`, String.raw`m_3(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(K(x,z),L(x)\), \(M(x)\)`))
      .toEqual([String.raw`K(x,z)`, String.raw`L(x)`, String.raw`M(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`m_1(h_n), \(m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\), m_2(h_n)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`K(x,z), \(L(x)\)`))
      .toEqual([String.raw`K(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\;,\;m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(K\;(x,z),L(x)\)`))
      .toEqual([String.raw`K\;(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(K\,(x,z),L(x)\)`))
      .toEqual([String.raw`K\,(x,z)`, String.raw`L(x)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h)\,,\,m_2(h)\)`))
      .toEqual([String.raw`m_1(h)`, String.raw`m_2(h)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(m_1(h_n)\;\text{and}\;m_2(h_n)\)`))
      .toEqual([String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]);
    expect(atomicRequestedNotationSymbols(String.raw`\(A\quad and\quad B\)`))
      .toEqual(["A", "B"]);
    expect(atomicRequestedNotationSymbols(String.raw`\(A\;and\;B\)`))
      .toEqual(["A", "B"]);
    expect(atomicRequestedNotationSymbols(String.raw`A; B`)).toEqual(["A", "B"]);
    expect(atomicRequestedNotationSymbols(String.raw`F_{A and B,C}, G(x)`))
      .toEqual([String.raw`F_{A and B,C}`, "G(x)"]);
    expect(atomicRequestedNotationSymbols(String.raw`K(A\quad and\quad B,z); L(x)`))
      .toEqual([String.raw`K(A\quad and\quad B,z)`, "L(x)"]);
    const calls: string[][] = [];
    const paired: P1Env = { id: "pair", env: "definitionv", statement: "pair",
      body: String.raw`\[m_1(h):=1,\quad m_2(h):=2\]`, refSet: [] };
    const r = await runP1Loop([env("t1")], hooks([
      [{ gate: "notation-reviewer", symbol: String.raw`\(m_1(h_n)\) and \(m_2(h_n)\)`, fixLocus: "synthesize-def", detail: "moments undefined" }],
      [],
    ], { synthesize: async (symbols) => { calls.push(symbols); return [paired]; } }));
    expect(calls).toEqual([[String.raw`m_1(h_n)`, String.raw`m_2(h_n)`]]);
    expect(r.ok).toBe(true);
    expect(r.envs.filter((e) => e.id === "pair")).toHaveLength(1);
  });

  it("persists separate atomic synthesis outputs through the next review round", async () => {
    const r = await runP1Loop([env("t1")], hooks([
      [
        { gate: "notation-reviewer", symbol: String.raw`m_1(h_n)`, fixLocus: "synthesize-def", detail: "first undefined" },
        { gate: "notation-reviewer", symbol: String.raw`m_2(h_n)`, fixLocus: "synthesize-def", detail: "second undefined" },
      ],
      [],
    ], { synthesize: async (symbols) => symbols.map((symbol, i) => ({
      id: `moment_${i}`, env: "definitionv", statement: symbol,
      body: `We define \\(${symbol}:=0\\).`, refSet: [],
    })) }));
    expect(r.ok).toBe(true);
    expect(r.envs.slice(0, 2).map((e) => e.id)).toEqual(["moment_0", "moment_1"]);
  });

  it("treats notation-unresolved (ledger-exhausted synthesis) as advisory — converges with a receipt", async () => {
    let synthCalled = false;
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "notation-unresolved", symbol: "\\mathcal H", detail: "synthesis already attempted once" }],
    ], { synthesize: async () => { synthCalled = true; return []; } }));
    expect(r.ok).toBe(true);
    expect(synthCalled).toBe(false);
    expect(r.advisories.some((f) => f.gate === "notation-unresolved")).toBe(true);
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

  it("fast-exits on a persistent identical finding instead of burning the iteration cap", async () => {
    const r = await runP1Loop([env("a1")], hooks([
      [{ gate: "lean-identifier", objId: "a1", detail: "persists" }],
    ]));
    expect(r.ok).toBe(false);
    // Round 1 flags it, the repair re-renders, round 2 sees the identical actionable
    // set and exits with the findings — re-paying rounds 3..cap cannot change anything.
    expect(r.iterations).toBe(2);
    expect(r.unresolved.map((f) => f.objId)).toEqual(["a1"]);
  });
});

// Mangled-word guard: the 2026-08-20 operator risk→u rename class.
import { lintClarity } from "../src/presentation/tex_anchors.js";
describe("lintClarity mangled-word guard", () => {
  const wrap = (body: string) =>
    `\\begin{theoremv}{thm:x}[T]\n${body}\n\\end{theoremv}`;
  it("flags a bare single-letter word in prose", () => {
    const hits = lintClarity(wrap("\\textbf{(ACE fixed-code u.)} If the law is nonempty, then \\(x\\ge0\\)."));
    expect(hits.some((p) => p.gate === "mangled-word" && p.detail.includes('"u"'))).toBe(true);
  });
  it("ignores articles, list markers, math, refs, and macros", () => {
    const hits = lintClarity(wrap(
      "A bound holds; I state it. (b) For a value \\(u\\) with $v>0$, see \\cref{obj:def:x}. The rate is 5\\% by \\emph{design}.",
    ));
    expect(hits.filter((p) => p.gate === "mangled-word")).toEqual([]);
  });
});

// Synth placement preference: the paper-order minimum section over ALL users of a
// synth's covered symbols — appendix only when every user is appendix-placed. The
// planner never sees synth envs, so this deterministic preference is what lets
// appendix-only synthesized apparatus actually reach the appendix.
import { preferredSectionsForSynths } from "../src/presentation/stages/p1_plan.js";
describe("preferredSectionsForSynths", () => {
  const outline = [
    "## section: Setup and assumptions", "brief", "objs: def:a, thm:b",
    "## section: Appendix proofs", "brief", "objs: lem:c, lem:d",
  ].join("\n");
  const envs = [
    { id: "def:a", body: "defines the class" },
    { id: "thm:b", body: "main theorem uses \\(w_k\\) here" },
    { id: "lem:c", body: "appendix lemma uses \\(z_j\\) and \\(w_k\\)" },
    { id: "lem:d", body: "appendix lemma uses \\(q_m\\)" },
  ];
  it("appendix-only users -> appendix; any main-body user pulls to the earlier section", () => {
    const m = preferredSectionsForSynths(outline, envs, new Map([
      ["synth_1", ["q_m"]],        // used only by lem:d (appendix)
      ["synth_2", ["w_k"]],        // used by thm:b (main) AND lem:c (appendix) -> main wins
      ["synth_3", ["z_j", "q_m"]], // both users in appendix
      ["synth_4", ["absent_sym"]], // no user -> no preference (setup default downstream)
    ]));
    expect(m.get("synth_1")).toBe("Appendix proofs");
    expect(m.get("synth_2")).toBe("Setup and assumptions");
    expect(m.get("synth_3")).toBe("Appendix proofs");
    expect(m.has("synth_4")).toBe(false);
  });
  it("drops the preference when ANOTHER synth env uses the symbol (mutual sections undetermined)", () => {
    const synthEnvs = [
      { id: "synth_9", body: "This synthesized body displays \\(q_m\\) too." },
      { id: "synth_1", body: "defines \\(q_m\\)" },
    ];
    const m = preferredSectionsForSynths(outline, envs, new Map([["synth_1", ["q_m"]]]), synthEnvs);
    expect(m.has("synth_1")).toBe(false);
  });
  it("routes an appendix-only synth into the appendix objs line before its user", () => {
    const layer = ["synth_1", "lem:d", "lem:c"];
    const pref = preferredSectionsForSynths(outline, envs, new Map([["synth_1", ["q_m"]]]));
    const placed = placeSynthesizedDefinitions(outline, ["synth_1"], pref, layer);
    const objsLines = placed.split("\n").filter((l) => l.startsWith("objs:"));
    expect(objsLines[1]).toContain("synth_1");
    expect(objsLines[1].indexOf("synth_1")).toBeLessThan(objsLines[1].indexOf("lem:d"));
    expect(objsLines[0]).not.toContain("synth_1");
  });
});
