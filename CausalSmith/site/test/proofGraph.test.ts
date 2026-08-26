// The Proof map's pure layer: what a bundle's `paper_graph.json` is allowed to
// be, and the layered layout built from it.
//
// The realistic fixture in `fixtures/proof_graph/` was derived from the
// discrete-ATE paper's own `paper.tex` — every `\begin{proof}[Proof of
// \cref{obj:X}]` block's `\cref{obj:Y}` references, for Y a theorem /
// proposition / lemma in that bundle's crosswalk — so the shapes here are the
// shapes the emitter will produce.

import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import {
  buildProofGraph,
  graphSummary,
  parsePaperGraph,
  reconcilePaperGraph,
  shortLabel,
  type PaperGraph,
} from "../src/lib/proofGraph.js";

const REAL = JSON.parse(
  readFileSync(
    resolve(
      import.meta.dirname,
      "..",
      "fixtures",
      "proof_graph",
      "stat_discrete_ate_minimax_loggap_polynomial_upper_match.json",
    ),
    "utf8",
  ),
) as unknown;

/** A tiny hand-built graph: T1's proof cites L2, whose proof cites L1. */
function chain(): PaperGraph {
  return {
    commit: "abc1234",
    nodes: [
      { obj_id: "thm:main", env: "theoremv", paper_label: "Theorem 1", title: "Main result" },
      { obj_id: "lem:mid", env: "lemmav", paper_label: "Lemma 2", title: "Middle step" },
      { obj_id: "lem:base", env: "lemmav", paper_label: "Lemma 1", title: null },
    ],
    edges: [
      { from: "thm:main", to: "lem:mid", kind: "proof-cites" },
      { from: "lem:mid", to: "lem:base", kind: "proof-cites" },
    ],
  };
}

describe("parsePaperGraph", () => {
  it("accepts the emitted contract", () => {
    const g = parsePaperGraph(REAL)!;
    expect(g.commit).toMatch(/^[0-9a-f]{7,40}$/);
    expect(g.nodes).toHaveLength(24);
    expect(g.edges).toHaveLength(24);
    expect(g.nodes.filter((n) => n.env === "theoremv")).toHaveLength(2);
    expect(g.nodes.filter((n) => n.env === "propositionv")).toHaveLength(1);
    expect(g.edges.every((e) => e.kind === "proof-cites")).toBe(true);
  });

  it("rejects payloads it cannot use at all", () => {
    expect(parsePaperGraph(null)).toBeNull();
    expect(parsePaperGraph("nodes")).toBeNull();
    expect(parsePaperGraph([])).toBeNull();
    expect(parsePaperGraph({})).toBeNull();
    expect(parsePaperGraph({ nodes: [] })).toBeNull();
    expect(parsePaperGraph({ nodes: [{ env: "lemmav" }] })).toBeNull(); // no obj_id
  });

  it("repairs salvageable defects instead of losing the panel", () => {
    const g = parsePaperGraph({
      nodes: [
        { obj_id: "a", env: "theoremv", paper_label: "Theorem 1", title: "A" },
        { obj_id: "a", env: "lemmav", paper_label: "Lemma 9", title: "dup" }, // duplicate id
        { obj_id: "b" }, // missing fields → defaulted
        "junk",
      ],
      edges: [
        { from: "a", to: "b", kind: "proof-cites" },
        { from: "a", to: "b", kind: "proof-cites" }, // duplicate
        { from: "a", to: "a", kind: "proof-cites" }, // self-edge
        { from: "a", to: "ghost", kind: "proof-cites" }, // unknown endpoint
        { from: "a" }, // no target
        null,
      ],
    })!;
    expect(g.nodes.map((n) => n.obj_id)).toEqual(["a", "b"]);
    expect(g.nodes[1]).toMatchObject({ env: "lemmav", paper_label: "b", title: null });
    expect(g.edges).toEqual([{ from: "a", to: "b", kind: "proof-cites" }]);
    expect(g.commit).toBe("");
  });
});

describe("shortLabel", () => {
  it("compacts the paper's own numbering", () => {
    expect(shortLabel("Lemma 16", "lem:x")).toBe("L16");
    expect(shortLabel("Theorem 1", "thm:x")).toBe("T1");
    expect(shortLabel("Proposition 1", "prop:x")).toBe("P1");
    expect(shortLabel("Corollary 2.3", "cor:x")).toBe("C2.3");
  });

  it("degrades rather than throwing on an unnumbered label", () => {
    expect(shortLabel("Main theorem", "thm:x")).toBe("Main t");
    expect(shortLabel("", "lem:sandwich")).toBe("ndwich");
  });
});

describe("buildProofGraph", () => {
  it("ranks a chain bottom-up and keeps the theorem on top", () => {
    const l = buildProofGraph(chain());
    const rank = new Map(l.nodes.map((n) => [n.id, n.rank]));
    expect(rank.get("lem:base")).toBe(0);
    expect(rank.get("lem:mid")).toBe(1);
    expect(rank.get("thm:main")).toBe(2);
    expect(l.rows).toEqual([["lem:base"], ["lem:mid"], ["thm:main"]]);
    // Lines are drawn top-first, so the headline result comes first.
    expect(l.lines).toEqual([["thm:main"], ["lem:mid"], ["lem:base"]]);
    // Rank 0 sits at the BOTTOM of the drawing.
    const y = new Map(l.nodes.map((n) => [n.id, n.y]));
    expect(y.get("lem:base")!).toBeGreaterThan(y.get("thm:main")!);
  });

  it("records both directions of every edge on the node", () => {
    const l = buildProofGraph(chain());
    const mid = l.nodes.find((n) => n.id === "lem:mid")!;
    expect(mid.cites).toEqual(["lem:base"]);
    expect(mid.citedBy).toEqual(["thm:main"]);
    expect(l.edges).toHaveLength(2);
    expect(l.edges[0].d).toMatch(/^M[\d.]+,[\d.]+ C/);
  });

  it("lifts every theorem and proposition to the top row", () => {
    const g = parsePaperGraph(REAL)!;
    const l = buildProofGraph(g);
    const top = l.rows[l.rows.length - 1];
    for (const n of l.nodes) {
      if (n.env === "theoremv" || n.env === "propositionv") {
        expect(top).toContain(n.id);
        expect(n.top).toBe(true);
      }
    }
    expect(l.nodes).toHaveLength(24);
    expect(l.rows.flat()).toHaveLength(24); // every node lands in exactly one row
  });

  it("places a result above every result its proof cites", () => {
    const g = parsePaperGraph(REAL)!;
    const l = buildProofGraph(g);
    const rank = new Map(l.nodes.map((n) => [n.id, n.rank]));
    for (const e of g.edges) {
      expect(rank.get(e.from)!).toBeGreaterThan(rank.get(e.to)!);
    }
  });

  it("fits the rail: nothing overflows the width, nothing overlaps on a line", () => {
    const l = buildProofGraph(parsePaperGraph(REAL)!);
    expect(l.width).toBeLessThanOrEqual(240); // the side rail is 230px
    for (const n of l.nodes) {
      expect(n.x - n.w / 2).toBeGreaterThanOrEqual(0);
      expect(n.x + n.w / 2).toBeLessThanOrEqual(l.width);
      expect(n.y).toBeGreaterThan(0);
      expect(n.y).toBeLessThan(l.height);
    }
    for (const line of l.lines) {
      const xs = line
        .map((id) => l.nodes.find((n) => n.id === id)!)
        .sort((a, b) => a.x - b.x);
      for (let i = 1; i < xs.length; i++) {
        expect(xs[i].x - xs[i].w / 2).toBeGreaterThanOrEqual(xs[i - 1].x + xs[i - 1].w / 2 - 1);
      }
    }
    // Every node is drawn exactly once, on exactly one line.
    expect(l.lines.flat().sort()).toEqual(l.nodes.map((n) => n.id).sort());
  });

  it("wraps a rank too wide for the rail onto several lines, deepest at the bottom", () => {
    const l = buildProofGraph(parsePaperGraph(REAL)!);
    // The fixture's base rank holds 14 results — far more than 226px of chips.
    expect(l.rows[0].length).toBeGreaterThan(6);
    expect(l.lines.length).toBeGreaterThan(l.rows.length);
    const yOf = (id: string) => l.nodes.find((n) => n.id === id)!.y;
    const topY = Math.min(...l.nodes.filter((n) => n.top).map((n) => yOf(n.id)));
    const restY = Math.min(...l.nodes.filter((n) => !n.top).map((n) => yOf(n.id)));
    expect(topY).toBeLessThan(restY); // results above everything they rest on
  });

  it("honours a wider container when one is given", () => {
    const wide = buildProofGraph(parsePaperGraph(REAL)!, { maxWidth: 700 });
    const rail = buildProofGraph(parsePaperGraph(REAL)!);
    expect(wide.width).toBeGreaterThan(rail.width);
    expect(wide.lines.length).toBeLessThan(rail.lines.length); // fewer wraps
    expect(wide.height).toBeLessThan(rail.height);
  });

  it("survives a citation cycle rather than hanging the build", () => {
    const g: PaperGraph = {
      commit: "x",
      nodes: [
        { obj_id: "a", env: "lemmav", paper_label: "Lemma 1", title: null },
        { obj_id: "b", env: "lemmav", paper_label: "Lemma 2", title: null },
      ],
      edges: [
        { from: "a", to: "b", kind: "proof-cites" },
        { from: "b", to: "a", kind: "proof-cites" },
      ],
    };
    const l = buildProofGraph(g);
    expect(l.nodes).toHaveLength(2);
    expect(l.rows.flat().sort()).toEqual(["a", "b"]);
  });

  it("handles a lone node and a paper with no citation edges", () => {
    const g = parsePaperGraph({
      nodes: [{ obj_id: "solo", env: "theoremv", paper_label: "Theorem 1", title: "T" }],
    })!;
    const l = buildProofGraph(g);
    expect(l.rows).toEqual([["solo"]]);
    expect(l.edges).toEqual([]);
    expect(l.width).toBeGreaterThan(0);
    expect(l.height).toBeGreaterThan(0);
    expect(graphSummary(g)).toBe("1 statement · 0 edges");
  });
});

describe("reconcilePaperGraph", () => {
  const graph = parsePaperGraph({
    commit: "stale",
    nodes: [
      { obj_id: "thm:main", env: "theoremv", paper_label: "Theorem 1", title: "Old title" },
      { obj_id: "lem:a", env: "lemmav", paper_label: "Lemma 15", title: null },
      { obj_id: "lem:gone", env: "lemmav", paper_label: "Lemma 10", title: "Cut from the paper" },
    ],
    edges: [
      { from: "thm:main", to: "lem:a", kind: "proof-cites" },
      { from: "thm:main", to: "lem:gone", kind: "proof-cites" },
    ],
  })!;
  const entries = [
    { obj_id: "thm:main", paper_label: "Theorem 1", title: "Main result" },
    { obj_id: "lem:a", paper_label: "Lemma 16", title: "Heavy-cell rate" },
  ];
  const body = '<div data-objid="thm:main"></div><div data-objid="lem:a"></div>';

  // The bug this exists for: a bundle read mid-rewrite pairs a stale graph with
  // a renumbered body, and the map then labels a chip "Lemma 15" while the block
  // it jumps to reads "Lemma 16".
  it("takes labels and titles from the body's own record, not the graph's copy", () => {
    const g = reconcilePaperGraph(graph, entries, body)!;
    const byId = new Map(g.nodes.map((n) => [n.obj_id, n]));
    expect(byId.get("lem:a")!.paper_label).toBe("Lemma 16");
    expect(byId.get("lem:a")!.title).toBe("Heavy-cell rate");
    expect(byId.get("thm:main")!.title).toBe("Main result");
    expect(shortLabel(byId.get("lem:a")!.paper_label, "lem:a")).toBe("L16");
  });

  it("drops a node the paper no longer anchors, and the edges into it", () => {
    const g = reconcilePaperGraph(graph, entries, body)!;
    expect(g.nodes.map((n) => n.obj_id)).toEqual(["thm:main", "lem:a"]);
    expect(g.edges).toEqual([{ from: "thm:main", to: "lem:a", kind: "proof-cites" }]);
  });

  it("drops a node with a crosswalk entry but no block to jump to", () => {
    const g = reconcilePaperGraph(graph, entries, '<div data-objid="thm:main"></div>')!;
    expect(g.nodes.map((n) => n.obj_id)).toEqual(["thm:main"]);
    expect(g.edges).toEqual([]);
  });

  it("returns null when nothing survives, so the panel is simply absent", () => {
    expect(reconcilePaperGraph(graph, [], body)).toBeNull();
    expect(reconcilePaperGraph(graph, entries, "")).toBeNull();
  });
});
