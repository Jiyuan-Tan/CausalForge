import { describe, it, expect } from "vitest";
import {
  buildPaperGraph,
  lintIsolatedLemmas,
  paperGraphNodesFromTex,
  parseProofCitations,
  type PaperGraphNode,
} from "../src/presentation/paper_graph.js";

const env = (kind: string, id: string, title: string) =>
  `\\begin{${kind}}{${id}}[${title}]\nBody of ${id}.\n\\end{${kind}}`;

const proof = (id: string, body: string) =>
  `\\begin{proof}[Proof of \\cref{obj:${id}}]\n${body}\n\\end{proof}`;

/** Theorem 1 proved from Lemma 1 + Lemma 2; Lemma 2 proved from Lemma 1. */
const PAPER = [
  env("theoremv", "thm:main", "Main"),
  env("lemmav", "lem:a", "First"),
  env("lemmav", "lem:b", "Second"),
  proof("lem:b", "Apply \\cref{obj:lem:a} to the first term."),
  proof("thm:main", "Combine \\cref{obj:lem:a,obj:lem:b} and conclude."),
].join("\n\n");

describe("proof-citation parser", () => {
  it("attributes each cref to the proof whose head names it, and reads comma-lists", () => {
    expect(parseProofCitations(PAPER)).toEqual([
      { objId: "lem:b", targets: ["lem:a"] },
      { objId: "thm:main", targets: ["lem:a", "lem:b"] },
    ]);
  });

  it("ignores the head's own cref, \\Cref case, and references outside any proof", () => {
    const tex = [
      "As \\cref{obj:lem:a} shows, the setup is standard.",
      proof("thm:main", "\\Cref{obj:lem:a} gives the bound."),
    ].join("\n\n");
    expect(parseProofCitations(tex)).toEqual([{ objId: "thm:main", targets: ["lem:a"] }]);
  });

  it("skips a proof with no `[Proof of \\cref{obj:X}]` head — it contributes no edges", () => {
    const tex = "\\begin{proof}\nBy \\cref{obj:lem:a}, done.\n\\end{proof}";
    expect(parseProofCitations(tex)).toEqual([]);
    expect(parseProofCitations("\\begin{proof}[Sketch]\nBy \\cref{obj:lem:a}.\n\\end{proof}")).toEqual([]);
  });

  it("attributes a nested claim-proof's references to the enclosing headed proof", () => {
    const tex = [
      "\\begin{proof}[Proof of \\cref{obj:thm:main}]",
      "\\begin{proof}[Proof of Claim 1]",
      "By \\cref{obj:lem:a}.",
      "\\end{proof}",
      "Finally \\cref{obj:lem:b}.",
      "\\end{proof}",
    ].join("\n");
    expect(parseProofCitations(tex)).toEqual([{ objId: "thm:main", targets: ["lem:a", "lem:b"] }]);
  });

  it("does not count a commented-out reference", () => {
    const tex = proof("thm:main", "Step one. % lean: uses \\cref{obj:lem:a}\nThen \\cref{obj:lem:b}.");
    expect(parseProofCitations(tex)).toEqual([{ objId: "thm:main", targets: ["lem:b"] }]);
  });
});

describe("paper graph", () => {
  it("emits result nodes with paper labels and deduped, self-edge-free proof-cites edges", () => {
    const nodes = paperGraphNodesFromTex(PAPER);
    expect(nodes).toEqual([
      { obj_id: "thm:main", env: "theoremv", paper_label: "Theorem 1", title: "Main" },
      { obj_id: "lem:a", env: "lemmav", paper_label: "Lemma 1", title: "First" },
      { obj_id: "lem:b", env: "lemmav", paper_label: "Lemma 2", title: "Second" },
    ]);
    const graph = buildPaperGraph({ tex: PAPER, nodes, commit: "abc123" });
    expect(graph.commit).toBe("abc123");
    expect(graph.edges).toEqual([
      { from: "lem:b", to: "lem:a", kind: "proof-cites" },
      { from: "thm:main", to: "lem:a", kind: "proof-cites" },
      { from: "thm:main", to: "lem:b", kind: "proof-cites" },
    ]);
  });

  it("drops self-citations, repeated citations, and targets that are not result envs", () => {
    const tex = [
      env("theoremv", "thm:main", "Main"),
      env("lemmav", "lem:a", "First"),
      env("assumptionv", "ass:overlap", "Overlap"),
      proof(
        "thm:main",
        "Under \\cref{obj:ass:overlap} and \\cref{obj:thm:main} itself, \\cref{obj:lem:a} applies; \\cref{obj:lem:a} again.",
      ),
    ].join("\n\n");
    const graph = buildPaperGraph({ tex, nodes: paperGraphNodesFromTex(tex), commit: "c" });
    expect(graph.nodes.map((n) => n.obj_id)).toEqual(["thm:main", "lem:a"]);
    expect(graph.edges).toEqual([{ from: "thm:main", to: "lem:a", kind: "proof-cites" }]);
  });

  it("accepts crosswalk-shaped nodes and keeps only theorem/lemma/proposition entries", () => {
    const nodes: PaperGraphNode[] = [
      { obj_id: "thm:main", env: "theoremv", paper_label: "Theorem 1", title: "Main" },
      { obj_id: "lem:a", env: "lemmav", paper_label: "Lemma 1", title: "First" },
      { obj_id: "aux:helper", env: "auxiliary", paper_label: "Auxiliary 1", title: null },
    ];
    const tex = proof("thm:main", "By \\cref{obj:lem:a} and \\cref{obj:aux:helper}.");
    const graph = buildPaperGraph({ tex, nodes, commit: "c" });
    expect(graph.nodes.map((n) => n.obj_id)).toEqual(["thm:main", "lem:a"]);
    expect(graph.edges).toEqual([{ from: "thm:main", to: "lem:a", kind: "proof-cites" }]);
  });
});

describe("isolated-lemma gate", () => {
  it("passes a paper in which every lemma is cited by some proof", () => {
    expect(lintIsolatedLemmas(PAPER)).toEqual([]);
  });

  it("fails a lemma no proof cites, naming its paper label and obj_id", () => {
    const tex = [PAPER, env("lemmav", "lem:dead", "Unused")].join("\n\n");
    const problems = lintIsolatedLemmas(tex);
    expect(problems).toHaveLength(1);
    expect(problems[0].gate).toBe("isolated-lemma");
    expect(problems[0].objId).toBe("lem:dead");
    expect(problems[0].detail).toContain("Lemma 3 (lem:dead)");
    expect(problems[0].detail).toContain("cited by no proof");
    expect(problems[0].detail).toContain("\\cref{obj:lem:dead}");
    expect(problems[0].detail).toContain("should be cut");
  });

  it("does not count a mention in section prose as a proof citation", () => {
    const tex = [PAPER, env("lemmav", "lem:dead", "Unused"), "See \\cref{obj:lem:dead} for context."].join("\n\n");
    expect(lintIsolatedLemmas(tex).map((p) => p.objId)).toEqual(["lem:dead"]);
  });

  it("exempts standalone theorems and propositions", () => {
    const tex = [
      env("theoremv", "thm:standalone", "Alone"),
      env("propositionv", "prop:standalone", "Also alone"),
      env("lemmav", "lem:a", "First"),
      proof("thm:standalone", "Direct from \\cref{obj:lem:a}."),
      proof("prop:standalone", "Direct from \\cref{obj:lem:a}."),
    ].join("\n\n");
    expect(lintIsolatedLemmas(tex)).toEqual([]);
  });
});
