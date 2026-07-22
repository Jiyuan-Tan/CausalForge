import { describe, it, expect } from "vitest";
import { loadBankEntry, graphCrosswalk } from "../src/presentation/bank.js";
import { acceptedBankEntry, causalSmithRoot } from "./helpers.js";
import type { FormalizationGraph, GraphNode } from "../src/graph/types.js";

const gnode = (id: string, kind: GraphNode["kind"], over: Partial<GraphNode> = {}): GraphNode => ({
  id, kind, provenance: "from-note",
  nl: { statement: `s ${id}`, tex_anchor: "", frozen: true },
  lean: { decl_name: `${id}_decl`, file: "F.lean" },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
  ...over,
});

describe("graphCrosswalk — cited gates", () => {
  it("emits a `cited` verdict (not `unmatched`) and a def decl_kind for a source-matched cited gate", () => {
    const g: FormalizationGraph = {
      qid: "q", specialization: "v1",
      nodes: [
        gnode("thm:main", "theorem"),
        gnode("lem:pub", "gate", { gate: { gate_class: "cited", source: "cite:bk-2022" } }),
        gnode("lem:pub-unver", "gate", {
          gate: { gate_class: "cited", source: "cite:x-2020" },
          review: { status: "unreviewed", passed_hash: null },
        }),
      ],
      edges: [],
    };
    const cw = graphCrosswalk(g);
    const main = cw.find((e) => e.obj_id === "thm:main")!;
    const cited = cw.find((e) => e.obj_id === "lem:pub")!;
    const unver = cw.find((e) => e.obj_id === "lem:pub-unver")!;
    expect(main.verdict).toBe("equivalent");
    expect(cited.verdict).toBe("cited");
    expect(cited.lean!.decl_kind).toBe("def");
    expect(unver.verdict).toBe("cited-unverified");
  });
});

describe("graphCrosswalk — undelivered remarks", () => {
  it("keeps the row visible but removes its Lean anchor and verified verdict", () => {
    const g: FormalizationGraph = {
      qid: "q", specialization: "v1", edges: [],
      nodes: [gnode("thm:secondary", "theorem", {
        delivery: { status: "undelivered", role: "secondary", reason: "citation overflow" },
      })],
    };
    expect(graphCrosswalk(g)[0]).toMatchObject({
      obj_id: "thm:secondary", lean: null, verdict: "unmatched",
    });
  });
});

describe("bank loader (integration)", () => {
  it("loads the current accepted bank entry with its graph", async () => {
    const { qid, spec } = acceptedBankEntry();
    const entry = await loadBankEntry(causalSmithRoot(), qid, spec);
    // Structural (not paper-specific) so this survives a bank re-curation: the loader must produce a
    // non-empty note, a Lean-anchored graph (the trust anchor), a derived crosswalk, and a leanSubdir.
    expect(entry.noteMd.length).toBeGreaterThan(0);
    expect(entry.graph.nodes.length).toBeGreaterThan(20);
    expect(entry.graph.nodes.some((n) => n.lean?.decl_name)).toBe(true);
    expect(entry.graph.edges.length).toBeGreaterThan(0);
    expect(entry.crosswalk.length).toBeGreaterThan(0);
    expect(entry.leanSubdir.length).toBeGreaterThan(0);
    expect(entry.readme.qid).toBe(qid);
    expect(Array.isArray(entry.sourceBibliography)).toBe(true);
    // At least one of the discovery .tex artifacts (proposal / derivation) is present.
    expect(entry.proposalTex ?? entry.derivationTex).toContain("\\");
  });

  it("throws a useful error for a missing entry", async () => {
    await expect(loadBankEntry(causalSmithRoot(), "no_such_qid", "v9")).rejects.toThrow(
      /missing note\/state/,
    );
  });
});
