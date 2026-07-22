import { describe, it, expect } from "vitest";
import {
  indexBib,
  reconcileCite,
  assumptionCiteContext,
  escapeBibText,
  injectionEntry,
  citedStdFromNode,
} from "../src/presentation/assumption_citations.js";
import type { FormalizationGraph, GraphNode } from "../src/graph/types.js";

const BIB = `
@article{Chernozhukov2018,
  author = {Chernozhukov, Victor and Chetverikov, Denis and Demirer, Mert},
  title = {Double/debiased machine learning},
  year = {2018},
  journal = {Econometrics Journal}
}
@article{Athey2021,
  author = {Athey, Susan and Wager, Stefan},
  year = {2021}
}
@article{Audibert2007,
  author = {Audibert, Jean-Yves and Tsybakov, Alexandre B.},
  year = {2007}
}
`;

describe("indexBib", () => {
  it("parses key, author, year per entry", () => {
    const idx = indexBib(BIB);
    expect(idx.map((b) => b.key)).toEqual(["Chernozhukov2018", "Athey2021", "Audibert2007"]);
    expect(idx[0].year).toBe("2018");
    expect(idx[0].author).toContain("Chernozhukov");
  });
});

describe("reconcileCite", () => {
  const idx = indexBib(BIB);
  it("matches a discovery cite to the paper key by surname + exact year", () => {
    const r = reconcileCite(
      { name: "DML", cite: "ChernozhukovEtAl2018DML", citation: "Chernozhukov, V., et al. (2018). Double/debiased ML. Econ. J." },
      idx,
    );
    expect(r).toEqual({ citeKey: "Chernozhukov2018", inject: null });
  });
  it("injects a new entry when no paper match (right author, absent year)", () => {
    const r = reconcileCite(
      { name: "Tsybakov margin", cite: "Tsybakov2004OptimalAggregation", citation: "Tsybakov, A. B. (2004). Optimal aggregation. Ann. Statist." },
      idx,
    );
    expect(r.citeKey).toBe("Tsybakov2004OptimalAggregation");
    expect(r.inject).toContain("@misc{Tsybakov2004OptimalAggregation");
    expect(r.inject).toContain("year = {2004}");
    expect(r.inject).toContain("author = {Tsybakov}");
  });
  it("does NOT match on surname alone when the year differs (no false positive)", () => {
    // Tsybakov is in Audibert2007's author list, but year 2004 ≠ 2007 → inject, not mismatch.
    const r = reconcileCite(
      { name: "x", cite: "Tsybakov2004", citation: "Tsybakov, A. B. (2004). foo." },
      idx,
    );
    expect(r.inject).not.toBeNull();
  });
  it("uses the discovery key directly when it already IS a paper key", () => {
    const r = reconcileCite({ name: "x", cite: "Athey2021", citation: "Athey 2021" }, idx);
    expect(r).toEqual({ citeKey: "Athey2021", inject: null });
  });
  it("matches a cite slug to the same normalized BibTeX key despite version-year metadata", () => {
    const zeng = indexBib(`
@article{ZengBalakrishnanHanKennedy2024,
  author = {Zeng, Zhenghao and Balakrishnan, Sivaraman and Han, Yanjun and Kennedy, Edward H.},
  year = {2026},
  note = {Version 3}
}`);
    const r = reconcileCite(
      {
        name: "cited external result",
        cite: "zeng-balakrishnan-han-kennedy-2024",
        citation: "Zeng (2024)",
      },
      zeng,
    );
    expect(r).toEqual({ citeKey: "ZengBalakrishnanHanKennedy2024", inject: null });
  });
});

describe("injectionEntry", () => {
  it("extracts author, year, title from the citation", () => {
    const e = injectionEntry("K", "Bartlett, P. L., Bousquet, O., and Mendelson, S. (2005). Local Rademacher complexities. Ann. Statist.");
    expect(e).toContain("author = {Bartlett}");
    expect(e).toContain("year = {2005}");
    expect(e).toContain("title = {Local Rademacher complexities}");
  });
});

describe("escapeBibText / injectionEntry (TeX-safe injected bib entries)", () => {
  it("escapes ampersands, percent, underscore and hash", () => {
    expect(escapeBibText("Annals of Statistics & Probability, 50% draft, v_2 #1"))
      .toBe("Annals of Statistics \\& Probability, 50\\% draft, v\\_2 \\#1");
  });
  it("escapes backslash first (no double-escaping)", () => {
    expect(escapeBibText("a\\b & c")).toBe("a\\textbackslash{}b \\& c");
  });
  it("injectionEntry produces TeX-safe note/title fields", () => {
    const entry = injectionEntry("smith-2021", "Smith, J. (2021). Learning & testing rates_v2. Journal of X.");
    expect(entry).toContain("Learning \\& testing rates\\_v2");
    expect(entry).not.toMatch(/[^\\]&/);
  });
});

const node = (id: string, kind: GraphNode["kind"], standard?: GraphNode["standard"]): GraphNode => ({
  id, obj_id: id.toUpperCase(), kind, provenance: "from-note",
  nl: { statement: `s ${id}`, tex_anchor: "", frozen: true },
  lean: { decl_name: null, file: null },
  review: { status: "matched", passed_hash: null },
  proof: { state: "complete", sorry_count: 0 },
  ...(standard ? { standard } : {}),
});

describe("assumptionCiteContext", () => {
  const graph: FormalizationGraph = {
    qid: "q", specialization: "v1",
    nodes: [
      node("ass:margin", "assumption", { name: "Tsybakov decision margin", cite: "Tsybakov2004OptimalAggregation", citation: "Tsybakov, A. B. (2004). Optimal aggregation. Ann. Statist." }),
      node("ass:overlap-decay", "assumption"), // novel — no standard
      node("ass:dml", "assumption", { name: "cross-fit L2 nuisance rates", cite: "ChernozhukovEtAl2018DML", citation: "Chernozhukov, V., et al. (2018). DML. Econ. J." }),
      node("def:foo", "definition"),
      node("thm:main", "theorem"),
    ],
    edges: [],
  };

  it("emits a citable note + extra key for STANDARD assumptions and a no-cite note for NOVEL ones", () => {
    const ctx = assumptionCiteContext(graph, ["ass:margin", "ass:overlap-decay", "ass:dml", "def:foo", "thm:main"], BIB);
    expect(ctx.notes).toContain("STANDARD — the Tsybakov decision margin condition; cite it with \\citep{Tsybakov2004OptimalAggregation}");
    expect(ctx.notes).toContain("\\citep{Chernozhukov2018}"); // reconciled to the paper key
    expect(ctx.notes).toContain("ass:overlap-decay");
    expect(ctx.notes).toContain("NOVEL — specific to this analysis");
    // non-assumption objs ignored
    expect(ctx.notes).not.toContain("def:foo");
    expect(ctx.notes).not.toContain("thm:main");
    // Chernozhukov reconciled (no inject); Tsybakov injected.
    expect(ctx.extraKeys.sort()).toEqual(["Chernozhukov2018", "Tsybakov2004OptimalAggregation"]);
    expect(ctx.injections).toHaveLength(1);
    expect(ctx.injections[0]).toContain("Tsybakov2004OptimalAggregation");
  });
});

describe("citedStdFromNode", () => {
  const citedNode = (source: string | undefined): GraphNode => ({
    id: "lem:published-upper-bound-cited", obj_id: "L-17", kind: "gate", provenance: "from-note",
    nl: { statement: "Cited comparator (Bonvini-Kennedy 2022). R_n <= C rho_n.", tex_anchor: "", frozen: true },
    lean: { decl_name: "publishedUpperBoundCited", file: "Helpers/UpperBoundCited.lean" },
    review: { status: "matched", passed_hash: null },
    proof: { state: "complete", sorry_count: 0 },
    ...(source ? { gate: { gate_class: "cited", source } } : {}),
  });

  it("derives surname + year from the cite: slug for reconcile matching", () => {
    const std = citedStdFromNode(citedNode("cite:bonvini-kennedy-2022"));
    expect(std).toEqual({ name: "cited external result", cite: "bonvini-kennedy-2022", citation: "Bonvini (2022)" });
  });
  it("returns null when the gate carries no source", () => {
    expect(citedStdFromNode(citedNode(undefined))).toBeNull();
  });
});

describe("assumptionCiteContext — cited nodes", () => {
  const BK_BIB = `
@article{BonviniKennedy2022,
  author = {Bonvini, Marco and Kennedy, Edward H.},
  title = {Fast convergence rates for dose-response estimation},
  year = {2022}
}
`;
  const graph: FormalizationGraph = {
    qid: "q", specialization: "v1",
    nodes: [{
      id: "lem:published-upper-bound-cited", obj_id: "L-17", kind: "gate", provenance: "from-note",
      nl: { statement: "Cited comparator.", tex_anchor: "", frozen: true },
      lean: { decl_name: "publishedUpperBoundCited", file: "F.lean" },
      review: { status: "matched", passed_hash: null },
      proof: { state: "complete", sorry_count: 0 },
      gate: { gate_class: "cited", source: "cite:bonvini-kennedy-2022" },
    }],
    edges: [],
  };

  it("attributes a cited node via reconcile (no injection when the source is in the bib)", () => {
    const ctx = assumptionCiteContext(graph, ["lem:published-upper-bound-cited"], BK_BIB);
    expect(ctx.notes).toContain("IMPORTED external result");
    expect(ctx.notes).toContain("\\citep{BonviniKennedy2022}"); // reconciled to the paper key
    expect(ctx.notes).toContain("never present it as a contribution of this paper");
    expect(ctx.extraKeys).toEqual(["BonviniKennedy2022"]);
    expect(ctx.injections).toHaveLength(0);
  });

  it("injects a stub when the cited source is not in the bib (so \\citep still resolves)", () => {
    const ctx = assumptionCiteContext(graph, ["lem:published-upper-bound-cited"], "");
    expect(ctx.extraKeys).toEqual(["bonvini-kennedy-2022"]);
    expect(ctx.injections).toHaveLength(1);
    expect(ctx.injections[0]).toContain("bonvini-kennedy-2022");
  });
});
