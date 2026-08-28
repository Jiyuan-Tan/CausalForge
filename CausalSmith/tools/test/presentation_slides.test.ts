import { describe, expect, it } from "vitest";
import { lintSlides, parseSlidesMd } from "../src/presentation/slides.js";
import { bibSummary, extractDeckMarkdown, extractDsl } from "../src/presentation/stages/p6_slides.js";
import { parseFigureDsl, renderFigureSvg } from "../src/presentation/figure_layout.js";

const BLOCKS = [
  { obj_id: "ass:design", kind: "assumption" },
  { obj_id: "thm:main", kind: "theorem" },
  { obj_id: "thm:lower", kind: "theorem" },
];

const filler = Array.from({ length: 6 }, (_, i) => `## Filler ${i + 1}\n- a point`).join("\n\n---\n\n");

function deck(body: string): string {
  return `# A Talk\nOne-line pitch.\n\n---\n\n${body}\n\n---\n\n${filler}`;
}

describe("parseSlidesMd", () => {
  it("splits slides and types directive blocks", () => {
    const doc = parseSlidesMd(deck(
      "## Main result\n@informal thm:main: Plain headline.\nSome prose.\n@formal obj:thm:lower",
    ));
    expect(doc.talkTitle).toBe("A Talk");
    const main = doc.slides[1];
    expect(main.title).toBe("Main result");
    expect(main.blocks).toEqual([
      { kind: "informal", objId: "thm:main", text: "Plain headline." },
      { kind: "prose", md: "Some prose." },
      { kind: "formal", objId: "thm:lower" }, // obj: prefix normalized away
    ]);
  });

  it("rejects a deck without a title slide and slides without headings", () => {
    expect(() => parseSlidesMd("## no title\nx")).toThrow(/# <talk title>/);
    expect(() => parseSlidesMd("# T\n\n---\n\nno heading here")).toThrow(/slide 2/);
  });
});

describe("lintSlides", () => {
  it("passes a well-formed deck", () => {
    const doc = parseSlidesMd(deck("## Results\n@formal thm:main\n@informal thm:lower: Lower bound in words."));
    expect(lintSlides(doc, BLOCKS)).toEqual([]);
  });

  it("flags unknown obj_ids, dropped theorems, non-verbatim displays, and empty headlines", () => {
    const doc = parseSlidesMd(deck(
      "## Results\n@formal thm:nope\n@informal thm:main:\nAnd \\[x=1\\] inline-displayed.",
    ));
    const gates = lintSlides(doc, BLOCKS).map((p) => p.gate).sort();
    expect(gates).toEqual([
      "slides-display-not-verbatim", // \[x=1\] is not copied from the paper
      "slides-empty-informal",
      "slides-missing-theorem", // thm:lower never appears
      "slides-unknown-obj",
    ]);
  });

  it("allows a \\[…\\] display only when copied verbatim from the corpus", () => {
    const doc = parseSlidesMd(deck(
      "## Results\n@informal thm:main: Words.\n@informal thm:lower: Words.\nThe rate is \\[ n^{-1} \\log d \\] here.",
    ));
    expect(lintSlides(doc, BLOCKS, "we show risk \\(n^{-1}\\log d\\) for…").map((p) => p.gate)).toEqual([]);
    expect(lintSlides(doc, BLOCKS, "unrelated text").map((p) => p.gate)).toEqual(["slides-display-not-verbatim"]);
    const composed = parseSlidesMd(deck("## Results\n@informal thm:main: W.\n@informal thm:lower: W.\n$$x$$"));
    expect(lintSlides(composed, BLOCKS, "$$x$$").map((p) => p.gate)).toEqual(["slides-displayed-math"]);
    // Substring laundering: a prose fragment inside \[…\] is not a formula even
    // when the corpus contains it, and an unmatched \[ is malformed.
    const laundered = parseSlidesMd(deck(
      "## Results\n@informal thm:main: W.\n@informal thm:lower: W.\nSo \\[the\\] rate.",
    ));
    expect(lintSlides(laundered, BLOCKS, "we show the rate").map((p) => p.gate)).toEqual([
      "slides-display-not-verbatim",
    ]);
    const unmatched = parseSlidesMd(deck(
      "## Results\n@informal thm:main: W.\n@informal thm:lower: W.\nSo \\[ x=1 dangling.",
    ));
    expect(lintSlides(unmatched, BLOCKS, "x=1").map((p) => p.gate)).toEqual(["slides-displayed-math"]);
  });

  it("flags a bare @formal slide and third-person 'the paper' voice", () => {
    const bare = parseSlidesMd(deck("## Main result\n@formal thm:main\n\n---\n\n## B\n@informal thm:lower: W."));
    expect(lintSlides(bare, BLOCKS).map((p) => p.gate)).toEqual(["slides-bare-formal"]);
    const voiced = parseSlidesMd(deck(
      "## Main result\nThe paper establishes a bound.\n@formal thm:main\n@informal thm:lower: W.",
    ));
    expect(lintSlides(voiced, BLOCKS).map((p) => p.gate)).toEqual(["slides-voice"]);
  });

  it("waives coverage for a predecessor theorem whose extension is covered, not the reverse", () => {
    const blocks = [
      { obj_id: "thm:main", kind: "theorem" },
      { obj_id: "thm:main-all-d", kind: "theorem" },
    ];
    const extOnly = parseSlidesMd(deck("## Results\nIn words.\n@formal thm:main-all-d"));
    expect(lintSlides(extOnly, blocks)).toEqual([]); // thm:main subsumed by thm:main-all-d
    const restrictedOnly = parseSlidesMd(deck("## Results\nIn words.\n@formal thm:main"));
    expect(lintSlides(restrictedOnly, blocks).map((p) => p.objId)).toContain("thm:main-all-d");
  });

  it("flags a deck too short for a 15–20 minute talk", () => {
    const doc = parseSlidesMd("# T\npitch\n\n---\n\n## Only\n@formal thm:main\n@formal thm:lower");
    expect(lintSlides(doc, BLOCKS).map((p) => p.gate)).toContain("slides-deck-shape");
  });
});

describe("figures", () => {
  it("parses @figure and lints name/caption/count", () => {
    const doc = parseSlidesMd(deck(
      "## Results\nIn words.\n@formal thm:main\n@formal thm:lower\n@figure regime-map: Which term dominates where.",
    ));
    expect(doc.slides[1].blocks).toContainEqual({
      kind: "figure",
      name: "regime-map",
      caption: "Which term dominates where.",
    });
    expect(lintSlides(doc, BLOCKS)).toEqual([]);
    const bad = parseSlidesMd(deck(
      "## Results\n@formal thm:main\n@formal thm:lower\n@figure Bad_Name:\n@figure a: x\n@figure b: x\n@figure c: x",
    ));
    const gates = lintSlides(bad, BLOCKS).map((p) => p.gate);
    expect(gates).toContain("slides-figure-name");
    expect(gates).toContain("slides-figure-caption");
    expect(gates).toContain("slides-figure-count");
  });

  it("extractDsl keeps only node/edge lines and rejects DSL-free output", () => {
    const out = extractDsl("Here you go:\n```\nnode a | Title A\nnode b | Title B | detail\nedge a -> b\n```\ndone");
    expect(out).toBe("node a | Title A\nnode b | Title B | detail\nedge a -> b");
    expect(() => extractDsl("no dsl at all")).toThrow(/no `node`\/`edge`/);
  });

  it("parseFigureDsl validates ids, titles, and edge endpoints", () => {
    expect(() => parseFigureDsl("edge a -> b")).toThrow(/no nodes/);
    expect(() => parseFigureDsl("node a | T\nedge a -> ghost")).toThrow(/undeclared node "ghost"/);
    expect(() => parseFigureDsl("node a | T\nnode a | T2")).toThrow(/duplicate/);
    expect(() => parseFigureDsl("node a | T\nedge a -> a")).toThrow(/self-loop/);
  });

  it("renderFigureSvg lays out deterministically: every box fits its text, every edge is drawn", () => {
    const spec = parseFigureDsl(
      [
        "node data | Observed data",
        "node poly | Heavy-light polynomial | plug-in on heavy | Chebyshev on light",
        "node coll | Occupancy collision | crossed cells only",
        "node zero | Zero branch",
        "node sel | Known-radius selector | compares scales via σ",
        "edge data -> poly",
        "edge data -> coll",
        "edge data -> zero",
        "edge poly -> sel",
        "edge coll -> sel",
        "edge zero -> sel",
      ].join("\n"),
    );
    const svg = renderFigureSvg(spec);
    expect(svg).toContain("viewBox");
    expect((svg.match(/marker-end/g) ?? []).length).toBe(6); // all six edges drawn
    expect((svg.match(/<rect /g) ?? []).length).toBe(5);
    expect(svg).not.toMatch(/<text(?![^>]*stroke="none")/); // text never stroked
    // Box width always exceeds its widest measured line: rect widths ≥ text estimate.
    const widest = "Heavy-light polynomial".length * 17 * 0.62 * 1.08;
    const polyRect = /<rect [^>]*width="([\d.]+)" height/g;
    const widths = [...svg.matchAll(polyRect)].map((m) => Number(m[1]));
    expect(Math.max(...widths)).toBeGreaterThan(widest);
  });
});

describe("extractDeckMarkdown", () => {
  it("strips fences and pre-heading chatter", () => {
    const out = extractDeckMarkdown("Here is the deck:\n```markdown\n# T\nbody\n```");
    expect(out).toBe("# T\nbody\n");
    expect(() => extractDeckMarkdown("no heading at all")).toThrow(/# <talk title>/);
  });
});

describe("bibSummary", () => {
  it("renders one Author (Year) line per entry from references.bib", () => {
    const bib = `@article{Robinson1988,
  author = {Robinson, P. M.},
  title = {Root-{N}-consistent semiparametric regression},
  journal = {Econometrica},
  year = {1988}
}
@inproceedings{MackeySyrgkanisZadik2018,
  author = {Mackey, Lester and Syrgkanis, Vasilis and Zadik, Ilias},
  title = {Orthogonal Machine Learning},
  booktitle = {Proceedings of ICML},
  year = {2018}
}`;
    const out = bibSummary(bib);
    expect(out).toContain("- Robinson1988: Robinson (1988). Root-N-consistent semiparametric regression. Econometrica.");
    expect(out).toContain("- MackeySyrgkanisZadik2018: Mackey, Syrgkanis, Zadik (2018). Orthogonal Machine Learning. Proceedings of ICML.");
    expect(bibSummary("")).toBe("");
  });
});
