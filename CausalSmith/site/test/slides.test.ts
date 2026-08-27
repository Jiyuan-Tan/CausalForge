import { describe, expect, it } from "vitest";
import { parseSlidesMd, renderFormalBody, renderSlideProse, safeFigureSvg } from "../src/lib/slides.js";

const DECK = `# Minimax Frontier Talk
One-line pitch with \\(\\tau_n\\).

---

## Main result
@informal thm:main: The rate is sharp.
- a bullet
@formal obj:thm:main
`;

describe("parseSlidesMd (site mirror)", () => {
  it("parses slides, directives, and normalizes obj: prefixes", () => {
    const doc = parseSlidesMd(DECK);
    expect(doc.talkTitle).toBe("Minimax Frontier Talk");
    expect(doc.slides).toHaveLength(2);
    expect(doc.slides[1].blocks).toEqual([
      { kind: "informal", objId: "thm:main", text: "The rate is sharp." },
      { kind: "prose", md: "- a bullet" },
      { kind: "formal", objId: "thm:main" },
    ]);
  });

  it("throws on a missing title slide", () => {
    expect(() => parseSlidesMd("## nope\nx")).toThrow(/talk title/);
  });
});

describe("figures (site mirror)", () => {
  it("parses @figure blocks", () => {
    const doc = parseSlidesMd("# T\npitch\n\n---\n\n## Map\n@figure regime-map: Dominant terms.");
    expect(doc.slides[1].blocks).toEqual([
      { kind: "figure", name: "regime-map", caption: "Dominant terms." },
    ]);
  });

  it("safeFigureSvg passes clean svg and rejects scripts/external refs/handlers", () => {
    expect(safeFigureSvg('<svg viewBox="0 0 1 1"><rect/></svg>')).toContain("<svg");
    expect(safeFigureSvg('<svg><script>x</script></svg>')).toBeNull();
    expect(safeFigureSvg('<svg><a href="https://x"/></svg>')).toBeNull();
    expect(safeFigureSvg('<svg onload="x"><rect/></svg>')).toBeNull();
    expect(safeFigureSvg('<svg><use href="#frag"/></svg>')).toContain("<svg");
    expect(safeFigureSvg("not svg")).toBeNull();
  });
});

describe("slide rendering", () => {
  it("renders a frozen body with display math kept display and refs flattened", () => {
    const html = renderFormalBody("By \\cref{obj:ass:design},\n\\[\n\\Pr(Z=1)=p .\n\\]");
    expect(html).toContain("katex-display");
    expect(html).toContain("ass:design");
    expect(html).not.toContain("\\cref");
  });

  it("translates itemize/enumerate and comma-list crefs — no raw \\item/\\cref leaks", () => {
    const body =
      "Under \\cref{obj:ass:a,obj:ass:b}:\n\\begin{itemize}\n\\item first, with \\(\\mathcal M\\).\n\\item second.\n\\end{itemize}";
    const html = renderFormalBody(body);
    expect(html).toContain("<ul><li>");
    expect(html).toContain("ass:a, ass:b");
    expect(html).toContain("katex");
    expect(html).not.toMatch(/\\item|\\cref|\\begin\{itemize\}/);
  });

  it("flattens a cref INSIDE math mode to \\text — no ⟦ref⟧ token typeset by KaTeX", () => {
    const html = renderFormalBody(
      "Let\n\\[\nP \\in \\text{ of }\\cref{obj:def:non-gaussian-class} .\n\\]\nSee \\cref{obj:def:model-class}.",
    );
    expect(html).not.toContain("⟦");
    expect(html).toContain("def:non-gaussian-class"); // flattened as \text inside the display
    expect(html).toContain("def:model-class"); // prose cref still rendered (link or plain id)
    expect(html).not.toContain("\\cref");
  });

  it("renders prose bullets with inline math", () => {
    const html = renderSlideProse("- rate \\(n^{-1}\\)\n- second point");
    expect(html).toContain("<ul>");
    expect(html).toContain("katex");
  });
});

describe("titleCase", () => {
  it("capitalizes principal words, keeps minors lowercase, preserves acronyms and math", async () => {
    const { titleCase } = await import("../src/lib/slides.js");
    expect(titleCase("minimax ATE estimation with many discrete adjustment cells")).toBe(
      "Minimax ATE Estimation with Many Discrete Adjustment Cells",
    );
    expect(titleCase("the radius organizes the problem")).toBe("The Radius Organizes the Problem");
    expect(titleCase("bounds for \\(\\sigma\\) under overlap")).toBe("Bounds for \\(\\sigma\\) under Overlap");
  });
});
