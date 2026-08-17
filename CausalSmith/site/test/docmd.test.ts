import { describe, expect, it } from "vitest";
import {
  renderDoc,
  renderNl,
  nlOf,
  nlPlain,
  parseCrosslinks,
  stripCrosslinks,
  renderTexCompact,
  renderLabel,
} from "../src/lib/docmd.js";

describe("docmd", () => {
  it("escapes HTML", () => {
    expect(renderDoc("a <b> & c")).toContain("a &lt;b&gt; &amp; c");
  });
  it("renders inline and display math with KaTeX", () => {
    expect(renderDoc("rate $n^{-1/2}$")).toContain("katex");
    expect(renderDoc("$$\\int f$$")).toContain("katex-display");
  });
  it("renders code spans", () => {
    expect(renderDoc("see `PotentialOutcome`")).toContain("<code>PotentialOutcome</code>");
  });
  it("renders emphasis spanning a code span (bold over `code`)", () => {
    // Regression: `**General-`n` identification.**` used to split into unmatched
    // `**`…`**` because code spans were tokenized before emphasis was applied.
    const html = renderDoc("**General-`n` identification.** Rest.");
    expect(html).toContain("<strong>General-<code>n</code> identification.</strong>");
    expect(html).not.toContain("**");
  });
  it("does not mistake prose digits for code/math placeholders", () => {
    const html = renderDoc("Firpo 2007 proves `x` over Fin 2.");
    expect(html).toContain("Firpo 2007");
    expect(html).toContain("Fin 2");
    expect(html).toContain("<code>x</code>");
  });
  it("renders bullets and paragraphs", () => {
    const html = renderDoc("Intro.\n\n* one\n* two\n\nOutro.");
    expect(html).toContain("<ul>");
    expect((html.match(/<p>/g) ?? []).length).toBe(2);
  });
  it("renderTexCompact renders the Formal-layer panel's delimited math", () => {
    // Regression: the panel printed `nl` as text, so every formula showed as source.
    const html = renderTexCompact("For every \\(q\\geq1\\),\n\\[\\liminf_n R_n\\geq c.\\]");
    expect(html).toContain("katex");
    // No delimiter survives unrendered (the `\geq` inside KaTeX's own
    // `<annotation encoding="application/x-tex">` is the source echo, not output).
    expect(html).not.toContain("\\(");
    expect(html).not.toContain("\\[");
    // Display math is demoted to inline so an index row stays one row.
    expect(html).not.toContain("katex-display");
  });
  it("nlOf takes the first paragraph", () => {
    expect(nlOf("The NL part.\n\nImplementation notes.")).toBe("The NL part.");
    expect(nlOf(null)).toBeNull();
  });
});

describe("NL ↔ Lean crosslinks", () => {
  it("parses hyp and goal links, splitting comma-separated names", () => {
    const segs = parseCrosslinks("Fix [Λ at least 1](hyp:Λ,hΛ), then [it holds](goal).");
    expect(segs).toEqual([
      { text: "Fix ", links: null },
      { text: "Λ at least 1", links: ["Λ", "hΛ"] },
      { text: ", then ", links: null },
      { text: "it holds", links: ["⊢"] },
      { text: ".", links: null },
    ]);
  });
  it("handles balanced brackets inside a phrase (E[A·Y·(…)])", () => {
    const segs = parseCrosslinks("then [equals E[A·Y·(wMax if Y ≥ 0 else wMin)]](goal).");
    expect(segs[1]).toEqual({ text: "equals E[A·Y·(wMax if Y ≥ 0 else wMin)]", links: ["⊢"] });
  });
  it("ignores unbalanced brackets inside code/math spans (interval notation)", () => {
    const segs = parseCrosslinks("If [overlap holds at `ε ∈ (0, 1/2]`](hyp:hov), done.");
    expect(segs[1]).toEqual({ text: "overlap holds at `ε ∈ (0, 1/2]`", links: ["hov"] });
  });
  it("leaves ordinary markdown links and stray closers untouched", () => {
    const s = "see [the paper](https://x.y) and a stray ](hyp:h) closer";
    expect(stripCrosslinks("see [the paper](https://x.y)")).toBe("see [the paper](https://x.y)");
    // The stray closer has an opener candidate in the md link — but that link's
    // own `]` was consumed; strip keeps the text lossless either way.
    expect(stripCrosslinks(s)).toContain("the paper");
  });
  it("renderNl emits data-links spans; renderDoc and nlPlain strip the markup", () => {
    const nl = "If [overlap holds](hyp:hoverlap), then [the bound is sharp](goal).";
    const html = renderNl(nl);
    expect(html).toContain('<span class="nl-link" data-links="hoverlap" tabindex="0">overlap holds</span>');
    expect(html).toContain('data-links="⊢"');
    expect(renderDoc(nl)).not.toContain("hyp:");
    expect(renderDoc(nl)).toContain("overlap holds");
    expect(nlPlain(nl)).toBe("If overlap holds, then the bound is sharp.");
  });
  it("escapes quotes in data-links so crafted names cannot inject attributes", () => {
    // Audit repro: a `"` in a link name must not close the attribute early.
    const html = renderNl('Fix [x](hyp:a",onfocus=alert).');
    expect(html).not.toMatch(/data-links="[^"]*"\s+onfocus/);
    expect(html).toContain("&quot;");
  });
  it("renderNl falls back to renderDoc when there are no crosslinks", () => {
    expect(renderNl("Plain **bold** text.")).toBe(renderDoc("Plain **bold** text."));
  });
  it("crosslink phrases still render inline code and math", () => {
    const html = renderNl("If [the score `e` is bounded](hyp:h1), done.");
    expect(html).toContain("<code>e</code>");
  });
});

describe("docmd hardening", () => {
  it("escapes HTML through the compact renderer (its output is used with set:html)", () => {
    const html = renderTexCompact('<script>alert(1)</script> <img src=x onerror=y>');
    expect(html).not.toContain("<script");
    expect(html).not.toContain("<img");
    expect(html).toContain("&lt;script&gt;");
  });



  it("flattens every cross-reference form, not just \\ref{obj:…}", () => {
    // The panel has no label targets, so a surviving \\cref/\\ref printed as raw source.
    expect(renderTexCompact("defined in \\cref{obj:def:point-risk}, for x"))
      .toBe("defined in def:point-risk, for x");
    expect(renderTexCompact("the bound in Theorem~\\ref{thm:sharp} holds"))
      .toBe("the bound in Theorem thm:sharp holds");
  });

  it("cannot be confused by a private-use placeholder character in the input", () => {
    const html = renderTexCompact("\u{E000}9\u{E001} lone");
    expect(html).not.toContain("undefined");
    expect(html).toContain("lone");
  });
});

describe("renderLabel", () => {
  it("renders a bare symbol label as one formula", () => {
    // `symbol` rows carry the formula itself as the label, with no delimiters.
    expect(renderLabel("\\Delta_r(p)")).toContain("katex");
    expect(renderLabel("\\bar\\beta_d")).toContain("katex");
  });
  it("accepts a delimited symbol label too", () => {
    expect(renderLabel("\\(\\mathsf R_{n,d,\\epsilon}\\)")).toContain("katex");
    expect(renderLabel("\\(\\mathsf R_{n,d,\\epsilon}\\)")).not.toContain("\\(");
  });
  it("leaves an ordinary label as escaped text", () => {
    expect(renderLabel("Setup S-1")).toBe("Setup S-1");
    expect(renderLabel("Definition <CtyLaw>")).toBe("Definition &lt;CtyLaw&gt;");
  });
  it("falls back to escaped text when KaTeX rejects the label", () => {
    expect(renderLabel("\\mathcal{X of points")).toBe("\\mathcal{X of points");
  });
});

