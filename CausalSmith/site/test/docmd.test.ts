import { describe, expect, it } from "vitest";
import { renderDoc, nlOf, renderTexCompact, renderLabel } from "../src/lib/docmd.js";

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

