import { describe, expect, it } from "vitest";
import { renderDoc, nlOf } from "../src/lib/docmd.js";

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
  it("nlOf takes the first paragraph", () => {
    expect(nlOf("The NL part.\n\nImplementation notes.")).toBe("The NL part.");
    expect(nlOf(null)).toBeNull();
  });
});
