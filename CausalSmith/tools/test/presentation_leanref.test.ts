import { describe, it, expect } from "vitest";
import { renderLeanrefs, extractLeanrefIds } from "../src/presentation/tex2html.js";

describe("renderLeanrefs", () => {
  it("replaces a \\leanref with a token and records the drawer span + id", () => {
    const r = renderLeanrefs("We study \\leanref{P-2}{the disagreement set} in detail.");
    expect(r.ids).toEqual(["P-2"]);
    expect(r.tokens).toHaveLength(1);
    expect(r.tex).toBe(`We study ${r.tokens[0].token} in detail.`);
    expect(r.tokens[0].html).toBe(
      '<span class="leanref" data-objid="P-2">the disagreement set</span>',
    );
  });

  it("handles nested braces and inline math in the display text", () => {
    const r = renderLeanrefs("the model \\leanref{S-1}{policy class \\(\\mathcal{P}\\)} here");
    expect(r.ids).toEqual(["S-1"]);
    expect(r.tokens[0].html).toBe(
      '<span class="leanref" data-objid="S-1">policy class <span class="math inline">\\(\\mathcal{P}\\)</span></span>',
    );
  });

  it("collects every referenced id in order", () => {
    expect(extractLeanrefIds("\\leanref{A-1}{iid} and \\leanref{P-3}{exponents}")).toEqual([
      "A-1",
      "P-3",
    ]);
  });

  it("keeps a nested TeX group in a symbol id intact", () => {
    const r = renderLeanrefs("\\leanref{sym:kappa_{r}}{\\ensuremath{\\kappa_{r,a}(P)}}");
    expect(r.ids).toEqual(["sym:kappa_{r}"]);
    expect(r.tokens[0].html).toContain('data-objid="sym:kappa_{r}"');
  });

  it("does not truncate a display containing a literal escaped closing brace", () => {
    const r = renderLeanrefs("\\leanref{sym:set}{\\ensuremath{\\text{\\}}}}");
    expect(r.ids).toEqual(["sym:set"]);
    expect(r.tex).toBe(r.tokens[0].token);
  });

  it("returns [] when there are no \\leanref commands", () => {
    expect(extractLeanrefIds("plain prose with \\ref{obj:T-1}")).toEqual([]);
  });

  it("passes a malformed single-arg \\leanref through untouched", () => {
    const r = renderLeanrefs("oops \\leanref{P-9} end");
    expect(r.ids).toEqual([]);
    expect(r.tex).toBe("oops \\leanref{P-9} end");
  });
});
