import { describe, expect, it } from "vitest";
import {
  extractBalancedEnv,
  hasPlausibleSentenceEnd,
  maskNonBoundaryPeriods,
  normalizeTexWhitespace,
  stripTexComments,
  truncateTexSafe,
} from "../../src/shared/tex_text.js";

describe("maskNonBoundaryPeriods", () => {
  it("masks decimals and multi-dot abbreviations, keeps sentence periods", () => {
    const masked = maskNonBoundaryPeriods("The errors are i.i.d. with variance 0.5. Then it holds.");
    expect(masked).not.toContain("i.i.d.");
    expect(masked).not.toContain("0.5");
    // The two genuine sentence periods survive.
    expect(masked.match(/\./g)?.length).toBe(2);
  });

  it("masks w.r.t. / a.s. / Thm. but not a bare single-letter period", () => {
    const masked = maskNonBoundaryPeriods("bounded w.r.t. \\(\\mu\\) a.s. by Thm. 2.1; the map p. Ends.");
    expect(masked).not.toMatch(/w\.r\.t\./);
    expect(masked).not.toMatch(/a\.s\./);
    expect(masked).not.toMatch(/Thm\./);
    expect(masked).toContain("p."); // single letters are never treated as abbreviations
  });
});

describe("hasPlausibleSentenceEnd", () => {
  it("accepts period + closer + whitespace, rejects decimals after masking", () => {
    expect(hasPlausibleSentenceEnd(maskNonBoundaryPeriods("First. second"))).toBe(true);
    expect(hasPlausibleSentenceEnd(maskNonBoundaryPeriods("First.” Second"))).toBe(true);
    expect(hasPlausibleSentenceEnd(maskNonBoundaryPeriods("p(x) \\le 0.5 everywhere"))).toBe(false);
  });
});

describe("stripTexComments", () => {
  it("strips real comments, keeps \\% literals, and reads \\\\% as a comment", () => {
    expect(stripTexComments("a % gone\nb")).toBe("a \nb");
    expect(stripTexComments("50\\% of it % gone")).toBe("50\\% of it ");
    // row separator then a REAL comment — the lookbehind version missed this
    expect(stripTexComments("a \\\\% gone\nb")).toBe("a \\\\\nb");
  });
});

describe("extractBalancedEnv", () => {
  it("keeps a nested same-name environment intact", () => {
    const tex = "intro \\begin{proof}outer \\begin{proof}[Claim 1]inner\\end{proof} tail\\end{proof} after";
    expect(extractBalancedEnv(tex, "proof")).toBe(
      "\\begin{proof}outer \\begin{proof}[Claim 1]inner\\end{proof} tail\\end{proof}",
    );
  });

  it("returns null when the environment never closes", () => {
    expect(extractBalancedEnv("\\begin{proof} dangling", "proof")).toBeNull();
  });
});

describe("truncateTexSafe", () => {
  it("backs off rather than cutting inside inline math", () => {
    const text = "The estimand is \\(\\mathbb{E}[Y^{(1)} - Y^{(0)} \\mid W]\\) under overlap.";
    const cut = truncateTexSafe(text, 30); // 30 chars lands inside the \( … \)
    expect(cut).toBe("The estimand is");
    expect(cut).not.toContain("\\(");
  });

  it("leaves short strings untouched and cuts at safe points", () => {
    expect(truncateTexSafe("short", 30)).toBe("short");
    const dollar = "risk $R_n^*$ small";
    expect(truncateTexSafe(dollar, 8)).toBe("risk");
  });

  it("treats $$…$$ as one display and backs off from position 0", () => {
    // per-`$` toggling read the display body as text mode and hard-cut inside it
    const display = "a $$" + "m".repeat(30) + "$$ b";
    expect(truncateTexSafe(display, 20)).toBe("a");
    // a math span opening AT 0 longer than max backs off to empty (balanced),
    // relying on every caller's fallback — never a sealed unbalanced delimiter
    const leading = "\\(" + "x".repeat(50) + "\\) tail";
    expect(truncateTexSafe(leading, 20)).toBe("");
  });

  it("does not mask the genuine sentence enders no./etc.", () => {
    const masked = maskNonBoundaryPeriods("The answer is no. Bounded, etc. Then done.");
    expect(masked.match(/\./g)?.length).toBe(3);
  });
});

describe("normalizeTexWhitespace", () => {
  it("collapses spacing but preserves paragraph breaks (\\par is semantic)", () => {
    expect(normalizeTexWhitespace("a  b\n c")).toBe("a b c");
    expect(normalizeTexWhitespace("para one.\n\npara two.")).toBe("para one.\n\npara two.");
    // a paragraph-only difference is a REAL difference…
    expect(normalizeTexWhitespace("a.\n\nb.")).not.toBe(normalizeTexWhitespace("a.\nb."));
    // …while reflowed single-newline whitespace is not
    expect(normalizeTexWhitespace("a.\nb.")).toBe(normalizeTexWhitespace("a. b."));
  });
});
