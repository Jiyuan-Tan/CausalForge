import { describe, it, expect } from "vitest";
import { normalizeSymbolLeanrefs, fixOverEscapedTex, promoteSymbolLeanrefs, repairSymbolLeanrefTargets } from "../src/presentation/emit.js";

describe("normalizeSymbolLeanrefs", () => {
  it("wraps a $…$ symbol display in \\ensuremath (math-safe in any mode)", () => {
    expect(normalizeSymbolLeanrefs("\\leanref{sym:mu_a}{$\\mu_a(x)$}")).toBe(
      "\\leanref{sym:mu_a}{\\ensuremath{\\mu_a(x)}}",
    );
  });
  it("wraps a bare-math symbol display too", () => {
    expect(normalizeSymbolLeanrefs("\\leanref{sym:A}{A}")).toBe("\\leanref{sym:A}{\\ensuremath{A}}");
  });
  it("makes a display nested inside \\(…\\) compile (no $ left inside the \\(…\\))", () => {
    const out = normalizeSymbolLeanrefs("\\(\\leanref{sym:mu_a}{$\\mu_a(x)$}=E_P[Y]\\)");
    expect(out).toBe("\\(\\leanref{sym:mu_a}{\\ensuremath{\\mu_a(x)}}=E_P[Y]\\)");
    expect(out).not.toContain("{$"); // no $ delimiter survives inside the \(…\)
  });
  it("handles balanced escaped braces in the display", () => {
    expect(normalizeSymbolLeanrefs("\\leanref{sym:pi}{$\\pi:\\mathcal X\\to\\{0,1\\}$}")).toBe(
      "\\leanref{sym:pi}{\\ensuremath{\\pi:\\mathcal X\\to\\{0,1\\}}}",
    );
  });
  it("does not mistake an escaped closing brace for the end of a nested TeX group", () => {
    expect(normalizeSymbolLeanrefs("\\leanref{sym:set}{\\ensuremath{\\text{\\}}}}")).toBe(
      "\\leanref{sym:set}{\\ensuremath{\\text{\\}}}}",
    );
  });
  it("preserves a symbol id with a nested TeX subscript group", () => {
    expect(normalizeSymbolLeanrefs("\\leanref{sym:kappa_{r}}{$\\kappa_{r,a}(P)$}")).toBe(
      "\\leanref{sym:kappa_{r}}{\\ensuremath{\\kappa_{r,a}(P)}}",
    );
  });
  it("leaves object \\leanref (text display) untouched", () => {
    const s = "\\leanref{ass:iid}{i.i.d. sampling}";
    expect(normalizeSymbolLeanrefs(s)).toBe(s);
  });
  it("is idempotent (already-\\ensuremath display is preserved)", () => {
    const once = normalizeSymbolLeanrefs("\\leanref{sym:e_P}{$e_P(x)$}");
    expect(normalizeSymbolLeanrefs(once)).toBe(once);
  });
});

describe("promoteSymbolLeanrefs", () => {
  it("promotes a leanref that IS the whole \\(…\\) to standalone (clickable)", () => {
    expect(promoteSymbolLeanrefs("for one observation \\(\\leanref{sym:O}{\\ensuremath{O=(X,A,Y)}}\\).")).toBe(
      "for one observation \\leanref{sym:O}{\\ensuremath{O=(X,A,Y)}}.",
    );
  });
  it("promotes a leanref LEADING a defining equation, re-wrapping the remainder", () => {
    expect(
      promoteSymbolLeanrefs("regression \\(\\leanref{sym:mu_a}{\\ensuremath{\\mu_a(x)}}=E_P[Y\\mid A=a]\\)."),
    ).toBe("regression \\leanref{sym:mu_a}{\\ensuremath{\\mu_a(x)}}\\(=E_P[Y\\mid A=a]\\).");
  });
  it("leaves a leanref MID-equation untouched (cannot split cleanly)", () => {
    const s = "the map \\(x = \\leanref{sym:y}{\\ensuremath{y}}\\) holds";
    expect(promoteSymbolLeanrefs(s)).toBe(s);
  });
  it("leaves a plain \\(…\\) with no symbol link untouched", () => {
    const s = "the set \\(\\{0,1\\}\\) and \\(x+1\\)";
    expect(promoteSymbolLeanrefs(s)).toBe(s);
  });
  it("is idempotent on an already-standalone leanref", () => {
    const once = promoteSymbolLeanrefs("the propensity \\(\\leanref{sym:e_P}{\\ensuremath{e_P(x)}}\\)");
    expect(promoteSymbolLeanrefs(once)).toBe(once);
    expect(once).toBe("the propensity \\leanref{sym:e_P}{\\ensuremath{e_P(x)}}");
  });
  it("promotes multiple links across the document", () => {
    const out = promoteSymbolLeanrefs(
      "\\(\\leanref{sym:A}{\\ensuremath{A}}\\in\\{0,1\\}\\) and \\(\\leanref{sym:Y}{\\ensuremath{Y}}\\)",
    );
    expect(out).toBe("\\leanref{sym:A}{\\ensuremath{A}}\\(\\in\\{0,1\\}\\) and \\leanref{sym:Y}{\\ensuremath{Y}}");
  });
});

describe("repairSymbolLeanrefTargets", () => {
  const symbols = ["kappa_{r,a}(P)", "Phi^right_{m,L}"];

  it("repairs a legacy unclosed first argument from its unique realized-name prefix", () => {
    expect(repairSymbolLeanrefTargets("\\leanref{sym:kappa_{r}{$\\kappa_{r,a}(P)$}", symbols)).toBe(
      "\\leanref{sym:kappa_{r,a}(P)}{$\\kappa_{r,a}(P)$}",
    );
  });

  it("upgrades a legacy but syntactically valid truncated target", () => {
    expect(repairSymbolLeanrefTargets("\\leanref{sym:Phi^right_{m}}{x}", symbols)).toBe(
      "\\leanref{sym:Phi^right_{m,L}}{x}",
    );
  });
});

describe("fixOverEscapedTex", () => {
  it("de-doubles backslashes when \\\\( signals an over-escape", () => {
    expect(fixOverEscapedTex("\\\\(0\\le \\gamma\\\\) and \\\\mathrm{x}")).toBe(
      "\\(0\\le \\gamma\\) and \\mathrm{x}",
    );
  });
  it("is a no-op on a correctly-escaped body (no \\\\( present)", () => {
    const ok = "\\(x\\) holds, with a line break \\\\ here";
    expect(fixOverEscapedTex(ok)).toBe(ok);
  });
  it("does not touch a legit \\\\ line break that follows whitespace", () => {
    // the guard fires (has \\( ), but \\<space> is left alone (only \\<non-space-non-digit> collapses)
    expect(fixOverEscapedTex("\\\\(a\\\\) \\\\ \nb")).toBe("\\(a\\) \\\\ \nb");
  });
});
