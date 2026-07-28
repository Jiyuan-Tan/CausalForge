// The advisory lint that keeps `free_symbols` from rotting once it is load-bearing.
//
// `free_symbols` now scopes symbol invalidation (d0_working.declaredSymbolScope), so an
// under-declared node keeps a proof of a claim whose symbol moved. Nothing else reads the
// declaration, so it can rot unobserved — hence the lint. It is WARN tier by measurement:
// over all 1186 declaring assumptions in the 112 real cores under
// doc/research/{active,_bank}, a boundary-anchored text scan disagrees with the author's
// own declaration on 43.6% of assumptions raw, and still 10.1% after the two de-noising
// filters below, so it can never be allowed to block a round.
//
// FIXTURES ARE VERBATIM from doc/research/active/stat_reversekl_two_coverage's
// proto_core.json (symbol names and assumption conditions), plus the two failure modes
// the corpus scan actually produced.

import { describe, it, expect } from "vitest";
import { checkSymbolDeclarations, checkSymbolDeclarationDrift } from "../../src/discovery/core/preflight.js";
import { symbolDriftGate } from "../../src/discovery/framework/gate_registrations.js";

// Verbatim production symbol names (stat_reversekl_two_coverage).
const SYMBOLS = [
  { name: "d" },
  { name: "n" },
  { name: "\\eta" },
  { name: "\\mathcal X" },
  { name: "\\mathcal A" },
  { name: "\\pi_{\\mathrm{ref}}" },
];

describe("checkSymbolDeclarationDrift (advisory)", () => {
  it("flags a symbol used in the text but missing from free_symbols", () => {
    const v = checkSymbolDeclarationDrift({
      symbols: SYMBOLS,
      // Verbatim condition; the declaration is deliberately incomplete.
      assumptions: [{ id: "ass:finite-contexts", condition: "\\(\\mathcal X\\) is finite.", free_symbols: [] }],
    });
    expect(v).toHaveLength(1);
    expect(v[0].check).toBe("symbol-declaration-drift");
    expect(v[0].detail).toContain("\\mathcal X");
    expect(v[0].ids).toEqual(["ass:finite-contexts"]);
  });

  it("stays silent when the declaration is complete", () => {
    expect(
      checkSymbolDeclarationDrift({
        symbols: SYMBOLS,
        assumptions: [{ id: "ass:finite-contexts", condition: "\\(\\mathcal X\\) is finite.", free_symbols: ["\\mathcal X"] }],
      }),
    ).toEqual([]);
  });

  it("covers statements and definitions, which is where the field is new", () => {
    const v = checkSymbolDeclarationDrift({
      symbols: SYMBOLS,
      statements: [{ id: "thm:zero-risk-boundary", statement: "every \\(P\\) in \\(\\mathcal M(d,1,1,\\eta)\\) is degenerate", free_symbols: ["d"] }],
      definitions: [{ id: "def:exact-shell", construction: "the shell collects laws indexed by \\(\\eta\\)", free_symbols: [] }],
    });
    expect(v.map((x) => x.ids?.[0]).sort()).toEqual(["def:exact-shell", "thm:zero-risk-boundary"]);
    expect(v.find((x) => x.ids?.[0] === "thm:zero-risk-boundary")!.detail).toContain("\\eta");
  });

  it("says NOTHING about a node that never declared — that case is fail-safe, not drift", () => {
    // Every legacy statement/definition is in this state; warning on all of them would
    // bury the signal under the whole corpus.
    expect(
      checkSymbolDeclarationDrift({
        symbols: SYMBOLS,
        statements: [{ id: "thm:zero-risk-boundary", statement: "the shell \\(\\mathcal M(d,1,1,\\eta)\\) is nonempty" }],
      }),
    ).toEqual([]);
  });

  it("ignores 1-character symbol names, ACCEPTING the false negative to avoid the flood", () => {
    // Verbatim text from thm:zero-risk-boundary. `d` really is used here (it is inside
    // `\mathcal M(d,1,1,\eta)`, preceded by `(`, so it clears the boundary anchor) and
    // the lint deliberately stays quiet about it: admitting single letters raises the
    // corpus flag rate from 16.3% to 43.6% of assumptions, because a bare letter also
    // matches quoted indices and ordinary prose everywhere else. This is the one place
    // the lint knowingly under-reports; the invalidation path is unaffected, since it
    // reads the declaration and never the text.
    expect(
      checkSymbolDeclarationDrift({
        symbols: SYMBOLS,
        statements: [{
          id: "thm:zero-risk-boundary",
          statement: "If the shell \\(\\mathcal M(d,1,1,\\eta)\\) is nonempty, then every \\(P\\) in it is degenerate.",
          free_symbols: ["\\eta"],
        }],
      }),
    ).toEqual([]);
  });

  it("does not flag a declared symbol written at a different arity", () => {
    // The dominant real false positive: a condition declaring `Y_it(d)` also contains the
    // literal `Y_it`. Same object, not a missing declaration.
    expect(
      checkSymbolDeclarationDrift({
        symbols: [{ name: "Y_it" }, { name: "Y_it(d)" }],
        assumptions: [{ id: "ass:unit-untreated-exponential-mean", condition: "\\(Y_it(d)\\) has an exponential mean", free_symbols: ["Y_it(d)"] }],
      }),
    ).toEqual([]);
  });

  it("does not match a symbol name that is only a PREFIX of the symbol actually written", () => {
    // `\eta` and `\eta_n` are different symbol-table entries; a text using `\eta_n` does
    // not thereby use `\eta`. Real cores carry exactly this pair shape
    // (`\pi_{\mathrm{ref}}` alongside `\pi`).
    expect(
      checkSymbolDeclarationDrift({
        symbols: [{ name: "\\eta" }],
        assumptions: [{ id: "ass:a", condition: "\\(\\eta_n\\) is bounded away from zero", free_symbols: [] }],
      }),
    ).toEqual([]);
  });

  it("does not match a bare name that appears only as the tail of a LaTeX macro", () => {
    // A symbol legitimately named `eta` must not be found inside `\eta` — that is a
    // different token, and the left-boundary class excludes `\` for this reason.
    expect(
      checkSymbolDeclarationDrift({
        symbols: [{ name: "eta" }],
        assumptions: [{ id: "ass:a", condition: "\\(\\eta\\) is small", free_symbols: [] }],
      }),
    ).toEqual([]);
  });

  it("is registered as a WARN gate — it may never block a round", () => {
    expect(symbolDriftGate.tier).toBe("warn");
  });
});

describe("checkSymbolDeclarations (hard) now covers statements", () => {
  it("flags a statement declaring a symbol absent from the symbol table", () => {
    const v = checkSymbolDeclarations({
      symbols: [{ name: "\\eta" }],
      statements: [{ id: "thm:localized-upper", free_symbols: ["\\eta", "\\kappa_\\eta"] }],
    });
    expect(v).toHaveLength(1);
    expect(v[0].detail).toContain("\\kappa_\\eta");
    expect(v[0].ids).toEqual(["thm:localized-upper"]);
  });

  it("accepts a statement whose declaration resolves, including across delimiter styles", () => {
    expect(
      checkSymbolDeclarations({
        symbols: [{ name: "t_\\pi" }],
        statements: [{ id: "thm:a", free_symbols: ["\\(t_\\pi\\)"] }],
      }),
    ).toEqual([]);
  });
});
