// `free_symbols` is load-bearing for soundness once it scopes symbol invalidation, so the
// two ways it can silently become TOO SHORT are correctness bugs, not bookkeeping:
//
//   1. A solver that simply OMITS the field on a proposed assumption. Recording that as `[]`
//      ("uses nothing") rather than absent ("unknown") is the unsafe reading, and it leaks:
//      a statement's scope is its own declaration UNION its closure's, so one such assumption
//      narrows every statement depending on it.
//   2. A metadata-only `statement-replace` that echoes the claim text byte-for-byte while
//      dropping a symbol from the list. The echo check compares id/kind/statement/status and
//      never looked at the declaration, so the narrowing both escaped detection and persisted
//      in one step — after which no edit to the dropped symbol could ever reopen the node.
//
// Under-declaring is the UNSOUND direction (a symbol changes and nothing reopens);
// over-declaring only costs an extra re-derivation. These pin the safe side of that asymmetry.

import { describe, it, expect } from "vitest";
import { AssumptionSchema } from "../../src/discovery/core/schema.js";
import { declarationNarrowed } from "../../src/discovery/stages/d0_apply.js";

describe("assumption free_symbols: absent must not collapse to []", () => {
  it("keeps an omitted declaration ABSENT through the schema", () => {
    const parsed = AssumptionSchema.parse({
      id: "ass:tail-mgf",
      condition: "the moment generating function of the tail is finite",
      standard: { name: "sub-exponential tail", cite: "Vershynin2018" },
    });
    // NOT `[]` — absent means "may use any symbol", which is what makes a forgetful
    // solver fail safe instead of silently exempting the node from symbol invalidation.
    expect(parsed.free_symbols).toBeUndefined();
  });

  it("preserves a genuine empty declaration as distinct from an absent one", () => {
    const parsed = AssumptionSchema.parse({
      id: "ass:finite-actions",
      condition: "the action set is finite",
      free_symbols: [],
      standard: { name: "finite action support", cite: "ZhaoJiZhaoZhangGu2026SharpFDivergence" },
    });
    expect(parsed.free_symbols).toEqual([]);
    expect(parsed.free_symbols).not.toBeUndefined();
  });

  it("carries a real declaration through unchanged", () => {
    const parsed = AssumptionSchema.parse({
      id: "ass:feature-exact-shell",
      condition: "\\(D_P=D\\)",
      free_symbols: ["D_P", "D"],
      novel: { flag: true, justification: "representation-aware coverage diagnostic" },
    });
    expect(parsed.free_symbols).toEqual(["D_P", "D"]);
  });
});

describe("declarationNarrowed", () => {
  it("flags a dropped symbol — the escape that let a node become unreachable by its own edits", () => {
    expect(declarationNarrowed({ free_symbols: ["\\eta", "\\bar d"] }, { free_symbols: ["\\bar d"] })).toBe(true);
  });

  it("compares under the same normalization the scope uses, so a re-spelling is not a drop", () => {
    // `\(\eta\)` and `\eta` are the same symbol; 1605 of 3958 real names are `\(…\)`-wrapped.
    expect(declarationNarrowed({ free_symbols: ["\\eta"] }, { free_symbols: ["\\(\\eta\\)"] })).toBe(false);
  });

  it("does not flag an unchanged or WIDENED declaration — only shrinking is a basis change", () => {
    expect(declarationNarrowed({ free_symbols: ["\\bar d"] }, { free_symbols: ["\\bar d"] })).toBe(false);
    expect(declarationNarrowed({ free_symbols: ["\\bar d"] }, { free_symbols: ["\\bar d", "\\eta"] })).toBe(false);
  });

  it("does not flag the legacy migration absent -> declared", () => {
    // The node reaches this path only while VALID, i.e. no symbol changed since it was
    // proved — so recording what it uses cannot alter what it was proved against.
    expect(declarationNarrowed({}, { free_symbols: ["\\bar d"] })).toBe(false);
  });

  it("does not flag declared -> absent, which widens the scope back to `any symbol`", () => {
    expect(declarationNarrowed({ free_symbols: ["\\bar d"] }, {})).toBe(false);
  });

  it("flags dropping to an EMPTY declaration — the maximal narrowing", () => {
    expect(declarationNarrowed({ free_symbols: ["\\bar d"] }, { free_symbols: [] })).toBe(true);
  });
});
