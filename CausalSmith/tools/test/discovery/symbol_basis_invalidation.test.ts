// Symbol basis + SCOPED symbol invalidation (2026-07 cross-stage rewind audit, FIX 4,
// then scoped).
//
// `sym` is not in `NODE_KINDS`, so a symbol is never a `depends_on` edge, and
// `MemberSnapshot` captures only {stmt, depends_on, defs, assumptions} — an APPLIED
// symbol re-definition therefore changed what every statement quoting it CLAIMS while
// every statement's text stayed byte-identical, and `computeValidNodes` saw nothing.
//
// The reach of that change comes from a DECLARED edge (`free_symbols`), never from
// scanning prose for the symbol's name, which was MEASURED unsound in both directions on
// live runs: in stat_reversekl_two_coverage the symbol names are bare single letters
// (`d`,`n`,`C`,`D`,…) that match every statement through ordinary English prose, while in
// stat_cot_observational_efficiency all 82 wrapped names match zero statements; and
// transitive use (a symbol inside a def's construction) is invisible to prose matching
// entirely. A node that declares NOTHING is read as using EVERY symbol, so the 112 real
// cores — in which zero of 1077 statements and zero of 1269 definitions carry the field —
// keep the old global behaviour and stay sound.
//
// PROVENANCE, precisely (an overstated claim here misleads the next reader into trusting
// a fixture more than it deserves):
//   • SYMBOL entries and the ASSUMPTION are VERBATIM from
//     doc/research/active/stat_reversekl_two_coverage/discovery/proto_core.json.
//   • STATEMENT TEXTS are PARAPHRASES, not verbatim. They are deliberately shortened so a
//     given case turns on the declared `free_symbols` edge rather than on incidental prose.
//     Note the real texts DO contain bare `d` inside ordinary words — which is the whole
//     reason scoping must not be driven by scanning statement prose.
//   • `free_symbols` declarations on statements/definitions are authored here: no real core
//     carries them yet (0 of ~1000 statements, 0 of ~1100 definitions), which is exactly the
//     legacy case the absent-means-"may use any symbol" fail-safe covers.
// The corpus test (symbol_invalidation_legacy_corpus.test.ts) is the one that exercises
// this against REAL protos through CoreSchema; this file pins the unit behaviour.

import { describe, it, expect } from "vitest";
import {
  symbolBasis,
  changedSymbolNames,
  computeValidNodes,
  declaredSymbolScope,
  memberValid,
  snapshotMember,
  type WorkingState,
} from "../../src/discovery/stages/d0_working.js";
import type { Core } from "../../src/discovery/core/schema.js";

// Verbatim production symbols (doc/research/active/stat_reversekl_two_coverage).
const SYM_D = { name: "d", type: "integer", space: "\\(\\{4,5,\\ldots\\}\\)", def: "linear feature dimension", role: "shell index" };
const SYM_N = { name: "n", type: "integer", space: "\\(\\mathbb N\\)", def: "number of logged observations", role: "sample-size index" };
const SYM_ETA = { name: "\\eta", type: "scalar", space: "\\(\\mathbb R_{>0}\\)", def: "reverse-KL inverse temperature", role: "regularization index" };
const SYM_XCAL = { name: "\\mathcal X", type: "set", space: "finite set", def: "context support", role: "primitive support" };
const SYM_PIREF = {
  name: "\\pi_{\\mathrm{ref}}",
  type: "Markov kernel",
  sig: "\\(\\pi_{\\mathrm{ref}}:\\mathcal X\\to\\Delta(\\mathcal A)\\)",
  def: "known reference and logging policy",
  role: "sampling and regularization primitive",
  refs: ["\\mathcal X", "\\mathcal A"],
};
const ALL_SYMBOLS = [SYM_D, SYM_N, SYM_ETA, SYM_XCAL, SYM_PIREF];

// Verbatim production assumption (same run).
const ASS_FINITE_CONTEXTS = {
  id: "ass:finite-contexts",
  kind: "support",
  condition: "\\(\\mathcal X\\) is finite.",
  free_symbols: ["\\mathcal X"],
  standard: { name: "finite contextual-bandit context support", cite: "ZhaoJiZhaoZhangGu2026SharpFDivergence" },
};

// Two statements in the production shape. NOTE the prose: `thm:localized-upper`'s text
// contains the letter "d" (in "bounded", "and") without quoting the SYMBOL d — exactly
// why mention-scoping is unsound and the edge must be declared.
const STMTS = [
  {
    id: "thm:localized-upper",
    kind: "theorem",
    statement: "the localized and bounded estimator attains the risk bound",
    depends_on: [],
    status: "to-prove",
    justification: "j", gap: "g", consumer: "c",
  },
  {
    id: "thm:same-shell-lower",
    kind: "theorem",
    statement: "no estimator improves the rate over the same shell",
    depends_on: [],
    status: "to-prove",
    justification: "j", gap: "g", consumer: "c",
  },
];

function protoWith(symbols: object[], overrides: Partial<Core> = {}): Core {
  return {
    qid: "stat_reversekl_two_coverage",
    specialization: "linear_exact_shell",
    cluster: "stat",
    symbols,
    assumptions: [],
    definitions: [],
    statements: JSON.parse(JSON.stringify(STMTS)),
    bibliography: [],
    ...overrides,
  } as unknown as Core;
}

function solvedCursor(proto: Core): WorkingState {
  return {
    round: 3,
    symbol_basis: symbolBasis(proto),
    solved: Object.fromEntries(
      proto.statements.map((s) => [s.id, { proof_tex: `Proof of ${s.id}.`, snapshot: snapshotMember(proto, s) }]),
    ),
    resolved_oeqs: {},
  } as unknown as WorkingState;
}

/** `narrow(SYM, {space})` — the shipped fault class: identical name, different meaning. */
const narrow = <T extends object>(sym: T, patch: Partial<Record<string, string>>): T => ({ ...sym, ...patch });

describe("changedSymbolNames — semantic fingerprint over real symbol shapes", () => {
  const base = protoWith(ALL_SYMBOLS);

  it("detects a space narrowing (the shipped fault class: same text, different claim)", () => {
    const prev = solvedCursor(base);
    const narrowed = protoWith([narrow(SYM_D, { space: "\\(\\{4\\}\\)" }), SYM_N, SYM_ETA, SYM_XCAL, SYM_PIREF]);
    expect([...changedSymbolNames(prev, narrowed)]).toEqual(["d"]);
  });

  it("detects a deleted symbol", () => {
    const prev = solvedCursor(base);
    expect([...changedSymbolNames(prev, protoWith([SYM_D, SYM_N, SYM_XCAL, SYM_PIREF]))]).toEqual(["\\eta"]);
  });

  it("an ADDED symbol invalidates nothing — no carried proof was solved against it", () => {
    const prev = solvedCursor(base);
    const added = protoWith([...ALL_SYMBOLS, { name: "\\kappa_\\eta", type: "scalar", def: "condition index" }]);
    expect(changedSymbolNames(prev, added).size).toBe(0);
  });

  it("a `refs`-only rewire is bookkeeping, NOT a semantic change", () => {
    // `refs` lists the other symbols this symbol's `def` mentions and exists for G1's
    // defined-before-use ordering check. It is derived from `def`, which IS hashed, so it
    // carries no meaning of its own — and it is the field most likely to be rewritten by
    // a re-ordering rather than by anyone changing what the symbol means.
    const prev = solvedCursor(base);
    const rewired = protoWith([SYM_D, SYM_N, SYM_ETA, SYM_XCAL, { ...SYM_PIREF, refs: ["\\mathcal X"] }]);
    expect(changedSymbolNames(prev, rewired).size).toBe(0);
  });

  it("`ref` IS semantic — re-pointing it swaps the symbol's referent", () => {
    // Originally excluded alongside `refs` as "dependency bookkeeping d0_apply rewires on
    // unrelated definition edits". Re-checked against the source: the only writers are
    // statement-delete-with-replacement (re-point) and definition-delete (clear), and in
    // both the referenced node genuinely vanished — there is no unrelated-rewire case.
    // Meanwhile `type`/`space`/`sig`/`def`/`role` can all stay byte-identical across a
    // re-point, because `def` describes the object generically ("known reference and
    // logging policy") without naming which definition carves it. So a statement quoting
    // the symbol kept a proof about the OLD object.
    const prev = solvedCursor(base);
    const rewired = protoWith([SYM_D, SYM_N, SYM_ETA, SYM_XCAL, { ...SYM_PIREF, ref: "def:common-experiment" }]);
    expect([...changedSymbolNames(prev, rewired)]).toEqual([SYM_PIREF.name]);
  });

  it("symbol ORDER is irrelevant (topologicallyOrderSymbols reorders on every apply)", () => {
    const prev = solvedCursor(base);
    expect(changedSymbolNames(prev, protoWith([SYM_PIREF, SYM_XCAL, SYM_ETA, SYM_N, SYM_D])).size).toBe(0);
  });

  it("a legacy cursor with no recorded basis invalidates nothing (no mass-invalidation on upgrade)", () => {
    const prev = solvedCursor(base);
    delete (prev as { symbol_basis?: unknown }).symbol_basis;
    const narrowed = protoWith([narrow(SYM_D, { space: "\\(\\{4\\}\\)" }), SYM_N, SYM_ETA, SYM_XCAL, SYM_PIREF]);
    expect(changedSymbolNames(prev, narrowed).size).toBe(0);
  });
});

// ── the fail-safe: an UNDECLARED node may use any symbol ─────────────────────────────

describe("legacy cores (no free_symbols anywhere) keep the global invalidation", () => {
  const base = protoWith(ALL_SYMBOLS);

  it("carries everything while the symbol table is unchanged", () => {
    const prev = solvedCursor(base);
    const valid = computeValidNodes(prev, protoWith(ALL_SYMBOLS));
    expect(valid.has("thm:localized-upper")).toBe(true);
    expect(valid.has("thm:same-shell-lower")).toBe(true);
  });

  it("invalidates EVERY carried proof on a semantic symbol change — no statement declares, so every scope is universal", () => {
    const prev = solvedCursor(base);
    const narrowed = protoWith([narrow(SYM_D, { space: "\\(\\{4\\}\\)" }), SYM_N, SYM_ETA, SYM_XCAL, SYM_PIREF]);
    // The statements' own texts and their whole def/assumption closures are unchanged:
    // without the symbol basis this carry is silent and proofs of materially different
    // claims are published as current.
    expect(computeValidNodes(prev, narrowed).size).toBe(0);
    expect(memberValid(prev, narrowed, narrowed.statements[0])).toBe(false);
  });

  it("declaredSymbolScope returns null (= may use ANY symbol) for a node with no declaration", () => {
    const prev = solvedCursor(base);
    const member = base.statements[0];
    expect(declaredSymbolScope(base, member, prev.solved[member.id].snapshot)).toBeNull();
  });

  it("does NOT invalidate on a pure refs rewire or a symbol addition", () => {
    const prev = solvedCursor(base);
    const benign = protoWith([SYM_D, SYM_N, SYM_ETA, SYM_XCAL, { ...SYM_PIREF, refs: [] }, { name: "T", type: "scalar", def: "temperature" }]);
    expect(computeValidNodes(prev, benign).size).toBe(2);
    expect(memberValid(prev, benign, benign.statements[0])).toBe(true);
  });
});

// ── scoping: a declared node reopens only for ITS symbols ────────────────────────────

/** A core in which every statement/definition/assumption declares its symbols, i.e. what
 *  the updated D-1.2 / D0 prompts emit. Real symbol names and real assumption; the
 *  statement texts are the production ones above. */
function declaredProto(symbols: object[]): Core {
  return protoWith(symbols, {
    assumptions: [ASS_FINITE_CONTEXTS],
    definitions: [
      {
        id: "def:exact-shell",
        name: "exact coverage shell",
        construction: "\\(\\mathcal M(d,C,D,\\eta)\\) collects the laws whose exact coverage indices match.",
        free_symbols: ["d", "\\eta"],
        by_member_properties: ["ass:finite-contexts"],
      },
    ],
    statements: [
      {
        // declares `n` ONLY: the letter d appears in its prose ("bounded", "and") but the
        // SYMBOL d is not part of this claim.
        id: "thm:localized-upper",
        kind: "theorem",
        statement: "the localized and bounded estimator attains the risk bound",
        free_symbols: ["n"],
        depends_on: [],
        status: "to-prove",
        justification: "j", gap: "g", consumer: "c",
      },
      {
        // reaches `d` and `\eta` only THROUGH def:exact-shell, and `\mathcal X` only
        // through that definition's member-property assumption.
        id: "thm:same-shell-lower",
        kind: "theorem",
        statement: "no estimator improves the rate over the same shell",
        free_symbols: [],
        depends_on: ["def:exact-shell"],
        status: "to-prove",
        justification: "j", gap: "g", consumer: "c",
      },
      {
        // consumes thm:same-shell-lower; declares nothing of its own.
        id: "prop:canonical-tabular-reduction",
        kind: "proposition",
        statement: "the canonical tabular reduction preserves the lower bound",
        free_symbols: [],
        depends_on: ["thm:same-shell-lower"],
        status: "to-prove",
        justification: "j", gap: "g", consumer: "c",
      },
    ] as unknown as Core["statements"],
  });
}

describe("scoped symbol invalidation over a fully declared core", () => {
  const base = declaredProto(ALL_SYMBOLS);
  const cursor = (): WorkingState => solvedCursor(base);

  const after = (symbols: object[]): Set<string> => computeValidNodes(cursor(), declaredProto(symbols));

  it("reopens ONLY the statement that declares the moved symbol", () => {
    const valid = after([SYM_D, narrow(SYM_N, { space: "\\(\\{1,2\\}\\)" }), SYM_ETA, SYM_XCAL, SYM_PIREF]);
    expect(valid.has("thm:localized-upper")).toBe(false);
    // The other two neither declare `n` nor depend on the reopened node.
    expect(valid.has("thm:same-shell-lower")).toBe(true);
    expect(valid.has("prop:canonical-tabular-reduction")).toBe(true);
  });

  it("reaches a statement through a DEFINITION in its snapshot closure, then propagates along depends_on", () => {
    // `d` is declared by def:exact-shell, not by any statement.
    const valid = after([narrow(SYM_D, { space: "\\(\\{4\\}\\)" }), SYM_N, SYM_ETA, SYM_XCAL, SYM_PIREF]);
    expect(valid.has("thm:same-shell-lower")).toBe(false);
    // Reached by the ORDINARY depends_on fixpoint — no second propagation.
    expect(valid.has("prop:canonical-tabular-reduction")).toBe(false);
    expect(valid.has("thm:localized-upper")).toBe(true);
  });

  it("reaches a statement through an ASSUMPTION carried transitively by a definition", () => {
    // `\mathcal X` is declared only by ass:finite-contexts, which enters the closure as
    // def:exact-shell's member property.
    const valid = after([SYM_D, SYM_N, SYM_ETA, narrow(SYM_XCAL, { space: "countable set" }), SYM_PIREF]);
    expect(valid.has("thm:same-shell-lower")).toBe(false);
    expect(valid.has("prop:canonical-tabular-reduction")).toBe(false);
    expect(valid.has("thm:localized-upper")).toBe(true);
  });

  it("a symbol NO node declares reopens nothing", () => {
    const valid = after([SYM_D, SYM_N, SYM_ETA, SYM_XCAL, narrow(SYM_PIREF, { def: "a different reference policy" })]);
    expect(valid.size).toBe(3);
  });

  it("declaring `[]` is a real declaration, distinct from never declaring", () => {
    const cur = cursor();
    const member = base.statements.find((s) => s.id === "thm:same-shell-lower")!;
    const scope = declaredSymbolScope(base, member, cur.solved[member.id].snapshot);
    // `[]` on the statement itself, widened by its closure — NOT null.
    expect(scope).not.toBeNull();
    expect([...scope!].sort()).toEqual(["\\eta", "\\mathcal X", "d"]);
  });

  it("ONE undeclared definition in the closure poisons the whole scope back to universal", () => {
    // The trap: a statement that declares its symbols can still reach any symbol through
    // a legacy definition that declares none.
    const legacyDef = declaredProto(ALL_SYMBOLS);
    delete (legacyDef.definitions[0] as { free_symbols?: unknown }).free_symbols;
    const cur = solvedCursor(legacyDef);
    const member = legacyDef.statements.find((s) => s.id === "thm:same-shell-lower")!;
    expect(declaredSymbolScope(legacyDef, member, cur.solved[member.id].snapshot)).toBeNull();

    const moved = declaredProto([SYM_D, SYM_N, SYM_ETA, SYM_XCAL, narrow(SYM_PIREF, { def: "a different policy" })]);
    delete (moved.definitions[0] as { free_symbols?: unknown }).free_symbols;
    const valid = computeValidNodes(cur, moved);
    expect(valid.has("thm:same-shell-lower")).toBe(false);
    // The statement that DOES declare fully is still carried.
    expect(valid.has("thm:localized-upper")).toBe(true);
  });

  it("matches a declaration written with LaTeX delimiters against a bare symbol-table name", () => {
    // Real cores declare the same symbol in both styles (`t_\pi` and `\(t_\pi\)`); an
    // unnormalized comparison would silently UNDER-invalidate.
    const delimited = declaredProto(ALL_SYMBOLS);
    (delimited.statements[0] as { free_symbols: string[] }).free_symbols = ["\\(n\\)"];
    const cur = solvedCursor(delimited);
    const moved = declaredProto([SYM_D, narrow(SYM_N, { space: "\\(\\{1,2\\}\\)" }), SYM_ETA, SYM_XCAL, SYM_PIREF]);
    (moved.statements[0] as { free_symbols: string[] }).free_symbols = ["\\(n\\)"];
    expect(computeValidNodes(cur, moved).has("thm:localized-upper")).toBe(false);
  });

  it("memberValid agrees with computeValidNodes on the scoped decision", () => {
    const cur = cursor();
    const moved = declaredProto([SYM_D, narrow(SYM_N, { space: "\\(\\{1,2\\}\\)" }), SYM_ETA, SYM_XCAL, SYM_PIREF]);
    expect(memberValid(cur, moved, moved.statements[0])).toBe(false); // declares n
    expect(memberValid(cur, moved, moved.statements[1])).toBe(true); // does not
  });
});
