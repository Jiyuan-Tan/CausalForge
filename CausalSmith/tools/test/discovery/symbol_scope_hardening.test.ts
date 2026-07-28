// Three ways the DECLARED symbol scope could still go stale or shrink unobserved, closed
// together because they are the same soundness property seen from three places:
//
//   1. AUTHORING. `free_symbols` on a statement/definition scopes symbol invalidation, but
//      only assumptions were gated on the names resolving. An unresolvable name on the two
//      unpoliced kinds is worse than on an assumption: the scope reads the list as the
//      complete set of symbols the claim rests on, so a typo contributes nothing and the
//      real symbol goes unwatched.
//   2. THE BASIS. `ref` names the node a symbol denotes. Re-pointing it swaps the referent
//      while every hashed field stayed byte-identical, so no carried proof reopened.
//   3. THE DEFINITION CHANNEL. `definition-replace` had no echo check at all, so a payload
//      could drop a symbol from a definition's declaration while echoing `construction` —
//      narrowing the scope of every node that cites it in one unobserved step.

import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { runStructuralGate } from "../../src/discovery/core/gate.js";
import { symbolBasis, changedSymbolNames, saveWorkingState, snapshotMember } from "../../src/discovery/stages/d0_working.js";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { createDStageHarness } from "./d_stage_harness.js";
import type { Core } from "../../src/discovery/core/schema.js";

function goldenCore(): Core {
  const raw = readFileSync(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8");
  return JSON.parse(raw) as Core;
}

describe("G1 gates the declared free symbols of every node kind", () => {
  it("passes the golden fixture unchanged — legacy nodes declare nothing and must not newly fail", () => {
    const res = runStructuralGate(goldenCore(), { requireDischarged: true });
    expect(res.violations).toEqual([]);
  });

  it("rejects a DEFINITION naming a symbol that is not in the symbol table", () => {
    const core = goldenCore();
    core.definitions[0].free_symbols = ["\\phi_{typo}"];
    const res = runStructuralGate(core, { requireDischarged: true });
    const g1 = res.violations.filter((v) => v.code === "G1");
    expect(g1.map((v) => v.where)).toContain(core.definitions[0].id);
    expect(g1[0].message).toMatch(/not in symbol table/);
  });

  it("rejects a STATEMENT naming a symbol that is not in the symbol table", () => {
    const core = goldenCore();
    core.statements[0].free_symbols = ["\\phi_{typo}"];
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.violations.filter((v) => v.code === "G1").map((v) => v.where)).toContain(core.statements[0].id);
  });

  it("accepts declarations that do resolve, on both newly gated kinds", () => {
    const core = goldenCore();
    const real = core.symbols[0].name;
    core.definitions[0].free_symbols = [real];
    core.statements[0].free_symbols = [real];
    expect(runStructuralGate(core, { requireDischarged: true }).violations).toEqual([]);
  });

  it("still accepts a genuinely empty declaration — `[]` is a claim about usage, not an omission", () => {
    const core = goldenCore();
    core.statements[0].free_symbols = [];
    expect(runStructuralGate(core, { requireDischarged: true }).violations).toEqual([]);
  });
});

describe("symbolBasis: `ref` is semantic, `refs` is bookkeeping", () => {
  const proto = (sym: Record<string, unknown>): Core =>
    ({ symbols: [{ name: "\\mathcal M", type: "law_class", def: "A subclass of the ambient family.", ...sym }] }) as never;

  it("re-pointing `ref` re-fingerprints the symbol — the referent changed", () => {
    const before = symbolBasis(proto({ ref: "def:block-class" }));
    const after = symbolBasis(proto({ ref: "def:other-class" }));
    expect(after["\\mathcal M"]).not.toBe(before["\\mathcal M"]);
  });

  it("CLEARING `ref` re-fingerprints too — a symbol whose referent vanished is not the same symbol", () => {
    expect(symbolBasis(proto({}))["\\mathcal M"]).not.toBe(symbolBasis(proto({ ref: "def:block-class" }))["\\mathcal M"]);
  });

  it("the generic `def` prose is NOT enough on its own — this is why `ref` had to join", () => {
    // Both symbols describe the object the same way and differ only in which definition
    // carves it, which is exactly the shape the 13 real ref-bearing symbols have.
    const a = proto({ ref: "def:block-class" });
    const b = proto({ ref: "def:other-class" });
    expect(a.symbols[0].def).toBe(b.symbols[0].def);
    expect(symbolBasis(a)["\\mathcal M"]).not.toBe(symbolBasis(b)["\\mathcal M"]);
  });

  it("rewriting `refs` does NOT re-fingerprint — it is derived from `def`, which is already hashed", () => {
    const before = symbolBasis(proto({ refs: ["\\eta"] }));
    const after = symbolBasis(proto({ refs: ["\\eta", "\\bar d", "n"] }));
    expect(after["\\mathcal M"]).toBe(before["\\mathcal M"]);
  });

  it("a symbol with no `ref` keeps its OLD fingerprint, so the upgrade re-baselines nothing", () => {
    // `JSON.stringify` omits an undefined value, so admitting the field cannot disturb the
    // 2082 of 2095 real symbols that never carried it. Pinned because the alternative —
    // every stored basis going stale at once — would drop every carried proof in every
    // in-flight run.
    const legacyStored = { "\\mathcal M": symbolBasis(proto({}))["\\mathcal M"] };
    expect(changedSymbolNames({ symbol_basis: legacyStored } as never, proto({})).size).toBe(0);
  });

  it("reports the re-pointed symbol through changedSymbolNames, which is what scopes invalidation", () => {
    const stored = symbolBasis(proto({ ref: "def:block-class" }));
    expect([...changedSymbolNames({ symbol_basis: stored } as never, proto({ ref: "def:other-class" }))])
      .toEqual(["\\mathcal M"]);
  });
});

const DEF = {
  id: "def:tilt", name: "tilt", construction: "\\(T(\\eta) = \\exp(\\eta X)/Z\\)",
  free_symbols: ["\\eta", "X"], inputs: ["X"],
};
const PROTO = {
  qid: "stat_defscope", specialization: "v1", cluster: "stat",
  symbols: [
    { name: "\\eta", type: "scalar", def: "inverse temperature" },
    { name: "X", type: "random vector", def: "covariates" },
    { name: "Z", type: "scalar", def: "normalizing constant" },
  ],
  assumptions: [{ id: "ass:bounded", kind: "regularity", condition: "\\(X\\) is bounded", free_symbols: ["X"], novel: { flag: true, justification: "t" } }],
  definitions: [DEF],
  statements: [{
    id: "thm:main", kind: "theorem", statement: "The tilt is normalized.",
    depends_on: ["def:tilt"], status: "proved", proof_tex: "By construction.",
    justification: "j", gap: "g", consumer: "c",
  }],
  target_estimand: "\\(T\\)", bibliography: [],
};

/** Seed the harness with `thm:main` proved against `def:tilt`, then adjudicate one
 *  definition-replace and report the definition as applied. */
async function applyDefinitionReplace(proposed: Record<string, unknown>): Promise<Core["definitions"][number]> {
  const h = await createDStageHarness({ qid: "stat_defscope", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    await saveWorkingState(h.ctx(), {
      round: 1,
      solved: { "thm:main": { proof_tex: "By construction.", snapshot: snapshotMember(proto, proto.statements[0]) } },
      resolved_oeqs: {},
      proposals: {
        statements: [], definitions: [], assumptions: [], proofs: [],
        coreEdits: [{ kind: "definition-replace", id: "def:tilt", proposed, reason: "r", direction: "correct" }],
      },
    } as never);
    await applyProposedChanges({ ctx: h.ctx() });
    return (await h.readProto()).definitions[0];
  } finally { await h.dispose(); }
}

describe("definition-replace cannot silently narrow the scope it lends its dependents", () => {
  it("retains a symbol dropped while `construction` was echoed byte-for-byte", async () => {
    const applied = await applyDefinitionReplace({ ...DEF, free_symbols: ["X"] });
    // `\eta` is back: `thm:main` was proved when `def:tilt` declared it, and the scope it
    // inherits must stay a superset of that. Without this, re-defining `\eta` would leave
    // the theorem's proof standing as a proof about a different object.
    expect(new Set(applied.free_symbols)).toEqual(new Set(["X", "\\eta"]));
  });

  it("retains under re-spelling, not just literal absence", async () => {
    // `\(\eta\)` and `\eta` are the same symbol under the normalization the scope uses;
    // a delimiter change must not read as a drop and duplicate the entry.
    const applied = await applyDefinitionReplace({ ...DEF, free_symbols: ["X", "\\(\\eta\\)"] });
    expect(applied.free_symbols).toEqual(["X", "\\(\\eta\\)"]);
  });

  it("applies a narrowing UNCHANGED when `construction` also changed — dependents re-derive anyway", async () => {
    // The snapshot stores the construction text, so every citing node already fails
    // `snapshotBasisValid` and re-derives against the new declaration. Retaining here
    // would permanently over-declare a definition that genuinely stopped using `\eta`.
    const applied = await applyDefinitionReplace({
      ...DEF, construction: "\\(T(X) = X/Z\\)", free_symbols: ["X"],
    });
    expect(applied.free_symbols).toEqual(["X"]);
  });

  it("leaves an ordinary widening edit exactly as proposed", async () => {
    const applied = await applyDefinitionReplace({ ...DEF, free_symbols: ["\\eta", "X", "Z"] });
    expect(applied.free_symbols).toEqual(["\\eta", "X", "Z"]);
  });

  it("leaves an undeclared definition alone — absent already means `any symbol`", async () => {
    const { free_symbols: _drop, ...undeclared } = DEF;
    const applied = await applyDefinitionReplace(undeclared);
    expect(applied.free_symbols).toBeUndefined();
  });
});
