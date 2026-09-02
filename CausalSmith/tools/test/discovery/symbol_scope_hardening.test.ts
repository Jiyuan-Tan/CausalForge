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
import { symbolBasis, changedSymbolNames, loadWorkingState, saveWorkingState, snapshotMember } from "../../src/discovery/stages/d0_working.js";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { coreRevision, definitionRevision } from "../../src/discovery/core/revision.js";
import { assembleCore } from "../../src/discovery/core/assemble.js";
import { createDStageHarness } from "./d_stage_harness.js";
import { CoreSchema, type Core } from "../../src/discovery/core/schema.js";

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

describe("symbolBasis: `ref` and transitive `refs` are semantic", () => {
  const proto = (sym: Record<string, unknown>): Core =>
    ({
      symbols: [{ name: "\\mathcal M", type: "law_class", def: "A subclass of the ambient family.", ...sym }],
      definitions: [], assumptions: [], statements: [],
    }) as never;

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

  it("rewriting `refs` re-fingerprints because it changes the semantic dependency closure", () => {
    const before = symbolBasis(proto({ refs: ["\\eta"] }));
    const after = symbolBasis(proto({ refs: ["\\eta", "\\bar d", "n"] }));
    expect(after["\\mathcal M"]).not.toBe(before["\\mathcal M"]);
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

  it("follows literal core ids in a referenced definition construction", () => {
    const core = proto({ ref: "def:outer" });
    core.definitions = [
      { id: "def:inner", name: "inner", construction: "old inner", inputs: [], free_symbols: [] },
      { id: "def:outer", name: "outer", construction: "built from def:inner", inputs: [], free_symbols: [] },
    ];
    const before = symbolBasis(core)["\\mathcal M"];
    core.definitions[0].construction = "corrected inner";
    expect(symbolBasis(core)["\\mathcal M"]).not.toBe(before);
  });

  it("normalizes free-symbol spellings while traversing a referenced core node", () => {
    const core = proto({ ref: "def:model" });
    core.symbols.push({ name: "tau", type: "scalar", def: "old target" } as never);
    core.definitions = [{
      id: "def:model", name: "model", construction: "model indexed by tau",
      inputs: [], free_symbols: ["\\(tau\\)"],
    }];
    const before = symbolBasis(core)["\\mathcal M"];
    core.symbols[1].def = "corrected target";
    expect(symbolBasis(core)["\\mathcal M"]).not.toBe(before);
  });

  it("does not treat statement motivation prose as symbol semantics", () => {
    const core = proto({ ref: "thm:referent" });
    core.statements = [{
      id: "thm:referent", kind: "theorem", statement: "the formal claim",
      depends_on: [], free_symbols: [], status: "to-prove", consumer: "old consumer",
    }];
    const before = symbolBasis(core)["\\mathcal M"];
    core.statements[0].consumer = "new consumer only";
    expect(symbolBasis(core)["\\mathcal M"]).toBe(before);
  });

  it("does not treat cited-source provenance as symbol semantics, but retains verbatim claim bytes", () => {
    const core = proto({ ref: "thm:referent" });
    core.statements = [{
      id: "thm:referent", kind: "theorem", statement: "the cited claim",
      depends_on: [], free_symbols: [], status: "cited",
      source: {
        cite: "Ref", locator: "Theorem 1", verbatim_statement: "Exact source claim.",
        attestation: { by: "main", note: "old provenance note" },
      },
    }];
    const before = symbolBasis(core)["\\mathcal M"];
    core.statements[0].source!.attestation!.note = "new provenance note only";
    expect(symbolBasis(core)["\\mathcal M"]).toBe(before);
    core.statements[0].source!.verbatim_statement = "Corrected exact source claim.";
    expect(symbolBasis(core)["\\mathcal M"]).not.toBe(before);
  });

  it("does not treat definition labels or assumption citation tags as symbol semantics", () => {
    const definitionCore = proto({ ref: "def:model" });
    definitionCore.definitions = [{
      id: "def:model", name: "old prose label", construction: "the formal model",
      inputs: [], free_symbols: [],
    }];
    const definitionBefore = symbolBasis(definitionCore)["\\mathcal M"];
    definitionCore.definitions[0].name = "new prose label";
    expect(symbolBasis(definitionCore)["\\mathcal M"]).toBe(definitionBefore);

    const assumptionCore = proto({ ref: "ass:regularity" });
    assumptionCore.assumptions = [{
      id: "ass:regularity", condition: "the formal condition", free_symbols: [],
      standard: { name: "regularity", cite: "OldReference" },
    }];
    const assumptionBefore = symbolBasis(assumptionCore)["\\mathcal M"];
    assumptionCore.assumptions[0].standard!.cite = "CorrectedReference";
    expect(symbolBasis(assumptionCore)["\\mathcal M"]).toBe(assumptionBefore);
  });

  it("rejects ambiguous delimiter-normalized symbol declarations", () => {
    const core = proto({});
    core.symbols.push({ name: "\\(\\mathcal M\\)", type: "duplicate", def: "ambiguous" } as never);
    expect(() => symbolBasis(core)).toThrow(/Ambiguous symbol declarations/);
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

async function saveWithProposalBasis(
  ctx: Parameters<typeof saveWorkingState>[0],
  proto: Core,
  state: Parameters<typeof saveWorkingState>[1],
): Promise<void> {
  await saveWorkingState(ctx, state);
  const persisted = await loadWorkingState(ctx);
  if (persisted?.proposals === undefined) throw new Error("test fixture lost its proposal carrier");
  persisted.proposals.basis_revision = coreRevision(CoreSchema.parse(assembleCore(proto, persisted)));
  await saveWorkingState(ctx, persisted);
}

/** Seed the harness with `thm:main` proved against `def:tilt`, then adjudicate one
 *  definition-replace and report the definition as applied. */
async function applyDefinitionReplace(proposed: Record<string, unknown>): Promise<Core["definitions"][number]> {
  const h = await createDStageHarness({ qid: "stat_defscope", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    const revision = definitionRevision(proto.definitions[0], proto);
    const constructionChanged = proposed.construction !== undefined && proposed.construction !== DEF.construction;
    await saveWithProposalBasis(h.ctx(), proto, {
      round: 1,
      solved: { "thm:main": { proof_tex: "By construction.", snapshot: snapshotMember(proto, proto.statements[0]) } },
      resolved_oeqs: {},
      proposals: {
        statements: [],
        definitions: constructionChanged ? [{
          id: "def:tilt", current: DEF.construction, based_on_revision: revision,
          proposed: proposed.construction, reason: "formula correction", direction: "correct",
        }] : [],
        assumptions: [], proofs: [],
        coreEdits: [{
          kind: "definition-replace", id: "def:tilt", proposed,
          based_on_revision: revision, reason: "r", direction: "correct",
        }],
      },
    } as never);
    await applyProposedChanges({ ctx: h.ctx() });
    return (await h.readProto()).definitions[0];
  } finally { await h.dispose(); }
}

async function applyPairedDefinitionReplaceAndDeleteSymbol(): Promise<Core> {
  const h = await createDStageHarness({ qid: "stat_defscope_pair", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    const proposed = {
      ...DEF,
      construction: "\\(T(X) = X/Z\\)",
      free_symbols: ["X", "Z"],
    };
    const revision = definitionRevision(proto.definitions[0], proto);
    await saveWithProposalBasis(h.ctx(), proto, {
      round: 1,
      solved: { "thm:main": { proof_tex: "By construction.", snapshot: snapshotMember(proto, proto.statements[0]) } },
      resolved_oeqs: {},
      proposals: {
        statements: [],
        definitions: [{
          id: "def:tilt",
          current: DEF.construction,
          based_on_revision: revision,
          proposed: proposed.construction,
          reason: "remove the obsolete parameter",
          direction: "correct",
        }],
        assumptions: [], proofs: [],
        coreEdits: [
          { kind: "definition-replace", id: "def:tilt", proposed, based_on_revision: revision, reason: "complete post-image", direction: "correct" },
          { kind: "symbol-delete", name: "\\eta", reason: "no remaining declaration uses it", direction: "delete-obsolete" },
        ],
      },
    } as never);
    await applyProposedChanges({ ctx: h.ctx() });
    return await h.readProto();
  } finally { await h.dispose(); }
}

async function rejectPartialDefinitionBundleSelection(): Promise<void> {
  const h = await createDStageHarness({ qid: "stat_defscope_partial_pair", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    const proposed = {
      ...DEF,
      construction: "\\(T(X) = X/Z\\)",
      free_symbols: ["X", "Z"],
    };
    const revision = definitionRevision(proto.definitions[0], proto);
    await saveWithProposalBasis(h.ctx(), proto, {
      round: 1, solved: {}, resolved_oeqs: {},
      proposals: {
        statements: [], assumptions: [], proofs: [],
        definitions: [{
          id: "def:tilt", current: DEF.construction, proposed: proposed.construction,
          based_on_revision: revision, reason: "formula correction", direction: "correct",
        }],
        coreEdits: [
          { kind: "definition-replace", id: "def:tilt", proposed, based_on_revision: revision, reason: "complete post-image", direction: "correct" },
          { kind: "symbol-delete", name: "\\eta", reason: "obsolete", direction: "delete-obsolete" },
        ],
      },
    } as never);
    await expect(applyProposedChanges({ ctx: h.ctx(), ids: new Set(["def:tilt"]) }))
      .rejects.toThrow(/complete coherence closure/);
    expect((await h.readProto()).definitions[0].construction).toBe(DEF.construction);
  } finally { await h.dispose(); }
}

async function rejectStalePairedDefinition(drift: "metadata" | "basis"): Promise<void> {
  const h = await createDStageHarness({ qid: `stat_defscope_stale_${drift}`, specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    const revision = definitionRevision(proto.definitions[0], proto);
    const proposed = {
      ...DEF,
      construction: "\\(T(X) = X/Z\\)",
      free_symbols: ["X", "Z"],
    };
    await saveWithProposalBasis(h.ctx(), proto, {
      round: 1, solved: {}, resolved_oeqs: {},
      proposals: {
        statements: [], assumptions: [], proofs: [],
        definitions: [{
          id: "def:tilt", current: DEF.construction, based_on_revision: revision,
          proposed: proposed.construction, reason: "formula correction", direction: "correct",
        }],
        coreEdits: [{
          kind: "definition-replace", id: "def:tilt", proposed,
          based_on_revision: revision, reason: "complete post-image", direction: "correct",
        }],
      },
    } as never);
    if (drift === "metadata") proto.definitions[0].inputs = ["X", "Z"];
    else proto.symbols[0].def = "changed inverse temperature";
    await h.writeProto(proto);
    await expect(applyProposedChanges({ ctx: h.ctx() })).rejects.toThrow(/persisted assembled-core basis/);
    const unchanged = await h.readProto();
    expect(unchanged.definitions[0].construction).toBe(DEF.construction);
    if (drift === "metadata") expect(unchanged.definitions[0].inputs).toEqual(["X", "Z"]);
    else expect(unchanged.symbols[0].def).toBe("changed inverse temperature");
  } finally { await h.dispose(); }
}

async function rejectUnrevisionedDefinitionReplacement(): Promise<void> {
  const h = await createDStageHarness({ qid: "stat_defscope_legacy_replace", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    await saveWithProposalBasis(h.ctx(), proto, {
      round: 1, solved: {}, resolved_oeqs: {},
      proposals: {
        statements: [], assumptions: [], proofs: [],
        definitions: [{
          id: "def:tilt", current: DEF.construction,
          proposed: "\\(T(X) = X/Z\\)", reason: "legacy formula correction", direction: "correct",
        }],
        coreEdits: [{
          kind: "definition-replace", id: "def:tilt",
          proposed: { ...DEF, construction: "\\(T(X) = X/Z\\)", free_symbols: ["X", "Z"] },
          reason: "legacy unbound replacement", direction: "correct",
        }],
      },
    } as never);
    await expect(applyProposedChanges({ ctx: h.ctx() })).rejects.toThrow(/lacks a complete pre-bundle revision/);
  } finally { await h.dispose(); }
}

async function rejectRevisionedDefinitionWithoutPostImage(): Promise<void> {
  const h = await createDStageHarness({ qid: "stat_defscope_missing_pair", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    const revision = definitionRevision(proto.definitions[0], proto);
    await saveWithProposalBasis(h.ctx(), proto, {
      round: 1, solved: {}, resolved_oeqs: {},
      proposals: {
        statements: [], assumptions: [], proofs: [], coreEdits: [],
        definitions: [{
          id: "def:tilt", current: DEF.construction, based_on_revision: revision,
          proposed: "\\(T(X) = X/Z\\)", reason: "orphan formula correction", direction: "correct",
        }],
      },
    } as never);
    await expect(applyProposedChanges({ ctx: h.ctx() })).rejects.toThrow(/lacks its exact complete definition-replace/);
    expect((await h.readProto()).definitions[0].construction).toBe(DEF.construction);
  } finally { await h.dispose(); }
}

async function rejectConstructionChangingReplacementWithoutFormula(): Promise<void> {
  const h = await createDStageHarness({ qid: "stat_defscope_orphan_replace", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    const revision = definitionRevision(proto.definitions[0], proto);
    await saveWithProposalBasis(h.ctx(), proto, {
      round: 1, solved: {}, resolved_oeqs: {},
      proposals: {
        statements: [], definitions: [], assumptions: [], proofs: [],
        coreEdits: [{
          kind: "definition-replace", id: "def:tilt", based_on_revision: revision,
          proposed: { ...DEF, construction: "\\(T(X) = X/Z\\)", free_symbols: ["X", "Z"] },
          reason: "orphan complete replacement", direction: "correct",
        }],
      },
    } as never);
    await expect(applyProposedChanges({ ctx: h.ctx() })).rejects.toThrow(/lacks its exact formula correction pair/);
    expect((await h.readProto()).definitions[0].construction).toBe(DEF.construction);
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

  it("uses the pre-bundle construction for a paired correction that deletes its old symbol", async () => {
    const applied = await applyPairedDefinitionReplaceAndDeleteSymbol();
    expect(applied.definitions[0].free_symbols).toEqual(["X", "Z"]);
    expect(applied.symbols.some((symbol) => symbol.name === "\\eta")).toBe(false);
  });

  it("rejects selecting only part of a definition-containing coherence bundle", async () => {
    await rejectPartialDefinitionBundleSelection();
  });

  it("rejects a paired whole-definition post-image after metadata drifts", async () => {
    await rejectStalePairedDefinition("metadata");
  });

  it("rejects a paired correction after a referenced semantic basis changes", async () => {
    await rejectStalePairedDefinition("basis");
  });

  it("fails closed on an unrevisioned legacy whole-definition replacement", async () => {
    await rejectUnrevisionedDefinitionReplacement();
  });

  it("fails closed on a revisioned formula correction without its exact post-image", async () => {
    await rejectRevisionedDefinitionWithoutPostImage();
  });

  it("fails closed on a construction-changing post-image without its exact formula correction", async () => {
    await rejectConstructionChangingReplacementWithoutFormula();
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
