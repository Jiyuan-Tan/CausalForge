// A proposal carries `current`: the value the solver saw when it generated the change.
// If the node has MOVED since, applying `proposed` silently discards whatever moved it.
//
// Carried working-state nodes were checked for this; FROZEN proto statements and
// definitions were not -- they assigned unconditionally (stage0_apply.ts, the raw
// claim-change loop). Found by static audit 2026-07-20. The carried branch also dropped
// its edit WITHOUT recording it, so the bundle guard reported a bare count.

import { describe, it, expect } from "vitest";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { loadWorkingState, saveWorkingState } from "../../src/discovery/stages/d0_working.js";
import { coreRevision, definitionRevision, statementRevision } from "../../src/discovery/core/revision.js";
import { assembleCore } from "../../src/discovery/core/assemble.js";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import { createDStageHarness } from "./d_stage_harness.js";

const PROTO = {
  qid: "stat_stale", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [{
    id: "thm:main", kind: "theorem", statement: "LIVE CLAIM",
    depends_on: ["ass:overlap"], status: "to-prove",
    justification: "j", gap: "g", consumer: "c",
  }],
  target_estimand: "tau", bibliography: [{ key: "R1983" }],
};

async function applyWith(proposals: Record<string, unknown>): Promise<{ ok: boolean; err: string }> {
  const h = await createDStageHarness({ qid: "stat_stale", specialization: "v1", proto: PROTO });
  try {
    const proto = await h.readProto();
    const definitions = (proposals.definitions ?? []) as Array<Record<string, any>>;
    const statements = (proposals.statements ?? []) as Array<Record<string, any>>;
    const revision = definitionRevision(proto.definitions[0], proto);
    const statementRev = statementRevision(proto.statements[0]);
    const pairedDefinitions = definitions.map((change) => ({ ...change, based_on_revision: revision }));
    const pairedStatements = statements.map((change) => ({ ...change, based_on_revision: statementRev }));
    const pairedCoreEdits = definitions.map((change) => ({
      kind: "definition-replace", id: change.id, based_on_revision: revision,
      proposed: { ...proto.definitions[0], construction: change.proposed, free_symbols: [] },
      reason: "complete post-image", direction: "correct",
    }));
    const pairedStatementEdits = statements.map((change) => ({
      kind: "statement-replace", id: change.id, based_on_revision: statementRev,
      proposed: { ...proto.statements[0], statement: change.proposed },
      reason: "complete statement post-image", direction: "correct",
    }));
    await saveWorkingState(h.ctx(), {
      round: 1, solved: {}, resolved_oeqs: {},
      proposals: {
        assumptions: [], proofs: [], ...proposals,
        statements: pairedStatements,
        definitions: pairedDefinitions,
        coreEdits: [...pairedCoreEdits, ...pairedStatementEdits, ...((proposals.coreEdits ?? []) as unknown[])],
      },
    } as never);
    if (definitions.length > 0) {
      const working = await loadWorkingState(h.ctx());
      working!.proposals!.basis_revision = coreRevision(CoreSchema.parse(assembleCore(proto, working!)));
      await saveWorkingState(h.ctx(), working!);
    }
    try {
      await applyProposedChanges({ ctx: h.ctx() });
      return { ok: true, err: "" };
    } catch (e) { return { ok: false, err: String((e as Error).message) }; }
  } finally { await h.dispose(); }
}

describe("a stale proposal must not silently overwrite a moved node", () => {
  it("refuses a frozen STATEMENT change whose `current` no longer matches", async () => {
    // Proposal was generated against "OLD CLAIM"; the proto now says "LIVE CLAIM".
    // Applying it would discard whatever moved the node, with no error.
    const r = await applyWith({
      statements: [{ id: "thm:main", current: "OLD CLAIM", proposed: "NEW CLAIM", reason: "r", direction: "narrow" }],
    });
    expect(r.ok, "a stale claim change must not apply").toBe(false);
    expect(r.err).toMatch(/stale proposal/);
    expect(r.err, "must name the node").toMatch(/thm:main/);
    expect(r.err, "must still refuse to mutate anything").toMatch(/were mutated on disk/);
  }, 30000);

  it("refuses a frozen DEFINITION change whose `current` no longer matches", async () => {
    const r = await applyWith({
      definitions: [{ id: "def:env", current: "U = OLD", proposed: "U = NEW", reason: "r", direction: "correct" }],
    });
    expect(r.ok).toBe(false);
    expect(r.err).toMatch(/stale proposal/);
    expect(r.err).toMatch(/def:env/);
  }, 30000);

  it("APPLIES a statement change whose `current` matches — the guard is not blanket", async () => {
    const r = await applyWith({
      statements: [{ id: "thm:main", current: "LIVE CLAIM", proposed: "NEW CLAIM", reason: "r", direction: "narrow" }],
    });
    expect(r.ok, `a faithful proposal must still apply, got: ${r.err}`).toBe(true);
  }, 30000);

  it("APPLIES a definition change whose `current` matches", async () => {
    const r = await applyWith({
      definitions: [{ id: "def:env", current: "U = a", proposed: "U = a + b", reason: "r", direction: "correct" }],
    });
    expect(r.ok, `a faithful definition change must still apply, got: ${r.err}`).toBe(true);
  }, 30000);

  it("canonicalizes an under-escaped texttt in the frozen proto before comparing `current`", async () => {
    const corrupted = "Refer to \\(\t" + "exttt{def:env}\\).";
    const canonical = String.raw`Refer to \(\texttt{def:env}\).`;
    const h = await createDStageHarness({
      qid: "stat_stale",
      specialization: "v1",
      proto: {
        ...PROTO,
        statements: [{ ...PROTO.statements[0], statement: corrupted }],
      },
    });
    try {
      await saveWorkingState(h.ctx(), {
        round: 1, solved: {}, resolved_oeqs: {},
        proposals: {
          statements: [{
            id: "thm:main", current: canonical, proposed: `${canonical} Narrowed.`,
            reason: "repair", direction: "narrow",
          }],
          definitions: [], assumptions: [], coreEdits: [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...(await h.readProto()).statements[0], statement: `${canonical} Narrowed.` },
            reason: "complete statement post-image", direction: "correct",
          }], proofs: [],
        },
      } as never);
      await expect(applyProposedChanges({ ctx: h.ctx() })).resolves.toHaveLength(2);
    } finally {
      await h.dispose();
    }
  }, 30000);
});
