// Two proposals for one id must never apply in sequence: the second silently wins and the
// atomicity guard cannot see it, because each contributes equally to the selected and
// applied counts. The guard existed for `statements` and `definitions` only; `proofs`,
// `assumptions` and `coreEdits` had the same hole. Audit triage, 2026-07-20.

import { describe, it, expect } from "vitest";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { saveWorkingState } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness } from "./d_stage_harness.js";

const PROTO = {
  qid: "stat_dup", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [{
    id: "thm:main", kind: "theorem", statement: "LIVE", depends_on: ["ass:overlap"],
    status: "to-prove", justification: "j", gap: "g", consumer: "c",
  }],
  target_estimand: "tau", bibliography: [{ key: "R1983" }],
};

async function apply(proposals: Record<string, unknown>): Promise<string> {
  const h = await createDStageHarness({ qid: "stat_dup", specialization: "v1", proto: PROTO });
  try {
    await saveWorkingState(h.ctx(), {
      round: 1, solved: {}, resolved_oeqs: {},
      proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [], ...proposals },
    } as never);
    try { await applyProposedChanges({ ctx: h.ctx() }); return ""; }
    catch (e) { return String((e as Error).message); }
  } finally { await h.dispose(); }
}

describe("conflicting proposals for one id are refused, in every channel", () => {
  it("refuses two PROOFS for one id — they collapse in a Map, last writer wins", async () => {
    const err = await apply({
      proofs: [{ id: "thm:main", proof_tex: "FIRST PROOF" }, { id: "thm:main", proof_tex: "SECOND PROOF" }],
    });
    expect(err).toMatch(/MULTIPLE conflicting proposals/);
    expect(err).toMatch(/proof id\(s\)/);
    expect(err).toMatch(/thm:main/);
  }, 30000);

  it("refuses two CORE EDITS of the same kind on one target", async () => {
    const edit = (dep: string) => ({
      kind: "statement-replace", id: "thm:main",
      proposed: { ...PROTO.statements[0], depends_on: ["ass:overlap", dep] },
      reason: "r", direction: "correct",
    });
    const err = await apply({ coreEdits: [edit("def:env"), edit("ass:overlap")] });
    expect(err).toMatch(/MULTIPLE conflicting proposals/);
    expect(err).toMatch(/statement:thm:main/);
  }, 30000);

  it("refuses MUTUALLY EXCLUSIVE kinds on one target", async () => {
    // Different kinds are not automatically independent: a replace and a delete on one
    // node cannot both be honoured. Their keys used to differ, so both applied in array
    // order and the delete silently erased the replacement while the selected-vs-applied
    // count still matched.
    const err = await apply({
      coreEdits: [
        { kind: "statement-replace", id: "thm:main",
          proposed: { ...PROTO.statements[0], depends_on: ["ass:overlap", "def:env"] },
          reason: "rewire", direction: "correct" },
        { kind: "statement-delete", id: "thm:main", reason: "obsolete", direction: "delete-obsolete" },
      ],
    });
    expect(err).toMatch(/MULTIPLE conflicting proposals/);
    expect(err).toMatch(/statement:thm:main/);
  }, 30000);

  it("ALLOWS a structural edit alongside a metadata rebuild — genuinely independent", async () => {
    const err = await apply({
      coreEdits: [
        { kind: "statement-replace", id: "thm:main",
          proposed: { ...PROTO.statements[0], depends_on: ["ass:overlap", "def:env"] },
          reason: "rewire", direction: "correct" },
        { kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
          reason: "rebuild", direction: "correct" },
      ],
    });
    expect(err, `a legitimate pair must still apply, got: ${err}`).not.toMatch(/MULTIPLE conflicting/);
  }, 30000);

  it("ALLOWS repeated idempotent rebuilds", async () => {
    const rebuild = (reason: string) => ({
      kind: "rebuild-reverse-dependencies", id: "metadata:reverse-dependencies",
      reason, direction: "correct",
    });
    const err = await apply({ coreEdits: [rebuild("a"), rebuild("b")] });
    expect(err).not.toMatch(/MULTIPLE conflicting/);
  }, 30000);
});
