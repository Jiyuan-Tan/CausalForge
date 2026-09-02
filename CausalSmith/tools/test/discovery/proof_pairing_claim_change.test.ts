// A bundle can rewrite a node's CLAIM and pair a PROOF for that same node in one apply.
// The proof was written against the OLD claim, so attaching it to the new one -- and
// clearing `partial` -- presents a proof of one statement as a proof of another.
// Audit triage 2026-07-20; silent corruption at normal reachability.

import { describe, it, expect } from "vitest";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { saveWorkingState, loadWorkingState, snapshotMember } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness } from "./d_stage_harness.js";
import { coreRevision, definitionRevision } from "../../src/discovery/core/revision.js";
import { assembleCore } from "../../src/discovery/core/assemble.js";
import { CoreSchema, type Core } from "../../src/discovery/core/schema.js";

const STMT = {
  id: "thm:main", kind: "theorem", statement: "OLD CLAIM", depends_on: ["ass:overlap"],
  status: "to-prove", justification: "j", gap: "g", consumer: "c",
};
const PROTO = {
  qid: "stat_pair", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [STMT], target_estimand: "tau", bibliography: [{ key: "R1983" }],
};

async function sealDefinitionProposalBasis(
  h: Awaited<ReturnType<typeof createDStageHarness>>,
  proto: Core,
): Promise<void> {
  const working = await loadWorkingState(h.ctx());
  working!.proposals!.basis_revision = coreRevision(CoreSchema.parse(assembleCore(proto, working!)));
  await saveWorkingState(h.ctx(), working!);
}

describe("a proof is not paired onto a claim it did not argue", () => {
  it("atomically rejects a claim rewrite whose reviewed proof does not argue it", async () => {
    const h = await createDStageHarness({ qid: "stat_pair", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: { "thm:main": { proof_tex: "", snapshot: snapshotMember(proto, proto.statements[0]), partial: true } },
        resolved_oeqs: {},
        proposals: {
          // (a) rewrite the claim, and (b) pair a proof for the SAME id in one bundle
          statements: [{ id: "thm:main", current: "OLD CLAIM", proposed: "NEW CLAIM", reason: "narrow", direction: "narrow" }],
          definitions: [], assumptions: [],
          coreEdits: [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...STMT, statement: "NEW CLAIM", depends_on: ["ass:overlap", "def:env"] },
            reason: "declare the envelope dependency", direction: "correct",
          }],
          proofs: [{ id: "thm:main", proof_tex: "A proof of the OLD claim." }],
        },
      } as never);

      await expect(applyProposedChanges({ ctx: h.ctx() }))
        .rejects.toThrow(/argues_proposed:true/);
      expect((await h.readProto()).statements[0].statement).toBe("OLD CLAIM");
    } finally { await h.dispose(); }
  }, 30000);

  it("DOES pair a proof when the claim is untouched", async () => {
    const h = await createDStageHarness({ qid: "stat_pair", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: { "thm:main": { proof_tex: "A proof of the CURRENT claim.", snapshot: snapshotMember(proto, proto.statements[0]), partial: true } },
        resolved_oeqs: {},
        proposals: {
          statements: [], definitions: [], assumptions: [],
          coreEdits: [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...STMT, depends_on: ["ass:overlap", "def:env"] },
            reason: "declare the envelope dependency", direction: "correct",
          }],
          proofs: [{ id: "thm:main", proof_tex: "A proof of the CURRENT claim." }],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const w = await loadWorkingState(h.ctx());
      const rec = (w as never as { solved: Record<string, { proof_tex?: string; partial?: boolean }> }).solved["thm:main"];
      expect(rec?.proof_tex, "a proof of the unchanged claim must still pair").toContain("CURRENT claim");
      expect(rec?.partial, "and the node is no longer open").toBeUndefined();
      const after = await h.readProto();
      expect(after.statements[0].status).toBe("to-prove");
      expect(after.statements[0].proof_tex).toBeUndefined();
    } finally { await h.dispose(); }
  }, 30000);
});

describe("metadata-only carried-node replacements", () => {
  it("preserves a proved agent node when its proof-relevant snapshot is unchanged", async () => {
    const h = await createDStageHarness({ qid: "stat_pair", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      const node = {
        id: "thm:agent-result", kind: "theorem", statement: "The agent result holds.",
        depends_on: ["ass:overlap"], status: "proved", proof_tex: "Existing proof.",
        justification: "old note", gap: "old gap", consumer: "old consumer",
      } as never;
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "thm:agent-result": {
            proof_tex: "Existing proof.",
            snapshot: snapshotMember(proto, node),
            node,
          },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [], definitions: [], assumptions: [], proofs: [],
          coreEdits: [{
            kind: "statement-replace", id: "thm:agent-result",
            proposed: {
              ...(node as never as Record<string, unknown>),
              justification: "updated note", gap: "updated gap", consumer: "updated consumer",
            },
            reason: "synchronize narrative metadata", direction: "correct",
          }],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const w = await loadWorkingState(h.ctx());
      expect(w?.solved["thm:agent-result"]).toMatchObject({
        proof_tex: "Existing proof.",
        node: {
          status: "proved",
          proof_tex: "Existing proof.",
          justification: "updated note",
          gap: "updated gap",
          consumer: "updated consumer",
        },
      });
      expect(w?.solved["thm:agent-result"].partial).toBeUndefined();
    } finally { await h.dispose(); }
  }, 30000);
});

describe("a CITED node is not settled by a citation for the old claim", () => {
  // The retained citation still documents the old claim, so `partial` — not
  // destructive source loss — carries the revalidation obligation.
  it("reopens a cited node whose claim the same bundle changed", async () => {
    const CITED = {
      id: "lem:cited", kind: "lemma", statement: "OLD CITED CLAIM", depends_on: [],
      status: "cited", source: { cite: "R1983", locator: "Thm 1" }, free_symbols: [],
    };
    const h = await createDStageHarness({ qid: "stat_pair", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "lem:cited": {
            proof_tex: "", snapshot: snapshotMember(proto, CITED as never),
            node: CITED as never,
          },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "lem:cited", current: "OLD CITED CLAIM", proposed: "NEW CITED CLAIM", reason: "r", direction: "narrow" }],
          definitions: [], assumptions: [],
          coreEdits: [{
            kind: "statement-replace", id: "lem:cited",
            proposed: { ...CITED, statement: "NEW CITED CLAIM", depends_on: ["ass:overlap"] },
            reason: "rewire", direction: "correct",
          }],
          proofs: [],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const w = await loadWorkingState(h.ctx());
      const rec = (w as never as { solved: Record<string, { partial?: boolean; node?: { status?: string; source?: unknown } }> }).solved["lem:cited"];
      expect(rec?.partial, "the rewritten claim must be reopened, not certified by the old source").toBe(true);
      expect(rec?.node?.status).toBe("cited");
      expect(rec?.node?.source).toEqual({ cite: "R1983", locator: "Thm 1" });
    } finally { await h.dispose(); }
  }, 30000);
});

describe("a proof is not settled against an undischarged dependency", () => {
  // A frozen member's proof lives in the WORKING cursor, not the proto, so "exists in
  // proto" does not mean "discharged". The closure check passed on existence alone, so a
  // consumer rewired onto a partial frozen dependency had its `partial` flag cleared.
  const DEP = {
    id: "lem:dep", kind: "lemma", statement: "the dependency", depends_on: [],
    status: "to-prove", justification: "j", gap: "g", consumer: "thm:main",
  };
  const PROTO2 = { ...PROTO, statements: [STMT, DEP] };

  it("leaves the consumer open when its frozen dependency is still partial", async () => {
    const h = await createDStageHarness({ qid: "stat_dep", specialization: "v1", proto: { ...PROTO2, qid: "stat_dep" } });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          // the dependency is carried but PARTIAL — not a finished proof
          "lem:dep": { proof_tex: "prior progress", snapshot: snapshotMember(proto, proto.statements[1]), partial: true },
          "thm:main": { proof_tex: "", snapshot: snapshotMember(proto, proto.statements[0]), partial: true },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [], definitions: [], assumptions: [],
          coreEdits: [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...STMT, depends_on: ["ass:overlap", "lem:dep"] },
            reason: "declare the dependency", direction: "correct",
          }],
          proofs: [{ id: "thm:main", proof_tex: "A proof resting on lem:dep." }],
        },
      } as never);

      await expect(applyProposedChanges({ ctx: h.ctx() }))
        .rejects.toThrow(/did not reach a complete exact postimage/);
      expect((await h.readProto()).statements[0].depends_on).toEqual(["ass:overlap"]);
    } finally { await h.dispose(); }
  }, 30000);
});

describe("a proof is not settled when its supporting correction was rejected", () => {
  // Selection is per-id, so an operator can accept a statement edit with --ids and REJECT
  // the definition correction the same round's proof was written against. `def:`/`ass:`
  // dependencies used to pass unconditionally ("carried in the snapshot"), so the proof
  // was settled on support that never landed.
  it("leaves the consumer open when its def: correction is not selected", async () => {
    const h = await createDStageHarness({ qid: "stat_reject", specialization: "v1", proto: { ...PROTO, qid: "stat_reject" } });
    try {
      const proto = await h.readProto();
      const revision = definitionRevision(proto.definitions[0], proto);
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: { "thm:main": { proof_tex: "", snapshot: snapshotMember(proto, proto.statements[0]), partial: true } },
        resolved_oeqs: {},
        proposals: {
          statements: [],
          // the correction the proof relies on ...
          definitions: [{ id: "def:env", current: "U = a", proposed: "U = a + b", based_on_revision: revision, reason: "fix", direction: "correct" }],
          assumptions: [],
          coreEdits: [
            {
              kind: "statement-replace", id: "thm:main",
              proposed: { ...STMT, depends_on: ["ass:overlap", "def:env"] },
              reason: "rewire onto the corrected definition", direction: "correct",
            },
            {
              kind: "definition-replace", id: "def:env", based_on_revision: revision,
              proposed: { ...proto.definitions[0], construction: "U = a + b", free_symbols: [] },
              reason: "complete post-image", direction: "correct",
            },
          ],
          proofs: [{ id: "thm:main", proof_tex: "A proof using the CORRECTED U = a + b." }],
        },
      } as never);
      await sealDefinitionProposalBasis(h, proto);

      // ... accepted WITHOUT it
      await expect(applyProposedChanges({ ctx: h.ctx(), ids: new Set(["core-edit:thm:main", "proof:thm:main"]) }))
        .rejects.toThrow(/complete coherence closure/);
      expect((await h.readProto()).definitions[0].construction).toBe("U = a");
    } finally { await h.dispose(); }
  }, 30000);
});

describe("round-6: the rejected-support guard covers every channel", () => {
  const mk = (over: Record<string, unknown>) => ({
    round: 1,
    solved: { "thm:main": { proof_tex: "", snapshot: {} as never, partial: true } },
    resolved_oeqs: {},
    proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [], ...over },
  });

  it("catches a correction carried by a typed CORE EDIT, not just the raw lists", async () => {
    // The first version of this guard read only `definitions`/`assumptions`. A
    // definition-replace travelling through proposed_core_edits was invisible to it, which
    // is the same hole the guard exists to close. Three auditors flagged it independently.
    const h = await createDStageHarness({ qid: "stat_chan", specialization: "v1", proto: { ...PROTO, qid: "stat_chan" } });
    try {
      const proto = await h.readProto();
      const revision = definitionRevision(proto.definitions[0], proto);
      await saveWorkingState(h.ctx(), {
        ...mk({
          definitions: [{
            id: "def:env", current: "U = a", proposed: "U = a + b",
            based_on_revision: revision, reason: "correct the formula", direction: "correct",
          }],
          coreEdits: [
            { kind: "statement-replace", id: "thm:main",
              proposed: { ...STMT, depends_on: ["ass:overlap", "def:env"] },
              reason: "rewire", direction: "correct" },
            { kind: "definition-replace", id: "def:env", based_on_revision: revision,
              proposed: { id: "def:env", name: "U", construction: "U = a + b", inputs: ["a"], free_symbols: [] },
              reason: "correct the formula", direction: "correct" },
          ],
          proofs: [{ id: "thm:main", proof_tex: "A proof using the CORRECTED U." }],
        }),
        solved: { "thm:main": { proof_tex: "", snapshot: snapshotMember(proto, proto.statements[0]), partial: true } },
      } as never);
      await sealDefinitionProposalBasis(h, proto);

      // accept the statement rewiring, REJECT the definition correction
      await expect(applyProposedChanges({ ctx: h.ctx(), ids: new Set(["statement-replace:thm:main", "proof:thm:main"]) }))
        .rejects.toThrow(/complete coherence closure/);
    } finally { await h.dispose(); }
  }, 30000);
});

describe("a rejected CITATION correction is support too", () => {
  // A proof written against a corrected locator rests on that correction. A
  // statement-replace carrying a new `source` is a fourth support channel; rejecting it
  // while accepting the consumer settles the proof against the locator it was meant to
  // replace.
  it("leaves the consumer open when the source correction is not selected", async () => {
    const CITED = {
      id: "lem:cited", kind: "lemma", statement: "a cited result", depends_on: [],
      status: "cited", source: { cite: "R1983", locator: "Thm 1 (WRONG)" },
    };
    const P = { ...PROTO, qid: "stat_srcrej", statements: [STMT, CITED] };
    const h = await createDStageHarness({ qid: "stat_srcrej", specialization: "v1", proto: P });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: { "thm:main": { proof_tex: "", snapshot: snapshotMember(proto, proto.statements[0]), partial: true } },
        resolved_oeqs: {},
        proposals: {
          statements: [], definitions: [], assumptions: [],
          coreEdits: [
            { kind: "statement-replace", id: "thm:main",
              proposed: { ...STMT, depends_on: ["ass:overlap", "lem:cited"] },
              reason: "rewire onto the cited result", direction: "correct" },
            // the locator fix the proof was written against
            { kind: "statement-replace", id: "lem:cited",
              proposed: { ...CITED, source: { cite: "R1983", locator: "Thm 4 (CORRECTED)" } },
              reason: "correct the locator", direction: "correct" },
          ],
          proofs: [{ id: "thm:main", proof_tex: "A proof citing Thm 4." }],
        },
      } as never);

      // accept the consumer, REJECT the locator correction
      await expect(applyProposedChanges({
        ctx: h.ctx(), ids: new Set(["statement-replace:thm:main", "proof:thm:main"]),
      })).rejects.toThrow(/did not reach a complete exact postimage/);
      expect((await h.readProto()).statements[0].depends_on).toEqual(["ass:overlap"]);
    } finally { await h.dispose(); }
  }, 30000);
});
