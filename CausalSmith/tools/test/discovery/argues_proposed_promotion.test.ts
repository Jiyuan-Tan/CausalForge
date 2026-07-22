// One-round statement repair: a paired proof that DECLARES it argues the PROPOSED text
// (`argues_proposed: true`) is promoted at apply time — the node lands proved in the
// same adjudication instead of reopening for a full re-derivation round.
//
// The old behavior was unconditionally conservative: any claim change refused its paired
// proof ("argues the OLD statement"), which is exactly backwards for the common repair
// shape — a reviewer flags a redundant assumption, the solver rewrites the proof FOR the
// new statement and proposes the statement change in the same round, and the pipeline
// still paid a second ~40-minute dispatch to have the same proof re-emitted.
//
// Promotion is verified, not trusted: it fires only when the statement change actually
// applied, the node reopened as to-prove, the proof's content closure touches no
// proposal that adjudication did NOT apply, and the dependency closure is discharged.
// An undeclared proof keeps the conservative path (see proof_pairing_claim_change.test.ts).

import { describe, it, expect } from "vitest";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { saveWorkingState, loadWorkingState, snapshotMember } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness } from "./d_stage_harness.js";

const STMT = {
  id: "thm:main", kind: "theorem", statement: "Under ass:redundant, tau is identified", depends_on: ["ass:overlap"],
  status: "to-prove", justification: "j", gap: "g", consumer: "c",
};
const PROTO = {
  qid: "stat_promote", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [STMT], target_estimand: "tau", bibliography: [{ key: "R1983" }],
};

const NEW_TEXT = "tau is identified (no redundant assumption)";
const NEW_PROOF = "A direct argument for the NEW claim, using only ass:overlap.";

async function seedBundle(h: Awaited<ReturnType<typeof createDStageHarness>>, opts: {
  proofTex?: string;
  arguesProposed?: boolean;
  extraDefChange?: boolean;
}): Promise<void> {
  const proto = await h.readProto();
  await saveWorkingState(h.ctx(), {
    round: 1,
    solved: {
      // What merge banks when it defers the same-round proof: the payload bytes as the
      // node's hot partial.
      "thm:main": { proof_tex: opts.proofTex ?? NEW_PROOF, snapshot: snapshotMember(proto, proto.statements[0]), partial: true },
    },
    resolved_oeqs: {},
    proposals: {
      statements: [{ id: "thm:main", current: STMT.statement, proposed: NEW_TEXT, reason: "drop redundant assumption", direction: "correct" }],
      definitions: opts.extraDefChange
        ? [{ id: "def:env", current: "U = a", proposed: "U = a + b", reason: "widen", direction: "correct" }]
        : [],
      assumptions: [], coreEdits: [],
      proofs: [{ id: "thm:main", proof_tex: opts.proofTex ?? NEW_PROOF, ...(opts.arguesProposed ? { argues_proposed: true } : {}) }],
    },
  } as never);
}

type Rec = { proof_tex?: string; partial?: boolean; snapshot?: { stmt?: string } };
async function readRec(h: Awaited<ReturnType<typeof createDStageHarness>>): Promise<Rec | undefined> {
  const w = await loadWorkingState(h.ctx());
  return (w as never as { solved: Record<string, Rec> }).solved["thm:main"];
}

describe("argues_proposed paired-proof promotion", () => {
  it("promotes the node to proved in the SAME apply when the declared basis materialized", async () => {
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      await seedBundle(h, { arguesProposed: true });
      await applyProposedChanges({ ctx: h.ctx() });

      const after = await h.readProto();
      expect(after.statements[0].statement).toBe(NEW_TEXT);
      expect(after.statements[0].status, "no second round is owed — the proof argued this text").toBe("proved");
      expect(after.statements[0].proof_tex).toBe(NEW_PROOF);

      const rec = await readRec(h);
      expect(rec?.partial, "the record must be a settled reusable proof").toBeUndefined();
      expect(rec?.proof_tex).toBe(NEW_PROOF);
      expect(rec?.snapshot?.stmt, "validity must be measured against the NEW statement").toBe(NEW_TEXT);
    } finally { await h.dispose(); }
  }, 30000);

  it("does NOT promote when the proof's closure touches a proposal adjudication left unapplied", async () => {
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      // The proof cites def:env, whose own change the adjudicator did NOT select — the
      // basis the proof argued did not fully materialize.
      await seedBundle(h, {
        proofTex: "By def:env (as revised), the NEW claim follows.",
        arguesProposed: true,
        extraDefChange: true,
      });
      await applyProposedChanges({ ctx: h.ctx(), ids: new Set(["thm:main"]) });

      const after = await h.readProto();
      expect(after.statements[0].statement).toBe(NEW_TEXT);
      expect(after.statements[0].status, "ambiguous basis → conservative reopen").toBe("to-prove");
      const rec = await readRec(h);
      expect(rec?.partial).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("does NOT promote when a SAME-ID sibling variant in another channel was rejected", async () => {
    // Audit finding (2026-07-21): tracking applied proposals by bare id aliased distinct
    // same-id variants — accepting the statement change while rejecting a same-id
    // statement-replace (dependency rewire) removed the id from the unapplied set, and a
    // proof authored against the rejected rewire could be promoted. Every variant
    // targeting an id must have applied before that id counts as materialized.
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "thm:main": { proof_tex: NEW_PROOF, snapshot: snapshotMember(proto, proto.statements[0]), partial: true },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "thm:main", current: STMT.statement, proposed: NEW_TEXT, reason: "drop redundant assumption", direction: "correct" }],
          definitions: [], assumptions: [],
          coreEdits: [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...STMT, depends_on: ["ass:overlap", "def:env"] },
            reason: "declare the envelope dependency", direction: "correct",
          }],
          proofs: [{ id: "thm:main", proof_tex: NEW_PROOF, argues_proposed: true }],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx(), ids: new Set(["statement:thm:main"]) });

      const after = await h.readProto();
      expect(after.statements[0].statement).toBe(NEW_TEXT);
      expect(after.statements[0].status, "a rejected same-id variant makes the declared basis ambiguous").toBe("to-prove");
      const rec = await readRec(h);
      expect(rec?.partial).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("does NOT promote when an unapplied GLOBAL invalidator (new assumption) is in the bundle", async () => {
    // Symbol/bibliography edits and newly proposed assumptions are not addressed by
    // literal node references, so the closure walk cannot see them — merge defers
    // proofs globally for exactly this reason (hasGlobalProofInvalidation), and
    // promotion must mirror that: an unapplied global proposal blocks promotion.
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "thm:main": { proof_tex: NEW_PROOF, snapshot: snapshotMember(proto, proto.statements[0]), partial: true },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "thm:main", current: STMT.statement, proposed: NEW_TEXT, reason: "drop redundant assumption", direction: "correct" }],
          definitions: [],
          assumptions: [{ id: "ass:new-moment", condition: "a new moment bound", reason: "needed", standard_or_novel: "novel: needed", not_crux: "supporting" }],
          coreEdits: [],
          proofs: [{ id: "thm:main", proof_tex: NEW_PROOF, argues_proposed: true }],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx(), ids: new Set(["statement:thm:main"]) });

      const after = await h.readProto();
      expect(after.statements[0].status, "an unapplied global invalidator must block promotion").toBe("to-prove");
      expect((await readRec(h))?.partial).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("promotes a CARRIED (agent-authored) node the same way", async () => {
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      const agentNode = {
        id: "lem:helper", kind: "lemma", statement: "helper as first stated", depends_on: ["ass:overlap"],
        status: "proved", proof_tex: "old helper proof",
      };
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "lem:helper": {
            proof_tex: "Proof of the revised helper claim.",
            snapshot: snapshotMember(proto, agentNode as never),
            partial: true,
            node: agentNode,
            owner: "thm:main",
          },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "lem:helper", current: "helper as first stated", proposed: "helper, revised", reason: "narrow", direction: "correct" }],
          definitions: [], assumptions: [], coreEdits: [],
          proofs: [{ id: "lem:helper", proof_tex: "Proof of the revised helper claim.", argues_proposed: true }],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const w = await loadWorkingState(h.ctx());
      const rec = (w as never as { solved: Record<string, { proof_tex?: string; partial?: boolean; node?: { status?: string; statement?: string; proof_tex?: string } }> }).solved["lem:helper"];
      expect(rec?.node?.statement).toBe("helper, revised");
      expect(rec?.node?.status, "the carried node lands proved in the same apply").toBe("proved");
      expect(rec?.node?.proof_tex).toBe("Proof of the revised helper claim.");
      expect(rec?.partial).toBeUndefined();
    } finally { await h.dispose(); }
  }, 30000);

  it("does NOT promote an undeclared paired proof (conservative default)", async () => {
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      await seedBundle(h, { arguesProposed: false });
      await applyProposedChanges({ ctx: h.ctx() });
      const after = await h.readProto();
      expect(after.statements[0].status).toBe("to-prove");
      const rec = await readRec(h);
      expect(rec?.partial).toBe(true);
      expect(rec?.proof_tex, "the payload bytes stay as the hot repair basis").toBe(NEW_PROOF);
    } finally { await h.dispose(); }
  }, 30000);
});
