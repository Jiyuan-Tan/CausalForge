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
import { coreRevision, definitionRevision, statementRevision } from "../../src/discovery/core/revision.js";
import { assembleCore } from "../../src/discovery/core/assemble.js";
import { CoreSchema } from "../../src/discovery/core/schema.js";

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
  owner?: string;
}): Promise<void> {
  const proto = await h.readProto();
  const revision = definitionRevision(proto.definitions[0], proto);
  const statementRev = statementRevision(proto.statements[0]);
  await saveWorkingState(h.ctx(), {
    round: 1,
    solved: {
      // What merge banks when it defers the same-round proof: the payload bytes as the
      // node's hot partial.
      "thm:main": {
        proof_tex: opts.proofTex ?? NEW_PROOF,
        snapshot: snapshotMember(proto, proto.statements[0]),
        partial: true,
        ...(opts.owner ? { owner: opts.owner } : {}),
      },
    },
    resolved_oeqs: {},
    proposals: {
      statements: [{ id: "thm:main", current: STMT.statement, proposed: NEW_TEXT, based_on_revision: statementRev, reason: "drop redundant assumption", direction: "correct" }],
      definitions: opts.extraDefChange
        ? [{ id: "def:env", current: "U = a", proposed: "U = a + b", based_on_revision: revision, reason: "widen", direction: "correct" }]
        : [],
      assumptions: [], coreEdits: [
        {
          kind: "statement-replace", id: "thm:main", based_on_revision: statementRev,
          proposed: { ...proto.statements[0], statement: NEW_TEXT },
          reason: "complete statement post-image", direction: "correct",
        },
        ...(opts.extraDefChange ? [{
          kind: "definition-replace", id: "def:env", based_on_revision: revision,
          proposed: { ...proto.definitions[0], construction: "U = a + b", free_symbols: [] },
          reason: "complete post-image", direction: "correct",
        }] : []),
      ],
      proofs: [{ id: "thm:main", proof_tex: opts.proofTex ?? NEW_PROOF, ...(opts.arguesProposed ? { argues_proposed: true } : {}) }],
    },
  } as never);
  if (opts.extraDefChange) {
    const working = await loadWorkingState(h.ctx());
    working!.proposals!.basis_revision = coreRevision(CoreSchema.parse(assembleCore(proto, working!)));
    await saveWorkingState(h.ctx(), working!);
  }
}

type Rec = { proof_tex?: string; partial?: boolean; owner?: string; snapshot?: { stmt?: string } };
async function readRec(h: Awaited<ReturnType<typeof createDStageHarness>>): Promise<Rec | undefined> {
  const w = await loadWorkingState(h.ctx());
  return (w as never as { solved: Record<string, Rec> }).solved["thm:main"];
}

describe("argues_proposed paired-proof promotion", () => {
  it("promotes the node to proved in the SAME apply when the declared basis materialized", async () => {
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      await seedBundle(h, { arguesProposed: true, owner: "thm:directed-root" });
      await applyProposedChanges({ ctx: h.ctx() });

      const after = await h.readProto();
      expect(after.statements[0].statement).toBe(NEW_TEXT);
      expect(after.statements[0].status, "frozen proof ownership stays in the working overlay").toBe("to-prove");
      expect(after.statements[0].proof_tex).toBeUndefined();

      const rec = await readRec(h);
      expect(rec?.partial, "the record must be a settled reusable proof").toBeUndefined();
      expect(rec?.proof_tex).toBe(NEW_PROOF);
      expect(rec?.snapshot?.stmt, "validity must be measured against the NEW statement").toBe(NEW_TEXT);
      expect(rec?.owner, "paired promotion must preserve the frozen overlay's durable owner")
        .toBe("thm:directed-root");
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
      await expect(applyProposedChanges({ ctx: h.ctx(), ids: new Set(["thm:main"]) }))
        .rejects.toThrow(/complete coherence closure/);
      expect((await h.readProto()).statements[0].statement).toBe(STMT.statement);
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
            proposed: { ...STMT, statement: NEW_TEXT, depends_on: ["ass:overlap", "def:env"] },
            reason: "declare the envelope dependency", direction: "correct",
          }],
          proofs: [{ id: "thm:main", proof_tex: NEW_PROOF, argues_proposed: true }],
        },
      } as never);

      await expect(applyProposedChanges({ ctx: h.ctx(), ids: new Set(["statement:thm:main"]) }))
        .rejects.toThrow(/selected atomically/);
      expect((await h.readProto()).statements[0].statement).toBe(STMT.statement);
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
          coreEdits: [{
            kind: "statement-replace", id: "thm:main",
            proposed: { ...proto.statements[0], statement: NEW_TEXT },
            reason: "complete statement post-image", direction: "correct",
          }],
          proofs: [{ id: "thm:main", proof_tex: NEW_PROOF, argues_proposed: true }],
        },
      } as never);

      await expect(applyProposedChanges({ ctx: h.ctx(), ids: new Set(["thm:main"]) }))
        .rejects.toThrow(/did not reach a complete exact postimage/);
      expect((await h.readProto()).statements[0].statement).toBe(STMT.statement);
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
          definitions: [], assumptions: [], coreEdits: [{
            kind: "statement-replace", id: "lem:helper",
            proposed: { ...agentNode, statement: "helper, revised", status: "to-prove", proof_tex: undefined },
            reason: "complete carried statement post-image", direction: "correct",
          }],
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

  it("promotes a consumer after its later same-bundle helper reaches proved", async () => {
    const helper = {
      id: "lem:helper", kind: "lemma", statement: "helper, old", depends_on: ["ass:overlap"],
      status: "proved", proof_tex: "old helper proof",
    };
    const consumer = {
      ...STMT,
      statement: "main, old",
      depends_on: ["lem:helper"],
      status: "proved",
      proof_tex: "old main proof",
    };
    const h = await createDStageHarness({
      qid: "stat_promote", specialization: "v1", proto: { ...PROTO, statements: [consumer, helper] },
    });
    try {
      const proto = await h.readProto();
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "thm:main": {
            proof_tex: "new main proof using lem:helper",
            snapshot: snapshotMember(proto, proto.statements[0]),
            partial: true,
          },
          "lem:helper": {
            proof_tex: "new helper proof",
            snapshot: snapshotMember(proto, proto.statements[1]),
            partial: true,
          },
        },
        resolved_oeqs: {},
        proposals: {
          // Consumer deliberately precedes helper: a single proposal-order pass leaves
          // the consumer partial even though the accepted bundle discharges its basis.
          statements: [
            { id: "thm:main", current: "main, old", proposed: "main, new", reason: "tighten", direction: "correct" },
            { id: "lem:helper", current: "helper, old", proposed: "helper, new", reason: "tighten", direction: "correct" },
          ],
          definitions: [], assumptions: [], coreEdits: [
            {
              kind: "statement-replace", id: "thm:main",
              proposed: { ...consumer, statement: "main, new", status: "to-prove", proof_tex: undefined },
              reason: "complete main post-image", direction: "correct",
            },
            {
              kind: "statement-replace", id: "lem:helper",
              proposed: { ...helper, statement: "helper, new", status: "to-prove", proof_tex: undefined },
              reason: "complete helper post-image", direction: "correct",
            },
          ],
          proofs: [
            { id: "thm:main", proof_tex: "new main proof using lem:helper", argues_proposed: true },
            { id: "lem:helper", proof_tex: "new helper proof", argues_proposed: true },
          ],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const after = await h.readProto();
      expect(after.statements.find((s) => s.id === "lem:helper")?.status).toBe("to-prove");
      expect(after.statements.find((s) => s.id === "thm:main")?.status).toBe("to-prove");
      expect((await readRec(h))?.partial).toBeUndefined();
      const working = await loadWorkingState(h.ctx());
      expect(working?.solved["lem:helper"].partial).toBeUndefined();
    } finally { await h.dispose(); }
  }, 30000);

  it("does NOT promote an undeclared paired proof (conservative default)", async () => {
    const h = await createDStageHarness({ qid: "stat_promote", specialization: "v1", proto: PROTO });
    try {
      await seedBundle(h, { arguesProposed: false });
      await expect(applyProposedChanges({ ctx: h.ctx() }))
        .rejects.toThrow(/argues_proposed:true/);
      expect((await h.readProto()).statements[0].statement).toBe(STMT.statement);
    } finally { await h.dispose(); }
  }, 30000);
});
