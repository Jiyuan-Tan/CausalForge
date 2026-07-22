import { describe, it, expect } from "vitest";
import { writeFile } from "node:fs/promises";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import {
  loadWorkingState,
  saveWorkingState,
  snapshotMember,
} from "../../src/discovery/stages/d0_working.js";
import {
  assembleSolveContext,
  oeqSourceFingerprint,
} from "../../src/discovery/solve/context.js";
import { reusableOeqAnswerMatches } from "../../src/discovery/solve/merge.js";
import { createDStageHarness } from "./d_stage_harness.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const question = {
  id: "oeq:coverage-and-power",
  kind: "openendedquestion",
  statement: "Can the procedure attain uniform coverage and characterize local power?",
  depends_on: ["def:procedure", "ass:overlap"],
  status: "to-prove",
  justification: "Both guarantees are open.",
  gap: "No tie-uniform result is known.",
  consumer: "A complete inference theorem.",
} as const;

const answer = {
  id: "thm:local-power-obstruction",
  kind: "theorem",
  statement: "Uniform root-n local power fails on the tie subexperiment.",
  depends_on: ["ass:overlap"],
  status: "proved",
  proof_tex: "Reduce to the tie subexperiment and apply the minimax lower bound.",
  justification: "Answers the local-power clause negatively.",
  gap: "The coverage clause remains open.",
  consumer: "The residual inference question.",
} as const;

const proto = {
  qid: "stat_oeq_reopen",
  specialization: "v1",
  cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{
    id: "ass:overlap",
    kind: "support",
    condition: "the propensity is bounded away from zero and one",
    free_symbols: [],
    standard: { name: "overlap", cite: "Rosenbaum1983" },
    used_by: [question.id],
  }],
  definitions: [{ id: "def:procedure", name: "Khat", construction: "a contact-set procedure", inputs: [] }],
  statements: [question],
  target_estimand: "tau",
  bibliography: [{ key: "Rosenbaum1983" }],
};

function resolutionSolver(emittedAnswer: object): StageDeps {
  let emittedResolution = false;
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = JSON.parse(segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1)) as Array<{ id: string }>;
      const resolvesQuestion = !emittedResolution && targets.some((target) => target.id === question.id);
      if (resolvesQuestion) emittedResolution = true;
      await writeFile(outPath, JSON.stringify({
        proofs: targets
          .filter((target) => target.id !== question.id)
          .map((target) => ({
            id: target.id,
            proof_tex: target.id === answer.id ? answer.proof_tex : "QED.",
          })),
        resolved_oeqs: resolvesQuestion ? [{ source_id: question.id, theorem: emittedAnswer }] : [],
        added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
        proposed_assumptions: [], proposed_core_edits: [], open_obligations: [],
      }), "utf8");
      return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}

async function seedReopenedQuestion(h: Awaited<ReturnType<typeof createDStageHarness>>): Promise<void> {
  await saveWorkingState(h.ctx(), {
    round: 4,
    solved: {
      [answer.id]: {
        proof_tex: answer.proof_tex,
        snapshot: snapshotMember(proto as never, answer as never),
        node: answer as never,
        owner: question.id,
      },
    },
    resolved_oeqs: {},
  });
}

describe("resolved OEQ reopen lifecycle", () => {
  it("detaches an accepted narrowing while preserving the old answer theorem and proof", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await saveWorkingState(h.ctx(), {
        round: 2,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(proto as never, answer as never),
            node: answer as never,
            owner: question.id,
          },
        },
        resolved_oeqs: {
          [question.id]: {
            theorem_id: answer.id,
            source_fingerprint: oeqSourceFingerprint(question as never),
          },
        },
        proposals: {
          statements: [{
            id: question.id,
            current: question.statement,
            proposed: "Can the procedure attain uniform coverage?",
            reason: "The local-power clause is answered by the obstruction theorem.",
            direction: "narrow",
          }],
          definitions: [], assumptions: [], coreEdits: [], proofs: [],
        },
      });

      await applyProposedChanges({ ctx: h.ctx() });

      const afterApply = await loadWorkingState(h.ctx());
      expect(afterApply?.resolved_oeqs?.[question.id]).toBeUndefined();
      expect(afterApply?.solved[answer.id]).toMatchObject({
        proof_tex: answer.proof_tex,
        node: { statement: answer.statement, status: "proved" },
      });
      expect(afterApply?.solved[answer.id].partial).toBeUndefined();

      const assembled = await assembleSolveContext({ ctx: h.ctx(), state: h.state() });
      expect(assembled.persistedOeqReplacements.size).toBe(0);
      expect(assembled.core.statements.find((s) => s.id === question.id)).toMatchObject({
        statement: "Can the procedure attain uniform coverage?",
        status: "to-prove",
      });
      expect(assembled.core.statements.find((s) => s.id === answer.id)).toMatchObject({
        statement: answer.statement,
        status: "proved",
        proof_tex: answer.proof_tex,
      });
      expect(assembled.next.solved[answer.id]?.partial).toBeUndefined();
    } finally {
      await h.dispose();
    }
  });

  it("migrates an old prose-sensitive fingerprint without re-answering unchanged mathematics", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      const oldFingerprint = JSON.stringify({
        kind: question.kind,
        statement: question.statement,
        depends_on: ["ass:overlap", "def:procedure", "ass:overlap"],
        justification: "Old motivation.",
        gap: "Old gap prose.",
        consumer: "Old consumer prose.",
      });
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(proto as never, answer as never),
            node: answer as never,
            // Deliberately absent: provenance is not the resolution identity.
          },
        },
        resolved_oeqs: {
          [question.id]: { theorem_id: answer.id, source_fingerprint: oldFingerprint },
        },
      });

      const assembled = await assembleSolveContext({ ctx: h.ctx(), state: h.state() });
      expect(assembled.persistedOeqReplacements.get(question.id)).toBe(answer.id);
      expect(assembled.next.resolved_oeqs?.[question.id]).toEqual({
        theorem_id: answer.id,
        source_fingerprint: oeqSourceFingerprint(question as never),
      });
      expect(assembled.core.statements.some((s) => s.id === question.id)).toBe(false);
      expect(assembled.core.statements.some((s) => s.id === answer.id)).toBe(true);
    } finally {
      await h.dispose();
    }
  });

  it("also detaches an adjudicated dependency change", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await saveWorkingState(h.ctx(), {
        round: 3,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(proto as never, answer as never),
            node: answer as never,
            owner: question.id,
          },
        },
        resolved_oeqs: {
          [question.id]: {
            theorem_id: answer.id,
            source_fingerprint: oeqSourceFingerprint(question as never),
          },
        },
        proposals: {
          statements: [], definitions: [], assumptions: [], proofs: [],
          coreEdits: [{
            kind: "statement-replace", id: question.id,
            proposed: {
              ...question,
              depends_on: ["ass:overlap"],
              justification: "Updated motivation only.",
            },
            reason: "remove the procedure object from the question's mathematical scope",
            direction: "correct",
          }],
        },
      });

      await applyProposedChanges({ ctx: h.ctx() });

      const afterApply = await loadWorkingState(h.ctx());
      expect(afterApply?.resolved_oeqs?.[question.id]).toBeUndefined();
      expect(afterApply?.solved[answer.id]).toMatchObject({ proof_tex: answer.proof_tex });
      expect(afterApply?.solved[answer.id].partial).toBeUndefined();
    } finally {
      await h.dispose();
    }
  });

  it("reuses an identical carried answer theorem when the reopened OEQ emits it again", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await seedReopenedQuestion(h);

      await runStage0Solve({
        ctx: h.ctx(), state: h.state(),
        deps: resolutionSolver({ ...answer, justification: "New solver wording must not replace durable metadata." }),
      });

      const core = await h.readCore();
      expect(core.statements.filter((s) => s.id === answer.id)).toHaveLength(1);
      expect(core.statements.some((s) => s.id === question.id)).toBe(false);
      const working = await h.readWorking();
      expect(working.solved[answer.id]).toMatchObject({
        proof_tex: answer.proof_tex,
        node: { statement: answer.statement, status: "proved", justification: answer.justification },
      });
      expect(working.resolved_oeqs?.[question.id]).toMatchObject({ theorem_id: answer.id });

      const noRedispatch: StageDeps = {
        runCodex: async () => { throw new Error("an exact reused OEQ answer must persist without redispatch"); },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      };
      await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: noRedispatch });
      const retriedCore = await h.readCore();
      const retriedWorking = await h.readWorking();
      expect(retriedCore.statements.filter((s) => s.id === answer.id)).toHaveLength(1);
      expect(retriedCore.statements.some((s) => s.id === question.id)).toBe(false);
      expect(retriedWorking.resolved_oeqs?.[question.id]).toMatchObject({ theorem_id: answer.id });
    } finally {
      await h.dispose();
    }
  });

  it("still fails when a reused OEQ theorem id carries different mathematics", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await seedReopenedQuestion(h);
      const changed = { ...answer, statement: "A different obstruction theorem." };

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: resolutionSolver(changed),
      })).rejects.toThrow(/collides with non-identical existing node/);
      const working = await h.readWorking();
      expect(working.resolved_oeqs?.[question.id]).toBeUndefined();
      expect(working.solved[answer.id]).toMatchObject({ proof_tex: answer.proof_tex });
    } finally {
      await h.dispose();
    }
  });

  it("requires exact dependency order, status, and proof bytes for reuse", () => {
    const base = answer as never;
    expect(reusableOeqAnswerMatches(base, { ...answer, depends_on: ["ass:overlap", "def:procedure"] } as never)).toBe(false);
    expect(reusableOeqAnswerMatches(
      { ...answer, depends_on: ["ass:overlap", "def:procedure"] } as never,
      { ...answer, depends_on: ["def:procedure", "ass:overlap"] } as never,
    )).toBe(false);
    expect(reusableOeqAnswerMatches(base, { ...answer, status: "to-prove" } as never)).toBe(false);
    expect(reusableOeqAnswerMatches(base, { ...answer, proof_tex: `${answer.proof_tex} ` } as never)).toBe(false);
  });

  it("rejects an otherwise identical partial carried answer", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await seedReopenedQuestion(h);
      const working = await h.readWorking();
      working.solved[answer.id].partial = true;
      await saveWorkingState(h.ctx(), working);

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: resolutionSolver(answer),
      })).rejects.toThrow(/collides with non-identical existing node/);
    } finally {
      await h.dispose();
    }
  });

  it("rejects an identical frozen theorem that has no durable agent-node proof record", async () => {
    const frozenProto = { ...proto, statements: [question, answer] };
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto: frozenProto });
    try {
      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: resolutionSolver(answer),
      })).rejects.toThrow(/collides with non-identical existing node/);
    } finally {
      await h.dispose();
    }
  });

  it("rejects two OEQs claiming the same theorem id before applying either resolution", async () => {
    const secondQuestion = {
      ...question,
      id: "oeq:second-question",
      statement: "Can the second procedure attain uniform coverage?",
    };
    const twinProto = { ...proto, statements: [question, secondQuestion] };
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto: twinProto });
    try {
      const deps: StageDeps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
          const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
          const targets = JSON.parse(segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1)) as Array<{ id: string }>;
          await writeFile(outPath, JSON.stringify({
            proofs: [],
            resolved_oeqs: targets
              .filter((target) => target.id === question.id || target.id === secondQuestion.id)
              .map((target) => ({ source_id: target.id, theorem: answer })),
            added_lemmas: [], proposed_statement_changes: [], proposed_definition_changes: [],
            proposed_assumptions: [], proposed_core_edits: [], open_obligations: [],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      };

      await expect(runStage0Solve({ ctx: h.ctx(), state: h.state(), deps }))
        .rejects.toThrow(/multiple OEQ resolutions claiming theorem id/);
    } finally {
      await h.dispose();
    }
  });
});
