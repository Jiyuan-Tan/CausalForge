import { describe, it, expect } from "vitest";
import { writeFile } from "node:fs/promises";
import {
  applyProposedChanges,
  findUnsafeDeleteTextReferences,
} from "../../src/discovery/stages/d0_apply.js";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import {
  appendEscalationLog,
  loadWorkingState,
  saveWorkingState,
  snapshotMember,
  symbolBasis,
} from "../../src/discovery/stages/d0_working.js";
import {
  assembleSolveContext,
  oeqSourceFingerprint,
} from "../../src/discovery/solve/context.js";
import {
  pruneOrphanStatementNotes,
  removeAtomicallyDeletedOeqResolutionEdges,
  reusableOeqAnswerMatches,
} from "../../src/discovery/solve/merge.js";
import { createDStageHarness } from "./d_stage_harness.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { runStructuralGate } from "../../src/discovery/core/gate.js";
import type { CoreStatement } from "../../src/discovery/core/schema.js";

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

function resolutionSolver(emittedAnswer: object, proposedStatementChanges: object[] = []): StageDeps {
  let emittedResolution = false;
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = JSON.parse(segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1)) as Array<{ id: string }>;
      const resolvesQuestion = !emittedResolution && targets.some((target) => target.id === question.id);
      if (resolvesQuestion) emittedResolution = true;
      const targetIds = new Set(targets.map((target) => target.id));
      const statementChanges = (proposedStatementChanges as Array<{ id: string; proposed: string }>)
        .filter((change) => targetIds.has(change.id));
      await writeFile(outPath, JSON.stringify({
        proofs: targets
          .filter((target) => target.id !== question.id)
          .map((target) => ({
            id: target.id,
            proof_tex: target.id === answer.id ? answer.proof_tex : "QED.",
          })),
        resolved_oeqs: resolvesQuestion ? [{ source_id: question.id, theorem: emittedAnswer }] : [],
        added_lemmas: [],
        proposed_statement_changes: statementChanges,
        proposed_definition_changes: [],
        proposed_assumptions: [],
        proposed_core_edits: statementChanges.map((change) => {
          const prior = change.id === question.id ? question : emittedAnswer as Record<string, unknown>;
          const { proof_tex: _proof, source: _source, ...metadata } = prior as Record<string, unknown>;
          return {
            kind: "statement-replace",
            id: change.id,
            proposed: {
              ...metadata,
              id: change.id,
              statement: change.proposed,
              status: "to-prove",
              free_symbols: metadata.free_symbols ?? [],
            },
            reason: "synchronize the corrected claim metadata",
            direction: "correct",
          };
        }),
        open_obligations: [],
      }), "utf8");
      return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}

function recoveredSourceDeleteSolver(coreEdits: object[], targetId: string = question.id): StageDeps {
  let emitted = false;
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const targetBlock = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "")
        .split("SOLVE_OUTPUT_PATH")[0];
      const mine = targetBlock.includes(`"id": "${targetId}"`) && !emitted;
      if (mine) emitted = true;
      await writeFile(outPath, JSON.stringify({
        proofs: [], resolved_oeqs: [], added_lemmas: [],
        proposed_statement_changes: [], proposed_definition_changes: [],
        proposed_assumptions: [], proposed_core_edits: mine ? coreEdits : [],
        open_obligations: [],
      }), "utf8");
      return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}

function recoveredSourceMutationSolver(statementChanges: object[], coreEdits: object[]): StageDeps {
  let emitted = false;
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const targetBlock = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "")
        .split("SOLVE_OUTPUT_PATH")[0];
      const mine = targetBlock.includes(`"id": "${question.id}"`) && !emitted;
      if (mine) emitted = true;
      await writeFile(outPath, JSON.stringify({
        proofs: [], resolved_oeqs: [], added_lemmas: [],
        proposed_statement_changes: mine ? statementChanges : [],
        proposed_definition_changes: [], proposed_assumptions: [],
        proposed_core_edits: mine ? coreEdits : [], open_obligations: [],
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
  it("normalizes symbol refs through fresh resolution and restart", async () => {
    const symbolProto = structuredClone(proto) as any;
    symbolProto.symbols[0].ref = question.id;
    const symbolConsumer: CoreStatement = {
      id: "thm:symbol-only-consumer", kind: "theorem",
      statement: "The symbol-only consumer is valid at the current referent.",
      depends_on: [], free_symbols: ["tau"], status: "to-prove",
    };
    const directConsumer: CoreStatement = {
      id: "thm:direct-oeq-consumer", kind: "theorem",
      statement: "The direct consumer is valid at the resolved question answer.",
      depends_on: [question.id], free_symbols: [], status: "to-prove",
    };
    const agentConsumer: CoreStatement = {
      id: "lem:agent-direct-oeq-consumer", kind: "lemma",
      statement: "The agent-authored consumer is valid at the resolved question answer.",
      depends_on: [question.id], free_symbols: ["tau"], status: "proved",
      proof_tex: "Use the durable answer theorem.",
    };
    symbolProto.statements.push(symbolConsumer, directConsumer);
    const h = await createDStageHarness({
      qid: `${proto.qid}_symbol_ref`, specialization: "v1", proto: symbolProto,
    });
    try {
      await saveWorkingState(h.ctx(), {
        round: 1,
        symbol_basis: symbolBasis(symbolProto),
        solved: {
          [symbolConsumer.id]: {
            proof_tex: "Proof at the question referent.",
            snapshot: snapshotMember(symbolProto, symbolConsumer),
          },
          [directConsumer.id]: {
            proof_tex: "Proof using the question answer.",
            snapshot: snapshotMember(symbolProto, directConsumer),
          },
        },
        resolved_oeqs: {},
      });
      await runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: resolutionSolver(answer),
      });
      const rendered = await h.readCore();
      expect(rendered.symbols[0].ref).toBe(answer.id);
      expect(rendered.statements.find((statement: any) => statement.id === symbolConsumer.id)?.status)
        .toBe("to-prove");
      expect(runStructuralGate(rendered, { requireDischarged: false }).ok).toBe(true);

      const afterResolution = await h.readWorking();
      expect(afterResolution.solved[symbolConsumer.id]?.partial).toBe(true);
      expect(afterResolution.symbol_basis).toEqual(symbolBasis(
        symbolProto,
        Object.values(afterResolution.solved).flatMap((record: any) => record.node ? [record.node] : []),
        afterResolution.resolved_oeqs,
      ));

      const restarted = await assembleSolveContext({ ctx: h.ctx(), state: h.state() });
      expect(restarted.core.symbols[0].ref).toBe(answer.id);
      expect(runStructuralGate(restarted.core, { requireDischarged: false }).ok).toBe(true);

      // Once re-proved at the effective Q→T symbol basis, an unchanged restart
      // must not reopen the consumer one round late.
      const settled = await h.readWorking();
      settled.solved[symbolConsumer.id] = {
        proof_tex: "Proof at the answer referent.",
        snapshot: snapshotMember(symbolProto, symbolConsumer),
      };
      settled.solved[directConsumer.id] = {
        proof_tex: "Re-proved using the durable answer theorem.",
        snapshot: snapshotMember(symbolProto, directConsumer),
      };
      settled.solved[answer.id] = {
        proof_tex: answer.proof_tex,
        snapshot: snapshotMember(symbolProto, answer as never),
        node: answer as never,
        owner: question.id,
      };
      settled.solved[agentConsumer.id] = {
        proof_tex: "Use the durable answer theorem.",
        snapshot: snapshotMember(symbolProto, agentConsumer),
        node: agentConsumer,
        owner: agentConsumer.id,
      };
      settled.symbol_basis = symbolBasis(
        symbolProto,
        Object.values(settled.solved).flatMap((record: any) => record.node ? [record.node] : []),
        settled.resolved_oeqs,
      );
      await saveWorkingState(h.ctx(), settled);
      const stableRestart = await assembleSolveContext({ ctx: h.ctx(), state: h.state() });
      expect(stableRestart.validIds.has(symbolConsumer.id)).toBe(true);
      expect(stableRestart.validIds.has(directConsumer.id)).toBe(true);
      expect(stableRestart.validIds.has(agentConsumer.id)).toBe(true);
      expect(stableRestart.next.solved[agentConsumer.id]?.node?.depends_on).toEqual([answer.id]);
      expect(stableRestart.next.solved[agentConsumer.id]?.snapshot.depends_on).toEqual([answer.id]);
      expect(stableRestart.core.statements.find((statement) => statement.id === agentConsumer.id)?.depends_on)
        .toEqual([answer.id]);
      expect(runStructuralGate(stableRestart.core, { requireDischarged: false }).ok).toBe(true);
      expect(stableRestart.next.symbol_basis).toEqual(settled.symbol_basis);

      const dangling = structuredClone(rendered);
      dangling.symbols[0].ref = question.id;
      expect(runStructuralGate(dangling, { requireDischarged: false }).violations)
        .toContainEqual(expect.objectContaining({ code: "G1", where: "symbol:tau" }));
    } finally {
      await h.dispose();
    }
  });

  it("removes stale resolution edges when an OEQ source and answer are atomically deleted", () => {
    const resolved = {
      [question.id]: {
        theorem_id: answer.id,
        source_fingerprint: oeqSourceFingerprint(question as never),
      },
      "oeq:unrelated": { theorem_id: "thm:unrelated", source_fingerprint: "{}" },
    };

    removeAtomicallyDeletedOeqResolutionEdges(
      resolved,
      new Set([question.id, answer.id]),
    );

    expect(resolved).toEqual({
      "oeq:unrelated": { theorem_id: "thm:unrelated", source_fingerprint: "{}" },
    });
  });

  it("does not treat a deleted statement's own prose-note key as an inbound reference", () => {
    const working = {
      round: 1,
      solved: {},
      prose_overlay: {
        statement_notes: {
          [answer.id]: { justification: "This node is obsolete." },
        },
      },
    };

    expect(findUnsafeDeleteTextReferences(proto as never, working as never, answer.id)).toEqual([]);
  });

  it("restores an agent-authored source when its adjudicated answer theorem is deleted", async () => {
    const agentProto = {
      ...structuredClone(proto),
      statements: [],
      assumptions: [{ ...structuredClone(proto.assumptions[0]), used_by: [] }],
    };
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto: agentProto as never });
    try {
      const resolvedWorking = {
        round: 3,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(agentProto as never, answer as never),
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
        prose_overlay: {
          statement_notes: {
            [question.id]: { consumer: "Restore this note when the answer is deleted." },
          },
        },
        proposals: {
          statements: [], definitions: [], assumptions: [], proofs: [],
          coreEdits: [{
            kind: "statement-delete", id: answer.id,
            reason: "the proposed answer was rejected after review",
            direction: "delete-obsolete",
          }],
        },
      };
      // Simulate final-merge cleanup on a restarted resolved state. The agent
      // source is absent from proto and solved, but remains canonically recoverable.
      expect(pruneOrphanStatementNotes(agentProto as never, resolvedWorking as never)).toEqual([]);
      await saveWorkingState(h.ctx(), resolvedWorking as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const working = await h.readWorking();
      expect(working.solved[answer.id]).toBeUndefined();
      expect(working.resolved_oeqs?.[question.id]).toBeUndefined();
      expect(working.solved[question.id]).toMatchObject({
        partial: true,
        proof_tex: "",
        node: {
          id: question.id,
          kind: "openendedquestion",
          statement: question.statement,
          // Spread: the fixture is `as const`, so `depends_on` is a readonly tuple and
          // `arrayContaining` takes a mutable `unknown[]`.
          depends_on: expect.arrayContaining([...question.depends_on]),
          status: "to-prove",
        },
      });
      expect(working.sealed_open_oeqs?.[question.id]).toBe(oeqSourceFingerprint(question as never));
      expect(working.prose_overlay?.statement_notes?.[question.id]).toEqual({
        consumer: "Restore this note when the answer is deleted.",
      });

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(),
        deps: {
          runCodex: async () => { throw new Error("a sealed residual OEQ must not be redispatched"); },
          runClaude: async () => { throw new Error("unused"); },
          lean: undefined as never,
        },
      })).resolves.toBeDefined();
      expect((await h.readWorking()).sealed_open_oeqs?.[question.id])
        .toBe(oeqSourceFingerprint(question as never));
      expect((await h.readWorking()).prose_overlay?.statement_notes?.[question.id]).toEqual({
        consumer: "Restore this note when the answer is deleted.",
      });
    } finally {
      await h.dispose();
    }
  });

  it("explicitly deletes a canonically recovered agent-OEQ source and its note", async () => {
    const agentProto = {
      ...structuredClone(proto), statements: [],
      assumptions: [{ ...structuredClone(proto.assumptions[0]), used_by: [] }],
    };
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto: agentProto as never });
    try {
      await saveWorkingState(h.ctx(), {
        round: 3,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(agentProto as never, answer as never),
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
        prose_overlay: {
          statement_notes: { [question.id]: { consumer: "Retire with the source." } },
        },
        proposals: {
          statements: [], definitions: [], assumptions: [], proofs: [],
          coreEdits: [{
            kind: "statement-delete", id: question.id,
            reason: "the residual question is no longer in scope", direction: "delete-obsolete",
          }],
        },
      });

      await expect(applyProposedChanges({ ctx: h.ctx(), checkOnly: true })).resolves.toBeDefined();
      await applyProposedChanges({ ctx: h.ctx() });

      const working = await h.readWorking();
      expect(working.resolved_oeqs?.[question.id]).toBeUndefined();
      expect(working.prose_overlay?.statement_notes?.[question.id]).toBeUndefined();
      expect(working.solved[answer.id]?.node?.id).toBe(answer.id);
      expect(working.solved[question.id]).toBeUndefined();
    } finally {
      await h.dispose();
    }
  });

  it("atomically deletes a recovered agent-OEQ source before its answer", async () => {
    const agentProto = {
      ...structuredClone(proto), statements: [],
      assumptions: [{ ...structuredClone(proto.assumptions[0]), used_by: [] }],
    };
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto: agentProto as never });
    try {
      await saveWorkingState(h.ctx(), {
        round: 3,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(agentProto as never, answer as never),
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
        prose_overlay: {
          statement_notes: {
            [question.id]: { consumer: "Retire with the source." },
            [answer.id]: { consumer: "Retire with the answer." },
          },
        },
        proposals: {
          statements: [], definitions: [], assumptions: [], proofs: [],
          coreEdits: [
            {
              kind: "statement-delete", id: question.id,
              reason: "retire the source first", direction: "delete-obsolete",
            },
            {
              kind: "statement-delete", id: answer.id,
              reason: "retire its answer second", direction: "delete-obsolete",
            },
          ],
        },
      });

      await expect(applyProposedChanges({ ctx: h.ctx(), checkOnly: true })).resolves.toBeDefined();
      await applyProposedChanges({ ctx: h.ctx() });

      const working = await h.readWorking();
      expect(working.resolved_oeqs?.[question.id]).toBeUndefined();
      expect(working.solved[question.id]).toBeUndefined();
      expect(working.solved[answer.id]).toBeUndefined();
      expect(working.prose_overlay?.statement_notes?.[question.id]).toBeUndefined();
      expect(working.prose_overlay?.statement_notes?.[answer.id]).toBeUndefined();
    } finally {
      await h.dispose();
    }
  });

  it("carries recovered-source deletions through solve checkpoint, preview, commit, and restart", async () => {
    const sourceDelete = {
      kind: "statement-delete", id: question.id,
      reason: "retire the recovered question", direction: "delete-obsolete",
    };
    const answerDelete = {
      kind: "statement-delete", id: answer.id,
      reason: "retire its answer", direction: "delete-obsolete",
    };
    const cases = [
      { name: "source-only", edits: [sourceDelete], deletesAnswer: false },
      { name: "source-first", edits: [sourceDelete, answerDelete], deletesAnswer: true },
      { name: "answer-first", edits: [answerDelete, sourceDelete], deletesAnswer: true },
    ];
    const terminalDeleteStates = new Map<string, unknown>();
    for (const testCase of cases) {
      const agentProto = {
        ...structuredClone(proto), statements: [],
        assumptions: [{ ...structuredClone(proto.assumptions[0]), used_by: [] }],
      };
      const h = await createDStageHarness({
        qid: `${proto.qid}_${testCase.name}`, specialization: "v1", proto: agentProto as never,
      });
      try {
        await saveWorkingState(h.ctx(), {
          round: 3,
          solved: {
            [answer.id]: {
              proof_tex: answer.proof_tex,
              snapshot: snapshotMember(agentProto as never, answer as never),
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
          prose_overlay: {
            statement_notes: {
              [question.id]: { consumer: "Retire with the source." },
              [answer.id]: { consumer: "Retire with the answer if selected." },
            },
          },
        });
        await appendEscalationLog(h.ctx(), {
          round: 3,
          changed: [],
          directive: `apply the ${testCase.name} recovered-source deletion transaction`,
          required_core_targets: [question.id],
          require_core_changes: true,
        });

        await expect(runStage0Solve({
          ctx: h.ctx(), state: h.state(), deps: recoveredSourceDeleteSolver(testCase.edits),
        })).resolves.toMatchObject({ status: "checkpoint", advance: false });
        const checkpoint = await h.readWorking();
        expect(checkpoint.proposals?.coreEdits).toEqual(expect.arrayContaining(testCase.edits));

        await expect(applyProposedChanges({ ctx: h.ctx(), checkOnly: true })).resolves.toBeDefined();
        await applyProposedChanges({ ctx: h.ctx() });
        const restarted = await loadWorkingState(h.ctx());
        expect(restarted?.resolved_oeqs?.[question.id]).toBeUndefined();
        expect(restarted?.sealed_open_oeqs?.[question.id]).toBeUndefined();
        expect(restarted?.prose_overlay?.statement_notes?.[question.id]).toBeUndefined();
        if (testCase.deletesAnswer) {
          expect(restarted?.solved[answer.id]).toBeUndefined();
          expect(restarted?.prose_overlay?.statement_notes?.[answer.id]).toBeUndefined();
        } else {
          expect(restarted?.solved[answer.id]?.node?.id).toBe(answer.id);
        }
        if (testCase.deletesAnswer) {
          terminalDeleteStates.set(testCase.name, {
            solved: restarted?.solved,
            resolved_oeqs: restarted?.resolved_oeqs,
            sealed_open_oeqs: restarted?.sealed_open_oeqs,
            statement_notes: restarted?.prose_overlay?.statement_notes,
          });
        }
      } finally {
        await h.dispose();
      }
    }
    expect(terminalDeleteStates.get("answer-first")).toEqual(terminalDeleteStates.get("source-first"));
  });

  it("uses a recovered agent OEQ as a surviving replacement endpoint end-to-end", async () => {
    const agentProto = {
      ...structuredClone(proto), statements: [],
      assumptions: [{ ...structuredClone(proto.assumptions[0]), used_by: [] }],
    };
    const retired = {
      id: "lem:retired-agent-node", kind: "lemma",
      statement: "A retired helper is superseded by the residual question.",
      depends_on: [], status: "proved", proof_tex: "Old proof.",
    } as const;
    const consumer = {
      id: "lem:carried-consumer", kind: "lemma",
      statement: "The carried consumer uses the retired helper.",
      depends_on: [retired.id], status: "proved", proof_tex: "Consumer proof.",
    } as const;
    const h = await createDStageHarness({ qid: `${proto.qid}_replacement`, specialization: "v1", proto: agentProto as never });
    try {
      await saveWorkingState(h.ctx(), {
        round: 3,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(agentProto as never, answer as never),
            node: answer as never,
            owner: question.id,
          },
          [retired.id]: {
            proof_tex: retired.proof_tex,
            snapshot: snapshotMember(agentProto as never, retired as never),
            node: retired as never,
            owner: retired.id,
          },
          [consumer.id]: {
            proof_tex: consumer.proof_tex,
            snapshot: snapshotMember(agentProto as never, consumer as never),
            node: consumer as never,
            owner: consumer.id,
          },
        },
        resolved_oeqs: {
          [question.id]: {
            theorem_id: answer.id,
            source_fingerprint: oeqSourceFingerprint(question as never),
          },
        },
      });
      await appendEscalationLog(h.ctx(), {
        round: 3, changed: [], directive: "supersede the retired helper by the recovered question",
        required_core_targets: [retired.id], require_core_changes: true,
      });
      const edit = {
        kind: "statement-delete", id: retired.id, replacement_id: question.id,
        reason: "the recovered question is the surviving endpoint", direction: "delete-obsolete",
      };

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: recoveredSourceDeleteSolver([edit], retired.id),
      })).resolves.toMatchObject({ status: "checkpoint", advance: false });
      await expect(applyProposedChanges({ ctx: h.ctx(), checkOnly: true })).resolves.toBeDefined();
      await applyProposedChanges({ ctx: h.ctx() });

      const restarted = await loadWorkingState(h.ctx());
      expect(restarted?.solved[retired.id]).toBeUndefined();
      expect(restarted?.resolved_oeqs?.[question.id]).toMatchObject({ theorem_id: answer.id });
      expect(restarted?.solved[consumer.id]?.node?.depends_on).toEqual([answer.id]);
      const assembled = await assembleSolveContext({ ctx: h.ctx(), state: h.state() });
      expect(assembled.core.statements.find((statement) => statement.id === consumer.id)?.depends_on)
        .toEqual([answer.id]);
    } finally {
      await h.dispose();
    }
  });

  it("merge restores an answer-deleted agent OEQ before later definition applicability", async () => {
    const agentProto = {
      ...structuredClone(proto), statements: [],
      assumptions: [{ ...structuredClone(proto.assumptions[0]), used_by: [] }],
    };
    const h = await createDStageHarness({ qid: `${proto.qid}_answer_def`, specialization: "v1", proto: agentProto as never });
    try {
      await saveWorkingState(h.ctx(), {
        round: 3,
        solved: {
          [answer.id]: {
            proof_tex: answer.proof_tex,
            snapshot: snapshotMember(agentProto as never, answer as never),
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
      });
      await appendEscalationLog(h.ctx(), {
        round: 3, changed: [], directive: "delete the rejected answer but retain its live source dependencies",
        required_core_targets: [answer.id], require_core_changes: true,
      });
      const answerDelete = {
        kind: "statement-delete", id: answer.id,
        reason: "reject the answer", direction: "delete-obsolete",
      };
      const definitionDelete = {
        kind: "definition-delete", id: "def:procedure",
        reason: "incorrectly assumed unused", direction: "delete-obsolete",
      };

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(),
        deps: recoveredSourceDeleteSolver([answerDelete, definitionDelete], answer.id),
      })).resolves.toMatchObject({ status: "checkpoint", advance: false });
      const checkpoint = await h.readWorking();
      expect(checkpoint.proposals?.coreEdits).toContainEqual(answerDelete);
      expect(checkpoint.proposals?.coreEdits).not.toContainEqual(definitionDelete);

      await expect(applyProposedChanges({ ctx: h.ctx(), checkOnly: true })).resolves.toBeDefined();
      await applyProposedChanges({ ctx: h.ctx() });
      const restarted = await loadWorkingState(h.ctx());
      expect(restarted?.solved[question.id]?.node?.depends_on).toContain("def:procedure");
      const frozen = await h.readProto();
      expect(frozen.definitions.some((definition: any) => definition.id === "def:procedure")).toBe(true);
    } finally {
      await h.dispose();
    }
  });

  it("materializes and detaches recovered agent OEQs before claim or dependency mutation", async () => {
    const cases = [
      {
        name: "claim",
        statement: "Can the procedure attain uniform coverage alone?",
        dependsOn: [...question.depends_on],
        changes: [{
          id: question.id, current: question.statement,
          proposed: "Can the procedure attain uniform coverage alone?",
          reason: "narrow the recovered residual", direction: "narrow",
        }],
      },
      {
        name: "dependency",
        statement: question.statement,
        dependsOn: ["ass:overlap"],
        changes: [],
      },
    ];
    for (const testCase of cases) {
      const agentProto = {
        ...structuredClone(proto), statements: [],
        assumptions: [{ ...structuredClone(proto.assumptions[0]), used_by: [] }],
      };
      const h = await createDStageHarness({
        qid: `${proto.qid}_mutate_${testCase.name}`, specialization: "v1", proto: agentProto as never,
      });
      try {
        await saveWorkingState(h.ctx(), {
          round: 3,
          solved: {
            [answer.id]: {
              proof_tex: answer.proof_tex,
              snapshot: snapshotMember(agentProto as never, answer as never),
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
        });
        await appendEscalationLog(h.ctx(), {
          round: 3, changed: [], directive: `apply recovered-source ${testCase.name} mutation`,
          required_core_targets: [question.id], require_core_changes: true,
        });
        const replacement = {
          kind: "statement-replace", id: question.id,
          proposed: {
            id: question.id, kind: "openendedquestion", statement: testCase.statement,
            depends_on: testCase.dependsOn, status: "to-prove", free_symbols: [],
          },
          reason: `synchronize the recovered ${testCase.name} postimage`, direction: "correct",
        };

        await expect(runStage0Solve({
          ctx: h.ctx(), state: h.state(),
          deps: recoveredSourceMutationSolver(testCase.changes, [replacement]),
        })).resolves.toMatchObject({ status: "checkpoint", advance: false });
        await expect(applyProposedChanges({ ctx: h.ctx(), checkOnly: true })).resolves.toBeDefined();
        await applyProposedChanges({ ctx: h.ctx() });

        const restarted = await loadWorkingState(h.ctx());
        expect(restarted?.resolved_oeqs?.[question.id]).toBeUndefined();
        expect(restarted?.solved[answer.id]?.node?.id).toBe(answer.id);
        expect(restarted?.solved[question.id]).toMatchObject({
          partial: true,
          node: { statement: testCase.statement, depends_on: testCase.dependsOn, status: "to-prove" },
        });
        const assembled = await assembleSolveContext({ ctx: h.ctx(), state: h.state() });
        expect(assembled.core.statements.find((statement) => statement.id === question.id)).toMatchObject({
          statement: testCase.statement, depends_on: testCase.dependsOn, status: "to-prove",
        });
        expect(assembled.core.statements.find((statement) => statement.id === answer.id)?.proof_tex)
          .toBe(answer.proof_tex);
      } finally {
        await h.dispose();
      }
    }
  });

  it("detaches an accepted claim correction while preserving the old answer theorem and proof", async () => {
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
            direction: "correct",
          }],
          definitions: [], assumptions: [], proofs: [],
          coreEdits: [{
            kind: "statement-replace",
            id: question.id,
            proposed: {
              ...question,
              statement: "Can the procedure attain uniform coverage?",
            },
            reason: "synchronize the narrowed question's complete post-image",
            direction: "correct",
          }],
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

  it("accepts an identical OEQ answer re-derived over its stale open projection", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await seedReopenedQuestion(h);
      const changedProto = structuredClone(proto);
      changedProto.assumptions[0].condition =
        "the propensity is bounded away from zero and one by a revised constant";
      await h.writeProto(changedProto as never);

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: resolutionSolver(answer),
      })).resolves.toBeDefined();

      const working = await h.readWorking();
      expect(working.solved[answer.id]).toMatchObject({
        proof_tex: answer.proof_tex,
        node: { statement: answer.statement, status: "proved" },
      });
      expect(working.solved[answer.id].partial).toBeUndefined();
      expect(working.resolved_oeqs?.[question.id]).toMatchObject({ theorem_id: answer.id });
    } finally {
      await h.dispose();
    }
  });

  // REGRESSION. The solver may re-emit a resolution WITHOUT a duplicate `proofs[]` entry
  // for the answer id — the schema and prompt both allow it (only a proof on the SOURCE id
  // is forbidden). Every other test here happens to emit one, so the proof lands via the
  // ordinary proof path and the resolution INSTALLER is never exercised. Without it, the
  // installer saw the id already present (as the open projection), took the
  // exact-re-emission no-op branch, and discarded the proved answer: the core kept the
  // `to-prove` placeholder and the emitted proof bytes were persisted nowhere.
  it("installs a re-derived answer over its open projection when no duplicate proof is emitted", async () => {
    const resolutionOnlySolver = (): StageDeps => ({
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
        const targets = JSON.parse(segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1)) as Array<{ id: string }>;
        await writeFile(outPath, JSON.stringify({
          // Deliberately NO proofs[] entry for the answer id.
          proofs: targets
            .filter((target) => target.id !== question.id && target.id !== answer.id)
            .map((target) => ({ id: target.id, proof_tex: "QED." })),
          resolved_oeqs: targets.some((target) => target.id === question.id)
            ? [{ source_id: question.id, theorem: answer }]
            : [],
          added_lemmas: [],
          proposed_statement_changes: [], proposed_definition_changes: [],
          proposed_assumptions: [], proposed_core_edits: [], open_obligations: [],
        }), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    });

    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await seedReopenedQuestion(h);
      const changedProto = structuredClone(proto);
      changedProto.assumptions[0].condition =
        "the propensity is bounded away from zero and one by a revised constant";
      await h.writeProto(changedProto as never);

      await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: resolutionOnlySolver() });

      // The proved answer must REPLACE the open projection in the durable core...
      const core = await h.readCore();
      const installed = core.statements.find((s) => s.id === answer.id);
      expect(installed).toMatchObject({ statement: answer.statement, status: "proved" });
      // ...and the working cursor must carry it as settled, not partial.
      const working = await h.readWorking();
      expect(working.solved[answer.id].partial).toBeUndefined();
      expect(working.solved[answer.id].proof_tex).toBe(answer.proof_tex);
      expect(working.resolved_oeqs?.[question.id]).toMatchObject({ theorem_id: answer.id });
    } finally {
      await h.dispose();
    }
  });

  it("gates a proposal-backed OEQ answer cleanup before installing the new text", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await seedReopenedQuestion(h);
      const changedProto = structuredClone(proto);
      changedProto.assumptions[0].condition =
        "the propensity is bounded away from zero and one by a revised constant";
      await h.writeProto(changedProto as never);
      const cleaned = { ...answer, statement: "Uniform root-n local power fails on the tie subexperiment (clean rendering)." };
      const change = {
        id: answer.id,
        current: answer.statement,
        proposed: cleaned.statement,
        reason: "remove serialization debris without changing the claim",
        direction: "narrow",
      };

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: resolutionSolver(cleaned, [change]),
      })).resolves.toBeDefined();

      const working = await h.readWorking();
      expect(working.proposals?.statements).toEqual([expect.objectContaining(change)]);
      // The unadjudicated overlay is not installed merely because the resolution
      // theorem re-emitted it; apply owns that transition after review.
      expect(working.solved[answer.id].node?.statement).toBe(answer.statement);
    } finally {
      await h.dispose();
    }
  });

  it("withholds a reused OEQ theorem id carrying different mathematics", async () => {
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto });
    try {
      await seedReopenedQuestion(h);
      const changed = { ...answer, statement: "A different obstruction theorem." };

      await expect(runStage0Solve({
        ctx: h.ctx(), state: h.state(), deps: resolutionSolver(changed),
      })).resolves.toMatchObject({ status: "checkpoint", advance: false });
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
    expect(reusableOeqAnswerMatches(base, { ...answer, free_symbols: [] } as never)).toBe(false);
    expect(reusableOeqAnswerMatches(base, { ...answer, route: "substituted route" } as never)).toBe(false);
    expect(reusableOeqAnswerMatches(base, { ...answer, consumer: "ignored recovery wording" } as never)).toBe(true);
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

  it("withholds two OEQs claiming the same theorem id without aborting the round", async () => {
    const secondQuestion = {
      ...question,
      id: "oeq:second-question",
      statement: "Can the second procedure attain uniform coverage?",
    };
    const twinProto = { ...proto, statements: [question, secondQuestion] };
    const h = await createDStageHarness({ qid: proto.qid, specialization: "v1", proto: twinProto });
    try {
      await appendEscalationLog(h.ctx(), {
        round: 1,
        changed: [],
        directive: "resolve both questions without choosing between contested answer transactions",
        require_core_changes: true,
        required_core_targets: [question.id, secondQuestion.id],
      });
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

      const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps });
      expect(result).toHaveProperty("status", "checkpoint");
      const core = await h.readCore();
      expect(core.statements.filter((statement) =>
        statement.id === question.id || statement.id === secondQuestion.id
      )).toHaveLength(2);
      expect(core.statements.some((statement) => statement.id === answer.id)).toBe(false);
      const working = await h.readWorking();
      expect(working.resolved_oeqs ?? {}).toEqual({});
      expect(working.escalation_entries_consumed ?? 0).toBe(0);
    } finally {
      await h.dispose();
    }
  });
});
