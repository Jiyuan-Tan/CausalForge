import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { authorMetadataEdits } from "../../src/discovery/stages/d0_author_edits.js";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import {
  readEscalationLog,
  saveWorkingState,
  snapshotMember,
  workingPath,
} from "../../src/discovery/stages/d0_working.js";
import { loadState, saveState } from "../../src/state.js";
import { oeqSourceFingerprint } from "../../src/discovery/solve/oeq_source.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { StateJson } from "../../src/types.js";
import { createDStageHarness } from "./d_stage_harness.js";

const MAIN = {
  id: "thm:main", kind: "theorem", statement: "The estimand is identified.",
  depends_on: ["ass:overlap"], free_symbols: ["tau"], status: "to-prove",
  justification: "old justification", gap: "old gap", consumer: "old consumer",
};
const CITED = {
  id: "lem:cited", kind: "lemma", statement: "A borrowed inequality.", depends_on: [], free_symbols: [],
  status: "cited", source: { cite: "R1983", locator: "Theorem 1" },
  justification: "cited j", gap: "cited gap", consumer: "thm:main",
};
const HELPER = {
  id: "lem:helper", kind: "lemma", statement: "A helper bound.", depends_on: ["ass:overlap"], free_symbols: [],
  status: "proved", proof_tex: "Direct.", justification: "helper j", gap: "helper gap", consumer: "thm:main",
};
const PROTO = {
  qid: "stat_author_edits", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal parameter", def: "E[Y(1)-Y(0)]", role: "target" }],
  assumptions: [{
    id: "ass:overlap", condition: "positivity holds", free_symbols: [],
    standard: { name: "overlap", cite: "R1983" },
  }],
  definitions: [], statements: [MAIN], target_estimand: "tau",
  bibliography: [{ key: "R1983", citation: "Rosenbaum and Rubin (1983)" }],
};
/** Same paper with a frozen cited leaf (a cited leaf with no working record is itself a D0 target). */
const PROTO_CITED = { ...PROTO, statements: [MAIN, CITED] };

/** thm:main proved (frozen node, record without `node`); lem:helper agent-authored (record with `node`). */
function provedWorking(proto: typeof PROTO, extra: Record<string, unknown> = {}) {
  return {
    round: 2,
    solved: {
      [MAIN.id]: { proof_tex: "Immediate from overlap.", snapshot: snapshotMember(proto as never, MAIN as never) },
      [HELPER.id]: { proof_tex: HELPER.proof_tex, snapshot: snapshotMember(proto as never, HELPER as never), node: HELPER },
    },
    resolved_oeqs: {},
    ...extra,
  };
}

const replace = (node: Record<string, unknown>, overrides: Record<string, unknown>) => {
  const { proof_tex: _proof, ...echo } = node; // the channel never carries proof bytes
  return { kind: "statement-replace", id: node.id, reason: "positioning", direction: "correct", proposed: { ...echo, ...overrides } };
};
/** Payload that supplies ONLY the given prose fields (everything else echoed, prose omitted). */
const replaceProse = (node: Record<string, unknown>, prose: Record<string, string>) => {
  const { proof_tex: _proof, justification: _j, gap: _g, consumer: _c, ...echo } = node;
  return { kind: "statement-replace", id: node.id, reason: "positioning", direction: "correct", proposed: { ...echo, ...prose } };
};
const replaceMain = (overrides: Record<string, unknown>) => {
  const { ...frozen } = MAIN;
  return replace(frozen, overrides);
};

/** The harness state stub is in-memory only; persist a schema-valid state.json so the
 * "stage pointer not rewound" assertion exercises apply's real state path. */
const persistableState = (h: { state(): StateJson }): StateJson => ({
  ...h.state(),
  proposed_from: {
    topic: "t", novelty_target: "field", pivot_budget_used: 0, final_verdict: "ACCEPT",
    proposal_path: "p", novelty_justification: "j", chosen_qid: PROTO.qid, chosen_specialization: "v1",
  },
} as unknown as StateJson);

const forbiddenSolver: StageDeps = {
  runCodex: async ({ prompt }: { prompt: string }) => {
    const seg = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "").slice(0, 400).replace(/\s+/g, " ");
    throw new Error(`runCodex must not be called after a metadata-only edit; dispatched: ${seg}`);
  },
  runClaude: async () => { throw new Error("unused"); },
  lean: undefined as never,
};

/** Every working record byte-identical except justification/gap/consumer inside `node`. */
function stripNodeProse(record: unknown): unknown {
  const copy = structuredClone(record) as { node?: Record<string, unknown> };
  if (copy?.node) for (const f of ["justification", "gap", "consumer"]) delete copy.node[f];
  return copy;
}
function expectRecordsMovedOnlyInProse(before: Record<string, unknown>, after: Record<string, unknown>): void {
  expect(Object.keys(after).sort()).toEqual(Object.keys(before).sort());
  for (const id of Object.keys(before)) {
    expect(stripNodeProse(after[id]), `record ${id} moved beyond prose`).toEqual(stripNodeProse(before[id]));
  }
}

describe("d0_author_edits — orchestrator-authored statement prose (no rewind, no reopen, no waste)", () => {
  it("lands a justification-only edit on a frozen node: proto + core.json updated, nothing else moves", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
    try {
      await saveWorkingState(h.ctx(), provedWorking(PROTO) as never);
      await saveState(h.repoRoot, PROTO.qid, "v1", persistableState(h));
      const discoveryDir = path.dirname(coreJsonPath(h.ctx()));
      const obligationsPath = path.join(discoveryDir, "open_obligations.json");
      await writeFile(obligationsPath, "[]", "utf8");
      await writeFile(coreJsonPath(h.ctx()), JSON.stringify({ stale: true }), "utf8");
      const workingBefore = JSON.parse(await readFile(workingPath(h.ctx()), "utf8"));

      const changed = await authorMetadataEdits({
        ctx: h.ctx(), note: "fix positioning", edits: [replaceMain({ justification: "new justification" })],
      });
      expect(changed.map((c) => `${c.kind}:${c.id}`)).toEqual([`statement:${MAIN.id}`]);

      const main = (await h.readProto()).statements.find((s) => s.id === MAIN.id)!;
      expect(main.justification).toBe("new justification");
      expect(main.statement).toBe(MAIN.statement);
      const working = await h.readWorking();
      expectRecordsMovedOnlyInProse(workingBefore.solved, working.solved as Record<string, unknown>);
      expect(working.solved[MAIN.id]).toEqual(workingBefore.solved[MAIN.id]); // frozen record: byte-identical
      expect(working.round).toBe(workingBefore.round);
      expect(working.proposals?.coreEdits ?? []).toEqual([]);
      expect((await loadState(h.repoRoot, PROTO.qid, "v1")).stage_completed).toBe(h.state().stage_completed);
      expect(existsSync(obligationsPath)).toBe(true);
      const rendered = (await h.readCore()).statements.find((s) => s.id === MAIN.id)!;
      expect(rendered.justification).toBe("new justification");
      expect(rendered.status).toBe("proved");
      const entry = (await readEscalationLog(h.ctx())).at(-1)!;
      expect(entry.note).toMatch(/^orchestrator-authored metadata edit: fix positioning/);
      expect(entry.provenance_only).toBe(true);
      expect(entry.directive).toBeUndefined();
      const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: forbiddenSolver });
      expect(String((result as { message?: string }).message)).toMatch(/across 0 dispatched unit\(s\)/);
      expectRecordsMovedOnlyInProse(workingBefore.solved, (await h.readWorking()).solved as Record<string, unknown>);
    } finally { await h.dispose(); }
  }, 30000);

  it("an agent-authored node's record changes only in node prose, and an existing overlay note is synced", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
    try {
      await saveWorkingState(h.ctx(), provedWorking(PROTO, {
        prose_overlay: { statement_notes: { [HELPER.id]: { gap: "overlay gap", consumer: "overlay consumer" } } },
      }) as never);
      const workingBefore = JSON.parse(await readFile(workingPath(h.ctx()), "utf8"));
      await authorMetadataEdits({ ctx: h.ctx(), note: "helper gap", edits: [replaceProse(HELPER, { gap: "authored gap" })] });
      const working = await h.readWorking();
      expectRecordsMovedOnlyInProse(workingBefore.solved, working.solved as Record<string, unknown>);
      expect((working.solved[HELPER.id] as { node?: { gap?: string } }).node?.gap).toBe("authored gap");
      // Overlay: exactly the SUPPLIED field is synced, unsupplied fields survive, no entry created for thm:main.
      expect(working.prose_overlay?.statement_notes?.[HELPER.id]).toEqual({ gap: "authored gap", consumer: "overlay consumer" });
      expect(working.prose_overlay?.statement_notes?.[MAIN.id]).toBeUndefined();
      // Rendered core shows the authored text (would have shown "overlay gap" without the sync).
      expect((await h.readCore()).statements.find((s) => s.id === HELPER.id)?.gap).toBe("authored gap");
      // A STALE overlay is overwritten even when the node already carries the authored value.
      const stale = await h.readWorking();
      stale.prose_overlay = { statement_notes: { [HELPER.id]: { gap: "stale overlay", consumer: "overlay consumer" } } };
      await saveWorkingState(h.ctx(), stale);
      await authorMetadataEdits({ ctx: h.ctx(), note: "re-assert", edits: [replaceProse({ ...HELPER, gap: "authored gap" }, { gap: "authored gap" })] });
      expect((await h.readWorking()).prose_overlay?.statement_notes?.[HELPER.id]).toEqual({ gap: "authored gap", consumer: "overlay consumer" });
      expect((await h.readCore()).statements.find((s) => s.id === HELPER.id)?.gap).toBe("authored gap");
    } finally { await h.dispose(); }
  }, 30000);

  it("refuses every proof-relevant or non-prose edit, cited leaves, and partial records; mutates nothing", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO_CITED });
    try {
      await saveWorkingState(h.ctx(), provedWorking(PROTO_CITED) as never);
      const before = await readFile(workingPath(h.ctx()), "utf8");
      const cases: Array<[string, unknown, RegExp]> = [
        ["claim text", replaceMain({ statement: "A stronger claim." }), /statement.*d0_directive/],
        ["depends_on", replaceMain({ depends_on: [] }), /depends_on/],
        ["free_symbols", replaceMain({ free_symbols: [] }), /free_symbols/],
        ["route", replaceMain({ route: "a different proof route" }), /route/],
        ["cited leaf", replace(CITED, { gap: "new gap" }), /cited leaf.*d0_directive/],
        ["symbol", { kind: "symbol-replace", name: "tau", reason: "r", proposed: { ...PROTO.symbols[0], role: "x" } }, /symbol-basis.*d0_directive/],
        ["bibliography", { kind: "bibliography-replace", key: "R1983", reason: "r", proposed: { key: "R1983", citation: "x" } }, /citation string.*d0_directive/],
        ["comparator table", { kind: "comparator-promise-table-replace", id: "metadata:comparator-promise-table", reason: "r", proposed: [] }, /positioning.*d0_directive/],
        ["definition-replace", { kind: "definition-replace", id: "def:x", reason: "r", proposed: { id: "def:x", construction: "x" } }, /solver-owned.*d0_directive/],
        ["statement-delete", { kind: "statement-delete", id: MAIN.id, reason: "r" }, /solver-owned.*d0_directive/],
      ];
      for (const [label, edit, pattern] of cases) {
        await expect(authorMetadataEdits({ ctx: h.ctx(), note: label, edits: [edit] }), label).rejects.toThrow(pattern);
      }
      expect(await readFile(workingPath(h.ctx()), "utf8"), "refusals mutate nothing").toBe(before);
      expect((await h.readProto()).statements[0].justification).toBe("old justification");
      expect((await readEscalationLog(h.ctx())).length).toBe(0);
      expect(existsSync(coreJsonPath(h.ctx()))).toBe(false);

      // Partial (reopened) record: refused at compose.
      const partial = provedWorking(PROTO_CITED);
      (partial.solved[MAIN.id] as Record<string, unknown>).partial = true;
      await saveWorkingState(h.ctx(), partial as never);
      await expect(
        authorMetadataEdits({ ctx: h.ctx(), note: "p", edits: [replaceMain({ gap: "g" })] }),
      ).rejects.toThrow(/partial/);
    } finally { await h.dispose(); }
  }, 30000);

  it("apply-side invariant: a prose edit that would settle a shelved partial cited leaf is refused even when compose is bypassed", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
    try {
      // An AGENT-authored cited leaf carried as shelved partial debt: apply's cited shortcut
      // would otherwise adopt the composed node and `delete carried.partial`.
      const agentCited = { ...CITED, id: "lem:agent-cited" };
      const working = provedWorking(PROTO, {
        solved: {
          [MAIN.id]: { proof_tex: "Immediate from overlap.", snapshot: snapshotMember(PROTO as never, MAIN as never) },
          [agentCited.id]: {
            proof_tex: "", snapshot: snapshotMember(PROTO as never, agentCited as never),
            node: agentCited, partial: true, shelved: true,
          },
        },
      });
      await saveWorkingState(h.ctx(), working as never);
      const before = await readFile(workingPath(h.ctx()), "utf8");
      const bundle = {
        statements: [], definitions: [], assumptions: [], proofs: [], citationRevalidations: [],
        coreEdits: [{ kind: "statement-replace", id: agentCited.id, reason: "gap", direction: "correct", proposed: { ...agentCited, gap: "new gap" } }],
      };
      for (const checkOnly of [true, false]) {
        await expect(applyProposedChanges({
          ctx: h.ctx(), ids: null, note: "bypass", authoredMetadataOnly: true, proposalsOverride: bundle as never, checkOnly,
        }), `checkOnly=${checkOnly}`).rejects.toThrow(/beyond prose|prose edits only/);
      }
      expect(await readFile(workingPath(h.ctx()), "utf8")).toBe(before);
      expect((await h.readWorking()).solved[agentCited.id]?.partial).toBe(true);
    } finally { await h.dispose(); }
  }, 30000);

  it("seeds non-prose fields from the proto carrier, not the re-wired render (consumer of an answered OEQ)", async () => {
    const QUESTION = { id: "oeq:q", kind: "openendedquestion", statement: "What is the rate?", depends_on: ["ass:overlap"], free_symbols: [], status: "to-prove", justification: "q", gap: "q", consumer: "thm:consumer" };
    const CONSUMER = { id: "thm:consumer", kind: "theorem", statement: "The procedure attains the rate.", depends_on: ["oeq:q"], free_symbols: [], status: "to-prove", justification: "old", gap: "g", consumer: "paper" };
    const ANSWER = { id: "thm:answer", kind: "theorem", statement: "The rate is n^{-1/2}.", depends_on: ["ass:overlap"], free_symbols: [], status: "proved", proof_tex: "Direct.", justification: "a", gap: "a", consumer: "thm:consumer" };
    const proto = { ...PROTO, statements: [QUESTION, CONSUMER] };
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto });
    try {
      await saveWorkingState(h.ctx(), {
        round: 3,
        solved: {
          [ANSWER.id]: { proof_tex: ANSWER.proof_tex, snapshot: snapshotMember(proto as never, ANSWER as never), node: ANSWER, owner: QUESTION.id },
          [CONSUMER.id]: { proof_tex: "By thm:answer.", snapshot: snapshotMember(proto as never, CONSUMER as never) },
        },
        resolved_oeqs: { [QUESTION.id]: { theorem_id: ANSWER.id, source_fingerprint: oeqSourceFingerprint(QUESTION as never) } },
      } as never);
      // The render re-wires the consumer onto the answer; the proto still names the question.
      const renderedBefore = (await (async () => { const { assembleCore } = await import("../../src/discovery/core/assemble.js"); return assembleCore(await h.readProto(), await h.readWorking()); })());
      expect(renderedBefore.statements.find((s) => s.id === CONSUMER.id)?.depends_on).toEqual([ANSWER.id]);
      const workingBefore = JSON.parse(await readFile(workingPath(h.ctx()), "utf8"));

      const changed = await authorMetadataEdits({
        ctx: h.ctx(), note: "consumer prose", edits: [replace(CONSUMER, { justification: "authored" })],
      });
      expect(changed.map((c) => c.id)).toEqual([CONSUMER.id]);
      const protoAfter = await h.readProto();
      const consumer = protoAfter.statements.find((s) => s.id === CONSUMER.id)!;
      expect(consumer.justification).toBe("authored");
      expect(consumer.depends_on, "proto keeps its own edge; the render's re-wired edge must not leak in").toEqual(["oeq:q"]);
      expect(protoAfter.statements.some((s) => s.id === QUESTION.id)).toBe(true);
      expectRecordsMovedOnlyInProse(workingBefore.solved, (await h.readWorking()).solved as Record<string, unknown>);
      const core = await h.readCore();
      expect(core.statements.find((s) => s.id === CONSUMER.id)?.depends_on).toEqual([ANSWER.id]);
      expect(core.statements.find((s) => s.id === CONSUMER.id)?.justification).toBe("authored");
      const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: forbiddenSolver });
      expect(String((result as { message?: string }).message)).toMatch(/across 0 dispatched unit\(s\)/);
    } finally { await h.dispose(); }
  }, 30000);

  it("refuses while solver proposals are pending, and --check is a true dry run", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
    try {
      await saveWorkingState(h.ctx(), provedWorking(PROTO, {
        proposals: {
          statements: [{ id: MAIN.id, current: MAIN.statement, proposed: "narrower", reason: "r", direction: "narrow" }],
          definitions: [], assumptions: [], coreEdits: [], proofs: [],
        },
      }) as never);
      await expect(
        authorMetadataEdits({ ctx: h.ctx(), note: "n", edits: [replaceMain({ gap: "new gap" })] }),
      ).rejects.toThrow(/pending adjudication/);

      await saveWorkingState(h.ctx(), provedWorking(PROTO) as never);
      await saveState(h.repoRoot, PROTO.qid, "v1", persistableState(h));
      const before = await readFile(workingPath(h.ctx()), "utf8");
      const protoBefore = JSON.stringify(await h.readProto());
      const preview = await authorMetadataEdits({
        ctx: h.ctx(), note: "preview", checkOnly: true, edits: [replaceMain({ gap: "new gap" })],
      });
      expect(preview.map((c) => c.id)).toEqual([MAIN.id]);
      expect(await readFile(workingPath(h.ctx()), "utf8")).toBe(before);
      expect(JSON.stringify(await h.readProto())).toBe(protoBefore);
      expect((await readEscalationLog(h.ctx())).length).toBe(0);
      expect(existsSync(coreJsonPath(h.ctx()))).toBe(false);
      expect((await loadState(h.repoRoot, PROTO.qid, "v1")).stage_completed).toBe(h.state().stage_completed);
    } finally { await h.dispose(); }
  }, 30000);
});
