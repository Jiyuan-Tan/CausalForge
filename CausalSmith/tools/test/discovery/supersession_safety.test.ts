import { readFile, writeFile } from "node:fs/promises";
import { describe, expect, it } from "vitest";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { runStage0Render } from "../../src/discovery/stages/d0_render.js";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { saveWorkingState, snapshotMember } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness, provingSolver } from "./d_stage_harness.js";

const OLD = {
  id: "lem:old-conditions", kind: "lemma", statement: "The old conditions suffice.",
  depends_on: ["ass:overlap"], status: "to-prove", justification: "old", gap: "old", consumer: "thm:main",
};
const CONSUMER = {
  id: "thm:main", kind: "theorem",
  statement: String.raw`The conclusion holds under the conditions in \texttt{lem:old-conditions}.`,
  depends_on: ["lem:old-conditions"], status: "to-prove", justification: "main", gap: "gap", consumer: "paper",
};
const PROTO = {
  qid: "stat_supersession_safety", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{
    id: "ass:overlap", condition: "positivity holds", free_symbols: [],
    standard: { name: "overlap", cite: "R1983" },
  }],
  definitions: [], statements: [OLD, CONSUMER], target_estimand: "tau",
  bibliography: [{ key: "R1983" }],
};

const replacement = {
  ...OLD,
  id: "lem:new-scale-aware-conditions",
  statement: "Different scale-aware conditions suffice.",
  status: "proved",
  proof_tex: "Proof of the scale-aware conditions.",
};

function supersessionWorking(proto: typeof PROTO) {
  return {
    round: 4,
    solved: {
      [CONSUMER.id]: {
        proof_tex: String.raw`Apply \texttt{lem:old-conditions}; that lemma yields the conclusion.`,
        snapshot: snapshotMember(proto as never, CONSUMER as never),
      },
      [replacement.id]: {
        proof_tex: replacement.proof_tex,
        snapshot: snapshotMember(proto as never, replacement as never),
        node: replacement,
      },
    },
    proposals: {
      statements: [], definitions: [], assumptions: [], proofs: [],
      coreEdits: [{
        kind: "statement-delete", id: OLD.id, replacement_id: replacement.id,
        reason: "the scale-aware lemma supersedes the old conditions", direction: "delete-obsolete",
      }],
    },
  } as const;
}

describe("statement supersession safety", () => {
  it("refuses metadata remapping while claim/proof text still names the obsolete node", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
    try {
      await saveWorkingState(h.ctx(), supersessionWorking(PROTO) as never);
      const beforeProto = await readFile(
        // The harness exposes parsed proto, while this assertion intentionally pins bytes.
        protoCoreJsonPath(h.ctx()),
        "utf8",
      );

      let message = "";
      try {
        await applyProposedChanges({ ctx: h.ctx() });
      } catch (err) {
        message = err instanceof Error ? err.message : String(err);
      }
      expect(message).toMatch(/literal claim\/proof references remain/i);
      expect(message).toMatch(/thm:main\.statement/);
      expect(message).toMatch(/working\.thm:main\.proof_tex/);

      const afterProto = await readFile(
        protoCoreJsonPath(h.ctx()),
        "utf8",
      );
      expect(afterProto, "a refused claim-changing delete must not touch the frozen source").toBe(beforeProto);
      expect((await h.readWorking()).proposals?.coreEdits).toHaveLength(1);
    } finally { await h.dispose(); }
  }, 30000);

  it("carries the gated half through a retry instead of overwriting the relation", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
    try {
      await saveWorkingState(h.ctx(), supersessionWorking(PROTO) as never);
      const solver = provingSolver();

      const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: solver.deps });
      expect(result).toMatchObject({ status: "checkpoint", advance: false });
      expect(solver.dispatchedSince().size, "the retry may restate/re-prove affected consumers").toBeGreaterThan(0);
      const after = await h.readWorking();
      expect(after.proposals?.coreEdits).toContainEqual(expect.objectContaining({
        kind: "statement-delete", id: OLD.id, replacement_id: replacement.id,
      }));
    } finally { await h.dispose(); }
  }, 30000);

  it("refuses the real render path when both chains are present with a pending supersession", async () => {
    const h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
    try {
      await saveWorkingState(h.ctx(), supersessionWorking(PROTO) as never);
      await writeFile(coreJsonPath(h.ctx()), JSON.stringify({
        ...PROTO,
        statements: [
          { ...OLD, status: "proved", proof_tex: "Old proof." },
          { ...CONSUMER, status: "proved", proof_tex: "Consumer proof." },
          replacement,
        ],
      }), "utf8");

      await expect(runStage0Render({ ctx: h.ctx(), state: h.state() }))
        .rejects.toThrow(/refuses a core containing both sides.*pending supersession/i);
    } finally { await h.dispose(); }
  }, 30000);
});
