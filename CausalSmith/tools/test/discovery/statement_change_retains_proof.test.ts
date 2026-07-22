// An adjudicated statement change reopens the node — but the previous proof is usually
// 90% reusable after a narrowing, so its bytes must survive as the node's single hot
// PARTIAL repair basis ("extend/realign this"), not be blanked. Blanking them (the old
// behavior) forced the next round to restart from nothing AND lost the bytes forever.
// The stale snapshot is kept with them: it records which statement the bytes argued,
// which is what lets dispatch label the partial as arguing a previous claim.

import { describe, it, expect } from "vitest";
import { writeFile } from "node:fs/promises";
import { applyProposedChanges } from "../../src/discovery/stages/d0_apply.js";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { saveWorkingState, loadWorkingState, snapshotMember } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness } from "./d_stage_harness.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const STMT = {
  id: "thm:main", kind: "theorem", statement: "OLD CLAIM", depends_on: ["ass:overlap"],
  status: "proved", proof_tex: "The old argument, of the OLD claim.",
  justification: "j", gap: "g", consumer: "c",
};
const PROTO = {
  qid: "stat_retain", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", kind: "support", condition: "c", free_symbols: [], standard: { name: "o", cite: "R1983" } }],
  definitions: [],
  statements: [STMT], target_estimand: "tau", bibliography: [{ key: "R1983" }],
};

describe("a frozen statement change retains the old proof as the hot partial", () => {
  it("keeps the bytes and the old-basis snapshot; the node still reopens", async () => {
    const h = await createDStageHarness({ qid: "stat_retain", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      const oldSnapshot = snapshotMember(proto, proto.statements[0]);
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: { "thm:main": { proof_tex: "The old argument, of the OLD claim.", snapshot: oldSnapshot } },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "thm:main", current: "OLD CLAIM", proposed: "NEW, NARROWER CLAIM", reason: "narrow", direction: "narrow" }],
          definitions: [], assumptions: [], coreEdits: [], proofs: [],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const after = await h.readProto();
      expect(after.statements[0].statement).toBe("NEW, NARROWER CLAIM");
      expect(after.statements[0].status, "the node must reopen").toBe("to-prove");
      expect(after.statements[0].proof_tex, "the proto must not present the old proof as proving the new claim").toBeUndefined();

      const w = await loadWorkingState(h.ctx());
      const rec = (w as never as { solved: Record<string, { proof_tex?: string; partial?: boolean; snapshot?: unknown }> }).solved["thm:main"];
      expect(rec?.partial, "the record must be an open repair basis, not a reusable proof").toBe(true);
      expect(rec?.proof_tex, "the previous proof bytes must survive as the repair basis")
        .toBe("The old argument, of the OLD claim.");
      expect(rec?.snapshot, "the snapshot must keep recording the OLD basis the bytes argued").toEqual(oldSnapshot);

      // The NEXT dispatch must label the retained partial as arguing a PREVIOUS
      // statement (with that statement's text), so the solver realigns the argument
      // instead of extending a stale basis past the change (laundering).
      const prompts: string[] = [];
      const deps: StageDeps = {
        runCodex: async ({ prompt }: { prompt: string }) => {
          prompts.push(prompt);
          const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
          await writeFile(outPath, JSON.stringify({
            proofs: [{ id: "thm:main", proof_tex: "Realigned proof of the NEW claim." }],
          }), "utf8");
          return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
        },
        runClaude: async () => { throw new Error("unused"); },
        lean: undefined as never,
      };
      await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps });
      const prompt = prompts.join("\n");
      expect(prompt).toContain("PRIOR PARTIAL PROGRESS");
      expect(prompt, "the label must say the partial argued a previous statement").toMatch(/PREVIOUS statement/);
      expect(prompt, "the label must show WHICH statement the bytes argued").toContain("OLD CLAIM");
    } finally { await h.dispose(); }
  }, 30000);

  it("a CARRIED claim change + same-bundle statement-replace still keeps the OLD-basis snapshot", async () => {
    // The claim-change branch preserves the old snapshot, but the statement-replace
    // reopen branch used to re-snapshot against the new claim right after — erasing
    // what the retained bytes argued (third-audit finding, 2026-07-21).
    const h = await createDStageHarness({ qid: "stat_retain", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      const agentNode = {
        id: "lem:agent", kind: "lemma", statement: "AGENT OLD CLAIM", depends_on: ["ass:overlap"],
        status: "proved", proof_tex: "agent proof of the OLD claim",
      };
      const oldSnapshot = snapshotMember(proto, agentNode as never);
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "lem:agent": { proof_tex: "agent proof of the OLD claim", snapshot: oldSnapshot, node: agentNode, owner: "thm:main" },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "lem:agent", current: "AGENT OLD CLAIM", proposed: "AGENT NEW CLAIM", reason: "narrow", direction: "correct" }],
          definitions: [], assumptions: [],
          coreEdits: [{
            kind: "statement-replace", id: "lem:agent",
            proposed: { ...agentNode, depends_on: ["ass:overlap"] },
            reason: "metadata echo", direction: "correct",
          }],
          proofs: [],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const w = await loadWorkingState(h.ctx());
      const rec = (w as never as { solved: Record<string, { partial?: boolean; snapshot?: { stmt?: string }; node?: { statement?: string } }> }).solved["lem:agent"];
      expect(rec?.node?.statement).toBe("AGENT NEW CLAIM");
      expect(rec?.partial).toBe(true);
      expect(rec?.snapshot?.stmt, "the replace branch must not erase the OLD basis").toBe("AGENT OLD CLAIM");
    } finally { await h.dispose(); }
  }, 30000);

  it("a CARRIED node's claim change also keeps the OLD-basis snapshot with the bytes", async () => {
    // The frozen branch preserves the snapshot the retained bytes argued; the carried
    // branch used to re-snapshot against the NEW statement, so dispatch could no longer
    // tell the partial argued a previous claim and presented stale bytes as ordinary
    // partial progress (audit finding, 2026-07-21).
    const h = await createDStageHarness({ qid: "stat_retain", specialization: "v1", proto: PROTO });
    try {
      const proto = await h.readProto();
      const agentNode = {
        id: "lem:agent", kind: "lemma", statement: "AGENT OLD CLAIM", depends_on: ["ass:overlap"],
        status: "proved", proof_tex: "agent proof of the OLD claim",
      };
      const oldSnapshot = snapshotMember(proto, agentNode as never);
      await saveWorkingState(h.ctx(), {
        round: 1,
        solved: {
          "lem:agent": { proof_tex: "agent proof of the OLD claim", snapshot: oldSnapshot, node: agentNode, owner: "thm:main" },
        },
        resolved_oeqs: {},
        proposals: {
          statements: [{ id: "lem:agent", current: "AGENT OLD CLAIM", proposed: "AGENT NEW CLAIM", reason: "narrow", direction: "correct" }],
          definitions: [], assumptions: [], coreEdits: [], proofs: [],
        },
      } as never);

      await applyProposedChanges({ ctx: h.ctx() });

      const w = await loadWorkingState(h.ctx());
      const rec = (w as never as { solved: Record<string, { proof_tex?: string; partial?: boolean; snapshot?: { stmt?: string }; node?: { statement?: string } }> }).solved["lem:agent"];
      expect(rec?.node?.statement, "the durable catalog carries the NEW claim").toBe("AGENT NEW CLAIM");
      expect(rec?.partial).toBe(true);
      expect(rec?.proof_tex, "the bytes survive as the repair basis").toBe("agent proof of the OLD claim");
      expect(rec?.snapshot?.stmt, "the snapshot must keep recording the OLD basis").toBe("AGENT OLD CLAIM");
    } finally { await h.dispose(); }
  }, 30000);
});
