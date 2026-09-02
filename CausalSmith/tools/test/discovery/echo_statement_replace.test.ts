import { afterAll, beforeAll, beforeEach, describe, expect, it } from "vitest";
import { readFile, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { appendEscalationLog, saveWorkingState, snapshotMember } from "../../src/discovery/stages/d0_working.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { createDStageHarness, type DStageHarness } from "./d_stage_harness.js";

const MAIN = {
  id: "thm:main", kind: "theorem", statement: "tau is identified", depends_on: ["ass:overlap"],
  status: "to-prove", justification: "core ID", gap: "vs prior", consumer: "applied",
};
const PROTO = {
  qid: "stat_echo_edit", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", condition: "positivity holds", free_symbols: [], standard: { name: "overlap", cite: "R1983" } }],
  definitions: [], statements: [MAIN], target_estimand: "tau", bibliography: [{ key: "R1983" }],
};
/** Settled AGENT-AUTHORED helper owned by a different (earlier) unit. */
const AUX = {
  id: "lem:aux", kind: "lemma", statement: "a supporting fact", depends_on: ["ass:overlap"],
  status: "proved", free_symbols: [], justification: "supports thm", gap: "vs prior", consumer: "thm:main",
};

let h: DStageHarness;
beforeAll(async () => { h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO }); });
afterAll(async () => { await h.dispose(); });
beforeEach(async () => {
  await h.reset();
  await saveWorkingState(h.ctx(), {
    round: 1,
    solved: {
      "lem:aux": { proof_tex: "Aux proof.", snapshot: snapshotMember(PROTO as never, AUX as never), node: AUX, owner: "lem:aux" },
    },
    resolved_oeqs: {},
  } as never);
  await appendEscalationLog(h.ctx(), {
    round: 1, changed: [], directive: "settle the exact target", required_core_targets: ["thm:main"],
  });
});

/** Sole unit (thm:main) proves its target citing lem:aux and also emits a statement-replace on lem:aux. */
function soleUnitDeps(auxPostimage: (node: Record<string, unknown>) => Record<string, unknown>): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      await writeFile(outPath, JSON.stringify({
        proofs: [{ id: "thm:main", proof_tex: "Combine ass:overlap with lem:aux." }],
        proposed_core_edits: [{
          kind: "statement-replace", id: "lem:aux", proposed: auxPostimage({ ...AUX }),
          reason: "synchronize", direction: "correct",
        }],
      }), "utf8");
      return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}

describe("identical-postimage statement-replace echoes never seed quarantine or conflict closure", () => {
  it("drops the echo on a non-owned settled node and lands the sole unit's own work", async () => {
    const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: soleUnitDeps((n) => n) }) as
      { status: string; message?: string };
    expect(String(result.message ?? "")).not.toMatch(/WITHHELD/);
    const core = JSON.parse(await readFile(coreJsonPath(h.ctx()), "utf8"));
    expect(core.statements.find((s: { id: string }) => s.id === "thm:main")?.status).toBe("proved");
    expect(core.statements.find((s: { id: string }) => s.id === "lem:aux")).toMatchObject({ status: "proved", depends_on: ["ass:overlap"] });
    const working = await h.readWorking();
    expect(working.solved["thm:main"]?.partial).toBeUndefined();
  });

  it("a non-owned statement-replace whose postimage differs is still withheld, not landed", async () => {
    const result = await runStage0Solve({
      ctx: h.ctx(), state: h.state(), deps: soleUnitDeps((n) => ({ ...n, depends_on: [] })),
    }) as { status: string; message?: string };
    expect(result.status).toBe("checkpoint");
    expect(String(result.message ?? "")).toMatch(/WITHHELD/);
    const core = JSON.parse(await readFile(coreJsonPath(h.ctx()), "utf8"));
    expect(core.statements.find((s: { id: string }) => s.id === "lem:aux")?.depends_on).toEqual(["ass:overlap"]);
  });
});

/** Generic sole-unit emitter for the follow-up cases. */
function emitDeps(body: (outPath: string) => Record<string, unknown>): StageDeps {
  return {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      await writeFile(outPath, JSON.stringify(body(outPath)), "utf8");
      return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("unused"); },
    lean: undefined as never,
  };
}
const mainProof = { id: "thm:main", proof_tex: "Combine ass:overlap with lem:aux." };
const readCore = async () => JSON.parse(await readFile(coreJsonPath(h.ctx()), "utf8"));
const mainStatus = async () => (await readCore()).statements.find((s: { id: string }) => s.id === "thm:main")?.status;

describe("no-op carriers never seed quarantine; noise never forces a checkpoint", () => {
  it("drops a no-op correction PAIR on a non-owned settled node and lands the owned target", async () => {
    const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: emitDeps(() => ({
      proofs: [mainProof],
      proposed_statement_changes: [{ id: "lem:aux", current: AUX.statement, proposed: AUX.statement, reason: "restate", direction: "narrow" }],
      proposed_core_edits: [{ kind: "statement-replace", id: "lem:aux", proposed: { ...AUX }, reason: "restate", direction: "correct" }],
    })) }) as { status: string; message?: string };
    expect(String(result.message ?? "")).not.toMatch(/WITHHELD/);
    expect(await mainStatus()).toBe("proved");
  });

  it("a quarantined non-owned open obligation keeps its receipt but does not withhold the emitter's own proof", async () => {
    // Two dispatched units (prop:side is open but not exact-required); thm:main's proof cites prop:side,
    // and thm:main's unit also attests an obligation on prop:side that it does not own.
    const side = { id: "prop:side", kind: "proposition", statement: "a side fact", depends_on: ["ass:overlap"],
      status: "to-prove", justification: "side", gap: "vs prior", consumer: "thm:main" };
    await h.writeProto({ ...PROTO, statements: [MAIN, side] } as never);
    await rm(path.join(path.dirname(coreJsonPath(h.ctx())), "d0_escalation_log.jsonl"), { force: true });
    await appendEscalationLog(h.ctx(), {
      round: 1, changed: [], directive: "settle the main target", required_core_targets: ["thm:main"],
    });
    const deps: StageDeps = {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        const owns = (id: string) => prompt.includes(`(unit: ${id})`);
        const body = owns("thm:main")
          ? { proofs: [{ id: "thm:main", proof_tex: "By prop:side and ass:overlap." }],
              open_obligations: [{ node_id: "prop:side", what_is_open: "unowned attestation", obstruction: "o", attempted: "a" }] }
          // The owner stays silent: no collision, only an unauthorized attestation to quarantine.
          : {};
        await writeFile(outPath, JSON.stringify(body), "utf8");
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    };
    const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps }) as { status: string; message?: string };
    expect(await mainStatus(), String(result.message)).toBe("proved");
    expect((await h.readWorking()).solved["thm:main"]?.partial).toBeUndefined();
    // Whatever the attestation's fate, it must not have reopened the emitter's own target.
    expect(String(result.message ?? "")).not.toMatch(/conflicted-dependency-consumer/);
  });

  it("a stray tldr from a non-owner in an undirected round commits without a checkpoint and is logged", async () => {
    // Undirected: drop the directive the shared beforeEach appended.
    await rm(path.join(path.dirname(coreJsonPath(h.ctx())), "d0_escalation_log.jsonl"), { force: true });
    const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: emitDeps(() => ({
      proofs: [mainProof],
      prose_updates: { tldr: "stray narrative", statement_notes: [] },
    })) }) as { status: string; message?: string };
    expect(String(result.message ?? "")).not.toMatch(/surfaced proposed change/);
    expect(await mainStatus()).toBe("proved");
    const log = await readFile(path.join(path.dirname(coreJsonPath(h.ctx())), "withheld_log.jsonl"), "utf8");
    const lines = log.trim().split("\n").map((l) => JSON.parse(l));
    expect(lines.at(-1).withheld_payloads.some((r: { reason: string }) => /prose/.test(r.reason))).toBe(true);
  });

  it("drops a statement note that changes no field before the ownership census", async () => {
    const result = await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: emitDeps(() => ({
      proofs: [mainProof],
      prose_updates: { statement_notes: [{ id: "thm:main", consumer: MAIN.consumer, gap: MAIN.gap }] },
    })) }) as { status: string; message?: string };
    expect(String(result.message ?? "")).not.toMatch(/WITHHELD|statement-note/);
    expect(await mainStatus()).toBe("proved");
  });
});

describe("a structured directive on an already-settled target names the cause", () => {
  it("aborts with the settled-target diagnostic instead of the generic message", async () => {
    await appendEscalationLog(h.ctx(), {
      round: 1, changed: [], directive: "promote the helper", required_core_targets: ["lem:aux"], require_core_changes: true,
    });
    // The worker can only re-emit what already landed: the same proof and a status-echo replace.
    const deps = emitDeps(() => ({
      proofs: [{ id: "lem:aux", proof_tex: "Aux proof." }],
      proposed_core_edits: [{ kind: "statement-replace", id: "lem:aux", proposed: { ...AUX, status: "proved" }, reason: "promote", direction: "correct" }],
    }));
    await expect(runStage0Solve({ ctx: h.ctx(), state: h.state(), deps })).rejects.toThrow(
      /already settled in the rendered core: lem:aux[\s\S]*cancel the mandate/,
    );
  });
});
