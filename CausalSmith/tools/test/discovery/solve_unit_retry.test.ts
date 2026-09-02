import { afterAll, beforeAll, beforeEach, describe, expect, it } from "vitest";
import { writeFile } from "node:fs/promises";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { createDStageHarness, type DStageHarness } from "./d_stage_harness.js";

const PROTO = {
  qid: "stat_unit_retry", specialization: "v1", cluster: "stat",
  symbols: [{ name: "tau", type: "causal parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [{ id: "ass:overlap", condition: "positivity holds", free_symbols: [], standard: { name: "overlap", cite: "R1983" } }],
  definitions: [],
  statements: [{ id: "thm:main", kind: "theorem", statement: "tau is identified", depends_on: ["ass:overlap"],
    status: "to-prove", justification: "j", gap: "g", consumer: "c" }],
  target_estimand: "tau", bibliography: [{ key: "R1983" }],
};
let h: DStageHarness;
beforeAll(async () => { h = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO }); });
afterAll(async () => { await h.dispose(); });
beforeEach(async () => { await h.reset(); });

/** Codex mock writing `bodies[call]` verbatim (raw bytes) and counting calls. */
function rawDeps(bodies: string[]): { deps: StageDeps; calls: () => number } {
  let n = 0;
  return {
    calls: () => n,
    deps: {
      runCodex: async ({ prompt }: { prompt: string }) => {
        const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
        await writeFile(outPath, bodies[Math.min(n, bodies.length - 1)], "utf8");
        n += 1;
        return { stdout: JSON.stringify({ status: "completed", artifacts: [outPath] }), stderr: "" };
      },
      runClaude: async () => { throw new Error("unused"); },
      lean: undefined as never,
    },
  };
}
const good = JSON.stringify({ proofs: [{ id: "thm:main", proof_tex: "By ass:overlap." }] });

describe("same-unit retry is typed: carrier defects retry once, schema contradictions do not", () => {
  it("a damaged JSON carrier is repeated once and the retry's artifact is accepted", async () => {
    const { deps, calls } = rawDeps(['{"proofs": [ {"id": "thm:main", "proof_tex": "By ass:overlap."', good]);
    await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps });
    expect(calls()).toBe(2);
    expect((await h.readCore()).statements[0].status).toBe("proved");
  });

  it("a readable carrier that fails the strict schema is not retried", async () => {
    // Unknown top-level key: strict schema rejects it, but the bytes are a valid carrier.
    const { deps, calls } = rawDeps([JSON.stringify({ proofs: [{ id: "thm:main", proof_tex: "P" }], proposedCoreEdits: [] }), good]);
    await expect(runStage0Solve({ ctx: h.ctx(), state: h.state(), deps })).rejects.toThrow(/invalid solve JSON/);
    expect(calls()).toBe(1);
  });
});
