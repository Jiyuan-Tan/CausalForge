// D0.5's CONSISTENCY GATE, driven offline.
//
// The gate catches "cite-without-emit": a proof that invokes a helper the solver never
// emitted. On detection it appends ONE capped auto-heal directive telling the next round
// to emit the missing member.
//
// On 2026-07-19 that produced the worst fault of the run — a PERMANENT DEADLOCK. A
// resolved OEQ's answer theorem legitimately cites the `oeq:` id it settles, but the D0
// boundary REPLACES the question node with its answer, so the id leaves the core. The
// gate read that as cite-without-emit and issued a directive to "emit every cited helper
// as a defined member". That is obeyable only by re-authoring a node frozen at D-1, which
// the silent-alteration guard then refuses. Two correct guards, mutually unsatisfiable;
// every resume reproduced it.
//
// The unit test in `dangling_resolved_oeq.test.ts` covers the detector. This covers the
// STAGE: that a clean round carrying a resolved OEQ produces no auto-heal directive at
// all. D0.5 previously had no offline coverage of this path, which is why the deadlock
// reached a live run.

import { describe, it, expect, beforeAll, afterAll, beforeEach } from "vitest";
import { readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { runStage0Typed } from "../../src/discovery/stages/d0.js";
import { escalationLogPath } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness, provingSolver, type DStageHarness, type RecordingSolver } from "./d_stage_harness.js";

/** `thm:main` cites the OEQ it answers — the exact shape that deadlocked the run. */
const PROTO = {
  qid: "stat_d05gate",
  specialization: "v1",
  cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [
    { id: "ass:overlap", kind: "support", condition: "bounded away from 0 and 1", free_symbols: [], standard: { name: "overlap", cite: "Rosenbaum1983" } },
  ],
  definitions: [{ id: "def:env", name: "U", construction: "U = a", inputs: ["a"] }],
  statements: [
    {
      id: "thm:main", kind: "theorem", statement: "tau is identified",
      depends_on: ["ass:overlap", "def:env"], status: "to-prove",
      justification: "core ID", gap: "vs prior", consumer: "applied",
    },
    {
      id: "oeq:open", kind: "openendedquestion", statement: "is the rate sharp?",
      depends_on: ["ass:overlap"], status: "to-prove",
      justification: "open", gap: "unknown", consumer: "thm:main",
    },
  ],
  target_estimand: "tau = E[Y(1) - Y(0)]",
  bibliography: [{ key: "Rosenbaum1983" }],
};

let h: DStageHarness;
let solver: RecordingSolver;

/** Every directive appended to the journal so far. */
async function directives(): Promise<string[]> {
  const p = escalationLogPath(h.ctx());
  if (!existsSync(p)) return [];
  return (await readFile(p, "utf8"))
    .split("\n")
    .filter((l) => l.trim())
    .map((l) => JSON.parse(l))
    .map((e) => (e.directive as string | undefined) ?? "")
    .filter(Boolean);
}

beforeAll(async () => { h = await createDStageHarness({ qid: "stat_d05gate", specialization: "v1", proto: PROTO }); });
afterAll(async () => { await h.dispose(); });
beforeEach(async () => { await h.reset(); solver = provingSolver(); });

describe("D0.5 consistency gate — a resolved OEQ is not a dangling citation", () => {
  it("raises no auto-heal directive for a round whose answer theorem cites its own question", async () => {
    // The deadlock's precondition: a resolved OEQ whose answer cites the question id.
    await runStage0Typed({ ctx: h.ctx(), state: h.state(), deps: solver.deps });
    const working = await h.readWorking();
    expect(Object.keys(working.resolved_oeqs ?? {}), "scenario did not resolve the OEQ").toEqual(["oeq:open"]);

    const heals = (await directives()).filter((d) => /cite-without-emit|CONSISTENCY GATE/i.test(d));
    expect(heals, "auto-heal fired on a resolved OEQ — this is the deadlock precondition").toEqual([]);
  });

  it("keeps the answered question out of the open frontier on the next round", async () => {
    // If the gate (or the carry) sends the OEQ back, the round is wasted re-answering it
    // — and under the old auto-heal, unrecoverably so.
    await runStage0Typed({ ctx: h.ctx(), state: h.state(), deps: solver.deps });
    solver.resetLog();
    await runStage0Typed({ ctx: h.ctx(), state: h.state(), deps: solver.deps });

    expect([...solver.dispatchedSince()], "the answered question was dispatched again").not.toContain("oeq:open");
  });

  it("still reports a GENUINELY undefined helper, so the exemption is narrow", async () => {
    // The fix must not blanket-suppress the gate it narrows: a proof citing a helper that
    // was never emitted is the laundering-by-citation case the gate exists for.
    const { findDanglingCitations } = await import("../../src/discovery/stages/d0_working.js");
    const core = {
      title: "t", assumptions: [], definitions: [], bibliography: [],
      statements: [{
        id: "thm:answer", kind: "theorem", status: "proved", statement: "S", depends_on: [],
        proof_tex: "By lem:never-emitted, this settles oeq:open.",
      }],
    } as never;
    const found = findDanglingCitations(core, { alsoKnown: ["oeq:open"] });
    expect(found).toEqual([{ node: "thm:answer", ref: "lem:never-emitted" }]);
  });
});
