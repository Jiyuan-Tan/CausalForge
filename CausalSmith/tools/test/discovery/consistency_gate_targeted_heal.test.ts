// D0 CONSISTENCY GATE auto-heal must be TARGETED, structurally.
//
// The gate is documented as "ONE capped, targeted self-heal (re-solve only the citing
// node(s))" and it does invalidate only the citing nodes — but its directive used to be
// appended WITHOUT `required_core_targets`. The dispatcher treats an untargeted pending
// directive as "force EVERY core statement open", so the intended one-node heal became a
// whole-paper re-derivation (observed 3× in one run's escalation journal, each round
// reporting "reused 0 carried member proof(s)"). This pins the directive's targets and
// the resulting dispatch scope.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import { readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { runStage0Typed } from "../../src/discovery/stages/d0.js";
import { escalationLogPath, type EscalationLogEntry } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness, type DStageHarness } from "./d_stage_harness.js";
import type { StageDeps } from "../../src/pipeline_support.js";

// Two INDEPENDENT theorems: only thm:main's proof cites a never-emitted helper. The
// heal must reopen thm:main alone; thm:other's carried proof must survive untouched.
const PROTO = {
  qid: "stat_healtarget",
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
      depends_on: ["ass:overlap"], status: "to-prove",
      justification: "core ID", gap: "vs prior", consumer: "applied",
    },
    {
      id: "thm:other", kind: "theorem", statement: "tau is estimable",
      depends_on: ["def:env"], status: "to-prove",
      justification: "estimation", gap: "vs prior", consumer: "applied",
    },
  ],
  target_estimand: "tau = E[Y(1) - Y(0)]",
  bibliography: [{ key: "Rosenbaum1983" }],
};

/** Proves every target; thm:main's FIRST proof cites `lem:ghost` (cite-without-emit),
 *  its second proof is clean — modelling a solver that obeys the heal directive. */
function ghostCitingSolver(): { deps: StageDeps; dispatches: string[][] } {
  const dispatches: string[][] = [];
  let mainProofs = 0;
  const deps: StageDeps = {
    runCodex: async ({ prompt }: { prompt: string }) => {
      const outPath = /SOLVE_OUTPUT_PATH:\s*(\S+)/.exec(prompt)![1];
      const segment = (prompt.split("TARGET STATEMENT(S) TO SOLVE")[1] ?? "[]").split("SOLVE_OUTPUT_PATH")[0];
      const targets = JSON.parse(
        segment.slice(segment.indexOf("["), segment.lastIndexOf("]") + 1),
      ) as Array<{ id: string }>;
      dispatches.push(targets.map((t) => t.id));
      const proofFor = (id: string): string =>
        id === "thm:main" && ++mainProofs === 1 ? "By lem:ghost, tau is identified." : "QED.";
      const body = {
        proofs: targets.map((t) => ({ id: t.id, proof_tex: proofFor(t.id) })),
        added_lemmas: [],
        proposed_statement_changes: [],
        resolved_oeqs: [],
      };
      await writeFile(outPath, JSON.stringify(body), "utf8");
      return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [outPath] }), stderr: "" };
    },
    runClaude: async () => { throw new Error("runClaude is not used by D0 solve"); },
    lean: undefined as never,
  };
  return { deps, dispatches };
}

let h: DStageHarness;

async function healEntries(): Promise<EscalationLogEntry[]> {
  const p = escalationLogPath(h.ctx());
  if (!existsSync(p)) return [];
  return (await readFile(p, "utf8"))
    .split("\n")
    .filter((l) => l.trim())
    .map((l) => JSON.parse(l) as EscalationLogEntry)
    .filter((e) => /CONSISTENCY GATE \(auto-heal\)/.test(e.directive ?? ""));
}

beforeAll(async () => { h = await createDStageHarness({ qid: "stat_healtarget", specialization: "v1", proto: PROTO }); });
afterAll(async () => { await h.dispose(); });

describe("consistency-gate auto-heal is targeted at the citing nodes", () => {
  it("appends the heal directive WITH required_core_targets = the citing node(s)", async () => {
    const solver = ghostCitingSolver();
    const first = await runStage0Typed({ ctx: h.ctx(), state: h.state(), deps: solver.deps });
    expect(first.status, "round 1 must trip the gate").toBe("rewound");

    const heals = await healEntries();
    expect(heals.length).toBe(1);
    expect(heals[0].required_core_targets, "an untargeted heal forces the WHOLE paper open").toEqual(["thm:main"]);

    // The heal round re-dispatches ONLY the citing node; thm:other's proof is carried.
    const before = solver.dispatches.length;
    const second = await runStage0Typed({ ctx: h.ctx(), state: h.state(), deps: solver.deps });
    const healRound = solver.dispatches.slice(before).flat();
    expect(healRound, "heal round must reopen the citing node").toContain("thm:main");
    expect(healRound, "heal round must NOT re-derive the unrelated theorem").not.toContain("thm:other");
    expect(second.status, "clean re-proof passes the gate").not.toBe("rewound");
  }, 30000);
});
