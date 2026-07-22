// D-STAGE SOAK: multi-round scenarios, invariants asserted after EVERY round.
//
// The ~1600 unit tests caught none of the twelve faults found by driving one real run on
// 2026-07-19, because none of those faults is a property of a single function. They live
// where two code paths meet — two writers of one store, two builders of one payload, two
// guards that each work alone. Such a fault is only visible in the state a ROUND leaves
// behind, and several need MORE THAN ONE round to appear at all.
//
// Setup lives in `d_stage_harness.ts` and the assertions in `d_stage_invariants.ts`, so
// what remains here is the scenarios themselves.

import { describe, it, expect, beforeAll, afterAll, beforeEach } from "vitest";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { appendEscalationLog } from "../../src/discovery/stages/d0_working.js";
import type { WorkingState } from "../../src/discovery/stages/d0_working.js";
import { createDStageHarness, provingSolver, type DStageHarness, type RecordingSolver } from "./d_stage_harness.js";
import { assertRoundInvariants } from "./d_stage_invariants.js";

/** Carries an OEQ, so the resolution seam — the source of the worst faults — is exercised. */
const PROTO = {
  qid: "stat_soak",
  specialization: "v1",
  cluster: "stat",
  symbols: [{ name: "tau", type: "causal_parameter", def: "E[Y(1)-Y(0)]" }],
  assumptions: [
    {
      id: "ass:overlap",
      kind: "support",
      condition: "the propensity is bounded away from 0 and 1",
      free_symbols: [],
      standard: { name: "overlap", cite: "Rosenbaum1983" },
    },
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

/** One round, plus the full invariant sweep. Returns the state it left behind. */
async function round(where: string, before?: WorkingState): Promise<WorkingState> {
  await runStage0Solve({ ctx: h.ctx(), state: h.state(), deps: solver.deps });
  const [proto, core, after] = [await h.readProto(), await h.readCore(), await h.readWorking()];
  assertRoundInvariants({ proto, core, before, after }, where);
  return after;
}

/** Perturb the shared assumption: everything depending on it goes stale, the OEQ text does not. */
async function perturbOverlap(note: string, condition: string): Promise<void> {
  const proto = await h.readProto();
  proto.assumptions[0].condition = condition;
  await h.writeProto(proto);
  await appendEscalationLog(h.ctx(), { round: 1, changed: [], note });
}

beforeAll(async () => { h = await createDStageHarness({ qid: "stat_soak", specialization: "v1", proto: PROTO }); });
afterAll(async () => { await h.dispose(); });
beforeEach(async () => {
  await h.reset();
  solver = provingSolver();
});

describe("D-stage soak — invariants hold across consecutive rounds", () => {
  it("discharges a first round into a coherent pair of stores", async () => {
    const after = await round("round 1");
    expect(Object.keys(after.resolved_oeqs ?? {})).toEqual(["oeq:open"]);
  });

  it("re-runs idempotently without violating an invariant", async () => {
    const before = await round("round 1");
    await round("round 2 (idempotent)", before);
  });

  it("keeps the OEQ answer id stable when an unrelated edit invalidates the answer", async () => {
    // THE CHURN CASE. Requiring the answer to be VALID dropped the whole source->answer
    // mapping whenever anything in its closure moved, returning the OEQ to the frontier
    // so the solver derived a fresh answer under a NEW id — a full round spent
    // re-deriving a result that only needed its proof re-checked, and every downstream
    // reference churned. The question is untouched here, so the id must not move.
    // `assertRoundInvariants` enforces this; the explicit check names the value.
    const before = await round("round 1");
    const answerBefore = before.resolved_oeqs!["oeq:open"];

    await perturbOverlap("tightened overlap", "bounded away from 0 and 1, uniformly in n");
    solver.resetLog();
    const after = await round("round 2 (closure perturbed)", before);

    // The COST of the fault is the wasted round, so assert on re-dispatch directly.
    // The id check alone is not enough on its own: it only fires because the stub renames.
    expect([...solver.dispatchedSince()], "the answered OEQ was dispatched again")
      .not.toContain("oeq:open");
    expect(after.resolved_oeqs!["oeq:open"], "answer id churned after an unrelated edit").toEqual(answerBefore);
  });

  it("survives three consecutive perturbed rounds", async () => {
    // Sustained pressure. Each round re-derives against a moved closure, which is where
    // the multi-round faults — the silent-loss class especially — become reachable.
    let before: WorkingState | undefined;
    for (let n = 1; n <= 3; n++) {
      before = await round(`perturbed round ${n}`, before);
      await perturbOverlap(`perturb ${n}`, `overlap variant ${n}`);
    }
  });
});
