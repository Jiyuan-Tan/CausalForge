// F3→D0 rewind adjudication (`adjudicateRedoMathRewind`) — the cross-stage rewind
// hardening from the 2026-07 audit.
//
// The witnessed-refutation rewind must be INCREMENTAL: proto + working cursor stay
// intact, and only the refuted step's core consumers are forced open, through the
// TARGETED escalation-directive channel. Two prior shapes are pinned as regressions:
//   - propose mode routed through applyInterventionRoute("stage_0"), re-invoking the
//     D-1.2 proposal producer; the revision bump made the next D0 assembly discard
//     EVERY carried proof (prev = null) to fix one node.
//   - non-propose mode moved the cursor with NO escalation entry, so the next D0 round
//     had an empty frontier, dispatched nobody, passed the discharge gate, and consumed
//     the witness — the identical refuted core was re-published.
//
// ID SPACES: `rm.obj_id` is ALWAYS an agent-introduced Lean id (verified against the
// live run stat_reversekl_two_coverage: graph.json aux nodes are `aux_BanditLaw`,
// `aux_cleanQ`, `aux_dimensionWitnessC`, … with provenance "agent-introduced", while
// every core statement id is `thm:`/`lem:`/`prop:`-shaped). A required_core_target in
// the Lean id space is UNSATISFIABLE — merge.ts hard-throws before commitRound, wedging
// every subsequent resume — so the adjudicator must emit ONLY core statement ids.

import { describe, it, expect, afterEach } from "vitest";
import { writeFile, mkdir } from "node:fs/promises";
import path from "node:path";
import { adjudicateRedoMathRewind } from "../../src/formalization/dispatcher.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import {
  loadWorkingState,
  readEscalationLog,
  saveWorkingState,
  snapshotMember,
} from "../../src/discovery/stages/d0_working.js";
import { assembleSolveContext } from "../../src/discovery/solve/context.js";
import { runStage0Solve } from "../../src/discovery/stages/d0_solve.js";
import { createDStageHarness, provingSolver, type DStageHarness } from "../discovery/d_stage_harness.js";
import type { StateJson } from "../../src/types.js";
import type { Core } from "../../src/discovery/core/schema.js";

// Two INDEPENDENT proved statements, shaped after the live stat_reversekl_two_coverage
// run (kebab thm ids, standard-cited assumption, structured definition). `thm:localized-upper`
// is the expensive established proof the rewind must NOT discard; `thm:erm-plugin-upper`
// is the core consumer of the refuted Lean step.
const PROTO = {
  qid: "stat_redo_rewind",
  specialization: "v1",
  cluster: "stat",
  symbols: [{ name: "d", type: "scalar", space: "\\(\\mathbb N\\)", def: "feature dimension", role: "index" }],
  assumptions: [
    {
      id: "ass:overlap",
      kind: "support",
      condition: "the propensity is bounded away from 0 and 1",
      free_symbols: [],
      standard: { name: "overlap", cite: "Rosenbaum1983" },
    },
  ],
  definitions: [
    { id: "def:minimax-risk", name: "R", construction: "the minimax risk over the model class", inputs: [] },
  ],
  statements: [
    {
      id: "thm:localized-upper",
      kind: "theorem",
      statement: "the localized estimator attains the risk bound",
      depends_on: ["ass:overlap"],
      status: "to-prove",
      justification: "upper half",
      gap: "vs prior",
      consumer: "applied",
    },
    {
      id: "thm:erm-plugin-upper",
      kind: "theorem",
      statement: "the ERM plug-in attains the same rate",
      depends_on: ["ass:overlap"],
      status: "to-prove",
      justification: "plug-in half",
      gap: "vs prior",
      consumer: "applied",
    },
  ],
  target_estimand: "R",
  bibliography: [{ key: "Rosenbaum1983" }],
};

const PROOF_A = "Localize and apply the bounded-projection concentration lemma.";
const PROOF_B = "Convert the Gibbs regret identity into the plug-in bound.";

// The refuted node + blast radius, in REAL id shapes: the refuted obj_id and one
// dependent are agent-introduced Lean aux ids (never core ids); one dependent is the
// core theorem whose formal proof rests on the refuted step.
const RM = {
  obj_id: "aux_dimensionWitnessC",
  witness: { type: "counterexample", detail: "d=1 with a degenerate logging design refutes the coercivity step" },
  dependents: ["aux_cleanQ", "thm:erm-plugin-upper"],
  touchesProven: false,
};

function makeState(overrides: Partial<StateJson> = {}): StateJson {
  return {
    stage_completed: "2",
    lean_subdir: "CausalSmith/Stat/StatRedoRewind",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    flags: {},
    ...overrides,
  } as unknown as StateJson;
}

/** Seed the post-D0 stores: a round-1 cursor with both proofs, and the assembled core.
 *  `proposalRevision` must mirror the state's `proposed_from` (a real cursor records the
 *  revision at assembly; a mismatch is the D-1.2 rewind case, which discards the carry). */
async function seedSolvedRun(h: DStageHarness, proposalRevision?: string): Promise<void> {
  const proto = PROTO as unknown as Core;
  const rec = (id: string, proofTex: string) => ({
    proof_tex: proofTex,
    snapshot: snapshotMember(proto, proto.statements.find((s) => s.id === id)!),
  });
  await saveWorkingState(h.ctx(), {
    round: 1,
    escalation_entries_consumed: 0,
    ...(proposalRevision !== undefined ? { proposal_revision: proposalRevision } : {}),
    solved: {
      "thm:localized-upper": rec("thm:localized-upper", PROOF_A),
      "thm:erm-plugin-upper": rec("thm:erm-plugin-upper", PROOF_B),
    },
    resolved_oeqs: {},
  });
  const core = JSON.parse(JSON.stringify(PROTO)) as Core;
  for (const s of core.statements) {
    s.status = "proved";
    s.proof_tex = s.id === "thm:localized-upper" ? PROOF_A : PROOF_B;
  }
  const corePath = coreJsonPath(h.ctx());
  await mkdir(path.dirname(corePath), { recursive: true });
  await writeFile(corePath, JSON.stringify(core), "utf8");
}

let harness: DStageHarness | null = null;
afterEach(async () => {
  await harness?.dispose();
  harness = null;
});

async function setup(proposalRevision?: string): Promise<DStageHarness> {
  harness = await createDStageHarness({ qid: PROTO.qid, specialization: "v1", proto: PROTO });
  await seedSolvedRun(harness, proposalRevision);
  return harness;
}

describe("adjudicateRedoMathRewind — targeted incremental rewind", () => {
  it("appends a TARGETED escalation directive naming only CORE statement ids (never Lean aux ids)", async () => {
    const h = await setup();
    const state = makeState();
    const result = await adjudicateRedoMathRewind({ ctx: h.ctx(), state, rm: RM, reason: "claim-false" });

    expect(result.status).toBe("rewound");
    expect(state.stage_completed).toBe("-0.5");
    expect(state.flags.redo_math_witness).toMatchObject({ obj_id: RM.obj_id, type: "counterexample" });

    const log = await readEscalationLog(h.ctx());
    expect(log).toHaveLength(1);
    // The trap this pins: writing rm.obj_id / aux dependents here is UNSATISFIABLE
    // (merge.ts throws pre-commit on a target no solver payload can name) and would
    // wedge every subsequent resume.
    expect(log[0].required_core_targets).toEqual(["thm:erm-plugin-upper"]);
    // A real directive (not provenance-only): this is what makes hasPendingDirective
    // true so the next D0 round actually dispatches someone.
    expect((log[0].directive ?? "").trim().length).toBeGreaterThan(0);
    expect(log[0].provenance_only).not.toBe(true);
  });

  it("propose mode takes the SAME path: no proposal-producer rewind, no revision bump, carried proofs survive", async () => {
    const h = await setup("angle:0/version:2");
    const state = makeState({
      proposed_from: {
        topic: "t", novelty_target: "field", cluster: "stat",
        current_angle_index: 0, current_version: 2, current_mode: "revise", last_reviewer_verdict: "ACCEPT",
      },
    } as unknown as Partial<StateJson>);
    await adjudicateRedoMathRewind({ ctx: h.ctx(), state, rm: RM, reason: "claim-false" });

    // The old propose branch parked the cursor at D-1.2 and bumped the proposal state;
    // the next D0 assembly then saw a revision change and set prev = null, discarding
    // every carried proof (and running with an empty escalation context).
    expect(state.stage_completed).toBe("-0.5");
    const pf = state.proposed_from as unknown as { current_version: number; current_mode: string };
    expect(pf.current_version).toBe(2);
    expect(pf.current_mode).toBe("revise");

    const sctx = await assembleSolveContext({ ctx: h.ctx(), state });
    expect(sctx.prev).not.toBeNull();
    expect(sctx.hasPendingDirective).toBe(true);
    expect([...sctx.requiredCoreTargets]).toEqual(["thm:erm-plugin-upper"]);
    // The untouched established proof is still a valid carry — the whole point.
    expect(sctx.validIds.has("thm:localized-upper")).toBe(true);
    expect(sctx.escContext).toContain("thm:erm-plugin-upper");
  });

  it("checkpoints (does NOT auto-rewind untargeted) when no core statement is among the dependents", async () => {
    const h = await setup();
    const state = makeState();
    const result = await adjudicateRedoMathRewind({
      ctx: h.ctx(),
      state,
      rm: { ...RM, dependents: ["aux_cleanQ", "aux_BanditLaw"] },
      reason: "claim-false",
    });
    // An untargeted directive would force EVERY statement open (whole-paper
    // re-derivation); refusing to localize means refusing to auto-rewind.
    expect(result.status).toBe("checkpoint");
    expect(state.stage_completed).toBe("2");
    expect(await readEscalationLog(h.ctx())).toHaveLength(0);
    expect(state.flags.redo_math_witness).toBeUndefined();
  });

  it("still checkpoints on touchesProven and past the per-node cap", async () => {
    const h = await setup();
    const proven = await adjudicateRedoMathRewind({
      ctx: h.ctx(), state: makeState(), rm: { ...RM, touchesProven: true }, reason: "r",
    });
    expect(proven.status).toBe("checkpoint");

    const state = makeState({ flags: { redo_math_rewinds: { [RM.obj_id]: 3 } } } as unknown as Partial<StateJson>);
    const capped = await adjudicateRedoMathRewind({ ctx: h.ctx(), state, rm: RM, reason: "r" });
    expect(capped.status).toBe("checkpoint");
    expect(capped.message).toContain("cap 3 hit");
    expect(await readEscalationLog(h.ctx())).toHaveLength(0);
  });

  it("end-to-end: the rewound D0 round re-derives ONLY the targeted theorem, keeps the other proof, and consumes the witness", async () => {
    const h = await setup();
    const state = makeState();
    await adjudicateRedoMathRewind({ ctx: h.ctx(), state, rm: RM, reason: "claim-false" });

    const solver = provingSolver();
    const result = await runStage0Solve({ ctx: h.ctx(), state, deps: solver.deps });

    // Exactly one unit, targeting exactly the refuted theorem — not the whole paper.
    // (The old non-propose branch dispatched NOBODY here: empty frontier, clean
    // discharge, witness consumed with the refuted claim re-published verbatim.)
    expect(solver.dispatches()).toEqual([["thm:erm-plugin-upper"]]);
    expect("status" in result).toBe(false); // clean discharge

    const working = await loadWorkingState(h.ctx());
    expect(working?.solved["thm:localized-upper"]?.proof_tex).toBe(PROOF_A); // carried, not re-derived
    expect(working?.solved["thm:erm-plugin-upper"]?.proof_tex).toBe("QED."); // re-derived
    expect(state.flags.redo_math_witness).toBeUndefined(); // consumed by the clean discharge
  });
});
