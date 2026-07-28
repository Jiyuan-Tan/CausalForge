// Deterministic coverage for the statement-correction route (#2): the schema
// contract, the router's flag-setting (without theorem-split side effects), and
// the proposer-facing directive block. No LLM — pure plumbing.
import { describe, it, expect } from "vitest";
import { interventionSchema } from "../src/judgment.js";
import { applyInterventionRoute } from "../src/shared/intervention_routing.js";
import { buildStage0_5RejectionContext } from "../src/discovery/stages/neg0_5.js";
import type { Intervention } from "../src/judgment.js";
import type { PipelineContext, StateJson } from "../src/types.js";

function freshState(): StateJson {
  return {
    flags: { theorem_splits: 0 },
    added_assumptions: [],
    pending_sorries: [],
  } as unknown as StateJson;
}

const CORRECTED =
  "The sharp identified set for theta=Pr(Y1>Y0) is the CLOSURE of the conditional value set, " +
  "equal to [L_rho(P),U_rho(P)] with L,U the integrated conditional inf/sup (attainment not required).";

describe("statement_correction schema contract", () => {
  it("accepts a well-formed statement_correction", () => {
    const ok = {
      route: "stage_0",
      reason: "case 2a' over-precision — restate to closure-sharp",
      proposed_action: "replace thm:k-sharp-dual-confirmed statement with the closure/inf-sup form",
      action_kind: "statement_correction",
      proposed_restatement: { statement: CORRECTED, rationale: "attainment is regularity, not the contribution" },
    };
    expect(() => interventionSchema.parse(ok)).not.toThrow();
  });

  it("rejects statement_correction without proposed_restatement", () => {
    const bad = {
      route: "stage_0",
      reason: "x",
      proposed_action: "y",
      action_kind: "statement_correction",
    };
    expect(() => interventionSchema.parse(bad)).toThrow();
  });

  it("rejects statement_correction that smuggles a proposed_assumption", () => {
    const bad = {
      route: "stage_0",
      reason: "x",
      proposed_action: "y",
      action_kind: "statement_correction",
      proposed_restatement: { statement: CORRECTED },
      proposed_assumption: { label: "A-x", statement: "assume attainment" },
    };
    expect(() => interventionSchema.parse(bad)).toThrow();
  });

  it("rejects proposed_restatement on a non-correction action_kind", () => {
    const bad = {
      route: "stage_0",
      reason: "x",
      proposed_action: "y",
      action_kind: "re_derive",
      proposed_restatement: { statement: CORRECTED },
    };
    expect(() => interventionSchema.parse(bad)).toThrow();
  });
});

describe("applyInterventionRoute — statement_correction", () => {
  it("sets the directive flag, rewinds to -1.2, and does NOT increment theorem_splits", () => {
    const state = freshState();
    const intervention: Intervention = {
      route: "stage_0",
      reason: "case 2a' over-precision",
      proposed_action: "restate to closure-sharp",
      action_kind: "statement_correction",
      proposed_restatement: { statement: CORRECTED, rationale: "attainment is regularity" },
    };
    const rewound = applyInterventionRoute(state, intervention);
    expect(rewound).toBe(true);
    expect(state.stage_completed).toBe("-1.2");
    expect(state.flags.statement_correction_directive).toContain("CLOSURE");
    expect(state.flags.statement_correction_directive).toContain("attainment is regularity");
    // NOT a split: counter untouched, no assumption recorded.
    expect(state.flags.theorem_splits).toBe(0);
    expect(state.added_assumptions.length).toBe(0);
  });

  it("theorem_split still increments the counter (regression guard)", () => {
    const state = freshState();
    const intervention: Intervention = {
      route: "stage_0",
      reason: "case 2c regime_defining",
      proposed_action: "split",
      action_kind: "theorem_split",
      proposed_assumption: { label: "A-x", statement: "assume Q" },
      assumption_classifications: [{ label: "A-x", classification: "regime_defining", one_line: "kernel" }],
    };
    applyInterventionRoute(state, intervention);
    expect(state.flags.theorem_splits).toBe(1);
    expect(state.flags.statement_correction_directive ?? null).toBeNull();
  });
});

describe("buildStage0_5RejectionContext — correction directive", () => {
  const ctx = { repoRoot: "/nonexistent", qid: "pid_x", specialization: "v1" } as unknown as PipelineContext;

  it("emits the STATEMENT-CORRECTION block (not the generic revise/pivot framing) when the directive is set", async () => {
    const state = freshState();
    state.flags.rewound_from_stage0 = "case 2a' over-precision";
    state.flags.statement_correction_directive = CORRECTED;
    const block = await buildStage0_5RejectionContext({ ctx, state });
    expect(block).toContain("STATEMENT-CORRECTION DIRECTIVE");
    expect(block).toContain(CORRECTED);
    expect(block).toContain("Do NOT demote");
    // The generic "prior accept may have been over-optimistic" framing must not appear.
    expect(block).not.toContain("prior accept may have been over-optimistic");
  });

  it("falls back to the generic rejection block when no correction directive is set", async () => {
    const state = freshState();
    state.flags.rewound_from_stage0 = "case 2c regime_defining split";
    const block = await buildStage0_5RejectionContext({ ctx, state });
    expect(block).toContain("STAGE 0.5 REJECTION CONTEXT");
    expect(block).not.toContain("STATEMENT-CORRECTION DIRECTIVE");
  });
});

// ── Attempt-boundary hygiene (2026-07 cross-stage rewind audit) ──────────────────────
//
// A correction directive describes ONE specific rewind's fix. It is read by
// `buildStage0_5RejectionContext`, whose correction branch RETURNS EARLY — before the
// generic block that carries the CURRENT rewind's reason — so a stale round-A correction
// left on the flags would permanently displace every later rewind's critique. Each new
// stage_0 / stage_neg1 rewind must therefore clear (or replace) it.
describe("applyInterventionRoute — stale correction directive is cleared at the next rewind", () => {
  const STALE = "ROUND-A: restate thm:old in the closure form.";

  it("a later NON-correction stage_0 rewind clears the stale directive (and the context block shows the NEW critique)", async () => {
    const state = freshState();
    state.flags.statement_correction_directive = STALE;
    const rewound = applyInterventionRoute(state, {
      route: "stage_0",
      reason: "round B: the kernel novelty critique",
      proposed_action: "re-derive with the corrected comparator",
      action_kind: "re_derive",
    } as Intervention);
    expect(rewound).toBe(true);
    expect(state.flags.statement_correction_directive ?? null).toBeNull();

    // Observable consequence: the proposer context now carries round B's critique,
    // not round A's correction block.
    const ctx = { repoRoot: "/nonexistent", qid: "pid_x", specialization: "v1" } as unknown as PipelineContext;
    const block = await buildStage0_5RejectionContext({ ctx, state });
    expect(block).toContain("STAGE 0.5 REJECTION CONTEXT");
    expect(block).toContain("round B: the kernel novelty critique");
    expect(block).not.toContain("STATEMENT-CORRECTION DIRECTIVE");
    expect(block).not.toContain(STALE);
  });

  it("a later CORRECTION rewind replaces (not appends to) the stale directive", () => {
    const state = freshState();
    state.flags.statement_correction_directive = STALE;
    applyInterventionRoute(state, {
      route: "stage_0",
      reason: "round B over-precision",
      action_kind: "statement_correction",
      proposed_restatement: { statement: "ROUND-B corrected statement." },
    } as Intervention);
    expect(state.flags.statement_correction_directive).toContain("ROUND-B");
    expect(state.flags.statement_correction_directive).not.toContain("ROUND-A");
  });

  it("a stage_neg1 pivot clears the stale directive (it described the abandoned angle)", () => {
    const state = freshState();
    state.flags.statement_correction_directive = STALE;
    (state as unknown as { proposed_from: object }).proposed_from = {
      topic: "t", novelty_target: "field", cluster: "stat", current_angle_index: 0, current_version: 1,
    };
    const rewound = applyInterventionRoute(state, {
      route: "stage_neg1", reason: "angle blocked", action_kind: "redraft_proposal",
    } as Intervention);
    expect(rewound).toBe(true);
    expect(state.flags.statement_correction_directive ?? null).toBeNull();
  });
});

describe("applyInterventionRoute — stage_neg1 pivot retires the F-era artifacts", () => {
  it("sets both retirement markers so F1/F2 cold-start instead of patching the dead angle", () => {
    const state = freshState();
    (state as unknown as { proposed_from: object }).proposed_from = {
      topic: "t", novelty_target: "field", cluster: "stat", current_angle_index: 0, current_version: 1,
    };
    const rewound = applyInterventionRoute(state, {
      route: "stage_neg1", reason: "angle blocked", action_kind: "redraft_proposal",
    } as Intervention);
    expect(rewound).toBe(true);
    expect(state.flags.f1_plan_retired).toBe(true);
    expect(state.flags.f2_scaffold_retired).toBe(true);
  });

  it("a same-angle stage_0 re-derive does NOT retire the F-era", () => {
    const state = freshState();
    applyInterventionRoute(state, {
      route: "stage_0", reason: "re-derive", action_kind: "re_derive",
    } as Intervention);
    expect(state.flags.f1_plan_retired).toBeUndefined();
    expect(state.flags.f2_scaffold_retired).toBeUndefined();
  });
});
