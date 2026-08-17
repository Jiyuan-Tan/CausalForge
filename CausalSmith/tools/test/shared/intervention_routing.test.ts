import { describe, expect, it } from "vitest";
import type { Intervention, ReviewResult } from "../../src/judgment.js";
import { NEG1_PIVOT_BUDGET, NEG1_REVISE_CAP } from "../../src/discovery/stages/neg1_2.js";
import { applyInterventionRoute } from "../../src/shared/intervention_routing.js";
import { synthesizeInterventionFromReviews } from "../../src/pipeline_support.js";
import type { StateJson } from "../../src/types.js";
import { extensionEditBasePath } from "../../src/discovery/stages/d0_cross_boundary_rewind.js";
import { coreJsonPath } from "../../src/discovery/stages/d0_core.js";
import { legacyCrossBoundaryRewindGuard } from "../../src/discovery/stages/d0_cross_boundary_rewind.js";
import { runStageNeg0_5 } from "../../src/discovery/stages/neg0_5.js";
import { runStageNeg1_2 } from "../../src/discovery/stages/neg1_2.js";

describe("synthesizeInterventionFromReviews — deterministic escalation (B)", () => {
  it("routes stage_neg1 + redraft_proposal when a 0.5 review sets escalate_to_proposer", () => {
    const review = {
      status: "revise",
      classification: "structure",
      perItemFindings: [],
      verbatim_critique: "x",
      escalate_to_proposer: true,
      escalate_reason: "reclassify the identification theorem as a conjecture",
    } as unknown as ReviewResult;
    const out = synthesizeInterventionFromReviews([review], "stage_0.5_to_0");
    expect(out.route).toBe("stage_neg1");
    expect(out.action_kind).toBe("redraft_proposal");
    expect(out.proposed_action).toMatch(/reclassify/);
  });

  it("falls back to route=user when no escalate flag (correctness-only revise)", () => {
    const review = {
      status: "revise",
      classification: "correctness",
      perItemFindings: [{ verdict: "correctness", one_line: "underspecified pivot" }],
      verbatim_critique: "x",
    } as unknown as ReviewResult;
    const out = synthesizeInterventionFromReviews([review], "stage_0.5_to_0");
    expect(out.route).toBe("user");
  });
});

type ProposedFrom = NonNullable<StateJson["proposed_from"]>;

function makeProposedFrom(overrides: Partial<ProposedFrom> = {}): ProposedFrom {
  return {
    topic: "topic",
    novelty_target: "incremental",
    pivot_budget_used: 0,
    final_verdict: "",
    proposal_path: "proposal.tex",
    novelty_justification: "novel",
    chosen_qid: "qid",
    chosen_specialization: "spec",
    current_angle_index: 0,
    current_version: 0,
    current_mode: "cold-start",
    last_reviewer_verdict: "reject",
    last_draft_version: 0,
    last_draft_status: "completed",
    exhausted_angles: [],
    ...overrides,
  };
}

function makeState(
  overrides: Partial<Omit<StateJson, "flags" | "proposed_from">> & {
    flags?: Partial<StateJson["flags"]>;
    proposed_from?: ProposedFrom;
  } = {},
): StateJson {
  const base = {
    stage_completed: "4",
    lean_subdir: "CausalSmith/Panel",
    pending_sorries: [{ file: "A.lean", line: 10 }],
    design_decisions: {},
    added_assumptions: [],
    flags: {
      local_fix_from_4d: false,
      missing_architecture: false,
    },
    proposed_from: makeProposedFrom(),
  } as StateJson;

  return {
    ...base,
    ...overrides,
    flags: {
      ...base.flags,
      ...(overrides.flags ?? {}),
    },
  } as StateJson;
}

function intervention(overrides: Partial<Intervention>): Intervention {
  return {
    route: "user",
    reason: "route reason",
    ...overrides,
  };
}

describe("applyInterventionRoute", () => {
  it("route=user is no-op", () => {
    const state = makeState({ stage_completed: "2" });
    const before = state.stage_completed;

    const result = applyInterventionRoute(state, intervention({ route: "user" }));

    expect(result).toBe(false);
    expect(state.stage_completed).toBe(before);
  });

  it("resets the F3/F4 in-stage loop counters on a successful upstream rewind", () => {
    // The counters are per-formalization-attempt; an upstream rewind starts a
    // fresh attempt, so they must reset (else a re-entered F3 inherits an
    // exhausted assumption-review budget and routes new premises to the F4
    // backstop unaudited — a laundering escape).
    const state = makeState({
      stage_completed: "3",
      flags: {
        assumption_review_count: 3,
        f4_localpatch_rounds: 2,
        assumption_review_cap_hit: "X, Y",
      },
    });
    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_2", reason: "encoding drift" }),
    );
    expect(result).toBe(true); // stage_2 rewind succeeded
    expect(state.flags.assumption_review_count).toBe(0);
    expect(state.flags.f4_localpatch_rounds).toBe(0);
    expect(state.flags.assumption_review_cap_hit).toBeUndefined();
  });

  it("does NOT reset the loop counters on a no-op route (route=user)", () => {
    const state = makeState({
      stage_completed: "2",
      flags: { assumption_review_count: 2, f4_localpatch_rounds: 1 },
    });
    applyInterventionRoute(state, intervention({ route: "user" }));
    // route=user is a no-op (no rewind), so the in-attempt budget is preserved.
    expect(state.flags.assumption_review_count).toBe(2);
    expect(state.flags.f4_localpatch_rounds).toBe(1);
  });

  it("route=stage_neg1 without proposed_from returns false and sets fallback flag", () => {
    const state = makeState({ stage_completed: "0.5", proposed_from: undefined });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_neg1", reason: "needs pivot" }),
    );

    expect(result).toBe(false);
    expect(state.stage_completed).toBe("0.5");
    expect(state.flags.stage_neg1_fallback).toBe(
      "stage_neg1 requested without propose-mode: needs pivot",
    );
  });

  it("route=stage_neg1 exhausts pivot budget", () => {
    const state = makeState({
      stage_completed: "0.5",
      proposed_from: makeProposedFrom({
        current_angle_index: NEG1_PIVOT_BUDGET - 1,
      }),
    });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_neg1", reason: "no viable theorem" }),
    );

    expect(result).toBe(false);
    expect(state.stage_completed).toBe("0.5");
    expect(state.flags.stage_neg1_fallback).toBe(
      `stage_neg1 requested but pivot budget exhausted (NEG1_PIVOT_BUDGET=${NEG1_PIVOT_BUDGET}): no viable theorem`,
    );
  });

  it("route=stage_neg1 happy path rewinds to proposal review pivot", () => {
    expect(NEG1_PIVOT_BUDGET).toBeGreaterThanOrEqual(2);
    const state = makeState({
      stage_completed: "0.5",
      pending_sorries: [{ file: "A.lean", line: 1 }],
      proposed_from: makeProposedFrom({
        current_angle_index: 0,
        current_version: 2,
        current_mode: "revise",
        last_draft_version: 2,
        last_draft_status: "completed",
        exhausted_angles: [],
      }),
    });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_neg1", reason: "pivot requested" }),
    );

    expect(result).toBe(true);
    expect(state.stage_completed).toBe("-1.2");
    expect(state.proposed_from?.current_angle_index).toBe(1);
    expect(state.proposed_from?.current_version).toBe(0);
    expect(state.proposed_from?.current_mode).toBe("pivot");
    expect(state.proposed_from?.exhausted_angles).toEqual([0]);
    expect(state.proposed_from?.last_reviewer_verdict).toBe("");
    expect(state.proposed_from?.last_draft_version).toBeUndefined();
    expect(state.proposed_from?.last_draft_status).toBeUndefined();
    expect(state.flags.rewound_from_stage0_5_pivot).toBe("pivot requested");
    expect(state.pending_sorries).toEqual([]);
  });

  it("route=stage_0 theorem_split cap hit returns false and sets cap flag", () => {
    const state = makeState({
      stage_completed: "4",
      flags: { theorem_splits: 3 },
    });

    const result = applyInterventionRoute(
      state,
      intervention({
        route: "stage_0",
        reason: "split required",
        action_kind: "theorem_split",
      }),
    );

    expect(result).toBe(false);
    expect(state.stage_completed).toBe("4");
    expect(state.flags.theorem_splits_cap_hit).toBe(
      "theorem_split cap reached (3): split required",
    );
  });

  it("route=stage_0 happy path rewinds through proposal review", () => {
    const state = makeState({
      stage_completed: "4",
      pending_sorries: [{ file: "A.lean", line: 9 }],
      flags: { theorem_splits: 2 },
      proposed_from: makeProposedFrom({
        current_angle_index: 0,
        current_version: 0,
        current_mode: "cold-start",
        last_draft_version: 0,
        last_draft_status: "completed",
      }),
    });

    const result = applyInterventionRoute(
      state,
      intervention({
        route: "stage_0",
        reason: "add latent assumption",
        proposed_assumption: {
          label: "A_new",
          statement: "New assumption statement.",
          source: "review",
        },
        d0_rewind_intent: "replacement",
      }),
    );

    expect(result).toBe(true);
    expect(state.stage_completed).toBe("-1.2");
    expect(state.pending_sorries).toEqual([]);
    expect(state.flags.rewound_from_stage0).toBe("add latent assumption");
    expect(state.flags.theorem_splits).toBe(2);
    expect(state.proposed_from?.current_mode).toBe("revise");
    expect(state.proposed_from?.last_draft_version).toBeUndefined();
    expect(state.proposed_from?.last_draft_status).toBeUndefined();
    expect(state.flags.f1_plan_retired).toBe(true);
    expect(state.flags.f2_scaffold_retired).toBe(true);
    expect(state.added_assumptions).toEqual([
      {
        label: "A_new",
        statement: "New assumption statement.",
        user_approved: true,
        source: "review",
      },
    ]);
  });

  it("refuses an ambiguous cross-boundary stage_0 rewind instead of silently using D-1.2", () => {
    const state = makeState({ stage_completed: "4" });
    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_0", reason: "add another result", action_kind: "re_derive" }),
    );
    expect(result).toBe(false);
    expect(state.stage_completed).toBe("4");
    expect(state.flags.stage0_rewind_intent_required).toMatch(/ambiguous cross-boundary/);
  });

  it("routes an incremental repair directly to D0 without changing the proposal cursor", () => {
    const state = makeState({
      stage_completed: "4",
      proposed_from: makeProposedFrom({ current_angle_index: 2, current_version: 7 }),
    });
    const result = applyInterventionRoute(
      state,
      intervention({
        route: "stage_0",
        reason: "repair one accepted proof",
        proposed_action: "repair one accepted proof",
        action_kind: "re_derive",
        d0_rewind_intent: "incremental_repair",
      }),
    );
    expect(result).toBe(true);
    expect(state.stage_completed).toBe("-0.5");
    expect(state.proposed_from?.current_version).toBe(7);
    expect(state.flags.d0_cross_boundary_rewind).toMatchObject({
      intent: "incremental_repair",
      source_revision: "angle:2/version:7",
      status: "pending",
    });
  });

  it("routes an extension through D-1.2 with a typed rebase receipt, without retiring F", () => {
    const state = makeState({
      stage_completed: "4",
      proposed_from: makeProposedFrom({ current_angle_index: 1, current_version: 5 }),
    });
    const result = applyInterventionRoute(
      state,
      intervention({
        route: "stage_0",
        reason: "add a distinct theorem",
        proposed_action: "add a distinct theorem",
        action_kind: "re_derive",
        d0_rewind_intent: "extension",
      }),
    );
    expect(result).toBe(true);
    expect(state.stage_completed).toBe("-1.2");
    expect(state.flags.d0_cross_boundary_rewind).toMatchObject({
      intent: "extension",
      source_revision: "angle:1/version:5",
      status: "pending",
    });
    expect(state.flags.f1_plan_retired).toBeUndefined();
    expect(state.flags.f2_scaffold_retired).toBeUndefined();
    const ctx = {
      repoRoot: "/tmp/rewind-route",
      qid: "stat_rewind_route",
      specialization: "v1",
    } as never;
    expect(extensionEditBasePath({
      ctx,
      state,
      ordinaryProtoPath: "/tmp/stale-pre-d0-proto.json",
    })).toBe(coreJsonPath(ctx));
  });

  it("counts a replacement theorem split exactly once", () => {
    const state = makeState({ stage_completed: "4", flags: { theorem_splits: 1 } });
    expect(applyInterventionRoute(state, intervention({
      route: "stage_0",
      reason: "replace and split",
      proposed_action: "replace and split",
      action_kind: "theorem_split",
      d0_rewind_intent: "replacement",
      proposed_assumption: { label: "A-new", statement: "Q holds" },
    }))).toBe(true);
    expect(state.flags.theorem_splits).toBe(2);
  });

  it("blocks a legacy in-flight D-1.2 rewind whose intent cannot be proven", async () => {
    const state = makeState({ stage_completed: "-1.2" });
    state.flags.rewound_from_stage0 = "old untyped rewind";
    expect(legacyCrossBoundaryRewindGuard(state)).toMatch(/no typed intent/);
    expect(state.flags.stage0_rewind_intent_required).toMatch(/refusing to review\/edit/);
    expect(state.stage_completed).toBe("-1.2");
    const result = await runStageNeg0_5({
      ctx: {
        repoRoot: "/tmp/legacy-rewind-guard",
        qid: "stat_legacy_rewind",
        specialization: "v1",
        dryRun: false,
        resume: true,
      },
      state,
      deps: {
        runCodex: async () => { throw new Error("guard must stop before reviewer dispatch"); },
        runClaude: async () => { throw new Error("guard must stop before producer dispatch"); },
        lean: undefined as never,
      },
    });
    expect(result).toMatchObject({ stage: "-0.5", status: "checkpoint", advance: false });
    const authorResult = await runStageNeg1_2({
      ctx: {
        repoRoot: "/tmp/legacy-rewind-guard",
        qid: "stat_legacy_rewind",
        specialization: "v1",
        dryRun: false,
        resume: true,
      },
      state,
      deps: {
        runCodex: async () => { throw new Error("D-1.2 guard must stop before author dispatch"); },
        runClaude: async () => { throw new Error("D-1.2 guard must stop before author dispatch"); },
        lean: undefined as never,
      },
    });
    expect(authorResult).toMatchObject({ stage: "-1.2", status: "checkpoint", advance: false });
  });

  it("route=stage_0 with exhausted angle and version budget returns false", () => {
    const state = makeState({
      stage_completed: "4",
      proposed_from: makeProposedFrom({
        current_angle_index: NEG1_PIVOT_BUDGET - 1,
        current_version: NEG1_REVISE_CAP,
      }),
    });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_0", reason: "rederive needed" }),
    );

    expect(result).toBe(false);
    expect(state.stage_completed).toBe("4");
    expect(state.flags.stage0_budget_exhausted).toBe(
      "stage_0 route requested but -0.5 budget exhausted: rederive needed",
    );
  });

  it("route=stage_1 happy path rewinds to local fix stage", () => {
    const state = makeState({
      stage_completed: "4",
      pending_sorries: [{ file: "A.lean", line: 11 }],
      flags: { stage1_rewinds: 0 },
    });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_1", reason: "local tex fix" }),
    );

    expect(result).toBe(true);
    expect(state.stage_completed).toBe("0.5");
    expect(state.flags.local_fix_from_4d).toBe(true);
    expect(state.flags.stage1_rewinds).toBe(1);
    expect(state.pending_sorries).toEqual([]);
  });

  it("route=stage_1 cap hit returns false and sets cap flag", () => {
    const state = makeState({
      stage_completed: "4",
      flags: { stage1_rewinds: 3 },
    });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_1", reason: "too many local fixes" }),
    );

    expect(result).toBe(false);
    expect(state.stage_completed).toBe("4");
    expect(state.flags.stage1_rewinds_cap_hit).toBe(
      "stage_1 rewind cap reached (3): too many local fixes",
    );
  });

  it("route=stage_2 happy path rewinds to scaffold stage", () => {
    const state = makeState({
      stage_completed: "4",
      pending_sorries: [{ file: "A.lean", line: 12 }],
      flags: { scaffold_redirect_count: 0 },
    });

    const result = applyInterventionRoute(
      state,
      intervention({
        route: "stage_2",
        reason: "encoding drift",
        proposed_action: "rebuild scaffold",
      }),
    );

    expect(result).toBe(true);
    expect(state.stage_completed).toBe("1.5");
    expect(state.flags.scaffold_redirect).toBe("rebuild scaffold");
    expect(state.flags.scaffold_redirect_count).toBe(1);
    expect(state.pending_sorries).toEqual([]);
  });

  it("route=stage_2 cap hit returns false and sets cap flag", () => {
    const state = makeState({
      stage_completed: "4",
      flags: { scaffold_redirect_count: 5 },
    });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_2", reason: "sixth redirect" }),
    );

    expect(result).toBe(false);
    expect(state.stage_completed).toBe("4");
    expect(state.flags.scaffold_redirect_cap_hit).toBe(
      "stage_2 redirect cap reached (5): sixth redirect",
    );
  });

  it("route=stage_4d at non-stage-4 boundary returns false and sets misroute flag", () => {
    const state = makeState({ stage_completed: "2.5" });

    const result = applyInterventionRoute(
      state,
      intervention({ route: "stage_4d", reason: "localized patch" }),
    );

    expect(result).toBe(false);
    expect(state.stage_completed).toBe("2.5");
    expect(state.flags.stage4d_misrouted).toBe(
      "stage_4d received at non-stage-4 boundary: localized patch",
    );
  });
});
