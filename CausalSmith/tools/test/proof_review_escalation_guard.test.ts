import { mkdtemp } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  recordProofReviewOutcome,
  runFormalizationStage,
} from "../src/formalization/dispatcher.js";
import { runPipeline } from "../src/pipeline.js";
import { createInitialState, saveState, stateSchema } from "../src/state.js";
import type { StageDeps } from "../src/pipeline_support.js";
import type { PipelineContext, Stage } from "../src/types.js";

describe("proof-review escalation fail-closed guard", () => {
  it("records every escalation durably and leaves stage_completed at F2", () => {
    const state = createInitialState("eid_guard");
    state.stage_completed = "4";

    recordProofReviewOutcome(state, {
      status: "escalate",
      route: "hint",
      reason: "headline theorem still contains a proof hole",
    });

    expect(state.stage_completed).toBe("2");
    expect(state.flags.proof_review_escalation_pending).toEqual({
      route: "hint",
      reason: "headline theorem still contains a proof hole",
    });
    expect(stateSchema.parse(state).flags.proof_review_escalation_pending).toEqual(
      state.flags.proof_review_escalation_pending,
    );
  });

  it("resume from an escalation checkpoint re-enters F2.5", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-proof-review-resume-"));
    const qid = "eid_guard";
    const specialization = "v1";
    const state = createInitialState(qid);
    recordProofReviewOutcome(state, {
      status: "escalate",
      route: "fix-source",
      reason: "unresolved theorem hole",
    });
    await saveState(repoRoot, qid, specialization, state);

    const ctx: PipelineContext = {
      repoRoot,
      qid,
      specialization,
      dryRun: true,
      resume: true,
    };
    const entered: Stage[] = [];
    const resumed = await runPipeline(ctx, async ({ stage }) => {
      entered.push(stage);
      return {
        stage,
        status: "checkpoint",
        completedStage: "2",
        message: "test proof-review checkpoint",
      };
    });

    expect(entered).toEqual(["2.5"]);
    expect(resumed.stage_completed).toBe("2");
    expect(resumed.flags.proof_review_escalation_pending).toBeTruthy();
  });

  it.each(["3", "3.5", "4", "5"] as const)(
    "blocks stale entry into F%s and rewinds to F2 without advancing",
    async (stage) => {
      const state = createInitialState("eid_guard");
      state.stage_completed = stage;
      state.flags.proof_review_escalation_pending = {
        route: "bank-partial",
        reason: "proof obligations remain",
      };

      const result = await runFormalizationStage({
        ctx: {
          repoRoot: "/tmp/unused",
          qid: "eid_guard",
          specialization: "v1",
          dryRun: false,
          resume: true,
        },
        state,
        stage,
        // The guard must fire before any legacy/F5 dependency is touched.
        deps: {} as StageDeps,
      });

      expect(result).toMatchObject({
        stage,
        status: "checkpoint",
        advance: false,
        completedStage: "2",
      });
      expect(result?.status).not.toBe("skipped");
      expect(state.stage_completed).toBe("2");
      expect(state.flags.proof_review_escalation_pending).toBeTruthy();
    },
  );

  it("clears the marker only on genuine proof-review completion", () => {
    const state = createInitialState("eid_guard");
    state.stage_completed = "2";
    state.flags.proof_review_escalation_pending = {
      route: "hint",
      reason: "unresolved",
    };

    recordProofReviewOutcome(state, { status: "completed" });

    expect(state.flags.proof_review_escalation_pending).toBeNull();
    // The pipeline owns the later F4 advancement after the completed result.
    expect(state.stage_completed).toBe("2");
  });
});
