import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { initializeOrLoadState, nextStage, reconcilePaperStatus, runPipeline } from "../src/pipeline.js";
import type { PipelineContext, StateJson } from "../src/types.js";
import { canonicalLeanSubdir, pipelineLogPath } from "../src/paths.js";
import { createInitialState, loadState, saveState } from "../src/state.js";
import {
  appendEscalationLog,
  saveWorkingState,
  workingPath,
} from "../src/discovery/stages/d0_working.js";

describe("pipeline", () => {
  it("orders half-stages explicitly", () => {
    expect(nextStage("-1.1")).toBe("-1.2");
    expect(nextStage("-1.2")).toBe("-0.5");
    expect(nextStage("-0.5")).toBe("0");
    expect(nextStage("0")).toBe("0.5");
    expect(nextStage("1")).toBe("1.5");
    expect(nextStage("5")).toBeNull();
  });

  it("dry-runs all stages to completion", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-pipeline-"));
    const ctx: PipelineContext = {
      repoRoot,
      qid: "panel_minimal_basis",
      specialization: "p1_bernoulli",
      resume: false,
      dryRun: true,
    };
    const state = await runPipeline(ctx);
    expect(state.stage_completed).toBe("5");
  });

  it("logs a combined handler at the logical stage it completed", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-combined-log-"));
    const ctx: PipelineContext = {
      repoRoot,
      qid: "panel_combined_log",
      specialization: "v1",
      resume: false,
      dryRun: true,
    };
    await runPipeline(ctx, async ({ stage }) => {
      if (stage === "2.5") {
        return {
          stage,
          status: "completed",
          completedStage: "4",
          message: "combined proof-review loop converged",
        };
      }
      if (stage === "5") return { stage, status: "checkpoint", message: "stop" };
      return { stage, status: "completed", message: "ok" };
    });
    const rows = (await readFile(pipelineLogPath(repoRoot, ctx.qid, ctx.specialization), "utf8"))
      .trim().split("\n").map((line) => JSON.parse(line) as { stage: string; message?: string });
    expect(rows.find((row) => row.message === "combined proof-review loop converged")?.stage).toBe("4");
  });

  it("journals a handler exception as a failed stage event before rethrowing", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-handler-failure-"));
    const ctx: PipelineContext = {
      repoRoot,
      qid: "panel_handler_failure",
      specialization: "v1",
      resume: false,
      dryRun: true,
    };
    await expect(runPipeline(ctx, async ({ stage }) => {
      throw new Error(`handler exploded at ${stage}`);
    })).rejects.toThrow(/handler exploded/);
    const rows = (await readFile(pipelineLogPath(repoRoot, ctx.qid, ctx.specialization), "utf8"))
      .trim().split("\n").map((line) => JSON.parse(line) as { stage: string; status: string; message: string });
    expect(rows.at(-1)).toMatchObject({ stage: "-0.5", status: "failed", message: "handler exploded at -0.5" });
  });

  it("honors stop-after at a combined handler's logical completion stage", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-combined-stop-"));
    const seen: string[] = [];
    const state = await runPipeline(
      {
        repoRoot,
        qid: "panel_combined_stop",
        specialization: "v1",
        resume: false,
        dryRun: true,
      },
      async ({ stage }) => {
        seen.push(stage);
        if (stage === "2.5") {
          return { stage, status: "completed", completedStage: "4", message: "combined completion" };
        }
        return { stage, status: "completed", message: "ok" };
      },
      { stopAfterStage: "4" },
    );
    expect(state.stage_completed).toBe("4");
    expect(seen).not.toContain("5");
  });

  it("persists resume preflight changes before a stage handler can fail", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-preflight-save-"));
    const qid = "stat_preflight_save";
    const spec = "v1";
    const state = createInitialState(qid);
    state.stage_completed = "0";
    (state.flags as unknown as Record<string, unknown>).stage0_budget_exhausted = "old cap";
    await saveState(repoRoot, qid, spec, state);

    await expect(runPipeline(
      { repoRoot, qid, specialization: spec, resume: true, dryRun: true, auto: true },
      async () => { throw new Error("simulated stage crash"); },
      { clearGates: ["stage0_budget_exhausted"] },
    )).rejects.toThrow(/simulated stage crash/);

    const onDisk = await loadState(repoRoot, qid, spec);
    expect(onDisk.auto_mode).toBe(true);
    expect((onDisk.flags as unknown as Record<string, unknown>).stage0_budget_exhausted).toBeUndefined();
  });

  it("plain resume re-enters D0 when durable escalation entries are still unconsumed", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-pending-d0-"));
    const qid = "stat_pending_d0";
    const spec = "v1";
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, resume: true, dryRun: true };
    const state = createInitialState(qid);
    state.stage_completed = "0";
    await saveState(repoRoot, qid, spec, state);
    await mkdir(path.dirname(workingPath(ctx)), { recursive: true });
    await saveWorkingState(ctx, { round: 4, escalation_entries_consumed: 0, solved: {} });
    await appendEscalationLog(ctx, { round: 4, changed: [], directive: "repair stale theorem positioning" });

    const seen: string[] = [];
    await runPipeline(ctx, async ({ stage }) => {
      seen.push(stage);
      return { stage, status: "checkpoint", advance: false, message: "stop after routing check" };
    });
    expect(seen).toEqual(["0"]);
  });

  it("plain resume from completed D0.5 also rewinds to D0 for an unconsumed directive", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-pending-after-d05-"));
    const qid = "stat_pending_after_d05";
    const spec = "v1";
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, resume: true, dryRun: true };
    const state = createInitialState(qid);
    state.stage_completed = "0.5";
    await saveState(repoRoot, qid, spec, state);
    await mkdir(path.dirname(workingPath(ctx)), { recursive: true });
    await saveWorkingState(ctx, { round: 5, escalation_entries_consumed: 0, solved: {} });
    await appendEscalationLog(ctx, { round: 5, changed: [], directive: "repair before formalization" });

    const seen: string[] = [];
    await runPipeline(ctx, async ({ stage }) => {
      seen.push(stage);
      return { stage, status: "checkpoint", advance: false, message: "stop" };
    });
    expect(seen).toEqual(["0"]);
  });

  it("rejects an explicit downstream override while D0 directives are unconsumed", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-pending-override-"));
    const qid = "stat_pending_override";
    const spec = "v1";
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, resume: true, dryRun: true };
    const state = createInitialState(qid);
    state.stage_completed = "0";
    await saveState(repoRoot, qid, spec, state);
    await mkdir(path.dirname(workingPath(ctx)), { recursive: true });
    await saveWorkingState(ctx, { round: 6, escalation_entries_consumed: 0, solved: {} });
    await appendEscalationLog(ctx, { round: 6, changed: [], directive: "must run in D0" });

    await expect(runPipeline(ctx, undefined, { startStage: "0.5" })).rejects.toThrow(
      /refusing --from-stage D0\.5: unconsumed D0 escalation entries/i,
    );
  });

  it("rechecks the directive cursor before an in-process D0-to-D0.5 transition", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-pending-transition-"));
    const qid = "stat_pending_transition";
    const spec = "v1";
    const ctx: PipelineContext = { repoRoot, qid, specialization: spec, resume: true, dryRun: true };
    const state = createInitialState(qid);
    state.stage_completed = "-0.5";
    await saveState(repoRoot, qid, spec, state);
    await mkdir(path.dirname(workingPath(ctx)), { recursive: true });
    await saveWorkingState(ctx, { round: 7, escalation_entries_consumed: 0, solved: {} });

    const seen: string[] = [];
    await runPipeline(ctx, async ({ stage }) => {
      seen.push(stage);
      if (seen.length === 1) {
        await appendEscalationLog(ctx, { round: 7, changed: [], directive: "arrived during live transition" });
        return { stage, status: "completed", message: "D0 returned without consuming late directive" };
      }
      return { stage, status: "checkpoint", advance: false, message: "rerouted before D0.5" };
    }, { startStage: "0" });
    expect(seen).toEqual(["0", "0"]);
  });

  it("logs a combined handler checkpoint at the phase which raised it", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-combined-checkpoint-log-"));
    const ctx: PipelineContext = {
      repoRoot,
      qid: "panel_combined_checkpoint_log",
      specialization: "v1",
      resume: false,
      dryRun: true,
    };
    await runPipeline(ctx, async ({ stage }) => {
      if (stage === "2.5") {
        return { stage: "3" as const, status: "checkpoint" as const, completedStage: "2" as const, message: "F3 filler stalled" };
      }
      return { stage, status: "completed", message: "ok" };
    });
    const rows = (await readFile(pipelineLogPath(repoRoot, ctx.qid, ctx.specialization), "utf8"))
      .trim().split("\n").map((line) => JSON.parse(line) as { stage: string; message?: string });
    expect(rows.find((row) => row.message === "F3 filler stalled")?.stage).toBe("3");
  });

  it("resumes an already-complete state as a no-op", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-resume-"));
    const cold: PipelineContext = {
      repoRoot,
      qid: "panel_minimal_basis",
      specialization: "p1_bernoulli",
      resume: false,
      dryRun: true,
    };
    await runPipeline(cold);
    const resumed = await runPipeline({ ...cold, resume: true });
    expect(resumed.stage_completed).toBe("5");
  });

  it("invalidates cached discovery artifacts on explicit D-1.1 re-entry", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-dneg11-reentry-"));
    const base: PipelineContext = {
      repoRoot,
      qid: "eid_structure_reentry",
      specialization: "v1",
      resume: false,
      dryRun: true,
      proposeTopic: "structure identification topic",
    };

    await runPipeline(base, async ({ stage, state }) => {
      expect(stage).toBe("-1.1");
      state.gaps = {
        gaps_path: path.join(repoRoot, "stale-gaps.json"),
        n_open_problems: 0,
        status: "needs-pivot",
      };
      state.proposed_from = {
        topic: base.proposeTopic!,
        novelty_target: "field",
        pivot_budget_used: 0,
        final_verdict: "pending",
        proposal_path: path.join(repoRoot, "stale-proposal.tex"),
        novelty_justification: "",
        chosen_qid: base.qid,
        chosen_specialization: base.specialization,
        current_angle_index: 1,
        current_version: 0,
        current_mode: "pivot",
        exhausted_angles: [0],
        iterations: [],
        archived_proposals: [],
      };
      return { stage, status: "checkpoint", advance: false, message: "stale scout halt" };
    });

    let observedFreshState = false;
    await runPipeline(
      { ...base, resume: true },
      async ({ stage, state }) => {
        expect(stage).toBe("-1.1");
        expect(state.gaps).toBeUndefined();
        expect(state.proposed_from).toBeUndefined();
        observedFreshState = true;
        return { stage, status: "checkpoint", advance: false, message: "fresh scout reran" };
      },
      { startStage: "-1.1" },
    );
    expect(observedFreshState).toBe(true);
  });

  it("rehydrates the persisted proposal topic on bare D-1.1 resume", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-dneg11-topic-"));
    const qid = "eid_persisted_topic";
    const spec = "v1";
    const state = createInitialState(qid);
    state.gaps = { gaps_path: "stale", n_open_problems: 4, status: "completed" };
    state.proposed_from = {
      topic: "persisted causal topic",
      novelty_target: "field",
      pivot_budget_used: 0,
      final_verdict: "pending",
      proposal_path: "stale-proposal",
      novelty_justification: "stale",
      chosen_qid: qid,
      chosen_specialization: spec,
    };
    await saveState(repoRoot, qid, spec, state);

    let observed = false;
    await runPipeline(
      { repoRoot, qid, specialization: spec, resume: true, dryRun: true },
      async ({ ctx, state: loaded, stage }) => {
        expect(stage).toBe("-1.1");
        expect(ctx.proposeTopic).toBe("persisted causal topic");
        expect(loaded.gaps).toBeUndefined();
        expect(loaded.proposed_from).toBeUndefined();
        observed = true;
        return { stage, status: "checkpoint", advance: false, message: "scout reran" };
      },
      { startStage: "-1.1" },
    );
    expect(observed).toBe(true);
  });

  it("keeps the prior D-1.1 proposal resumable when the fresh scout crashes", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-dneg11-crash-"));
    const qid = "eid_scout_crash";
    const spec = "v1";
    const state = createInitialState(qid);
    state.gaps = { gaps_path: "prior-gaps", n_open_problems: 4, status: "completed" };
    state.proposed_from = {
      topic: "recoverable topic",
      novelty_target: "field",
      pivot_budget_used: 0,
      final_verdict: "pending",
      proposal_path: "prior-proposal",
      novelty_justification: "prior",
      chosen_qid: qid,
      chosen_specialization: spec,
    };
    await saveState(repoRoot, qid, spec, state);

    await expect(runPipeline(
      { repoRoot, qid, specialization: spec, resume: true, dryRun: true },
      async () => { throw new Error("scout crashed"); },
      { startStage: "-1.1" },
    )).rejects.toThrow(/scout crashed/);

    const onDisk = await loadState(repoRoot, qid, spec);
    expect(onDisk.gaps?.gaps_path).toBe("prior-gaps");
    expect(onDisk.proposed_from?.topic).toBe("recoverable topic");
  });

  it("refuses to overwrite an authored but unreviewed D-1.2 draft", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-dneg12-unreviewed-"));
    const qid = "stat_unreviewed_proposal";
    const spec = "v1";
    const state = createInitialState(qid);
    state.stage_completed = "-1.2";
    state.proposed_from = {
      topic: "test topic",
      novelty_target: "field",
      pivot_budget_used: 0,
      final_verdict: "pending",
      proposal_path: path.join(repoRoot, "proto_core.json"),
      novelty_justification: "test",
      chosen_qid: qid,
      chosen_specialization: spec,
      current_angle_index: 0,
      current_version: 1,
      current_mode: "cold-start",
      last_draft_status: "completed",
      exhausted_angles: [],
      iterations: [],
      archived_proposals: [],
    };
    await saveState(repoRoot, qid, spec, state);

    await expect(runPipeline(
      { repoRoot, qid, specialization: spec, resume: true, dryRun: true },
      async ({ stage }) => ({ stage, status: "checkpoint", message: "must not run" }),
      { startStage: "-1.2" },
    )).rejects.toThrow(/authored but unreviewed/);
  });

  it("rejects cold start when the same state is already active", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-active-"));
    const ctx: PipelineContext = {
      repoRoot,
      qid: "panel_minimal_basis",
      specialization: "p1_bernoulli",
      resume: false,
      dryRun: false,
    };
    await expect(runPipeline(ctx, async ({ stage }) => ({
      stage,
      status: "checkpoint",
      message: "stop after first stage",
    }))).resolves.toMatchObject({ stage_completed: "-0.5" });

    await expect(runPipeline(ctx)).rejects.toThrow(/use --resume/);
  });

  it("rejects cold start when a completed state already exists", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-complete-exists-"));
    const ctx: PipelineContext = {
      repoRoot,
      qid: "panel_minimal_basis",
      specialization: "p1_bernoulli",
      resume: false,
      dryRun: true,
    };
    await runPipeline(ctx);
    await expect(runPipeline(ctx)).rejects.toThrow(/use --resume/);
  });

  it("dry-runs an upgrade-mode pipeline end-to-end", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-upgrade-dry-"));
    await writeFile(
      path.join(repoRoot, "lakefile.toml"),
      'name = "CausalSmith"\n',
    );
    const bankDir = path.join(
      repoRoot,
      "doc",
      "research",
      "_bank",
      "accepted",
      "pid_demo_v1",
    );
    await mkdir(bankDir, { recursive: true });
    await writeFile(
      path.join(bankDir, "README.md"),
      `---\nqid: pid_demo\nspec: v1\ntopic: "Demo topic"\nnovelty_target: field\ntier_at_proposal: ACCEPT\ntier_at_derivation: ACCEPT\nreusable_artifacts: []\nseeds_burned: []\nbanked_on: "2026-05-14"\n---\n\n# pid_demo_v1\n`,
    );
    await writeFile(
      path.join(bankDir, "pid_demo_v1_state.json"),
      JSON.stringify({
        stage_completed: "0.5",
        proposed_from: {
          topic: "Demo topic",
          novelty_target: "field",
          cluster: "partialid",
        },
      }),
    );
    await writeFile(
      path.join(bankDir, "pid_demo_v1_proposal.tex"),
      "parent proposal\n",
    );

    const finalState = await runPipeline({
      repoRoot,
      qid: "pid_demo",
      specialization: "v2",
      resume: false,
      dryRun: true,
      proposeTopic: undefined,
      noveltyTarget: "flagship",
      upgradeFrom: {
        parent_qid: "pid_demo",
        parent_spec: "v1",
        parent_tier: "accepted",
        upgrade_axis: "estimation",
      },
    });
    expect(finalState.stage_completed).toBe("5");
  });

  it("blocks resume when flags.stage_neg1_fallback is set", async () => {
    // After a D0.5 reject routes to D-1 (pivot fast-path) and the pivot
    // budget is already exhausted, `intervention_routing` records the
    // verdict in `flags.stage_neg1_fallback`. The pipeline must refuse to
    // resume — otherwise `nextStage("0")` re-enters D0.5 and reproduces
    // the same reject indefinitely.
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-neg1-fallback-"));
    const qid = "eid_foo";
    const spec = "v1";
    const dir = path.join(repoRoot, "doc", "research", "active", qid);
    await mkdir(dir, { recursive: true });
    const seed = {
      stage_completed: "0",
      lean_subdir: canonicalLeanSubdir(qid),
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: {
        local_fix_from_4d: false,
        missing_architecture: false,
        stage_neg1_fallback: "pivot budget exhausted: kernel below flagship",
      },
    };
    await writeFile(path.join(dir, `${qid}_${spec}_state.json`), JSON.stringify(seed), "utf8");

    const ctx: PipelineContext = {
      repoRoot,
      qid,
      specialization: spec,
      dryRun: true,
      resume: true,
    };
    const state = await runPipeline(ctx);
    // The gate logs blocked + saves; stage_completed must NOT advance past "0".
    expect(state.stage_completed).toBe("0");
    expect(state.flags.stage_neg1_fallback).toContain("pivot budget exhausted");
  });

  it("initializeOrLoadState preserves seed theorems[] and current_theorem_index on --resume", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-paper-seed-"));
    const qid = "ins1";
    const spec = "v1";

    // Mimic paper_dispatcher's seed write:
    //   <repoRoot>/doc/study/runs/<qid>/<qid>_<spec>_state.json
    // (qid "ins1" is insight-style → routes under study/) with the lean_subdir
    // invariant that loadState enforces.
    const dir = path.join(repoRoot, "doc", "study", "runs", qid);
    await mkdir(dir, { recursive: true });
    const seed = {
      stage_completed: "0.5",
      lean_subdir: canonicalLeanSubdir(qid),
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { local_fix_from_4d: false, missing_architecture: false },
      theorems: [
        {
          theorem_local_id: "t1",
          origin_theorem_id: "ins1_t1",
          statement: "If A then B.",
          proof_sketch: "Apply L.",
          status: "pending",
          stage_completed: null,
          lean_file_relpath: null,
        },
        {
          theorem_local_id: "t2",
          origin_theorem_id: "ins1_t2",
          statement: "If B then C.",
          proof_sketch: "Apply L2.",
          status: "pending",
          stage_completed: null,
          lean_file_relpath: null,
        },
      ],
      current_theorem_index: 0,
    };
    await writeFile(path.join(dir, `${qid}_${spec}_state.json`), JSON.stringify(seed), "utf8");

    const ctx: PipelineContext = {
      repoRoot,
      qid,
      specialization: spec,
      dryRun: true,
      resume: true,
    };
    const state = await initializeOrLoadState(ctx);
    expect(state.theorems).toHaveLength(2);
    expect(state.theorems?.[0]).toMatchObject({
      theorem_local_id: "t1",
      origin_theorem_id: "ins1_t1",
      status: "pending",
      stage_completed: null,
    });
    expect(state.theorems?.[1]).toMatchObject({
      theorem_local_id: "t2",
      origin_theorem_id: "ins1_t2",
      status: "pending",
      stage_completed: null,
    });
    expect(state.current_theorem_index).toBe(0);
  });
});

describe("reconcilePaperStatus", () => {
  it("returns zero counts when state.theorems is undefined", () => {
    const state = {} as StateJson;
    expect(reconcilePaperStatus(state)).toEqual({
      completed: 0,
      in_progress: 0,
      pending: 0,
      stuck: 0,
      failed: 0,
    });
  });

  it("returns zero counts when state.theorems is empty", () => {
    const state = { theorems: [] } as unknown as StateJson;
    expect(reconcilePaperStatus(state)).toEqual({
      completed: 0,
      in_progress: 0,
      pending: 0,
      stuck: 0,
      failed: 0,
    });
  });

  it("counts by status correctly", () => {
    const state = {
      theorems: [
        {
          theorem_local_id: "t1",
          origin_theorem_id: "ins1_t1",
          statement: "If A then B.",
          proof_sketch: "Apply L.",
          status: "completed",
          stage_completed: "3",
          lean_file_relpath: "Theorem_t1.lean",
        },
        {
          theorem_local_id: "t2",
          origin_theorem_id: "ins1_t2",
          statement: "If B then C.",
          proof_sketch: "Apply L2.",
          status: "completed",
          stage_completed: "3",
          lean_file_relpath: "Theorem_t2.lean",
        },
        {
          theorem_local_id: "t3",
          origin_theorem_id: "ins1_t3",
          statement: "If C then D.",
          proof_sketch: "Apply L3.",
          status: "stuck",
          stage_completed: "1",
          lean_file_relpath: null,
          failure_reason: "No matching lemma",
        },
        {
          theorem_local_id: "t4",
          origin_theorem_id: "ins1_t4",
          statement: "If D then E.",
          proof_sketch: null,
          status: "pending",
          stage_completed: null,
          lean_file_relpath: null,
        },
      ],
    } as StateJson;
    expect(reconcilePaperStatus(state)).toEqual({
      completed: 2,
      in_progress: 0,
      pending: 1,
      stuck: 1,
      failed: 0,
    });
  });

  it("handles all 5 status values", () => {
    const state = {
      theorems: [
        {
          theorem_local_id: "t1",
          origin_theorem_id: "ins1_t1",
          statement: "A.",
          proof_sketch: null,
          status: "pending",
          stage_completed: null,
          lean_file_relpath: null,
        },
        {
          theorem_local_id: "t2",
          origin_theorem_id: "ins1_t2",
          statement: "B.",
          proof_sketch: null,
          status: "in_progress",
          stage_completed: "0",
          lean_file_relpath: null,
        },
        {
          theorem_local_id: "t3",
          origin_theorem_id: "ins1_t3",
          statement: "C.",
          proof_sketch: null,
          status: "completed",
          stage_completed: "5",
          lean_file_relpath: "Theorem_t3.lean",
        },
        {
          theorem_local_id: "t4",
          origin_theorem_id: "ins1_t4",
          statement: "D.",
          proof_sketch: null,
          status: "stuck",
          stage_completed: "2",
          lean_file_relpath: null,
          failure_reason: "Stuck at stage 2",
        },
        {
          theorem_local_id: "t5",
          origin_theorem_id: "ins1_t5",
          statement: "E.",
          proof_sketch: null,
          status: "failed",
          stage_completed: "3",
          lean_file_relpath: null,
          failure_reason: "Failed at stage 3",
        },
      ],
    } as StateJson;
    expect(reconcilePaperStatus(state)).toEqual({
      pending: 1,
      in_progress: 1,
      completed: 1,
      stuck: 1,
      failed: 1,
    });
  });
});
