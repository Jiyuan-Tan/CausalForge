import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createInitialState, loadState, saveState } from "../src/state.js";
import { proposalTexPath } from "../src/paths.js";
import { applyProposalAngleAction } from "../src/discovery/proposal_angle_checkpoint.js";
import { neg1EscalationLogPath } from "../src/discovery/stageNeg1_directive.js";
import { parseArgsForTest } from "../src/cli.js";

const qid = "stat_angle_checkpoint_test";
const spec = "v1";
let repoRoot: string;

async function seed(kind: "revise" | "angle-boundary") {
  const state = createInitialState(qid);
  const proposal = proposalTexPath(repoRoot, qid, spec);
  state.proposed_from = {
    topic: "test",
    novelty_target: "field",
    pivot_budget_used: 0,
    final_verdict: "pending",
    proposal_path: proposal,
    novelty_justification: "test",
    chosen_qid: qid,
    chosen_specialization: spec,
    current_angle_index: 0,
    current_version: 5,
    current_mode: "revise",
    last_draft_status: "completed",
    last_draft_handoff: "stale-reviewed-draft",
    exhausted_angles: [],
    archived_proposals: [],
    iterations: [],
    angle_checkpoint: {
      kind,
      angle: 0,
      version: 5,
      verdict: "REVISE",
      reason: kind === "revise" ? "reviewer requested revision" : "revision cap exhausted",
      revise_cap: 5,
      next_angle: kind === "angle-boundary" ? 1 : undefined,
    },
  };
  await saveState(repoRoot, qid, spec, state);
  await mkdir(path.dirname(proposal), { recursive: true });
  await writeFile(proposal, "% angle zero\n", "utf8");
  await writeFile(path.join(path.dirname(proposal), "proto_core.json"), "{}\n", "utf8");
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "proposal-angle-checkpoint-"));
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("proposal angle checkpoint actions", () => {
  it("persists a directive before continuing a revise checkpoint", async () => {
    await seed("revise");
    const result = await applyProposalAngleAction({
      repoRoot, qid, specialization: spec, action: "continue", directive: "repair the marginal null",
    });
    expect(result).toMatchObject({ action: "continue", directivePersisted: true, resume: true });
    const state = await loadState(repoRoot, qid, spec);
    expect(state.proposed_from!.angle_checkpoint).toBeUndefined();
    expect(state.proposed_from!.last_draft_handoff).toBeUndefined();
    expect(state.proposed_from!.current_mode).toBe("revise");
    const log = await readFile(neg1EscalationLogPath({
      repoRoot, qid, specialization: spec, dryRun: false, resume: true,
    }), "utf8");
    expect(log).toContain("repair the marginal null");
  });

  it("grants a persisted bounded retry on the same angle", async () => {
    await seed("angle-boundary");
    const result = await applyProposalAngleAction({
      repoRoot, qid, specialization: spec, action: "retry", extraRevisions: 2,
      directive: "replace the failed witness with the literature construction",
    });
    expect(result.reviseCap).toBe(7);
    const state = await loadState(repoRoot, qid, spec);
    expect(state.proposed_from!.revision_cap_by_angle).toEqual({ "0": 7 });
    expect(state.proposed_from!.current_angle_index).toBe(0);
    expect(state.proposed_from!.last_draft_handoff).toBeUndefined();
  });

  it("archives the old artifacts and switches only after explicit action", async () => {
    await seed("angle-boundary");
    const result = await applyProposalAngleAction({
      repoRoot, qid, specialization: spec, action: "switch",
    });
    expect(result.nextAngle).toBe(1);
    const state = await loadState(repoRoot, qid, spec);
    expect(state.proposed_from!.current_angle_index).toBe(1);
    expect(state.proposed_from!.current_version).toBe(0);
    expect(state.proposed_from!.current_mode).toBe("pivot");
    expect(state.proposed_from!.exhausted_angles).toEqual([0]);
    const dir = path.dirname(proposalTexPath(repoRoot, qid, spec));
    await expect(readFile(path.join(dir, "proposal_angle0_rejected.tex"), "utf8"))
      .resolves.toContain("angle zero");
    await expect(readFile(path.join(dir, "proto_core_angle0_rejected.json"), "utf8"))
      .resolves.toContain("{}");
  });

  it("give-up records a resume-blocking terminal proposal decision", async () => {
    await seed("angle-boundary");
    const result = await applyProposalAngleAction({
      repoRoot, qid, specialization: spec, action: "give-up",
    });
    expect(result.resume).toBe(false);
    const state = await loadState(repoRoot, qid, spec);
    expect(state.proposed_from!.final_verdict).toBe("NO-PASS");
    expect(state.flags.stage_neg1_fallback).toContain("give-up");
  });
});

describe("--angle-action parsing", () => {
  it("parses retry with an atomic directive and extra budget", () => {
    const args = parseArgsForTest([
      "--angle-action", "retry", qid, spec,
      "--extra-revisions", "3", "--angle-directive", "-", "--auto",
      "--stop-after", "D-1.2",
    ]);
    expect(args).toMatchObject({
      angleActionMode: true,
      angleAction: "retry",
      extraRevisions: 3,
      angleDirective: "-",
      resume: true,
      auto: true,
      stopAfter: "D-1.2",
    });
  });

  it("rejects extra revision budget on a non-retry action", () => {
    expect(() => parseArgsForTest([
      "--angle-action", "switch", qid, spec, "--extra-revisions", "2",
    ])).toThrow(/only with --angle-action retry/);
  });

  it("requires an explicit cap extension and repair directive for retry", () => {
    expect(() => parseArgsForTest([
      "--angle-action", "retry", qid, spec, "--angle-directive", "repair",
    ])).toThrow(/requires --extra-revisions/);
    expect(() => parseArgsForTest([
      "--angle-action", "retry", qid, spec, "--extra-revisions", "2",
    ])).toThrow(/requires --angle-directive/);
  });

  it("rejects a competing resume cursor on angle-action", () => {
    expect(() => parseArgsForTest([
      "--angle-action", "continue", qid, spec, "--from-stage", "F1",
    ])).toThrow(/resumes at D-1.2/);
  });

  it("rejects a partially numeric retry cap", () => {
    expect(() => parseArgsForTest([
      "--angle-action", "retry", qid, spec,
      "--extra-revisions", "2oops", "--angle-directive", "repair",
    ])).toThrow(/positive-integer/);
  });

  it("does not journal a directive when the requested action is invalid", async () => {
    await seed("angle-boundary");
    await expect(applyProposalAngleAction({
      repoRoot,
      qid,
      specialization: spec,
      action: "continue",
      directive: "must not leak into the next action",
    })).rejects.toThrow(/requires a revise checkpoint/);
    await expect(readFile(neg1EscalationLogPath({
      repoRoot, qid, specialization: spec, dryRun: false, resume: true,
    }), "utf8")).rejects.toThrow();
  });
});
