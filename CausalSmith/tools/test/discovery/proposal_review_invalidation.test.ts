import { access, mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { invalidateCurrentProposalReview } from "../../src/discovery/proposal_review_invalidation.js";
import { applyProposalSourceCorrection } from "../../src/discovery/proposal_source_correction.js";
import { protoCoreJsonPath } from "../../src/discovery/stages/neg1_2_author.js";
import { reviewsDir } from "../../src/paths.js";
import { loadState, saveState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";

let root = "";
afterEach(async () => {
  if (root) await rm(root, { recursive: true, force: true });
  root = "";
});

function state(): StateJson {
  return {
    stage_completed: "-1.2",
    lean_subdir: "CausalSmith/PartialID/PID_Test",
    pending_sorries: [],
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: { local_fix_from_4d: false, missing_architecture: false },
    proposed_from: {
      topic: "test",
      novelty_target: "field",
      pivot_budget_used: 0,
      final_verdict: "NO-PASS",
      proposal_path: "/tmp/proto_core.json",
      novelty_justification: "test",
      chosen_qid: "pid_test",
      chosen_specialization: "v1",
      cluster: "partialid",
      current_angle_index: 0,
      current_version: 6,
      current_mode: "revise",
      last_draft_status: "completed",
      last_draft_handoff: JSON.stringify({ status: "completed" }),
      last_reviewer_verdict: "invalid review",
      iterations: [
        { angle: 0, version: 5, mode: "revise", verdict: "REVISE" },
        { angle: 0, version: 6, mode: "revise", verdict: "REVISE" },
        { angle: 0, version: 6, mode: "revise", verdict: "revise-cap-exhausted" },
      ],
      angle_checkpoint: {
        kind: "angle-boundary",
        angle: 0,
        version: 6,
        verdict: "revise-cap-exhausted",
        reason: "invalid review reached cap",
        revise_cap: 6,
      },
    },
  } as unknown as StateJson;
}

describe("invalidateCurrentProposalReview", () => {
  it("archives only the invalid receipt and reopens the exact authored version", async () => {
    root = await mkdtemp(path.join(os.tmpdir(), "invalidate-neg1-review-"));
    const qid = "pid_test";
    const spec = "v1";
    await saveState(root, qid, spec, state());
    const dir = reviewsDir(root, qid, spec);
    await mkdir(dir, { recursive: true });
    const receipt = path.join(dir, "angle0_v6.json");
    await writeFile(receipt, JSON.stringify({ verdict: "REVISE", proposal_path_read: "stale.tex" }), "utf8");

    const result = await invalidateCurrentProposalReview(root, qid, spec, "reviewer was routed to stale .tex");
    expect(result.removedIterations).toBe(2);
    await expect(access(receipt)).rejects.toThrow();
    expect(JSON.parse(await readFile(result.archivedReview, "utf8"))).toMatchObject({ proposal_path_read: "stale.tex" });

    const saved = await loadState(root, qid, spec);
    expect(saved.proposed_from!.iterations).toEqual([
      { angle: 0, version: 5, mode: "revise", verdict: "REVISE" },
    ]);
    expect(saved.proposed_from!.angle_checkpoint).toBeUndefined();
    expect(saved.proposed_from!.last_reviewer_verdict).toBe("");
    expect(saved.proposed_from!.current_version).toBe(6);
    expect(saved.proposed_from!.last_draft_handoff).toContain("completed");
  });
});

describe("applyProposalSourceCorrection", () => {
  it("changes only literature-facing core and handoff fields without bumping the version", async () => {
    root = await mkdtemp(path.join(os.tmpdir(), "correct-neg1-source-"));
    const qid = "pid_test";
    const spec = "v1";
    const s = state();
    s.proposed_from!.last_draft_handoff = JSON.stringify({
      status: "completed",
      literature_checklist: [{ one_line: "Section 4, Lemma 4 and Theorem 4." }],
    });
    await saveState(root, qid, spec, s);

    const core = JSON.parse(await readFile(
      new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url),
      "utf8",
    )) as Record<string, unknown>;
    core.related_work = "Primary comparison: Section 4, Lemma 4 and Theorem 4.";
    core.comparator_promise_table = [{
      comparator_bibkey: "Primary2025",
      comparator_claim: "Section 4, Lemma 4 and Theorem 4.",
      matched_by: "Theorem 1",
      match_kind: "strict_tightening",
    }];
    const corePath = protoCoreJsonPath({
      repoRoot: root, qid, specialization: spec, dryRun: false, resume: true,
    });
    await mkdir(path.dirname(corePath), { recursive: true });
    await writeFile(corePath, JSON.stringify(core), "utf8");

    const result = await applyProposalSourceCorrection(
      root,
      qid,
      spec,
      "Lemma 4 and Theorem 4",
      "Lemma 1 and Theorem 1",
    );
    expect(result).toMatchObject({ coreReplacements: 2, handoffReplacements: 1 });
    const corrected = JSON.parse(await readFile(corePath, "utf8")) as Record<string, unknown>;
    expect(corrected.related_work).toContain("Lemma 1 and Theorem 1");
    expect(corrected.comparator_promise_table).toEqual([expect.objectContaining({
      comparator_claim: "Section 4, Lemma 1 and Theorem 1.",
    })]);
    const saved = await loadState(root, qid, spec);
    expect(saved.proposed_from!.current_version).toBe(6);
    expect(saved.proposed_from!.last_draft_handoff).toContain("Lemma 1 and Theorem 1");
  });
});
