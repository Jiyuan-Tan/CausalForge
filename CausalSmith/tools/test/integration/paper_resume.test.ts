import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { initializeOrLoadState } from "../../src/pipeline.js";
import { loadState, saveState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { canonicalLeanSubdir } from "../../src/paths.js";
import type { PipelineContext } from "../../src/types.js";

describe("paper_resume — mid-run state preservation", () => {
  it("mid-run state survives save/load round-trip with all per-theorem fields preserved", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-paper-midrun-"));
    const qid = "ins1";
    const spec = "v1";

    // Construct a mid-run state with stage_completed = "3" and theorems array
    // containing mixed statuses: completed, stuck, and pending.
    const midRunState: StateJson = {
      stage_completed: "3",
      lean_subdir: canonicalLeanSubdir(qid),
      pending_sorries: [],
      design_decisions: { "design_key": "design_value" },
      added_assumptions: [],
      flags: { local_fix_from_4d: false, missing_architecture: false },
      theorems: [
        {
          theorem_local_id: "t1",
          origin_theorem_id: "ins1_t1",
          statement: "If A then B.",
          proof_sketch: "Apply L.",
          status: "completed",
          stage_completed: "3",
          lean_file_relpath: "Theorem_t1.lean",
          lean_decl_name: "t1_thm",
          bt_id: "ins1_t1_v1",
        },
        {
          theorem_local_id: "t2",
          origin_theorem_id: "ins1_t2",
          statement: "If B then C.",
          proof_sketch: "Apply L2.",
          status: "stuck",
          stage_completed: "2",
          lean_file_relpath: "Theorem_t2.lean",
          lean_decl_name: "t2_thm",
          failure_reason: "Codex timeout on proof fill",
        },
        {
          theorem_local_id: "t3",
          origin_theorem_id: "ins1_t3",
          statement: "If C then D.",
          proof_sketch: null,
          status: "pending",
          stage_completed: null,
          lean_file_relpath: null,
        },
      ],
      current_theorem_index: 1,
    };

    // Save the state
    await saveState(repoRoot, qid, spec, midRunState);

    // Load it back
    const loaded = await loadState(repoRoot, qid, spec);

    // Verify stage_completed is preserved
    expect(loaded.stage_completed).toBe("3");

    // Verify theorems array has length 3
    expect(loaded.theorems).toHaveLength(3);

    // Verify t1 (completed entry)
    expect(loaded.theorems?.[0]).toMatchObject({
      theorem_local_id: "t1",
      origin_theorem_id: "ins1_t1",
      statement: "If A then B.",
      proof_sketch: "Apply L.",
      status: "completed",
      stage_completed: "3",
      lean_file_relpath: "Theorem_t1.lean",
      lean_decl_name: "t1_thm",
      bt_id: "ins1_t1_v1",
    });
    expect(loaded.theorems?.[0].failure_reason).toBeUndefined();

    // Verify t2 (stuck entry with failure_reason)
    expect(loaded.theorems?.[1]).toMatchObject({
      theorem_local_id: "t2",
      origin_theorem_id: "ins1_t2",
      statement: "If B then C.",
      proof_sketch: "Apply L2.",
      status: "stuck",
      stage_completed: "2",
      lean_file_relpath: "Theorem_t2.lean",
      lean_decl_name: "t2_thm",
      failure_reason: "Codex timeout on proof fill",
    });
    expect(loaded.theorems?.[1].bt_id).toBeUndefined();

    // Verify t3 (pending entry with nulls)
    expect(loaded.theorems?.[2]).toMatchObject({
      theorem_local_id: "t3",
      origin_theorem_id: "ins1_t3",
      statement: "If C then D.",
      proof_sketch: null,
      status: "pending",
      stage_completed: null,
      lean_file_relpath: null,
    });
    expect(loaded.theorems?.[2].lean_decl_name).toBeUndefined();
    expect(loaded.theorems?.[2].bt_id).toBeUndefined();

    // Verify current_theorem_index
    expect(loaded.current_theorem_index).toBe(1);

    // Verify other state fields
    expect(loaded.lean_subdir).toBe(canonicalLeanSubdir(qid));
    expect(loaded.design_decisions).toEqual({ design_key: "design_value" });
  });

  it("initializeOrLoadState with --resume over mid-run state returns theorems[] intact", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-paper-midrun-init-"));
    const qid = "ins2";
    const spec = "v1";

    // Create doc/study/runs/<qid>/<qid>_<spec>_state.json with mid-run state
    // (qid "ins2" is insight-style → routes under study/)
    const dir = path.join(repoRoot, "doc", "study", "runs", qid);
    await mkdir(dir, { recursive: true });

    const midRunState: StateJson = {
      stage_completed: "2",
      lean_subdir: canonicalLeanSubdir(qid),
      pending_sorries: [
        {
          file: "Theorem_t1.lean",
          line: 42,
          label: "sorry_1",
          goal: "⊢ A ∧ B",
        },
      ],
      design_decisions: { "choice1": "value1" },
      added_assumptions: [
        { label: "a1", statement: "∀ x, P x" },
      ],
      flags: { local_fix_from_4d: false, missing_architecture: false },
      theorems: [
        {
          theorem_local_id: "t1",
          origin_theorem_id: "ins2_t1",
          statement: "Theorem A.",
          proof_sketch: "By induction.",
          status: "in_progress",
          stage_completed: "1.5",
          lean_file_relpath: "Theorem_t1.lean",
          lean_decl_name: "t1_thm",
        },
        {
          theorem_local_id: "t2",
          origin_theorem_id: "ins2_t2",
          statement: "Theorem B.",
          proof_sketch: null,
          status: "pending",
          stage_completed: null,
          lean_file_relpath: null,
        },
      ],
      current_theorem_index: 0,
    };

    await writeFile(
      path.join(dir, `${qid}_${spec}_state.json`),
      JSON.stringify(midRunState),
      "utf8",
    );

    // Initialize with resume=true
    const ctx: PipelineContext = {
      repoRoot,
      qid,
      specialization: spec,
      dryRun: true,
      resume: true,
    };
    const loaded = await initializeOrLoadState(ctx);

    // Verify mid-run stage_completed
    expect(loaded.stage_completed).toBe("2");

    // Verify theorems[] is intact with all fields
    expect(loaded.theorems).toHaveLength(2);

    expect(loaded.theorems?.[0]).toMatchObject({
      theorem_local_id: "t1",
      origin_theorem_id: "ins2_t1",
      statement: "Theorem A.",
      proof_sketch: "By induction.",
      status: "in_progress",
      stage_completed: "1.5",
      lean_file_relpath: "Theorem_t1.lean",
      lean_decl_name: "t1_thm",
    });

    expect(loaded.theorems?.[1]).toMatchObject({
      theorem_local_id: "t2",
      origin_theorem_id: "ins2_t2",
      statement: "Theorem B.",
      proof_sketch: null,
      status: "pending",
      stage_completed: null,
      lean_file_relpath: null,
    });

    // Verify current_theorem_index
    expect(loaded.current_theorem_index).toBe(0);

    // Verify other state fields survive
    expect(loaded.pending_sorries).toHaveLength(1);
    expect(loaded.pending_sorries[0].file).toBe("Theorem_t1.lean");
    expect(loaded.pending_sorries[0].line).toBe(42);
    expect(loaded.design_decisions).toEqual({ choice1: "value1" });
    expect(loaded.added_assumptions).toHaveLength(1);
    expect(loaded.added_assumptions[0].label).toBe("a1");
  });
});
