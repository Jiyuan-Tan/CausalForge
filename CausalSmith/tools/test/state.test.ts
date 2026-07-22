import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { canonicalLeanSubdir, qidToCamel, statePath } from "../src/paths.js";
import { createInitialState, findActiveStates, loadState, saveState, stateSchema } from "../src/state.js";

describe("state schema", () => {
  it("normalizes legacy hook fields without preserving them", () => {
    const parsed = stateSchema.parse({
      stage_completed: "0.5",
      ckpt_pending: false,
      lean_subdir: "CausalSmith/Panel/Q1_GenericMinimality",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: {
        rewound_from_stage4d: null,
        local_fix_from_4d: false,
        bucket_a_blocked: false,
      },
    });

    expect("ckpt_pending" in parsed).toBe(false);
    expect("bucket_a_blocked" in parsed.flags).toBe(false);
    expect(parsed.flags.missing_architecture).toBe(false);
  });

  it("round-trips a valid state and enforces qid/lean_subdir", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-state-"));
    const state = createInitialState("panel_minimal_basis");
    await saveState(repoRoot, "panel_minimal_basis", "p1_bernoulli", state);
    const loaded = await loadState(repoRoot, "panel_minimal_basis", "p1_bernoulli");
    expect(loaded.lean_subdir).toBe("CausalSmith/Panel/PANEL_MinimalBasis_Research");

    const file = statePath(repoRoot, "panel_minimal_basis", "p1_bernoulli");
    expect(await readFile(file, "utf8")).toContain('"stage_completed": "-1.2"');
  });

  it("converts qid to canonical CamelCase Lean subdir with mode suffix", () => {
    // Research-mode qids carry a `_Research` suffix.
    expect(qidToCamel("panel_spectral_threshold")).toBe("PANEL_SpectralThreshold_Research");
    expect(canonicalLeanSubdir("panel_spectral_threshold")).toBe(
      "CausalSmith/Panel/PANEL_SpectralThreshold_Research",
    );
    // Study-mode (insight-style) qids carry a `_Study` suffix.
    expect(qidToCamel("manski_nonparametric_bounds")).toBe("ManskiNonparametricBounds_Study");
  });

  it("rejects drifted lean_subdir", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bad-state-"));
    const state = createInitialState("panel_minimal_basis");
    state.lean_subdir = "CausalSmith/Panel/PANEL_Wrong";
    await expect(saveState(repoRoot, "panel_minimal_basis", "p1_bernoulli", state)).rejects.toThrow(
      /invariant failed/,
    );
  });

  it("accepts proposed_from.final_verdict: null so hand-edited resumes load", () => {
    // Manual operators sometimes need to clear the verdict between resume
    // attempts (e.g. re-run D0 with an upgraded solver on a previously
    // banked proposal). Schema must accept null.
    const parsed = stateSchema.parse({
      stage_completed: "-0.5",
      lean_subdir: "CausalSmith/ExactID/Foo",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { local_fix_from_4d: false, missing_architecture: false },
      proposed_from: {
        topic: "t",
        novelty_target: "flagship",
        pivot_budget_used: 0,
        final_verdict: null,
        proposal_path: "/tmp/p.tex",
        novelty_justification: "",
        chosen_qid: "eid_foo",
        chosen_specialization: "v1",
      },
    });
    expect(parsed.proposed_from?.final_verdict).toBeNull();
  });

  it("accepts proposed_from.iterations[].version: 0 (pre-draft pivot marker)", () => {
    // Historical pipelines emit `version: 0` when pivoting to a new angle
    // before drafting; banked entries with this artifact must load on resume.
    const parsed = stateSchema.parse({
      stage_completed: "-0.5",
      lean_subdir: "CausalSmith/ExactID/Foo",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { local_fix_from_4d: false, missing_architecture: false },
      proposed_from: {
        topic: "t",
        novelty_target: "flagship",
        pivot_budget_used: 0,
        final_verdict: "ACCEPT",
        proposal_path: "/tmp/p.tex",
        novelty_justification: "",
        chosen_qid: "eid_foo",
        chosen_specialization: "v1",
        iterations: [
          { angle: 2, version: 0, mode: "pivot", verdict: "REVISE" },
          { angle: 2, version: 1, mode: "revise", verdict: "REVISE" },
        ],
      },
    });
    expect(parsed.proposed_from?.iterations?.[0].version).toBe(0);
    expect(parsed.proposed_from?.iterations?.[1].version).toBe(1);
  });

  it("finds active states using qid prefix rather than underscore counting", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-active-state-"));
    await saveState(
      repoRoot,
      "panel_minimal_basis",
      "p1_iid_bernoulli",
      createInitialState("panel_minimal_basis"),
    );
    const active = await findActiveStates(repoRoot);
    expect(active).toHaveLength(1);
    expect(active[0].specialization).toBe("p1_iid_bernoulli");
  });

  it("finds study active states whose qid looks research-like", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-active-study-"));
    const qid = "stat_paper_insight";
    const dir = path.join(repoRoot, "doc", "study", "runs", qid);
    await mkdir(dir, { recursive: true });
    await writeFile(path.join(dir, "state.json"), JSON.stringify({
      ...createInitialState(qid),
      specialization: "default",
      qid,
      lean_subdir: "CausalSmith/Stat/STAT_PaperInsight_Research",
    }), "utf8");
    const active = await findActiveStates(repoRoot);
    expect(active.map((a) => a.path)).toEqual([path.join(dir, "state.json")]);
  });
});

describe("StateJson — paper-scoped fields", () => {
  it("stateSchema accepts theorems[] and current_theorem_index", () => {
    const parsed = stateSchema.parse({
      stage_completed: "0.5",
      lean_subdir: "CausalSmith/PartialID/Manski1990",
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
      ],
      current_theorem_index: 0,
    });
    expect(parsed.theorems).toHaveLength(1);
    expect(parsed.theorems?.[0].theorem_local_id).toBe("t1");
    expect(parsed.current_theorem_index).toBe(0);
  });

  it("stateSchema accepts a state with no theorems[] (legacy single-theorem)", () => {
    const parsed = stateSchema.parse({
      stage_completed: "0.5",
      lean_subdir: "CausalSmith/Foo/Bar",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { local_fix_from_4d: false, missing_architecture: false },
    });
    expect(parsed.theorems).toBeUndefined();
    expect(parsed.current_theorem_index).toBeUndefined();
  });

  it("remaps legacy stage strings inside theoremEntrySchema.stage_completed", () => {
    const parsed = stateSchema.parse({
      stage_completed: "0.5",
      lean_subdir: "CausalSmith/PartialID/Manski1990",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { local_fix_from_4d: false, missing_architecture: false },
      theorems: [
        {
          theorem_local_id: "t1",
          origin_theorem_id: "ins1_t1",
          statement: "S",
          proof_sketch: null,
          status: "pending",
          stage_completed: "-1",
          lean_file_relpath: null,
        },
      ],
      current_theorem_index: 0,
    });
    expect(parsed.theorems?.[0].stage_completed).toBe("-1.2");
  });

  it("stateSchema accepts bt_id on a theorems[] entry", () => {
    const parsed = stateSchema.parse({
      stage_completed: "5",
      lean_subdir: "CausalSmith/PartialID/Manski1990",
      pending_sorries: [],
      design_decisions: {},
      added_assumptions: [],
      flags: { local_fix_from_4d: false, missing_architecture: false },
      theorems: [
        {
          theorem_local_id: "t1",
          origin_theorem_id: "manski1990_t1",
          statement: "If A then B.",
          proof_sketch: null,
          status: "completed",
          stage_completed: "5",
          lean_file_relpath: "Theorem_t1.lean",
          bt_id: "manski1990_t1_v1",
        },
      ],
      current_theorem_index: 0,
    });
    expect(parsed.theorems?.[0].bt_id).toBe("manski1990_t1_v1");
  });
});

describe("theoremEntry.minted_oq_id", () => {
  it("round-trips a failed theorem entry with a minted_oq_id", () => {
    const raw = {
      ...createInitialState("panel_minimal_basis"),
      stage_completed: "5",
      theorems: [{
        theorem_local_id: "t1",
        origin_theorem_id: "panel_minimal_basis_t1",
        statement: "...",
        proof_sketch: null,
        status: "failed",
        stage_completed: "3",
        lean_file_relpath: "CausalSmith/Panel/Q1_MinimalBasis/T1.lean",
        failure_reason: "stuck",
        minted_oq_id: "oq_failed_panel_minimal_basis_bernoulli_t1",
      }],
    };
    const parsed = stateSchema.parse(raw);
    expect(parsed.theorems?.[0]?.minted_oq_id).toBe(
      "oq_failed_panel_minimal_basis_bernoulli_t1",
    );
  });

  it("accepts a theorem entry without minted_oq_id (back-compat)", () => {
    const raw = {
      ...createInitialState("panel_minimal_basis"),
      stage_completed: "5",
      theorems: [{
        theorem_local_id: "t1",
        origin_theorem_id: "panel_minimal_basis_t1",
        statement: "...",
        proof_sketch: null,
        status: "completed",
        stage_completed: "5",
        lean_file_relpath: "CausalSmith/Panel/Q1_MinimalBasis/T1.lean",
        bt_id: "panel_minimal_basis_bernoulli",
      }],
    };
    const parsed = stateSchema.parse(raw);
    expect(parsed.theorems?.[0]?.minted_oq_id).toBeUndefined();
  });
});
