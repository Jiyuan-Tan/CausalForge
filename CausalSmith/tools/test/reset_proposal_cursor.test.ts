import { mkdir, mkdtemp, writeFile, readFile, access } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import { beforeEach, describe, expect, it } from "vitest";
import { createInitialState, loadState, saveState } from "../src/state.js";
import { proposalTexPath } from "../src/paths.js";
import type { PipelineContext, StateJson } from "../src/types.js";

const exec = promisify(execFile);
const __TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TSX_CLI = path.resolve(__TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");
const BIN = (name: string): string => path.resolve(__TOOLS_ROOT, "bin", name);

const QID = "eid_test_cursor";
const SPEC = "s1";

let repoRoot: string;

function run(bin: string, args: string[]): Promise<{ stdout: string; stderr: string }> {
  return exec(TSX_CLI, [BIN(bin), QID, SPEC, ...args], { cwd: repoRoot, env: { ...process.env } });
}

/** Seed a NO-PASS proposal state: angle 0 converged v1→v6 then pivoted through
 * angles 1–4 (all exhausted) → final_verdict NO-PASS with the cursor parked on
 * the dead angle 4. Also archives angle 0's .tex AND (single-artifact mode) its
 * proto_core.json; the live proto_core.json holds the stale needs-pivot record,
 * and last_draft_handoff holds a stale handoff. */
async function seedNoPass(): Promise<{
  proposalTex: string;
  archive0: string;
  protoCore: string;
  protoArchive0: string;
}> {
  const state = createInitialState(QID);
  state.stage_completed = "-1.2";
  const proposalTex = proposalTexPath(repoRoot, QID, SPEC);
  const dir = path.dirname(proposalTex);
  const archive0 = path.join(dir, "proposal_angle0_rejected.tex");
  const protoCore = path.join(dir, "proto_core.json");
  const protoArchive0 = path.join(dir, "proto_core_angle0_rejected.json");
  (state as StateJson).proposed_from = {
    topic: "minimal-order cumulant direction ID",
    novelty_target: "field",
    pivot_budget_used: 4,
    final_verdict: "NO-PASS",
    proposal_path: proposalTex,
    novelty_justification: "",
    chosen_qid: QID,
    chosen_specialization: SPEC,
    current_angle_index: 4,
    current_version: 1,
    current_mode: "pivot",
    last_draft_status: "needs-pivot",
    last_draft_handoff: '{"status":"needs-pivot","stale":true}',
    exhausted_angles: [0, 1, 2, 3, 4],
    iterations: [
      { angle: 0, version: 1, mode: "revise", verdict: "revise", tier: "field" },
      { angle: 0, version: 5, mode: "revise", verdict: "reject" },
      { angle: 0, version: 6, mode: "draft-rebuild", verdict: "revise", tier: "field" },
      { angle: 4, version: 1, mode: "pivot", verdict: "needs-pivot" },
    ],
    archived_proposals: [archive0],
  } as StateJson["proposed_from"];
  await saveState(repoRoot, QID, SPEC, state);
  await mkdir(dir, { recursive: true });
  await writeFile(archive0, "% angle-0 v6 converged draft\n", "utf8");
  // Live proto_core is the dead needs-pivot record; the good v6 core is archived.
  await writeFile(protoCore, JSON.stringify({ status: "needs-pivot", qid: QID }), "utf8");
  await writeFile(protoArchive0, JSON.stringify({ statements: [{ id: "thm:v6" }], tldr: "v6 core" }), "utf8");
  return { proposalTex, archive0, protoCore, protoArchive0 };
}

const exists = (p: string): Promise<boolean> => access(p).then(() => true, () => false);

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "reset-cursor-"));
  await writeFile(path.join(repoRoot, "lakefile.toml"), `name = "CausalSmith"\n`);
});

describe("reset_proposal_cursor.ts", () => {
  it("resets the cursor to angle 0, revise mode, clears NO-PASS, and un-exhausts the angle", async () => {
    await seedNoPass();
    await run("reset_proposal_cursor.ts", ["--angle", "0"]);
    const pf = (await loadState(repoRoot, QID, SPEC)).proposed_from!;
    expect(pf.current_angle_index).toBe(0);
    expect(pf.current_mode).toBe("revise");
    expect(pf.final_verdict).toBeNull();
    expect(pf.exhausted_angles).toEqual([1, 2, 3, 4]);
  });

  it("defaults current_version to the highest version seen for the target angle", async () => {
    await seedNoPass();
    await run("reset_proposal_cursor.ts", ["--angle", "0"]);
    const pf = (await loadState(repoRoot, QID, SPEC)).proposed_from!;
    // angle-0 iterations reached version 6 → continue from there (producer increments to 7).
    expect(pf.current_version).toBe(6);
  });

  it("restores the archived draft for the angle back to proposal.tex and drops it from archived_proposals", async () => {
    const { proposalTex, archive0 } = await seedNoPass();
    expect(await exists(proposalTex)).toBe(false);
    await run("reset_proposal_cursor.ts", ["--angle", "0"]);
    expect(await exists(proposalTex)).toBe(true);
    expect(await exists(archive0)).toBe(false);
    expect(await readFile(proposalTex, "utf8")).toMatch(/angle-0 v6 converged/);
    const pf = (await loadState(repoRoot, QID, SPEC)).proposed_from!;
    expect(pf.archived_proposals ?? []).not.toContain(archive0);
  });

  it("restores the archived proto_core.json (single-artifact mode) over the stale needs-pivot record", async () => {
    const { protoCore } = await seedNoPass();
    await run("reset_proposal_cursor.ts", ["--angle", "0"]);
    const core = JSON.parse(await readFile(protoCore, "utf8"));
    expect(core.tldr).toBe("v6 core");
    expect(core.status).not.toBe("needs-pivot");
  });

  it("rehydrates an empty seed list from the restored proto core", async () => {
    const { protoArchive0 } = await seedNoPass();
    const core = JSON.parse(await readFile(protoArchive0, "utf8"));
    core.seeds = ["heavy-tail corrected-coverage frontier", "certified-ratio robust WCP"];
    core.seed_details = [{ one_line: "heavy-tail corrected-coverage frontier" }];
    core.literature_map = "known ratio exact; learned ratio corrected";
    await writeFile(protoArchive0, JSON.stringify(core), "utf8");

    await run("reset_proposal_cursor.ts", ["--angle", "0"]);

    const pf = (await loadState(repoRoot, QID, SPEC)).proposed_from!;
    expect(pf.seed_list).toEqual([
      "heavy-tail corrected-coverage frontier",
      "certified-ratio robust WCP",
    ]);
    expect(pf.seed_details).toEqual([{ one_line: "heavy-tail corrected-coverage frontier" }]);
    expect(pf.literature_map).toBe("known ratio exact; learned ratio corrected");
  });

  it("clears the stale draft handoff and marks last_draft_status completed so the loop re-drives the producer", async () => {
    await seedNoPass();
    await run("reset_proposal_cursor.ts", ["--angle", "0"]);
    const pf = (await loadState(repoRoot, QID, SPEC)).proposed_from!;
    // stale needs-pivot handoff must be cleared → loop re-drives the revise producer, not a dead review
    expect(pf.last_draft_handoff ?? "").toBe("");
    expect(pf.last_draft_status).toBe("completed");
  });

  it("fresh-cleans one angle while preserving the D-1.1 gaps harvest", async () => {
    const { protoCore, archive0 } = await seedNoPass();
    const state = await loadState(repoRoot, QID, SPEC);
    state.gaps = {
      gaps_path: path.join(path.dirname(protoCore), "gaps.json"),
      n_open_problems: 4,
      status: "completed",
    };
    state.proposed_from!.angle_checkpoint = {
      kind: "revise",
      angle: 0,
      version: 6,
      verdict: "REVISE",
      reason: "test",
      revise_cap: 6,
    };
    state.proposed_from!.revision_cap_by_angle = { "0": 8 };
    await saveState(repoRoot, QID, SPEC, state);

    const runDir = path.dirname(path.dirname(protoCore));
    const reviewsDir = path.join(runDir, "reviews");
    await mkdir(reviewsDir, { recursive: true });
    await writeFile(path.join(reviewsDir, "angle0_v6.json"), "{}\n", "utf8");
    await writeFile(
      path.join(reviewsDir, "reviews.jsonl"),
      [
        JSON.stringify({ stage: "stage_neg1", report_summary: "angle=0 v6 verdict=REVISE" }),
        JSON.stringify({ stage: "stage_0", report_summary: "keep me" }),
      ].join("\n") + "\n",
      "utf8",
    );
    await writeFile(path.join(path.dirname(protoCore), "dneg1_escalation_log.jsonl"), "{}\n", "utf8");

    await run("reset_proposal_cursor.ts", ["--angle", "0", "--fresh-angle"]);

    const cleaned = await loadState(repoRoot, QID, SPEC);
    const pf = cleaned.proposed_from!;
    expect(cleaned.stage_completed).toBe("-1.1");
    expect(cleaned.gaps).toEqual(state.gaps);
    expect(pf.current_angle_index).toBe(0);
    expect(pf.current_version).toBe(0);
    expect(pf.current_mode).toBe("cold-start");
    expect(pf.angle_checkpoint).toBeUndefined();
    expect(pf.revision_cap_by_angle).toBeUndefined();
    expect(pf.iterations?.some((it) => it.angle === 0)).toBe(false);
    expect(await exists(protoCore)).toBe(false);
    expect(await exists(archive0)).toBe(false);
    expect(await exists(path.join(reviewsDir, "angle0_v6.json"))).toBe(false);
    expect(await readFile(path.join(reviewsDir, "reviews.jsonl"), "utf8")).toContain("keep me");
    expect(await exists(path.join(path.dirname(protoCore), "dneg1_escalation_log.jsonl"))).toBe(false);
  });

  it("errors when the run has no proposed_from (not a --propose run)", async () => {
    await saveState(repoRoot, QID, SPEC, createInitialState(QID));
    await expect(run("reset_proposal_cursor.ts", ["--angle", "0"])).rejects.toThrow();
  });
});
