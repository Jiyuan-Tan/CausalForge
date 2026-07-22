/**
 * End-to-end integration test for bin/bank_entry.ts with mixed theorem outcomes.
 *
 * Fixture: 2 completed + 1 failed-post-0.5 (t2, stage_completed="3") +
 *          1 failed-at-0.5 (t4, stage_completed="0.5").
 *
 * Asserts:
 *   1. Bank dir is created at _bank/accepted/<qid>_<spec>/.
 *   2. Patched state.json has minted_oq_id on t2 only (t4 is gated by Stage 0.5).
 *   3. OQ file exists only for t2; none for t4.
 *   4. OQ has correct schema_version, status, and minted_from backlink.
 *   5. README frontmatter + body reference both failures (minted + skipped rows).
 */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
const exec = promisify(execFile);
// Use node + tsx/cli.mjs instead of `npx tsx`: on Windows, execFile
// cannot launch the `.cmd` shim and (under Node 20+) `shell: true`
// breaks argument quoting for paths with spaces.
const __TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const TSX_CLI = path.resolve(__TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");

const __dirname = path.dirname(fileURLToPath(import.meta.url));

let repoRoot: string;
const QID = "panel_partial_success_test";
const SPEC = "v0";

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "bank-partial-"));
  // Minimal CausalSmith package marker so findRepoRoot resolves to repoRoot.
  await writeFile(
    path.join(repoRoot, "lakefile.toml"),
    `name = "CausalSmith"\n`,
    "utf8",
  );
  await mkdir(path.join(repoRoot, "doc", "research", "active", QID), { recursive: true });
  await mkdir(path.join(repoRoot, "doc", "study", "nodes", "open_question"), { recursive: true });
  await mkdir(path.join(repoRoot, "doc", "research", "active", QID, "discovery"), { recursive: true });
  await mkdir(path.join(repoRoot, "doc", "research", "active", QID, "formalization"), { recursive: true });
  await mkdir(path.join(repoRoot, "CausalSmith", "Panel", QID), { recursive: true });
  await writeFile(path.join(repoRoot, "doc", "research", "active", QID, "discovery", "core.json"), JSON.stringify({
    qid: QID, specialization: SPEC, symbols: [], assumptions: [], definitions: [], statements: [],
    target_estimand: "test target", bibliography: [],
  }));
  await writeFile(path.join(repoRoot, "doc", "research", "active", QID, "formalization", "plan.json"), JSON.stringify({
    qid: QID, specialization: SPEC, env: [], nodes: {}, citations: [], feasibility: "formalizable-now",
  }));
  await writeFile(path.join(repoRoot, "doc", "research", "active", QID, "graph.json"), JSON.stringify({
    qid: QID, specialization: SPEC, nodes: [], edges: [],
  }));
  await writeFile(path.join(repoRoot, "CausalSmith", "Panel", QID, "Basic.lean"), "namespace Test\nend Test\n");

  const state = {
    stage_completed: "5",
    lean_subdir: `CausalSmith/Panel/${QID}`,
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
    theorems: [
      {
        theorem_local_id: "t1",
        origin_theorem_id: `${QID}_t1`,
        statement: "T1 statement.",
        proof_sketch: null,
        status: "completed",
        stage_completed: "5",
        lean_file_relpath: `CausalSmith/Panel/${QID}/T1.lean`,
        bt_id: `${QID}_${SPEC}_t1`,
      },
      {
        theorem_local_id: "t2",
        origin_theorem_id: `${QID}_t2`,
        statement: "T2 statement (the one we could not prove; passed 0.5, failed at Stage 3).",
        proof_sketch: null,
        status: "failed",
        stage_completed: "3",
        lean_file_relpath: `CausalSmith/Panel/${QID}/T2.lean`,
        failure_reason: "stuck at lemma X",
      },
      {
        theorem_local_id: "t3",
        origin_theorem_id: `${QID}_t3`,
        statement: "T3 statement.",
        proof_sketch: null,
        status: "completed",
        stage_completed: "5",
        lean_file_relpath: `CausalSmith/Panel/${QID}/T3.lean`,
        bt_id: `${QID}_${SPEC}_t3`,
      },
      {
        theorem_local_id: "t4",
        origin_theorem_id: `${QID}_t4`,
        statement: "T4 statement (math reviewer rejected at Stage 0.5; should NOT mint OQ).",
        proof_sketch: null,
        status: "failed",
        stage_completed: "0.5",
        lean_file_relpath: null,
        failure_reason: "Stage 0.5 REJECT: counterexample in §3",
      },
    ],
  };
  await writeFile(
    path.join(repoRoot, "doc", "research", "active", QID, `${QID}_${SPEC}_state.json`),
    JSON.stringify(state, null, 2) + "\n",
    "utf8",
  );
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("bank_entry.ts partial-success integration", () => {
  it("mints exactly one OQ for the failed theorem and back-links it", async () => {
    const bankEntryPath = path.resolve(
      __dirname,
      "..",
      "..",
      "bin",
      "bank_entry.ts",
    );
    await exec(
      process.execPath,
      [
        TSX_CLI,
        bankEntryPath,
        "--qid", QID,
        "--spec", SPEC,
        "--tier", "accepted",
        "--reason", "test partial success",
      ],
      { cwd: repoRoot, env: { ...process.env } },
    );

    // 1. Banked dir exists.
    const bankedDir = path.join(
      repoRoot, "doc", "research", "_bank", "accepted", `${QID}_${SPEC}`,
    );
    expect(existsSync(bankedDir)).toBe(true);

    // 2. Patched state.json has minted_oq_id on t2 (failed post-0.5) only.
    //    t4 (failed at 0.5) is gated → minted_oq_id stays undefined.
    const patched = JSON.parse(
      await readFile(path.join(bankedDir, `${QID}_${SPEC}_state.json`), "utf8"),
    );
    const t1 = patched.theorems.find((t: any) => t.theorem_local_id === "t1");
    const t2 = patched.theorems.find((t: any) => t.theorem_local_id === "t2");
    const t3 = patched.theorems.find((t: any) => t.theorem_local_id === "t3");
    const t4 = patched.theorems.find((t: any) => t.theorem_local_id === "t4");
    expect(t1.minted_oq_id).toBeUndefined();
    expect(t3.minted_oq_id).toBeUndefined();
    expect(t2.minted_oq_id).toBe(`oq_failed_${QID}_${SPEC}_t2`);
    expect(t4.minted_oq_id).toBeUndefined(); // Stage 0.5 gate

    // 3. OQ file exists for t2 with correct shape; NO OQ file exists for t4.
    const oqDir = path.join(repoRoot, "doc", "study", "nodes", "open_question");
    const oqPathT2 = path.join(oqDir, `oq_failed_${QID}_${SPEC}_t2.json`);
    const oqPathT4 = path.join(oqDir, `oq_failed_${QID}_${SPEC}_t4.json`);
    expect(existsSync(oqPathT2)).toBe(true);
    expect(existsSync(oqPathT4)).toBe(false);

    const oq = JSON.parse(await readFile(oqPathT2, "utf8"));
    expect(oq.schema_version).toBe(2);
    expect(oq.status).toBe("open");
    expect(oq.minted_from).toEqual({
      qid: QID,
      spec: SPEC,
      theorem_local_id: "t2",
      lean_file_relpath: `CausalSmith/Panel/${QID}/T2.lean`,
      failure_reason: "stuck at lemma X",
    });

    // 4. README frontmatter + body reference BOTH failures (one minted, one skipped).
    const readme = await readFile(path.join(bankedDir, "README.md"), "utf8");
    expect(readme).toMatch(/failed_theorems:/);
    expect(readme).toMatch(new RegExp(`minted_oq_id:\\s*"?oq_failed_${QID}_${SPEC}_t2"?`));
    expect(readme).toMatch(/skipped_reason:/);
    expect(readme).toMatch(/stage_at_failure:\s*"?0\.5"?/);
    expect(readme).toMatch(/## Failed theorems/);
    expect(readme).toMatch(/t2.*minted/);
    expect(readme).toMatch(/t4.*skipped/);
  }, 30_000);
});
