/**
 * Integration coverage for `bin/bank_entry.ts` routing-by-kind + study-mode
 * failure tier.
 *
 * Asserts (all routes exercise the real CLI surface end-to-end):
 *   - Study qid + `--tier failed --reason nl_review_rejected`
 *       → `_literature_bank/_failed/nl_review_rejected/<bt_id>/`,
 *         with a BANK_REASON.md alongside the README.
 *   - Study qid + `--tier failed` (no reason) → error listing valid values.
 *   - Study qid + `--tier failed --reason bogus_reason` → error.
 *   - Study qid + `--tier accepted` → `_literature_bank/accepted/<bt_id>/`
 *         (symmetric with `_bank/accepted/`; study-pipeline S5 routes whole-paper
 *         successes here).
 *   - Research qid + `--tier failed` → `_bank/failed/<bt_id>/`; --reason
 *         not required (preserves pre-change behavior).
 */
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { execFile } from "node:child_process";
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";
import os from "node:os";
import path from "node:path";

const exec = promisify(execFile);
const __dirname = path.dirname(fileURLToPath(import.meta.url));
const BANK_ENTRY = path.resolve(__dirname, "..", "..", "bin", "bank_entry.ts");
// Use node + tsx/cli.mjs instead of `npx tsx`: on Windows, execFile
// cannot launch the `.cmd` shim and (under Node 20+) `shell: true`
// breaks argument quoting for paths with spaces.
const TOOLS_ROOT = path.resolve(__dirname, "..", "..");
const TSX_CLI = path.resolve(TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");

let repoRoot: string;

async function makePackageRoot(): Promise<string> {
  const root = await mkdtemp(path.join(os.tmpdir(), "bank-entry-lit-"));
  await writeFile(path.join(root, "lakefile.toml"), `name = "CausalSmith"\n`, "utf8");
  await mkdir(path.join(root, "doc", "study", "nodes", "open_question"), { recursive: true });
  return root;
}

async function seedRunDir(args: {
  repoRoot: string;
  kind: "research" | "study";
  qid: string;
  spec: string;
  state: Record<string, unknown>;
}): Promise<string> {
  const dir = args.kind === "research"
    ? path.join(args.repoRoot, "doc", "research", "active", args.qid)
    : path.join(args.repoRoot, "doc", "study", "runs", args.qid);
  await mkdir(dir, { recursive: true });
  await writeFile(
    path.join(dir, `${args.qid}_${args.spec}_state.json`),
    JSON.stringify(args.state, null, 2) + "\n",
    "utf8",
  );
  return dir;
}

function baseState(qid: string): Record<string, unknown> {
  return {
    stage_completed: "5",
    lean_subdir: `CausalSmith/Panel/${qid}`,
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
    theorems: [],
  };
}

beforeEach(async () => {
  repoRoot = await makePackageRoot();
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

async function runBankEntry(argv: string[]): Promise<{ stdout: string; stderr: string }> {
  return exec(process.execPath, [TSX_CLI, BANK_ENTRY, ...argv], {
    cwd: repoRoot,
    env: { ...process.env },
  });
}

describe("bank_entry.ts study-mode failure routing", () => {
  it("routes study qid + --tier failed --reason <r> to _literature_bank/_failed/<r>/<bt_id>/", async () => {
    const qid = "manski_demo_insight";
    const spec = "v1";
    await seedRunDir({ repoRoot, kind: "study", qid, spec, state: baseState(qid) });

    await runBankEntry([
      "--qid", qid,
      "--spec", spec,
      "--tier", "failed",
      "--reason", "nl_review_rejected",
    ]);

    const dst = path.join(
      repoRoot, "doc", "study", "_literature_bank", "_failed",
      "nl_review_rejected", `${qid}_${spec}`,
    );
    expect(existsSync(dst)).toBe(true);
    expect(existsSync(path.join(dst, `${qid}_${spec}_state.json`))).toBe(true);
    expect(existsSync(path.join(dst, "README.md"))).toBe(true);
    expect(existsSync(path.join(dst, "BANK_REASON.md"))).toBe(true);

    const md = await readFile(path.join(dst, "BANK_REASON.md"), "utf8");
    expect(md).toContain("Reason: nl_review_rejected");
    expect(md).toContain(`${qid}_${spec}`);

    // Patched state.json carries the bank metadata.
    const patched = JSON.parse(
      await readFile(path.join(dst, `${qid}_${spec}_state.json`), "utf8"),
    );
    expect(patched.banked).toBe(true);
    expect(patched.banked_tier).toBe("failed");
  });

  it("errors when --tier failed is passed for a study qid with no --reason", async () => {
    const qid = "another_insight";
    const spec = "v1";
    await seedRunDir({ repoRoot, kind: "study", qid, spec, state: baseState(qid) });

    await expect(
      runBankEntry([
        "--qid", qid,
        "--spec", spec,
        "--tier", "failed",
      ]),
    ).rejects.toMatchObject({
      stderr: expect.stringContaining("nl_review_rejected"),
    });
  });

  it("errors when --reason is not in LITERATURE_FAILURE_REASONS", async () => {
    const qid = "another_insight";
    const spec = "v1";
    await seedRunDir({ repoRoot, kind: "study", qid, spec, state: baseState(qid) });

    await expect(
      runBankEntry([
        "--qid", qid,
        "--spec", spec,
        "--tier", "failed",
        "--reason", "bogus_reason",
      ]),
    ).rejects.toMatchObject({
      stderr: expect.stringContaining("nl_review_rejected"),
    });
  });

  it("study qid + --tier accepted routes to _literature_bank/accepted/<bt_id>/", async () => {
    const qid = "happy_insight";
    const spec = "v1";
    await seedRunDir({ repoRoot, kind: "study", qid, spec, state: baseState(qid) });

    await runBankEntry([
      "--qid", qid,
      "--spec", spec,
      "--tier", "accepted",
    ]);

    const acceptedDir = path.join(
      repoRoot, "doc", "study", "_literature_bank", "accepted", `${qid}_${spec}`,
    );
    expect(existsSync(acceptedDir)).toBe(true);
    expect(existsSync(path.join(acceptedDir, "README.md"))).toBe(true);
    // Success tiers do NOT drop a BANK_REASON.md.
    expect(existsSync(path.join(acceptedDir, "BANK_REASON.md"))).toBe(false);
    // And the failed-bucket parent must not exist.
    expect(
      existsSync(path.join(repoRoot, "doc", "study", "_literature_bank", "_failed")),
    ).toBe(false);
    // The old flat path must NOT exist alongside the accepted/ subdir.
    expect(
      existsSync(path.join(repoRoot, "doc", "study", "_literature_bank", `${qid}_${spec}`)),
    ).toBe(false);
  });

  it("research qid + --tier failed still routes to _bank/failed/<bt_id>/ without requiring --reason", async () => {
    const qid = "pid_router_smoke";
    const spec = "v1";
    await seedRunDir({ repoRoot, kind: "research", qid, spec, state: baseState(qid) });

    await runBankEntry([
      "--qid", qid,
      "--spec", spec,
      "--tier", "failed",
    ]);

    const dst = path.join(
      repoRoot, "doc", "research", "_bank", "failed", `${qid}_${spec}`,
    );
    expect(existsSync(dst)).toBe(true);
    expect(existsSync(path.join(dst, "README.md"))).toBe(true);
    // Research failed tier should NOT drop BANK_REASON.md (no taxonomy stamp).
    expect(existsSync(path.join(dst, "BANK_REASON.md"))).toBe(false);
    // Literature bank should not have been touched.
    expect(
      existsSync(path.join(repoRoot, "doc", "study", "_literature_bank")),
    ).toBe(false);
  });
});
