import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, mkdir, writeFile, readdir, readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import os from "node:os";
import { migrateQidStores, migrateStoresInDir } from "../../../src/discovery/framework/migrate_stores.js";
import { stores } from "../../../src/discovery/framework/stores.js";
import type { PipelineContext } from "../../../src/types.js";

let tmp: string;
let ctx: PipelineContext;
let disc: string;

beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "migrate-test-"));
  ctx = { repoRoot: tmp, qid: "stat_demo", specialization: "econometrics", dryRun: false, resume: false } as PipelineContext;
  disc = path.join(tmp, "doc", "research", "active", "stat_demo", "discovery");
  await mkdir(disc, { recursive: true });
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("migrateQidStores", () => {
  it("folds legacy 5-file proposals into working.proposals and moves originals to backup", async () => {
    await writeFile(path.join(disc, "d0_working.json"), JSON.stringify({ round: 2, solved: {} }), "utf8");
    await writeFile(
      path.join(disc, "proposed_statement_changes.json"),
      JSON.stringify([{ id: "thm:a", current: "x", proposed: "y" }]),
      "utf8",
    );
    await writeFile(path.join(disc, "proposed_proofs.json"), JSON.stringify([{ id: "thm:a", proof_tex: "P" }]), "utf8");

    const report = await migrateQidStores(ctx);

    const working = await stores.working.load(ctx);
    expect(working.proposals?.statements).toEqual([{ id: "thm:a", current: "x", proposed: "y" }]);
    expect(working.proposals?.proofs).toEqual([{ id: "thm:a", proof_tex: "P" }]);
    expect(working.proposals?.definitions).toEqual([]);
    // originals are gone from the live tree, preserved in the backup
    expect(existsSync(path.join(disc, "proposed_statement_changes.json"))).toBe(false);
    expect(report.backupDir).not.toBeNull();
    const backed = await readdir(report.backupDir as string);
    expect(backed).toContain("proposed_statement_changes.json");
    expect(backed).toContain("d0_working.json"); // pre-fold snapshot
    expect(report.foldedKinds.sort()).toEqual(["proofs", "statements"]);
  });

  it("refuses to fold when working.proposals ALREADY exists and a legacy file also exists (divergence needs a human)", async () => {
    await writeFile(
      path.join(disc, "d0_working.json"),
      JSON.stringify({
        round: 2,
        solved: {},
        proposals: { statements: [], definitions: [], assumptions: [], coreEdits: [], proofs: [] },
      }),
      "utf8",
    );
    await writeFile(path.join(disc, "proposed_proofs.json"), JSON.stringify([{ id: "thm:b", proof_tex: "Q" }]), "utf8");
    await expect(migrateQidStores(ctx)).rejects.toThrow(/both working\.proposals and legacy/i);
  });

  it("normalizes a legacy qid-prefixed store to its canonical nested name", async () => {
    await writeFile(path.join(disc, "stat_demo_proto_core.json"), JSON.stringify({ marker: 1 }), "utf8");
    const report = await migrateQidStores(ctx);
    expect(existsSync(path.join(disc, "proto_core.json"))).toBe(true);
    expect(existsSync(path.join(disc, "stat_demo_proto_core.json"))).toBe(false);
    expect(report.renamed).toContainEqual({ from: "stat_demo_proto_core.json", to: "proto_core.json" });
  });

  it("normalizes a run-prefixed flat store (gaps.json legacy form)", async () => {
    const qidRoot = path.dirname(disc);
    await writeFile(path.join(qidRoot, "stat_demo_econometrics_gaps.json"), JSON.stringify({ n_open_problems: 4 }), "utf8");
    const report = await migrateQidStores(ctx);
    expect(existsSync(path.join(disc, "gaps.json"))).toBe(true);
    expect(report.renamed).toContainEqual({ from: "stat_demo_econometrics_gaps.json", to: "gaps.json" });
  });

  it("is idempotent — a second run reports nothing to do", async () => {
    await writeFile(path.join(disc, "d0_working.json"), JSON.stringify({ round: 1, solved: {} }), "utf8");
    await writeFile(path.join(disc, "proposed_assumptions.json"), JSON.stringify([{ id: "ass:k", condition: "c" }]), "utf8");
    await migrateQidStores(ctx);
    const second = await migrateQidStores(ctx);
    expect(second.foldedKinds).toEqual([]);
    expect(second.renamed).toEqual([]);
    expect(second.backupDir).toBeNull();
  });

  it("a qid with no discovery stores at all is a clean no-op", async () => {
    await rm(disc, { recursive: true, force: true });
    const report = await migrateQidStores(ctx);
    expect(report).toMatchObject({ foldedKinds: [], renamed: [], backupDir: null });
  });
});

describe("migrateStoresInDir (bank-entry shape)", () => {
  let bankDir: string;
  beforeEach(async () => {
    bankDir = path.join(tmp, "doc", "research", "_bank", "accepted", "stat_demo_v1");
    await mkdir(path.join(bankDir, "discovery"), { recursive: true });
  });

  it("folds legacy proposals into the entry's working state and renames the prefixed reviews dir", async () => {
    await writeFile(path.join(bankDir, "discovery", "d0_working.json"), JSON.stringify({ round: 9, solved: {} }), "utf8");
    await writeFile(
      path.join(bankDir, "discovery", "proposed_assumptions.json"),
      JSON.stringify([{ id: "ass:k", condition: "c" }]),
      "utf8",
    );
    await mkdir(path.join(bankDir, "stat_demo_v1_reviews"), { recursive: true });
    await writeFile(path.join(bankDir, "stat_demo_v1_reviews", "review_math.json"), "{}", "utf8");

    const report = await migrateStoresInDir({ runDir: bankDir, qid: "stat_demo", specialization: "v1" });

    const working = JSON.parse(await readFile(path.join(bankDir, "discovery", "d0_working.json"), "utf8"));
    expect(working.proposals.assumptions).toEqual([{ id: "ass:k", condition: "c" }]);
    expect(existsSync(path.join(bankDir, "discovery", "proposed_assumptions.json"))).toBe(false);
    expect(existsSync(path.join(bankDir, "reviews", "review_math.json"))).toBe(true);
    expect(existsSync(path.join(bankDir, "stat_demo_v1_reviews"))).toBe(false);
    expect(report.foldedKinds).toEqual(["assumptions"]);
    expect(report.renamed).toContainEqual({ from: "stat_demo_v1_reviews", to: "reviews" });
    // backup of the pre-fold working + originals exists
    expect(report.backupDir).not.toBeNull();
  });

  it("merges a SPLIT reviews pair file-by-file, dropping identical duplicates", async () => {
    await mkdir(path.join(bankDir, "reviews"), { recursive: true });
    await mkdir(path.join(bankDir, "stat_demo_v1_reviews"), { recursive: true });
    await writeFile(path.join(bankDir, "reviews", "angle0_v1.json"), "{\"a\":1}", "utf8");
    await writeFile(path.join(bankDir, "reviews", "shared.json"), "{\"same\":true}", "utf8");
    await writeFile(path.join(bankDir, "stat_demo_v1_reviews", "stage_1.5_attempt1.json"), "{\"b\":2}", "utf8");
    await writeFile(path.join(bankDir, "stat_demo_v1_reviews", "shared.json"), "{\"same\":true}", "utf8");
    const report = await migrateStoresInDir({ runDir: bankDir, qid: "stat_demo", specialization: "v1" });
    expect(existsSync(path.join(bankDir, "reviews", "angle0_v1.json"))).toBe(true);
    expect(existsSync(path.join(bankDir, "reviews", "stage_1.5_attempt1.json"))).toBe(true);
    expect(existsSync(path.join(bankDir, "stat_demo_v1_reviews"))).toBe(false); // emptied and removed
    expect(report.renamed).toContainEqual({ from: "stat_demo_v1_reviews/stage_1.5_attempt1.json", to: "reviews/stage_1.5_attempt1.json" });
  });

  it("refuses a reviews merge when the same filename differs in content", async () => {
    await mkdir(path.join(bankDir, "reviews"), { recursive: true });
    await mkdir(path.join(bankDir, "stat_demo_v1_reviews"), { recursive: true });
    await writeFile(path.join(bankDir, "reviews", "clash.json"), "{\"v\":1}", "utf8");
    await writeFile(path.join(bankDir, "stat_demo_v1_reviews", "clash.json"), "{\"v\":2}", "utf8");
    await expect(
      migrateStoresInDir({ runDir: bankDir, qid: "stat_demo", specialization: "v1" }),
    ).rejects.toThrow(/reviews merge collision.*clash\.json/s);
  });

  it("is idempotent on an already-canonical entry", async () => {
    await writeFile(path.join(bankDir, "discovery", "d0_working.json"), JSON.stringify({ round: 1, solved: {} }), "utf8");
    await mkdir(path.join(bankDir, "reviews"), { recursive: true });
    const report = await migrateStoresInDir({ runDir: bankDir, qid: "stat_demo", specialization: "v1" });
    expect(report).toMatchObject({ foldedKinds: [], renamed: [], backupDir: null });
  });
});
