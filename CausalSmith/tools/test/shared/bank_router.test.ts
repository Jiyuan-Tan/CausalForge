/**
 * Unit tests for the shared bank-router primitive.
 *
 * Covers the contract used by both study-pipeline run-level quarantine
 * (`bin/study_bank.ts`) and causalsmith theorem-level failure banking
 * (`bin/bank_entry.ts --tier failed`).
 */
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { routeToBank } from "../../src/shared/bank_router.js";

let tmp: string;

beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "bank-router-"));
});

afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("routeToBank", () => {
  it("throws when the source directory does not exist", async () => {
    const src = path.join(tmp, "nope");
    const dst = path.join(tmp, "_failed", "manual", "nope");
    await expect(
      routeToBank({ srcDir: src, destDir: dst, reason: "manual" }),
    ).rejects.toThrow(/Source directory not found/);
  });

  it("refuses to overwrite an existing destination", async () => {
    const src = path.join(tmp, "run_a");
    await mkdir(src, { recursive: true });
    const dst = path.join(tmp, "_failed", "manual", "run_a");
    await mkdir(dst, { recursive: true });
    await expect(
      routeToBank({ srcDir: src, destDir: dst, reason: "manual" }),
    ).rejects.toThrow(/Destination already exists/);
  });

  it("happy path: moves the dir, creates the parent, writes BANK_REASON.md with reason", async () => {
    const src = path.join(tmp, "run_b");
    await mkdir(src, { recursive: true });
    await writeFile(path.join(src, "state.json"), "{}");
    const dst = path.join(tmp, "_failed", "scaffold_failed", "run_b");

    const result = await routeToBank({
      srcDir: src,
      destDir: dst,
      reason: "scaffold_failed",
    });

    expect(result.dest).toBe(dst);
    expect(existsSync(src)).toBe(false);
    expect(existsSync(dst)).toBe(true);
    expect(existsSync(path.join(dst, "state.json"))).toBe(true);

    const md = await readFile(path.join(dst, "BANK_REASON.md"), "utf8");
    expect(md).toContain("Reason: scaffold_failed");
    expect(md).toMatch(/Banked at: \d{4}-\d{2}-\d{2}T/);
    // No note → no "- Note:" line.
    expect(md).not.toMatch(/^- Note:/m);
  });

  it("optional-note round-trip: note appears in BANK_REASON.md when provided", async () => {
    const src = path.join(tmp, "run_c");
    await mkdir(src, { recursive: true });
    const dst = path.join(tmp, "_failed", "proof_fill_failed", "run_c");

    await routeToBank({
      srcDir: src,
      destDir: dst,
      reason: "proof_fill_failed",
      note: "exhausted Stage 3 retries at depth 7",
      identifier: "bt_run_c",
    });

    const md = await readFile(path.join(dst, "BANK_REASON.md"), "utf8");
    expect(md).toContain("# Banked failed entry: bt_run_c");
    expect(md).toContain("Reason: proof_fill_failed");
    expect(md).toContain("Note: exhausted Stage 3 retries at depth 7");
  });
});
