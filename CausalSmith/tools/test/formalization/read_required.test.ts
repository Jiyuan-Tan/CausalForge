import { describe, it, expect } from "vitest";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { readRequired } from "../../src/pipeline_support.js";
import { planGatePrelint } from "../../src/formalization/stage1_5.js";

describe("readRequired", () => {
  it("throws a named fault on a missing file", async () => {
    await expect(readRequired(join(tmpdir(), "does-not-exist.json"), "F1.5 review")).rejects.toThrow(
      /F1\.5 review: required input missing/,
    );
  });
  it("reads an existing file", async () => {
    const dir = mkdtempSync(join(tmpdir(), "rr-"));
    writeFileSync(join(dir, "a.txt"), "content");
    expect(await readRequired(join(dir, "a.txt"), "x")).toBe("content");
  });
});

describe("planGatePrelint fail-loud core", () => {
  it("throws when core.json is missing instead of skipping the gate", async () => {
    const repoRoot = mkdtempSync(join(tmpdir(), "f15-"));
    const ctx = { repoRoot, qid: "q", specialization: "s" } as never;
    await expect(planGatePrelint({ ctx, state: { flags: {} } as never }, join(repoRoot, "plan.json"))).rejects.toThrow(
      /F1\.5 plan gate: required input missing/,
    );
  });
});
