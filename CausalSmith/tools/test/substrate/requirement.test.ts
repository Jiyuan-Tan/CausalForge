// CausalSmith/tools/test/substrate/requirement.test.ts
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, readFile, mkdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { REQUIREMENT_TEMPLATE, validateRequirementText, ensureRequirement } from "../../src/substrate/requirement.js";
import { requirementPath } from "../../src/substrate/paths.js";

let root: string;
beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "subreq-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

const FULL = `# Substrate requirement: x
## Goal
Build the Bretagnolle–Huber affinity bound.
## Provides (API contract)
bretagnolle_huber_affinity : ...
## Statement / milestones
½·exp(−KL) ≤ 1 − tvDist
## Standard reference
Bretagnolle–Huber 1979.
## Intended reuse
Le Cam two-point converses.
## May assume / must derive
Assume finite KL; derive the affinity identity.
`;

describe("requirement", () => {
  it("flags missing required sections", () => {
    const r = validateRequirementText("# x\n## Goal\nhi\n");
    expect(r.ok).toBe(false);
    expect(r.missingSections).toContain("Provides");
  });
  it("accepts a fully-filled template", () => {
    expect(validateRequirementText(FULL).ok).toBe(true);
  });
  it("treats an empty section body as missing", () => {
    const r = validateRequirementText(FULL.replace("Bretagnolle–Huber 1979.", ""));
    expect(r.ok).toBe(false);
    expect(r.missingSections).toContain("Standard reference");
  });
  it("bootstraps a template when the file is absent", async () => {
    const res = await ensureRequirement(root, "x");
    expect(res.status).toBe("bootstrapped");
    const written = await readFile(requirementPath(root, "x"), "utf8");
    expect(written).toBe(REQUIREMENT_TEMPLATE);
  });
  it("returns invalid for a present-but-incomplete file", async () => {
    await mkdir(path.dirname(requirementPath(root, "x")), { recursive: true });
    await writeFile(requirementPath(root, "x"), "# x\n## Goal\nhi\n", "utf8");
    const res = await ensureRequirement(root, "x");
    expect(res.status).toBe("invalid");
  });
  it("returns ok for a complete file", async () => {
    await mkdir(path.dirname(requirementPath(root, "x")), { recursive: true });
    await writeFile(requirementPath(root, "x"), FULL, "utf8");
    const res = await ensureRequirement(root, "x");
    expect(res.status).toBe("ok");
    expect(res.text).toBe(FULL);
  });
});
