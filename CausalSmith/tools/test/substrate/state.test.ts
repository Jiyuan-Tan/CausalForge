// CausalSmith/tools/test/substrate/state.test.ts
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { createInitialSubstrateState, loadSubstrateState, saveSubstrateState, substrateStateExists } from "../../src/substrate/state.js";
import { substrateLeanDir, substrateStatePath } from "../../src/substrate/paths.js";

let root: string;
beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "substate-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("substrate state", () => {
  it("creates an initial build-phase state", () => {
    const s = createInitialSubstrateState("x");
    expect(s.phase).toBe("build");
    expect(s.buildRounds).toBe(0);
  });
  it("reports non-existence before save", async () => {
    expect(await substrateStateExists(root, "x")).toBe(false);
  });
  it("round-trips through save/load", async () => {
    const s = createInitialSubstrateState("x");
    s.buildRounds = 2;
    s.phase = "review";
    await saveSubstrateState(root, "x", s);
    expect(await substrateStateExists(root, "x")).toBe(true);
    const loaded = await loadSubstrateState(root, "x");
    expect(loaded.buildRounds).toBe(2);
    expect(loaded.phase).toBe("review");
  });

  it("migrates a resumable legacy verdict to a fresh layering review", async () => {
    const s = createInitialSubstrateState("x") as any;
    s.phase = "coordinate";
    s.lastReview = {
      pass: true, findings: "old pass",
      checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true },
    };
    delete s.layeringReviewStatus;
    await mkdir(path.dirname(substrateStatePath(root, "x")), { recursive: true });
    await mkdir(substrateLeanDir(root, "x"), { recursive: true });
    await writeFile(substrateStatePath(root, "x"), JSON.stringify(s), "utf8");
    const loaded = await loadSubstrateState(root, "x");
    expect(loaded.phase).toBe("review");
    expect(loaded.lastReview?.pass).toBe(false);
    expect(loaded.lastReview?.checks.layered).toBe(false);
    expect(loaded.layeringReviewStatus).toBe("legacy-unreviewed");
  });

  it("preserves a completed legacy state but marks it for a separate audit", async () => {
    const s = createInitialSubstrateState("x") as any;
    s.phase = "done";
    s.lastReview = {
      pass: true, findings: "old pass",
      checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true },
    };
    delete s.layeringReviewStatus;
    await mkdir(path.dirname(substrateStatePath(root, "x")), { recursive: true });
    await writeFile(substrateStatePath(root, "x"), JSON.stringify(s), "utf8");
    const loaded = await loadSubstrateState(root, "x");
    expect(loaded.phase).toBe("done");
    expect(loaded.lastReview?.pass).toBe(false);
    expect(loaded.layeringReviewStatus).toBe("legacy-unreviewed");
    expect(loaded.terminalMessage).toMatch(/audit the promoted modules separately/);
  });
});
