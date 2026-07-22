import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { dischargeMetadata, reopenEntry } from "../bin/bank_entry.js";

/** Lay down a banked research entry at _bank/<tier>/<qid>_<spec>/state.json. */
async function seedBankedEntry(args: {
  repoRoot: string;
  tier: string;
  qid: string;
  spec: string;
  state: Record<string, unknown>;
  files?: Record<string, string>;
}): Promise<string> {
  const dir = path.join(
    args.repoRoot,
    "doc",
    "research",
    "_bank",
    args.tier,
    `${args.qid}_${args.spec}`,
  );
  await mkdir(dir, { recursive: true });
  await writeFile(path.join(dir, "state.json"), JSON.stringify(args.state, null, 2));
  for (const [name, content] of Object.entries(args.files ?? {})) {
    await writeFile(path.join(dir, name), content);
  }
  return dir;
}

describe("reopenEntry", () => {
  it("moves a banked accepted entry back to the working dir and clears banked", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-reopen-"));
    const bankDir = await seedBankedEntry({
      repoRoot,
      tier: "accepted",
      qid: "pid_reopen_test",
      spec: "v1",
      state: { banked: true, banked_tier: "accepted", banked_on: "2026-07-10", stage_completed: "5" },
      files: { "SUBSTRATE_DEBT.md": "# Substrate debt\n\n- **thm:x / Gate** — deferred.\n" },
    });

    const result = await reopenEntry({ repoRoot, qid: "pid_reopen_test", spec: "v1" });

    // Bank dir gone, working dir present with the moved files.
    expect(existsSync(bankDir)).toBe(false);
    const workingDir = path.join(repoRoot, "doc", "research", "active", "pid_reopen_test");
    expect(result.workingDir).toBe(workingDir);
    expect(existsSync(path.join(workingDir, "SUBSTRATE_DEBT.md"))).toBe(true);

    // state.json patched: banked cleared, reopened_from records prior tier.
    const state = JSON.parse(await readFile(path.join(workingDir, "state.json"), "utf8"));
    expect(state.banked).toBe(false);
    expect(state.reopened_from.tier).toBe("accepted");
    expect(state.reopened_from.banked_on).toBe("2026-07-10");
    expect(typeof state.reopened_from.reopened_on).toBe("string");
    expect(result.priorTier).toBe("accepted");
  });

  it("refuses when the working dir already exists", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-reopen-"));
    await seedBankedEntry({
      repoRoot,
      tier: "accepted",
      qid: "pid_reopen_test",
      spec: "v1",
      state: { banked: true, banked_tier: "accepted" },
    });
    const workingDir = path.join(repoRoot, "doc", "research", "active", "pid_reopen_test");
    await mkdir(workingDir, { recursive: true });

    await expect(
      reopenEntry({ repoRoot, qid: "pid_reopen_test", spec: "v1" }),
    ).rejects.toThrow(/working dir/i);
  });

  it("refuses when there is no banked entry to reopen", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-reopen-"));
    await expect(
      reopenEntry({ repoRoot, qid: "pid_missing", spec: "v1" }),
    ).rejects.toThrow(/no banked entry/i);
  });

  it("refuses to reopen a dir that is not marked banked", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "causalsmith-reopen-"));
    await seedBankedEntry({
      repoRoot,
      tier: "accepted",
      qid: "pid_reopen_test",
      spec: "v1",
      state: { banked: false },
    });
    await expect(
      reopenEntry({ repoRoot, qid: "pid_reopen_test", spec: "v1" }),
    ).rejects.toThrow(/not.*banked/i);
  });
});

describe("dischargeMetadata", () => {
  it("returns null for an entry that was never reopened", () => {
    expect(dischargeMetadata({ banked: true } as never, ["thm:x/Gate"])).toBeNull();
  });

  it("stamps revision 1 and the discharged gates on the first re-bank after reopen", () => {
    const meta = dischargeMetadata({ reopened_from: { tier: "accepted" } }, ["thm:x/Gate"]);
    expect(meta).toEqual({ revision: 1, discharged_gates: ["thm:x/Gate"] });
  });

  it("accumulates revision and gate history across successive discharges", () => {
    const meta = dischargeMetadata(
      { reopened_from: { tier: "accepted" }, revision: 1, discharged_gates: ["thm:x/GateA"] },
      ["thm:y/GateB"],
    );
    expect(meta).toEqual({ revision: 2, discharged_gates: ["thm:x/GateA", "thm:y/GateB"] });
  });

  it("bumps revision even when no gate was discharged (plain reopen→re-bank fix)", () => {
    const meta = dischargeMetadata({ reopened_from: { tier: "accepted" } }, []);
    expect(meta).toEqual({ revision: 1, discharged_gates: [] });
  });
});
