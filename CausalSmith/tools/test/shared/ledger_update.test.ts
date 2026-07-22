import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { updateLedgerFile } from "../../src/shared/ledger_update.js";

const HEADER = "| gate | run |\n| --- | --- |\n";

let dir = "";
let file = "";

beforeEach(async () => {
  dir = await mkdtemp(join(tmpdir(), "ledger-update-"));
  file = join(dir, "SUBSTRATE_DEBT.md");
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("updateLedgerFile", () => {
  it("seeds the header when the ledger does not exist yet", async () => {
    const out = await updateLedgerFile(file, HEADER, (b) => b + "| a | r1 |\n");
    expect(out).toBe(file);
    expect(await readFile(file, "utf8")).toBe(HEADER + "| a | r1 |\n");
  });

  it("returns undefined and does not rewrite when the mutation is a no-op", async () => {
    await updateLedgerFile(file, HEADER, (b) => b + "| a | r1 |\n");
    const before = await readFile(file, "utf8");
    const out = await updateLedgerFile(file, HEADER, (b) => b);
    expect(out).toBeUndefined();
    expect(await readFile(file, "utf8")).toBe(before);
  });

  // The defect this replaces: two runs each did read → append → write with no lock, so the
  // second write was computed from a snapshot taken before the first landed and erased its row.
  it("does not lose rows when many writers append concurrently", async () => {
    const runs = Array.from({ length: 12 }, (_, i) => `r${i}`);
    await Promise.all(
      runs.map((r) => updateLedgerFile(file, HEADER, (b) => b + `| gate | ${r} |\n`)),
    );
    const body = await readFile(file, "utf8");
    for (const r of runs) expect(body).toContain(`| gate | ${r} |\n`);
    // Header is `| gate | run |`; count only the appended run rows.
    expect(body.split("\n").filter((l) => /^\| gate \| r\d+ \|/.test(l))).toHaveLength(runs.length);
  });

  it("preserves rows written by another process between two of this process's updates", async () => {
    await updateLedgerFile(file, HEADER, (b) => b + "| a | r1 |\n");
    // Simulate an out-of-band writer landing a row.
    await writeFile(file, (await readFile(file, "utf8")) + "| b | r2 |\n", "utf8");
    await updateLedgerFile(file, HEADER, (b) => b + "| c | r3 |\n");
    const body = await readFile(file, "utf8");
    expect(body).toContain("| a | r1 |");
    expect(body).toContain("| b | r2 |");
    expect(body).toContain("| c | r3 |");
  });

  it("leaves no partial file behind when the mutation throws", async () => {
    await updateLedgerFile(file, HEADER, (b) => b + "| a | r1 |\n");
    const before = await readFile(file, "utf8");
    await expect(
      updateLedgerFile(file, HEADER, () => {
        throw new Error("mutation failed");
      }),
    ).rejects.toThrow("mutation failed");
    expect(await readFile(file, "utf8")).toBe(before);
  });
});
