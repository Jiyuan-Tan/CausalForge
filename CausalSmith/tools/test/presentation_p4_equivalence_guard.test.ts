import { describe, it, expect, afterAll } from "vitest";
import { writeFile, rm, mkdtemp } from "node:fs/promises";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { blocksMissingEquivalence, stageP4 } from "../src/presentation/stages/p4_emit.js";
import type { StageIO } from "../src/presentation/pipeline.js";

// The P4 equivalence guard reads only `io.outDir` and `io.ctx.deps.dryRun`
// before deciding to block, so a minimal StageIO with a temp outDir exercises it
// without standing up the full pipeline.
const dirs: string[] = [];
async function ioWithCache(cache: unknown): Promise<StageIO> {
  const outDir = await mkdtemp(join(tmpdir(), "p4-guard-"));
  dirs.push(outDir);
  await writeFile(join(outDir, "equivalence_cache.json"), JSON.stringify(cache), "utf8");
  return {
    ctx: { deps: { dryRun: false } },
    outDir,
  } as unknown as StageIO;
}

afterAll(async () => {
  await Promise.all(dirs.map((d) => rm(d, { recursive: true, force: true })));
});

describe("P4 equivalence drift guard", () => {
  it("does not require Lean-equivalence verdicts for presentation-synthesized blocks", () => {
    const missing = blocksMissingEquivalence([
      { obj_id: "synth_1", lean: null },
      { obj_id: "thm:main", lean: { decl: "Main.thm", file: "Main.lean" } },
    ], { "thm:main": { verdict: "faithful" } });
    expect(missing).toEqual([]);
  });

  it("blocks emission while any equivalence verdict is drift", async () => {
    const io = await ioWithCache({
      "P-8": { key: "k", verdict: "drift", detail: "Lean only records the tail-truncation envelope" },
      "P-1": { key: "k2", verdict: "faithful" },
    });
    await expect(stageP4(io)).rejects.toThrow(/P4 blocked.*P-8/s);
  });

  it("names every drifting obj-id in the error", async () => {
    const io = await ioWithCache({
      "P-8": { key: "k", verdict: "drift", detail: "d1" },
      "L-14": { key: "k", verdict: "drift", detail: "d2" },
    });
    await expect(stageP4(io)).rejects.toThrow(/P-8, L-14/);
  });

  it("does not block when all equivalence verdicts are faithful", async () => {
    const io = await ioWithCache({
      "P-8": { key: "k", verdict: "faithful" },
      "P-1": { key: "k2", verdict: "faithful" },
    });
    // It proceeds past the guard and fails later (no paper.tex / frozen_hashes) —
    // the point is the rejection is NOT the equivalence block.
    await expect(stageP4(io)).rejects.not.toThrow(/P4 blocked/);
  });

  it("does not block when the cache is absent", async () => {
    const outDir = await mkdtemp(join(tmpdir(), "p4-guard-"));
    dirs.push(outDir);
    const io = { ctx: { deps: { dryRun: false } }, outDir } as unknown as StageIO;
    await expect(stageP4(io)).rejects.not.toThrow(/P4 blocked/);
  });
});
