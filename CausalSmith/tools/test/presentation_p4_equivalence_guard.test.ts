import { describe, it, expect, afterAll } from "vitest";
import { writeFile, rm, mkdtemp, mkdir } from "node:fs/promises";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { blocksMissingEquivalence, stageP4 } from "../src/presentation/stages/p4_emit.js";
import { recordP2Assembly } from "../src/presentation/assembly_freshness.js";
import type { StageIO } from "../src/presentation/pipeline.js";

// The equivalence trust anchor is enforced ONCE, by `blocksMissingEquivalence` at the
// P4 entry (the outer cache-wide drift scan was removed 2026-08: it double-checked the
// same verdicts and blocked forever on verdicts for obj_ids no longer in the layer).
// stageP4 reaches that check after reading paper.tex + the assembly manifest + the
// formal layer, so the integration fixtures below stand those three up minimally.
const dirs: string[] = [];

const block = (obj_id: string, leanBacked: boolean) => ({
  obj_id,
  alias: null,
  kind: "theorem",
  env: "theoremv",
  title: null,
  body: `body of ${obj_id}`,
  ref_set: [],
  lean: leanBacked ? { decl: `${obj_id}.decl`, file: "Mock.lean" } : null,
  status: "matched",
  provenance: "test",
});

async function ioWithFixture(cache: unknown, blocks: unknown[]): Promise<StageIO> {
  const outDir = await mkdtemp(join(tmpdir(), "p4-guard-"));
  dirs.push(outDir);
  await writeFile(join(outDir, "equivalence_cache.json"), JSON.stringify(cache), "utf8");
  await writeFile(join(outDir, "paper.tex"), "\\begin{document}stub\\end{document}\n", "utf8");
  await writeFile(join(outDir, "outline.md"), "# Title\nStub\n# Sections\n", "utf8");
  await writeFile(join(outDir, "appendix_proofs.tex"), "", "utf8");
  await mkdir(join(outDir, "sections"), { recursive: true });
  await mkdir(join(outDir, "proofs"), { recursive: true });
  await recordP2Assembly(outDir);
  await writeFile(join(outDir, "formal_layer.json"), JSON.stringify({ commit: null, blocks }), "utf8");
  return {
    ctx: { deps: { dryRun: false } },
    outDir,
  } as unknown as StageIO;
}

afterAll(async () => {
  await Promise.all(dirs.map((d) => rm(d, { recursive: true, force: true })));
});

describe("P4 equivalence guard (single owner: blocksMissingEquivalence)", () => {
  it("does not require Lean-equivalence verdicts for presentation-synthesized blocks", () => {
    const missing = blocksMissingEquivalence([
      { obj_id: "synth_1", lean: null },
      { obj_id: "thm:main", lean: { decl: "Main.thm", file: "Main.lean" } },
    ], { "thm:main": { verdict: "faithful" } });
    expect(missing).toEqual([]);
  });

  it("a lean-null block with a lingering drift verdict still blocks (mapping removal must not launder drift)", () => {
    const missing = blocksMissingEquivalence(
      [{ obj_id: "P-8", lean: null }],
      { "P-8": { verdict: "drift" } },
    );
    expect(missing.map((b) => b.obj_id)).toEqual(["P-8"]);
  });

  it("flags drift, missing, and unparseable verdicts alike", () => {
    const missing = blocksMissingEquivalence([
      { obj_id: "P-8", lean: { decl: "d", file: "f" } },
      { obj_id: "L-14", lean: { decl: "d", file: "f" } },
      { obj_id: "T-1", lean: { decl: "d", file: "f" } },
    ], { "P-8": { verdict: "drift" }, "L-14": { verdict: "faithful" } });
    expect(missing.map((b) => b.obj_id)).toEqual(["P-8", "T-1"]);
  });

  it("blocks emission while any equivalence verdict is drift, naming id and detail", async () => {
    const io = await ioWithFixture(
      {
        "P-8": { key: "k", verdict: "drift", detail: "Lean only records the tail-truncation envelope" },
        "P-1": { key: "k2", verdict: "faithful" },
      },
      [block("P-8", true), block("P-1", true)],
    );
    await expect(stageP4(io)).rejects.toThrow(/P4 blocked.*P-8.*tail-truncation envelope/s);
  });

  it("does not block on a stale drift verdict for an obj_id no longer in the layer", async () => {
    const io = await ioWithFixture(
      {
        "P-gone": { key: "k", verdict: "drift", detail: "removed from the layer" },
        "P-1": { key: "k2", verdict: "faithful" },
      },
      [block("P-1", true)],
    );
    // It proceeds past the equivalence check and fails later in emission —
    // the point is the rejection is NOT the equivalence block.
    await expect(stageP4(io)).rejects.not.toThrow(/P4 blocked/);
  });

  it("names every blocked obj-id in the error", async () => {
    const io = await ioWithFixture(
      {
        "P-8": { key: "k", verdict: "drift", detail: "d1" },
        "L-14": { key: "k", verdict: "drift", detail: "d2" },
      },
      [block("P-8", true), block("L-14", true)],
    );
    await expect(stageP4(io)).rejects.toThrow(/P-8, L-14/);
  });

  it("does not block when all equivalence verdicts are faithful", async () => {
    const io = await ioWithFixture(
      { "P-8": { key: "k", verdict: "faithful" }, "P-1": { key: "k2", verdict: "faithful" } },
      [block("P-8", true), block("P-1", true)],
    );
    await expect(stageP4(io)).rejects.not.toThrow(/P4 blocked/);
  });
});
