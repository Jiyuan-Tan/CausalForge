import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { PROOF_AUDIT_FAILURE_MARKER, runPromotionRound } from "../src/presentation/promotion.js";
import type { PaperDeps, StageIO } from "../src/presentation/pipeline.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function fixture(): Promise<{ repoRoot: string; graphPath: string; outDir: string }> {
  const repoRoot = await mkdtemp(join(tmpdir(), "promo-"));
  dirs.push(repoRoot);
  const bankDir = join(repoRoot, "doc", "research", "_bank", "accepted", "q_v1");
  await mkdir(bankDir, { recursive: true });
  const graphPath = join(bankDir, "graph.json");
  await writeFile(graphPath, JSON.stringify({ nodes: [{ id: "lem:existing" }], edges: [] }), "utf8");
  const outDir = join(repoRoot, "bundle");
  await mkdir(outDir, { recursive: true });
  return { repoRoot, graphPath, outDir };
}

const ioFor = (repoRoot: string, outDir: string, runClaude: PaperDeps["runClaude"]): StageIO => ({
  ctx: { repoRoot, qid: "q", spec: "v1", deps: { runClaude, runCodex: async () => ({ stdout: "", stderr: "" }), dryRun: false }, outDir },
  state: { notes: [] } as unknown as StageIO["state"],
  bank: { leanSubdir: "CausalSmith" } as StageIO["bank"],
  outDir,
});

describe("runPromotionRound", () => {
  it("passes the failure detail and a write-enabled tool set to the agent, returns the added ids", async () => {
    const { repoRoot, graphPath, outDir } = await fixture();
    let call: Parameters<PaperDeps["runClaude"]>[0] | null = null;
    const runClaude: PaperDeps["runClaude"] = async (args) => {
      call = args;
      // The agent edits the bank graph on disk — the only mutation the round validates.
      const g = JSON.parse(await readFile(graphPath, "utf8"));
      g.nodes.push({ id: "lem:promoted-bound" });
      await writeFile(graphPath, JSON.stringify(g), "utf8");
      return "done";
    };
    const added = await runPromotionRound(ioFor(repoRoot, outDir, runClaude), `${PROOF_AUDIT_FAILURE_MARKER}: lem:x Step 4 underived`);
    expect(added).toBe("lem:promoted-bound");
    expect(call!.prompt).toContain("lem:x Step 4 underived");
    expect(call!.prompt).toContain("statement-uses");
    // Deliberate, call-site-visible trust escalation: without Edit/Write/Bash the agent
    // is read-only and the whole round is inert (audit finding F1(i)).
    expect(call!.allowedTools).toEqual(expect.arrayContaining(["Edit", "Write", "Bash"]));
  });

  it("re-raises with the full original audit detail when the agent adds no nodes", async () => {
    const { repoRoot, outDir } = await fixture();
    const io = ioFor(repoRoot, outDir, async () => "did nothing");
    await expect(runPromotionRound(io, "ORIGINAL DETAIL: lem:y Step 6 not self-contained"))
      .rejects.toThrow(/added no nodes[\s\S]*ORIGINAL DETAIL: lem:y Step 6/);
  });
});

// Audit-first reuse: a prior-faithful proof survives a statement change as an audit
// candidate; failing/never-audited proofs must NOT (their redraft path is load-bearing
// for the promotion round).
import { priorFaithfulProofVerdicts } from "../src/presentation/stages/p2_draft.js";
describe("priorFaithfulProofVerdicts", () => {
  it("returns only faithful obj ids; tolerates a missing cache file", async () => {
    const dir = await mkdtemp(join(tmpdir(), "pfv-"));
    dirs.push(dir);
    await writeFile(join(dir, "proof_audit_cache.json"), JSON.stringify({
      "thm:good": { key: "k1", verdict: "faithful", issues: [] },
      "lem:bad": { key: "k2", verdict: "unfaithful", issues: ["x"] },
      "lem:odd": { key: "k3" },
    }), "utf8");
    const set = await priorFaithfulProofVerdicts(dir);
    expect([...set].sort()).toEqual(["thm:good"]);
    expect((await priorFaithfulProofVerdicts(join(dir, "nope"))).size).toBe(0);
  });
});
