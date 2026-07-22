import { describe, it, expect, afterAll } from "vitest";
import { rm, access, mkdtemp } from "node:fs/promises";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { runPaperPipeline, type PaperDeps } from "../src/presentation/pipeline.js";
import { loadPaperState } from "../src/presentation/state.js";
import { acceptedBankEntry, causalSmithRoot } from "./helpers.js";

const stubDeps: PaperDeps = {
  runClaude: async () => "STUB",
  runCodex: async () => ({ stdout: "STUB", stderr: "" }),
  dryRun: true,
};

// Track whatever paper is currently banked (dry-run only loads the entry; every stage writes a stub).
const { qid: QID, spec: SPEC } = acceptedBankEntry();

describe("pipeline dry-run (integration)", () => {
  const root = causalSmithRoot();
  // NEVER the real presentationDir: a test run must not clobber live artifacts.
  const dirP = mkdtemp(join(tmpdir(), "causalsmith-dryrun-"));
  afterAll(async () => rm(await dirP, { recursive: true, force: true }));

  it("P0→P1 stops at outline checkpoint; resumes through draft to done", async () => {
    const dir = await dirP;
    const base = { repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, outDir: dir };
    const r1 = await runPaperPipeline(base);
    expect(r1.halt).toBe("checkpoint:outline");
    const s1 = await loadPaperState(dir, QID, SPEC);
    expect(s1!.stage_completed).toBe("P1");
    expect(s1!.checkpoint_pending).toBe("outline");

    const r2 = await runPaperPipeline({ ...base, resume: true });
    expect(r2.halt).toBe("checkpoint:draft");

    const r3 = await runPaperPipeline({ ...base, resume: true });
    expect(r3.halt).toBe("done");
    await access(join(dir, "p4.stub"));
    await access(join(dir, "p5.stub")); // P5 referee review runs as the terminal stage
    const s3 = await loadPaperState(dir, QID, SPEC);
    expect(s3!.stage_completed).toBe("P5");
  });

  it("--stop-after halts without checkpoint", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun2-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, stopAfter: "P0", outDir: dir,
      });
      expect(r.halt).toBe("stopped:P0");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("--auto approves P1/P2 checkpoints and runs smoothly through P5", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun-auto-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, auto: true, outDir: dir,
      });
      expect(r.halt).toBe("done");
      await access(join(dir, "p1.stub"));
      await access(join(dir, "p2.stub"));
      await access(join(dir, "p5.stub"));
      const state = await loadPaperState(dir, QID, SPEC);
      expect(state!.stage_completed).toBe("P5");
      expect(state!.checkpoint_pending).toBeNull();
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("--auto still respects explicit --stop-after", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun-auto-stop-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, auto: true, stopAfter: "P1", outDir: dir,
      });
      expect(r.halt).toBe("stopped:P1");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("--max-p5-reviews counts the initial P5 pass", async () => {
    const dir = await mkdtemp(join(tmpdir(), "causalsmith-dryrun-p5-cap-"));
    try {
      const r = await runPaperPipeline({
        repoRoot: root, qid: QID, spec: SPEC, deps: stubDeps, auto: true, maxP5Reviews: 1, outDir: dir,
      });
      expect(r.halt).toBe("p5:review-cap");
      const state = await loadPaperState(dir, QID, SPEC);
      expect(state!.stage_completed).toBe("P5");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
