import { describe, it, expect } from "vitest";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { dryRunBundle, findBundles, forbiddenCodex } from "../src/presentation/nl_links_dry.js";

const BUNDLE_ROOT = path.join(import.meta.dirname, "..", "..", "doc", "presentation");

/**
 * The sub-step ran paid on exactly one bundle before this suite existed. It
 * keeps the guarantee the operator CLI gives: every FREE pass — selection,
 * extraction, closure, both prompts, cache and artifact read sides — works on
 * every real bundle shape, so a new bundle fails here rather than halfway
 * through a paid run.
 */
describe("nl-links free passes on every real bundle", () => {
  it("has a codex double that refuses to be called", async () => {
    await expect(forbiddenCodex.runCodex()).rejects.toThrow(/free pass is not free/);
  });

  it("sweeps every bundle without an error or extraction failure", async () => {
    const dirs = await findBundles(BUNDLE_ROOT);
    if (dirs.length === 0) {
      console.warn("nl-links sweep: no bundles under doc/presentation — nothing to check");
      expect(dirs).toEqual([]);
      return;
    }
    const reports = await Promise.all(dirs.map(dryRunBundle));
    const broken = reports.filter((r) => !r.ok);
    expect(
      broken.map((r) => `${r.bundle}: ${[...r.errors, ...r.extractionFailures.map((i) => `extraction ${i}`)].join("; ")}`),
    ).toEqual([]);
    // A bundle with formal blocks must actually yield some, or selection has silently gone blind.
    for (const r of reports) {
      expect(r.blocks, `${r.bundle} selected no blocks`).toBeGreaterThan(0);
      expect(r.segments.min, `${r.bundle} has a block with no segment`).toBeGreaterThan(0);
    }
  }, 120_000);
});

describe("dryRunBundle on damaged bundles", () => {
  const withDir = async (fn: (dir: string) => Promise<void>) => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "nl-dry-"));
    try {
      await fn(dir);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  };

  const SNIPPET = {
    decl: "overlap_bound", file: "B.lean", line: 1, sorry_free: true, axioms: null,
    statement: "theorem overlap_bound\n    (eps : ℝ)\n    (h1 : 0 < eps) :\n    eps ≤ 1",
  };
  const BLOCK = "<p>Every cell carries positive mass here. The bound follows.</p>";

  const seed = async (dir: string, over: { html?: string; index?: unknown } = {}) => {
    await writeFile(path.join(dir, "presentation_crosswalk.json"),
      JSON.stringify({ entries: [{ obj_id: "a1", env: "assumptionv", status: "matched" }] }), "utf8");
    await writeFile(path.join(dir, "lean_snippets.json"), JSON.stringify({ snippets: { a1: SNIPPET } }), "utf8");
    await writeFile(path.join(dir, "paper_body.html"),
      over.html ?? `<div class="formal-block kind-assumption" id="obj-a1" data-objid="a1">${BLOCK}</div>`, "utf8");
    if (over.index !== null) {
      await writeFile(path.join(dir, "paper_library_index.json"),
        JSON.stringify(over.index ?? { entries: [{ name: "X.other", kind: "def", file: "B.lean", line: 1, source: "def other := 0" }] }),
        "utf8");
    }
  };

  it("reports a clean bundle as ready and renders both prompts", async () => {
    await withDir(async (dir) => {
      await seed(dir);
      const r = await dryRunBundle(dir);
      expect(r).toMatchObject({ ok: true, blocks: 1, extractionFailures: [] });
      expect(r.promptBytesMax).toBeGreaterThan(0);
      expect(r.assignChunks).toBeGreaterThan(0);
      expect(r.verifyChunks).toBeGreaterThan(0);
      expect(r.caches).toEqual({ assign: "absent", verify: "absent" });
      expect(r.artifact).toBe("absent");
    });
  });

  it("fails on a block whose markup never closes, rather than skipping it", async () => {
    await withDir(async (dir) => {
      // opening tag present, no matching </div> — extraction returns null
      await seed(dir, { html: `<div class="formal-block" id="obj-a1" data-objid="a1"><p>${BLOCK}` });
      const r = await dryRunBundle(dir);
      expect(r.ok).toBe(false);
      expect(r.extractionFailures).toEqual(["a1"]);
    });
  });

  it("fails loudly on a missing or empty declaration index", async () => {
    await withDir(async (dir) => {
      await seed(dir, { index: null });
      expect((await dryRunBundle(dir)).errors[0]).toMatch(/paper_library_index\.json is missing/);
      await writeFile(path.join(dir, "paper_library_index.json"), JSON.stringify({ entries: [] }), "utf8");
      expect((await dryRunBundle(dir)).errors[0]).toMatch(/lists no declarations/);
    });
  });

  it("reports a corrupted cache instead of crashing", async () => {
    await withDir(async (dir) => {
      await seed(dir);
      await writeFile(path.join(dir, "nl_links_cache.json"), '{"a1": {"trunc', "utf8");
      await writeFile(path.join(dir, "nl_links_verify_cache.json"), "not json at all", "utf8");
      const r = await dryRunBundle(dir);
      expect(r.caches.assign).toMatch(/^CORRUPT/);
      expect(r.caches.verify).toMatch(/^CORRUPT/);
      expect(r.anomalies).toHaveLength(2);
    });
  });

  it("reports a v3 artifact, and flags a superseded v2 one as dead", async () => {
    await withDir(async (dir) => {
      await seed(dir);
      await writeFile(path.join(dir, "nl_links.json"), JSON.stringify({
        commit: "c", qid: "q", spec: "s", policy: "nl-links-v3",
        blocks: { a1: { segments: [{ id: "s1", kind: "text", start: 0, end: 5 }], assignments: [{ row: "r1", unstated: true }] } },
      }), "utf8");
      expect((await dryRunBundle(dir)).artifact).toBe("1 blocks, 1 row assignments");

      await writeFile(path.join(dir, "nl_links.json"), JSON.stringify({
        commit: "c", policy: "nl-links-v2", links: { a1: [{ xl: "a1#1", nl: "x", lean: "y", leanPart: "statement" }] },
      }), "utf8");
      expect((await dryRunBundle(dir)).artifact).toMatch(/superseded by nl-links-v3 \(1 v2 pairs, dead\)/);
    });
  });

  it("reports unreadable inputs as an error, not an exception", async () => {
    await withDir(async (dir) => {
      const r = await dryRunBundle(dir);
      expect(r.ok).toBe(false);
      expect(r.errors[0]).toMatch(/inputs unreadable/);
    });
  });
});
