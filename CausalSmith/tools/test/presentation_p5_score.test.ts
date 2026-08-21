import { describe, it, expect } from "vitest";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { archivePriorReview, normalizeScore, upsertFrontmatter } from "../src/presentation/stages/p5_review.js";

describe("P5 normalizeScore", () => {
  it("passes a valid one-decimal score through", () => {
    expect(normalizeScore(8.5)).toBe(8.5);
  });
  it("rounds to one decimal", () => {
    expect(normalizeScore(7.24)).toBe(7.2);
    expect(normalizeScore(7.26)).toBe(7.3);
  });
  it("rejects out-of-range values instead of rewriting the referee score", () => {
    // why: invalid referee scores should fail the stage rather than be silently clamped.
    expect(normalizeScore(12)).toBeNull();
    expect(normalizeScore(-3)).toBeNull();
  });
  it("accepts a numeric string", () => {
    expect(normalizeScore("9")).toBe(9);
  });
  it("returns null for a missing / non-numeric score (caller fails the stage)", () => {
    expect(normalizeScore(undefined)).toBeNull();
    expect(normalizeScore("high")).toBeNull();
    expect(normalizeScore(null)).toBeNull();
  });
});

describe("P5 upsertFrontmatter", () => {
  const md = ["---", 'qid: demo', 'spec: v1', "topic: something", "---", "", "# Body"].join("\n");

  it("inserts new keys before the closing --- and byte-preserves other lines", () => {
    const out = upsertFrontmatter(md, { paper_score: "8.5", paper_score_rationale: '"clean"' });
    expect(out).not.toBeNull();
    const lines = out!.split("\n");
    expect(lines).toContain("paper_score: 8.5");
    expect(lines).toContain('paper_score_rationale: "clean"');
    // original lines intact
    expect(lines).toContain("qid: demo");
    expect(lines).toContain("topic: something");
    expect(out).toContain("\n# Body");
    // inserted inside the frontmatter block (before the closing ---)
    expect(out!.indexOf("paper_score: 8.5")).toBeLessThan(out!.indexOf("\n---"));
  });

  it("replaces an existing key in place rather than duplicating it", () => {
    const withScore = upsertFrontmatter(md, { paper_score: "5.0" })!;
    const replaced = upsertFrontmatter(withScore, { paper_score: "9.1" })!;
    const occurrences = replaced.split("\n").filter((l) => l.startsWith("paper_score:")).length;
    expect(occurrences).toBe(1);
    expect(replaced).toContain("paper_score: 9.1");
    expect(replaced).not.toContain("paper_score: 5.0");
  });

  it("returns null when the document has no frontmatter block", () => {
    expect(upsertFrontmatter("# Just a heading\n", { paper_score: "8" })).toBeNull();
  });
});

describe("P5 review history", () => {
  it("archives every prior referee draw instead of overwriting the trajectory", async () => {
    const dir = await mkdtemp(join(tmpdir(), "p5-history-"));
    try {
      await writeFile(join(dir, "p5_review.json"), "{\"score\":6.3}\n");
      await writeFile(join(dir, "p5_review.md"), "# 6.3\n");
      expect(await archivePriorReview(dir)).toBe("round_000");
      await writeFile(join(dir, "p5_review.json"), "{\"score\":5.5}\n");
      await writeFile(join(dir, "p5_review.md"), "# 5.5\n");
      expect(await archivePriorReview(dir)).toBe("round_001");
      expect(await readFile(join(dir, "p5_review_history", "round_000.json"), "utf8")).toContain("6.3");
      expect(await readFile(join(dir, "p5_review_history", "round_001.json"), "utf8")).toContain("5.5");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

// Referee copy: comments never reach the referee; escaped percents and content do.
import { refereeTexFor } from "../src/presentation/stages/p5_review.js";
describe("refereeTexFor", () => {
  it("strips % comments (incl. % lean: provenance) but keeps \\% and prose", () => {
    const tex = "A rate of 5\\% holds. % lean: adaptive_rootn_minimax\n% full-line comment\n\n\nNext paragraph.\n";
    const out = refereeTexFor(tex);
    expect(out).toContain("5\\% holds.");
    expect(out).not.toContain("lean:");
    expect(out).not.toContain("full-line comment");
    expect(out).not.toMatch(/\n[ \t]*\n[ \t]*\n/);
    expect(out).toContain("Next paragraph.");
  });
});

describe("title-only findings are repaired in-run, not escalated", () => {
  it("routes an overstating-title finding to the reviser but keeps math findings escalated", async () => {
    const { actionForFinding } = await import("../src/presentation/revision_routing.js");
    const titleFinding = {
      severity: "major", section: "main result", kind: "statement", remedy: "rewrite",
      issue: 'The title "Adaptive root-n minimaxity" overstates the delivered result, which is fixed-code.',
      fix: 'Rename the theorem to name the fixed-code, fixed-separation scope.',
    } as never;
    const mathFinding = {
      severity: "major", section: "main result", kind: "statement", remedy: "rewrite",
      issue: "The theorem assumes bounded outcomes but the proof needs sub-Gaussian tails.",
      fix: "Strengthen the hypothesis.",
    } as never;
    expect(actionForFinding(titleFinding)).toEqual({ type: "revise" });
    expect(actionForFinding(mathFinding)).toEqual({ type: "escalate" });
  });
});
