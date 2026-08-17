// D0.5.G calibration anchors. The block teaches the referee what a given paper_score BUYS,
// so each row must carry what the paper DELIVERED, not just P5's verdict on it — a verdict
// alone names no estimand, class or rate and only teaches which presentation problems cost
// points. These tests pin the source precedence, the range spread, and the degradations.
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { loadPaperScoreAnchors } from "../../src/discovery/stages/d0_5_general.js";

const roots: string[] = [];
afterEach(async () => {
  await Promise.all(roots.splice(0).map((r) => rm(r, { recursive: true, force: true })));
});

async function bank(
  entries: Array<{ qid: string; score?: number; why?: string; abstract?: string; tldr?: string }>,
): Promise<string> {
  const root = await mkdtemp(path.join(tmpdir(), "cs-anchors-"));
  roots.push(root);
  for (const e of entries) {
    const dir = path.join(root, "doc", "research", "_bank", "accepted", e.qid);
    await mkdir(dir, { recursive: true });
    await writeFile(
      path.join(dir, "README.md"),
      [
        "---",
        `qid: ${e.qid}`,
        `topic: "PROMISED a matched two-sided frontier"`,
        ...(e.score === undefined ? [] : [`paper_score: ${e.score}`]),
        ...(e.why === undefined ? [] : [`paper_score_rationale: ${JSON.stringify(e.why)}`]),
        "---",
      ].join("\n"),
      "utf8",
    );
    if (e.tldr !== undefined) {
      await mkdir(path.join(dir, "discovery"), { recursive: true });
      await writeFile(
        path.join(dir, "discovery", "writeup.tex"),
        `\\paragraph{TL;DR.} ${e.tldr}\n\n\\section{Setup}\n`,
        "utf8",
      );
    }
    if (e.abstract !== undefined) {
      const pdir = path.join(root, "doc", "presentation", e.qid);
      await mkdir(pdir, { recursive: true });
      await writeFile(
        path.join(pdir, "paper.tex"),
        `\\begin{abstract}\n${e.abstract}\n\\end{abstract}\n`,
        "utf8",
      );
    }
  }
  return root;
}

describe("loadPaperScoreAnchors", () => {
  it("prefers the delivered paper's abstract — the artifact P5 actually scored", async () => {
    const root = await bank([
      { qid: "a_v1", score: 8.2, why: "well scoped", abstract: "DELIVERED ABSTRACT", tldr: "STALE TLDR" },
    ]);
    const block = await loadPaperScoreAnchors(root);
    expect(block).toContain("DELIVERED:  DELIVERED ABSTRACT");
    expect(block).not.toContain("STALE TLDR");
    expect(block).toContain("P5 VERDICT: well scoped");
  });

  it("never shows the proposal topic: a run can deviate from what it set out to do", async () => {
    const root = await bank([{ qid: "a_v1", score: 6, why: "narrow", abstract: "what landed" }]);
    // The score attaches to the delivered paper, so a stale promise beside it would
    // misdescribe what earned the number.
    expect(await loadPaperScoreAnchors(root)).not.toContain("PROMISED");
  });

  it("falls back to the discovery TL;DR when no presentation bundle exists", async () => {
    const root = await bank([{ qid: "a_v1", score: 5.5, why: "thin", tldr: "the run's own summary" }]);
    expect(await loadPaperScoreAnchors(root)).toContain("DELIVERED:  the run's own summary");
  });

  it("degrades to score + verdict rather than dropping a row with neither source", async () => {
    const root = await bank([{ qid: "a_v1", score: 4, why: "one-sided" }]);
    const block = await loadPaperScoreAnchors(root);
    expect(block).toContain("4.0  a_v1");
    expect(block).toContain("P5 VERDICT: one-sided");
    expect(block).not.toContain("DELIVERED:");
  });

  it("spans the score range instead of showing the top slice, and skips unscored entries", async () => {
    const scores = [9, 8, 7, 6.5, 6, 5.5, 5, 4.5, 4, 3];
    const root = await bank([
      ...scores.map((s, i) => ({ qid: `q${i}_v1`, score: s, why: "w", abstract: `abs${s}` })),
      { qid: "unscored_v1", why: "no score recorded" }, // the misfiled-entry case
    ]);
    const block = await loadPaperScoreAnchors(root);
    const shown = [...block.matchAll(/^- (\d+\.\d)\s/gm)].map((m) => Number(m[1]));
    expect(shown).toHaveLength(6);
    // Both endpoints present: the referee must see what a 3 looks like, not only a 9.
    expect(shown[0]).toBe(9);
    expect(shown[5]).toBe(3);
    expect(new Set(shown).size).toBe(6);
    expect(block).not.toContain("unscored_v1");
  });

  it("returns an empty block when the bank is unreadable, leaving the thresholds intact", async () => {
    expect(await loadPaperScoreAnchors(path.join(tmpdir(), "cs-anchors-absent"))).toBe("");
  });
});
