import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import os from "node:os";
import {
  mintFailedTheoremOpenQuestion,
  OpenQuestionConflict,
} from "../../src/shared/mint_failed_theorem_oq.js";

let tmpRoot: string;
let graphRoot: string;

beforeEach(async () => {
  tmpRoot = await mkdtemp(path.join(os.tmpdir(), "mint-oq-"));
  graphRoot = path.join(tmpRoot, "doc", "study");
  await mkdir(path.join(graphRoot, "nodes", "open_question"), { recursive: true });
});

afterEach(async () => {
  await rm(tmpRoot, { recursive: true, force: true });
});

const theorem = {
  theorem_local_id: "t2",
  origin_theorem_id: "panel_minimal_basis_t2",
  statement: "Statement of T2.",
  status: "failed" as const,
  stage_completed: "3" as const,
  lean_file_relpath: "CausalSmith/Panel/PANEL_MinimalBasis/T2.lean",
  failure_reason: "stuck at nonneg lemma",
};

describe("mintFailedTheoremOpenQuestion", () => {
  it("writes an OQ JSON with the expected id and minted_from block (stage > 0.5)", async () => {
    const res = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis",
      spec: "bernoulli",
      theorem, // stage_completed: "3" (past 0.5)
      graphRoot,
    });
    expect(res.kind).toBe("created");
    if (res.kind !== "created") throw new Error("unreachable");
    expect(res.oq_id).toBe("oq_failed_panel_minimal_basis_bernoulli_t2");
    expect(existsSync(res.oq_path)).toBe(true);
    const node = JSON.parse(await readFile(res.oq_path, "utf8"));
    expect(node.schema_version).toBe(2);
    expect(node.open_question_id).toBe(res.oq_id);
    expect(node.status).toBe("open");
    expect(node.minted_from).toEqual({
      qid: "panel_minimal_basis",
      spec: "bernoulli",
      theorem_local_id: "t2",
      lean_file_relpath: "CausalSmith/Panel/PANEL_MinimalBasis/T2.lean",
      failure_reason: "stuck at nonneg lemma",
    });
  });

  it("is idempotent: a second call with the same inputs returns kind=existed", async () => {
    const first = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem, graphRoot,
    });
    const second = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem, graphRoot,
    });
    expect(first.kind).toBe("created");
    expect(second.kind).toBe("existed");
    if (first.kind !== "created" || second.kind !== "existed") throw new Error("unreachable");
    expect(second.oq_id).toBe(first.oq_id);
  });

  it("throws OpenQuestionConflict if the file exists with a different minted_from", async () => {
    const res = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem, graphRoot,
    });
    if (res.kind !== "created") throw new Error("unreachable");
    const tampered = JSON.parse(await readFile(res.oq_path, "utf8"));
    tampered.minted_from.failure_reason = "different reason";
    await writeFile(res.oq_path, JSON.stringify(tampered, null, 2), "utf8");

    await expect(
      mintFailedTheoremOpenQuestion({
        qid: "panel_minimal_basis", spec: "bernoulli", theorem, graphRoot,
      }),
    ).rejects.toBeInstanceOf(OpenQuestionConflict);
  });

  it("omits optional lean_file_relpath / failure_reason when absent on the theorem", async () => {
    const minimal = { ...theorem, lean_file_relpath: null, failure_reason: undefined };
    const res = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem: minimal, graphRoot,
    });
    if (res.kind !== "created") throw new Error("unreachable");
    const node = JSON.parse(await readFile(res.oq_path, "utf8"));
    expect(node.minted_from.lean_file_relpath).toBeUndefined();
    expect(node.minted_from.failure_reason).toBeUndefined();
  });

  it("throws if theorem.status is not 'failed' (guard against misuse)", async () => {
    const wrong = { ...theorem, status: "completed" as const };
    await expect(
      mintFailedTheoremOpenQuestion({
        qid: "panel_minimal_basis", spec: "bernoulli", theorem: wrong, graphRoot,
      }),
    ).rejects.toThrow(/status .* must be .failed./);
  });

  for (const stage of ["-1.2", "-0.5", "0", "0.5"] as const) {
    it(`skips minting when theorem failed at stage ${stage} (<= 0.5)`, async () => {
      const earlyFail = { ...theorem, stage_completed: stage };
      const res = await mintFailedTheoremOpenQuestion({
        qid: "panel_minimal_basis", spec: "bernoulli", theorem: earlyFail, graphRoot,
      });
      expect(res.kind).toBe("skipped");
      if (res.kind !== "skipped") throw new Error("unreachable");
      expect(res.reason).toBe("stage_below_0_5");
      const oqPath = path.join(
        graphRoot, "nodes", "open_question",
        "oq_failed_panel_minimal_basis_bernoulli_t2.json",
      );
      expect(existsSync(oqPath)).toBe(false);
    });
  }

  it("also skips when stage_completed is null (never advanced past gate)", async () => {
    const noStage = { ...theorem, stage_completed: null };
    const res = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem: noStage, graphRoot,
    });
    expect(res.kind).toBe("skipped");
  });

  it("derives title from the first line of the statement (truncated to 80 chars)", async () => {
    const long = {
      ...theorem,
      statement:
        "For every panel kernel K satisfying minimal-basis support and every assignment policy π in Π_admissible, the conditional sign-flip identity holds modulo the regularization term.\nLine 2 should not appear.",
    };
    const res = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem: long, graphRoot,
    });
    if (res.kind !== "created") throw new Error("unreachable");
    const node = JSON.parse(await readFile(res.oq_path, "utf8"));
    expect(node.title.startsWith("Unproved: ")).toBe(true);
    expect(node.title.length).toBeLessThanOrEqual(10 + 80);
    expect(node.title.endsWith("…")).toBe(true);
    expect(node.title).not.toMatch(/Line 2/);
  });

  it("falls back to a mechanical title when the statement is empty", async () => {
    const empty = { ...theorem, statement: "" };
    const res = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem: empty, graphRoot,
    });
    if (res.kind !== "created") throw new Error("unreachable");
    const node = JSON.parse(await readFile(res.oq_path, "utf8"));
    expect(node.title).toBe("Unproved: t2 of panel_minimal_basis (bernoulli)");
  });

  it("treats key-reordered minted_from as equal (no false conflict)", async () => {
    const first = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem, graphRoot,
    });
    if (first.kind !== "created") throw new Error("unreachable");

    // Rewrite the file with the minted_from keys in a different order.
    const node = JSON.parse(await readFile(first.oq_path, "utf8"));
    const reorderedMintedFrom = {
      failure_reason: node.minted_from.failure_reason,
      lean_file_relpath: node.minted_from.lean_file_relpath,
      theorem_local_id: node.minted_from.theorem_local_id,
      spec: node.minted_from.spec,
      qid: node.minted_from.qid,
    };
    node.minted_from = reorderedMintedFrom;
    await writeFile(first.oq_path, JSON.stringify(node, null, 2), "utf8");

    // Re-mint should detect equality and return kind=existed (not throw).
    const second = await mintFailedTheoremOpenQuestion({
      qid: "panel_minimal_basis", spec: "bernoulli", theorem, graphRoot,
    });
    expect(second.kind).toBe("existed");
  });
});
