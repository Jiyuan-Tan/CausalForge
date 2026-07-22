import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import os from "node:os";
import { mintProposalOpenEndedQuestion } from "../../src/shared/mint_proposal_oq.js";
import { OpenQuestionConflict } from "../../src/shared/mint_failed_theorem_oq.js";
import type { ParsedOpenEndedQuestion } from "../../src/shared/mint_proposal_oq.js";

let tmpRoot: string;
let graphRoot: string;

beforeEach(async () => {
  tmpRoot = await mkdtemp(path.join(os.tmpdir(), "mint-prop-oeq-"));
  graphRoot = path.join(tmpRoot, "doc", "study");
  await mkdir(path.join(graphRoot, "nodes", "open_question"), { recursive: true });
});

afterEach(async () => {
  await rm(tmpRoot, { recursive: true, force: true });
});

const oeq: ParsedOpenEndedQuestion = {
  index: 1,
  label: "estimator-design",
  title: "design estimator for tau-star",
  body:
    "Design a candidate estimator for tau-star using bridge functions.\n" +
    "\\textbf{Handle:} bridge-function class H_+.\n" +
    "\\textbf{Why it matters:} operationalizes tau-star.",
  handle: "bridge-function class H_+.",
  why_it_matters: "operationalizes tau-star.",
  beginLine: 42,
};

describe("mintProposalOpenEndedQuestion", () => {
  it("writes an OQ JSON with the expected id and proposal-origin minted_from block", async () => {
    const proposal_path = path.join(tmpRoot, "proposal.tex");
    await writeFile(proposal_path, "% proposal", "utf8");
    const res = await mintProposalOpenEndedQuestion({
      qid: "pid_estimator_design",
      spec: "v1",
      oeq,
      proposal_path,
      graphRoot,
    });
    expect(res.kind).toBe("created");
    if (res.kind !== "created") throw new Error("unreachable");
    expect(res.oq_id).toBe(
      "oq_proposal_pid_estimator_design_v1_estimator-design",
    );
    expect(existsSync(res.oq_path)).toBe(true);
    const node = JSON.parse(await readFile(res.oq_path, "utf8"));
    expect(node.schema_version).toBe(2);
    expect(node.open_question_id).toBe(res.oq_id);
    expect(node.status).toBe("open");
    expect(node.minted_from).toEqual({
      qid: "pid_estimator_design",
      spec: "v1",
      origin: "proposal_open_ended_question",
      oq_local_label: "estimator-design",
      proposal_path,
    });
    expect(node.body).toContain("bridge-function class");
    expect(node.body).toContain("operationalizes tau-star");
  });

  it("is idempotent: second call returns kind=existed", async () => {
    const proposal_path = path.join(tmpRoot, "proposal.tex");
    await writeFile(proposal_path, "% proposal", "utf8");
    const first = await mintProposalOpenEndedQuestion({
      qid: "pid_x",
      spec: "v1",
      oeq,
      proposal_path,
      graphRoot,
    });
    const second = await mintProposalOpenEndedQuestion({
      qid: "pid_x",
      spec: "v1",
      oeq,
      proposal_path,
      graphRoot,
    });
    expect(first.kind).toBe("created");
    expect(second.kind).toBe("existed");
  });

  it("throws OpenQuestionConflict when an existing OQ has a different minted_from", async () => {
    const proposal_path = path.join(tmpRoot, "proposal.tex");
    await writeFile(proposal_path, "% proposal", "utf8");
    const first = await mintProposalOpenEndedQuestion({
      qid: "pid_x",
      spec: "v1",
      oeq,
      proposal_path,
      graphRoot,
    });
    if (first.kind !== "created") throw new Error("unreachable");
    const node = JSON.parse(await readFile(first.oq_path, "utf8"));
    node.minted_from.proposal_path = "different/path.tex";
    await writeFile(first.oq_path, JSON.stringify(node, null, 2), "utf8");
    await expect(
      mintProposalOpenEndedQuestion({
        qid: "pid_x",
        spec: "v1",
        oeq,
        proposal_path,
        graphRoot,
      }),
    ).rejects.toBeInstanceOf(OpenQuestionConflict);
  });
});
