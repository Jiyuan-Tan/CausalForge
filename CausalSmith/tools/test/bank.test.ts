import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import {
  loadBurnedSeeds,
  loadReusableArtifacts,
  renderReusableArtifactsBlock,
} from "../src/discovery/bank.js";
import { appendReview } from "../src/pipeline_support.js";
import type { ReviewResult } from "../src/judgment.js";
import type { PipelineContext } from "../src/types.js";

async function makeBankEntry(args: {
  repoRoot: string;
  tier: "accepted" | "downgraded" | "failed" | "legacy";
  entry: string;
  frontmatter: Record<string, unknown>;
  stateJson?: Record<string, unknown>;
  files?: Record<string, string>;
}): Promise<string> {
  const dir = path.join(
    args.repoRoot,
    "doc",
    "research",
    "_bank",
    args.tier,
    args.entry,
  );
  await mkdir(dir, { recursive: true });
  const fm: string[] = ["---"];
  for (const [k, v] of Object.entries(args.frontmatter)) {
    if (Array.isArray(v)) {
      if (v.length === 0) {
        fm.push(`${k}: []`);
        continue;
      }
      fm.push(`${k}:`);
      for (const item of v as Array<Record<string, string>>) {
        const keys = Object.keys(item);
        fm.push(`  - ${keys[0]}: ${JSON.stringify(item[keys[0]])}`);
        for (let i = 1; i < keys.length; i++) {
          fm.push(`    ${keys[i]}: ${JSON.stringify(item[keys[i]])}`);
        }
      }
    } else {
      fm.push(`${k}: ${JSON.stringify(v)}`);
    }
  }
  fm.push("---", "", `# ${args.entry}`, "");
  await writeFile(path.join(dir, "README.md"), fm.join("\n"));
  if (args.stateJson) {
    await writeFile(
      path.join(dir, `${args.entry}_state.json`),
      JSON.stringify(args.stateJson, null, 2),
    );
  }
  for (const [name, content] of Object.entries(args.files ?? {})) {
    await writeFile(path.join(dir, name), content);
  }
  return dir;
}

describe("loadReusableArtifacts", () => {
  it("returns [] when the bank is missing", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    const out = await loadReusableArtifacts(tmp, {
      qid: "pid_anything",
      topic: "anything",
    });
    expect(out).toEqual([]);
  });

  it("matches strict when topics are equal (whitespace-insensitive)", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "downgraded",
      entry: "pid_foo_v1",
      frontmatter: {
        qid: "pid_foo",
        spec: "v1",
        topic: "Partial ID of dynamic LATEs",
        reusable_artifacts: [
          {
            path: "pid_foo_v1_proposal.tex",
            kind: "literature_map",
            one_line: "12-paper map",
          },
        ],
      },
      stateJson: {
        proposed_from: { literature_map: "LIT MAP CONTENT" },
      },
    });
    const out = await loadReusableArtifacts(tmp, {
      qid: "pid_foo",
      topic: "  Partial ID of dynamic LATEs  ",
    });
    expect(out).toHaveLength(1);
    expect(out[0].match).toBe("strict");
    expect(out[0].kind).toBe("literature_map");
    expect(out[0].content).toBe("LIT MAP CONTENT");
    expect(out[0].source_tier).toBe("downgraded");
  });

  it("matches related when cluster prefix is shared but topic differs", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "downgraded",
      entry: "pid_a_v1",
      frontmatter: {
        qid: "pid_a",
        spec: "v1",
        topic: "Sharp bounds on the LATE under bounded defiers",
        reusable_artifacts: [
          {
            path: "pid_a_v1_proposal.tex",
            kind: "literature_map",
            one_line: "Imbens-Angrist family lit map",
          },
          {
            path: "pid_a_v1.tex",
            kind: "lp_setup",
            one_line: "LP formulation",
          },
        ],
      },
      stateJson: {
        proposed_from: { literature_map: "RELATED MAP" },
      },
    });
    const out = await loadReusableArtifacts(tmp, {
      qid: "pid_dynamic_iv_compliance",
      topic: "Different dynamic IV topic",
    });
    expect(out).toHaveLength(2);
    expect(out.every((a) => a.match === "related")).toBe(true);
    const lm = out.find((a) => a.kind === "literature_map");
    expect(lm?.content).toBe("RELATED MAP");
    const lp = out.find((a) => a.kind === "lp_setup");
    expect(lp?.content).toBeUndefined();
  });

  it("matches a panel_ bank entry against new panel_ work on a different topic", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "accepted",
      entry: "panel_spectral_phase_transition_v1",
      frontmatter: {
        qid: "panel_spectral_phase_transition",
        spec: "v1",
        topic: "Spectral phase transition for staggered TWFE",
        reusable_artifacts: [
          { path: "proposal.tex", kind: "literature_map", one_line: "panel map" },
        ],
      },
      stateJson: { proposed_from: { literature_map: "PANEL MAP" } },
    });
    const out = await loadReusableArtifacts(tmp, {
      qid: "panel_synthetic_control_geometry",
      topic: "A different panel topic",
    });
    expect(out).toHaveLength(1);
    expect(out[0].match).toBe("related");
    expect(out[0].content).toBe("PANEL MAP");
  });

  it("filters out distant entries (different cluster, different topic)", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "accepted",
      entry: "panel_other_v1",
      frontmatter: {
        qid: "panel_minimal_basis",
        spec: "v1",
        topic: "Panel minimal basis under static designs",
        reusable_artifacts: [
          { path: "panel_other_v1_proposal.tex", kind: "literature_map", one_line: "panel map" },
        ],
      },
      stateJson: { proposed_from: { literature_map: "PANEL MAP" } },
    });
    const out = await loadReusableArtifacts(tmp, {
      qid: "pid_dynamic_iv_compliance",
      topic: "Different topic, different cluster",
    });
    expect(out).toEqual([]);
  });

  it("treats flagship cluster as cross-matching every cluster", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "downgraded",
      entry: "flagship_explore_f1",
      frontmatter: {
        qid: "flagship_explore",
        spec: "f1",
        topic: "Some flagship-exploratory topic",
        reusable_artifacts: [
          { path: "x.tex", kind: "literature_map", one_line: "lit map" },
        ],
      },
      stateJson: { proposed_from: { literature_map: "FL MAP" } },
    });
    const out = await loadReusableArtifacts(tmp, {
      qid: "pid_anything",
      topic: "completely different",
    });
    expect(out).toHaveLength(1);
    expect(out[0].match).toBe("related");
  });

  it("falls back to reading the path file when state.json has no literature_map", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "failed",
      entry: "pid_b_v1",
      frontmatter: {
        qid: "pid_b",
        spec: "v1",
        topic: "Topic B",
        reusable_artifacts: [
          { path: "pid_b_v1.tex", kind: "literature_map", one_line: "B map" },
        ],
      },
      stateJson: { proposed_from: {} },
      files: { "pid_b_v1.tex": "FILE MAP CONTENT" },
    });
    const out = await loadReusableArtifacts(tmp, {
      qid: "pid_b",
      topic: "Topic B",
    });
    expect(out).toHaveLength(1);
    expect(out[0].content).toBe("FILE MAP CONTENT");
  });

  it("renders a non-empty block with grouped sources and pointer markers", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "downgraded",
      entry: "pid_c_v1",
      frontmatter: {
        qid: "pid_c",
        spec: "v1",
        topic: "Topic C",
        reusable_artifacts: [
          { path: "pid_c_v1_proposal.tex", kind: "literature_map", one_line: "C lit map" },
          { path: "pid_c_v1.tex", kind: "lp_setup", one_line: "C LP setup" },
        ],
      },
      stateJson: { proposed_from: { literature_map: "C MAP CONTENT" } },
    });
    const artifacts = await loadReusableArtifacts(tmp, {
      qid: "pid_c",
      topic: "Topic C",
    });
    const block = renderReusableArtifactsBlock(artifacts);
    expect(block).toContain("REUSABLE PRIOR-ART ARTIFACTS");
    expect(block).toContain("from pid_c_v1");
    expect(block).toContain("[tier=downgraded, match=strict]");
    expect(block).toContain("[literature_map]");
    expect(block).toContain("C MAP CONTENT");
    expect(block).toContain("[lp_setup pointer]");
  });

  it("returns empty block when no artifacts are present", () => {
    expect(renderReusableArtifactsBlock([])).toBe("");
  });

  it("includes downgraded-tier artifacts and labels them as novelty-biased", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "downgraded",
      entry: "pid_x_v2",
      frontmatter: {
        qid: "pid_x",
        spec: "v2",
        topic: "Topic X",
        reusable_artifacts: [
          { path: "pid_x_v2_proposal.tex", kind: "literature_map", one_line: "X map" },
        ],
      },
      stateJson: {
        stage_completed: "0.5",
        banked: true,
        banked_tier: "downgraded",
        proposed_from: { literature_map: "X CANDIDATE MAP" },
      },
    });
    const arts = await loadReusableArtifacts(tmp, { qid: "pid_x", topic: "Topic X" });
    expect(arts).toHaveLength(1);
    expect(arts[0].source_tier).toBe("downgraded");
    expect(arts[0].content).toBe("X CANDIDATE MAP");
    const block = renderReusableArtifactsBlock(arts);
    expect(block).toContain("trust: math-sound, novelty-biased");
    expect(block).toContain("[tier=downgraded, match=strict]");
  });

  it("burns seeds from every bank tier", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-bank-"));
    await makeBankEntry({
      repoRoot: tmp,
      tier: "downgraded",
      entry: "pid_z_v1",
      frontmatter: { qid: "pid_z", spec: "v1", topic: "Z", reusable_artifacts: [] },
      stateJson: {
        seeds_burned: [
          { index: 0, one_liner: "burn me", anchor_bibkey: "Z2024", reason: "r", burned_on: "2026-05-14" },
        ],
      },
    });
    const burned = await loadBurnedSeeds(tmp);
    expect(burned).toHaveLength(1);
    expect(burned[0].anchor_bibkey).toBe("Z2024");
  });
});

describe("appendReview persistence", () => {
  function makeCtx(repoRoot: string): PipelineContext {
    return {
      repoRoot,
      qid: "pid_test",
      specialization: "v1",
      dryRun: false,
      resume: false,
    } as unknown as PipelineContext;
  }

  it("writes per-attempt JSON for Stage 0.5/1.5/2.5 boundaries (mirrors Stage -0.5)", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "causalsmith-review-"));
    const ctx = makeCtx(tmp);
    const review: ReviewResult = {
      status: "revise",
      classification: "novelty",
      perItemFindings: [{ label: "kernel", verdict: "weak", one_line: "soft" }],
      verbatim_critique: "needs sharper kernel",
    };
    await appendReview(ctx, "stage_0.5_to_0", 1, review);
    await appendReview(ctx, "stage_0.5_to_0", 2, { ...review, classification: "soundness" });
    const reviewDir = path.join(
      tmp,
      "doc",
      "research",
      "active",
      "pid_test",
      "pid_test_v1_reviews",
    );
    expect(existsSync(path.join(reviewDir, "stage_0.5_to_0_attempt1.json"))).toBe(true);
    expect(existsSync(path.join(reviewDir, "stage_0.5_to_0_attempt2.json"))).toBe(true);
    const a1 = JSON.parse(
      await readFile(path.join(reviewDir, "stage_0.5_to_0_attempt1.json"), "utf8"),
    );
    expect(a1.status).toBe("revise");
    expect(a1.classification).toBe("novelty");
    expect(a1.verbatim_critique).toBe("needs sharper kernel");
  });
});
