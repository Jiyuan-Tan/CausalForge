import { afterEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { restoreFrozenEnvsAfterRevision, stageP5HolisticRevision } from "../src/presentation/stages/p5_holistic_revision.js";
import { freshPaperState } from "../src/presentation/state.js";
import type { PaperDeps, StageIO } from "../src/presentation/pipeline.js";
import type { PriorReview } from "../src/presentation/revision_brief.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

describe("P5 holistic manuscript reviser", () => {
  it("restores a deleted frozen environment at its prior relative location", () => {
    const a = "\\begin{definitionv}{def:a}[A]\nA body.\n\\end{definitionv}";
    const b = "\\begin{theoremv}{thm:b}[B]\nB body.\n\\end{theoremv}";
    const before = `Intro.\n${a}\nBetween.\n${b}\nAfter.`;
    const revised = `Sharper intro.\nBetween revised.\n${b.replace("B body.", "drifted")}\nAfter.`;
    const restored = restoreFrozenEnvsAfterRevision(before, revised, new Map([["def:a", a], ["thm:b", b]]));
    expect(restored).toContain("Sharper intro.");
    expect(restored.indexOf(a)).toBeLessThan(restored.indexOf(b));
    expect(restored).toContain("B body.");
    expect(restored).not.toContain("drifted");
  });

  it("rejects pasted, duplicated, or reordered frozen environments", () => {
    const a = "\\begin{definitionv}{def:a}[A]\nA body.\n\\end{definitionv}";
    const b = "\\begin{theoremv}{thm:b}[B]\nB body.\n\\end{theoremv}";
    const canonical = new Map([["def:a", a], ["thm:b", b]]);
    expect(() => restoreFrozenEnvsAfterRevision("Plain prose.", `Plain prose.\n${a}`, canonical))
      .toThrow(/moved\/added/i);
    expect(() => restoreFrozenEnvsAfterRevision(`${a}\n${b}`, `${a}\n${a}\n${b}`, canonical))
      .toThrow(/duplicated/i);
    expect(() => restoreFrozenEnvsAfterRevision(`${a}\n${b}`, `${b}\n${a}`, canonical))
      .toThrow(/reordered/i);
  });

  it("uses one high-effort presentation-model call, permits reframing, and records a source-changing receipt", async () => {
    const outDir = await mkdtemp(join(tmpdir(), "p5-holistic-"));
    dirs.push(outDir);
    await mkdir(join(outDir, "sections"));
    await mkdir(join(outDir, "proofs"));
    await writeFile(join(outDir, "outline.md"), "# Old title\n");
    await writeFile(join(outDir, "front_matter.tex"), "Old abstract.\n");
    await writeFile(join(outDir, "appendix_proofs.tex"), "");
    await writeFile(join(outDir, "references.bib"), "");
    await writeFile(join(outDir, "paper.tex"), "Old paper.\n");
    await writeFile(join(outDir, "sections", "01_intro.tex"), "Old introduction.\n");
    await writeFile(join(outDir, "verification_contract.json"), "{\"commit\":\"abc\"}\n");
    await writeFile(join(outDir, "formal_layer.json"), "{}\n");
    await writeFile(join(outDir, "related_work_brief.md"), "Existing comparison.\n");

    let call: Parameters<PaperDeps["runCodex"]>[0] | null = null;
    const deps: PaperDeps = {
      codexModel: "gpt-5.5",
      runClaude: async () => "",
      runCodex: async (args) => {
        call = args;
        await writeFile(join(outDir, "front_matter.tex"), "Econometric reframing.\n");
        await writeFile(join(outDir, "paper.tex"), "Econometric reframing.\n");
        return { stdout: "Reframed the verified contribution.", stderr: "" };
      },
      dryRun: false,
    };
    const io = {
      ctx: { repoRoot: outDir, qid: "q", spec: "v1", deps, outDir },
      state: freshPaperState("q", "v1"),
      bank: {} as StageIO["bank"],
      outDir,
    } satisfies StageIO;
    const review: PriorReview = {
      recommendation: "major_revision",
      findings: [{
        severity: "major",
        section: "contribution",
        issue: "The paper needs an econometric audience and reframing.",
        fix: "Reframe the verified population target.",
        kind: "structure",
        remedy: "rewrite",
        finding_id: "econometric-significance",
      }],
    };
    const result = await stageP5HolisticRevision(io, review, review.findings);

    expect(result.changed).toBe(true);
    expect(result.fingerprints).toEqual(["econometric significance"]);
    expect(call).toMatchObject({
      cwd: outDir,
      reasoningEffort: "high",
      leanLsp: false,
      model: "gpt-5.5",
      multiAgent: false,
    });
    expect(call!.prompt).toContain("Revision mode:\nreframe");
    expect(call!.prompt).toMatch(/may substantially reframe/i);
    expect(call!.prompt).toContain("Do not edit formal_layer.json");
    const receipt = await readFile(join(outDir, "p5_revision_pass_1.md"), "utf8");
    expect(receipt).toContain("mode: reframe");
    expect(receipt).toContain("Reframed the verified contribution.");
  });

  it("fails closed if the reviser touches a protected formal artifact", async () => {
    const outDir = await mkdtemp(join(tmpdir(), "p5-holistic-protected-"));
    dirs.push(outDir);
    await mkdir(join(outDir, "sections"));
    await mkdir(join(outDir, "proofs"));
    for (const [name, body] of [
      ["outline.md", "# Title\n"],
      ["front_matter.tex", "Abstract.\n"],
      ["appendix_proofs.tex", ""],
      ["references.bib", ""],
      ["paper.tex", "Paper.\n"],
      ["verification_contract.json", "{}\n"],
      ["formal_layer.json", "{\"frozen\":true}\n"],
    ]) await writeFile(join(outDir, name), body);
    const deps: PaperDeps = {
      runClaude: async () => "",
      runCodex: async () => {
        await writeFile(join(outDir, "formal_layer.json"), "{\"frozen\":false}\n");
        return { stdout: "changed", stderr: "" };
      },
      dryRun: false,
    };
    const review: PriorReview = {
      recommendation: "major_revision",
      findings: [{
        severity: "major", section: "intro", issue: "unclear", fix: "rewrite",
        kind: "prose", remedy: "rewrite", finding_id: "unclear-intro",
      }],
    };
    await expect(stageP5HolisticRevision({
      ctx: { repoRoot: outDir, qid: "q", spec: "v1", deps, outDir },
      state: freshPaperState("q", "v1"),
      bank: {} as StageIO["bank"],
      outDir,
    }, review, review.findings)).rejects.toThrow(/protected formal/i);
  });
});
