import { readFile } from "node:fs/promises";
import { describe, expect, it } from "vitest";

const read = (relativePath: string) =>
  readFile(new URL(relativePath, import.meta.url), "utf8");

describe("Stat proposal diversity guidance", () => {
  it("requires all Stat theorem-shape lanes before ranking", async () => {
    const [topicSkill, motifLibrary, repoGuide, api] = await Promise.all([
      read("../../../../.claude/skills/causalsmith-topics/SKILL.md"),
      read("../../src/discovery/prompts/D-1/stage_neg1_2_motif_library.txt"),
      read("../../../../.claude/CLAUDE.md"),
      read("../../../doc/API.md"),
    ]);

    for (const text of [topicSkill, motifLibrary]) {
      expect(text).toContain("M11(a)");
      expect(text).toContain("M11(b)");
      expect(text).toContain("M11(c)");
      expect(text).toContain("M16/M17");
    }

    expect(motifLibrary).toContain("enforceable generation constraint");
    expect(repoGuide).toContain("not a requirement or default");
    expect(api).toContain("A matching minimax converse is not required.");
  });

  it("uses a frontier-neutral review flag in every live review surface", async () => {
    const reviewSurfaces = await Promise.all([
      read("../../src/discovery/prompts/_shared/stage_flagship_rubric.txt"),
      read("../../src/discovery/prompts/D-0.5/stage_neg1_review.txt"),
      read("../../src/discovery/prompts/D-0.5/stage_neg1_review_core.txt"),
      read("../../src/templates/stage_neg1_review_output_template.json"),
    ]);

    for (const text of reviewSurfaces) {
      expect(text).toContain("N-no-stat-frontier-advance");
      expect(text).not.toContain("N-no-matching-converse");
    }
  });
});
