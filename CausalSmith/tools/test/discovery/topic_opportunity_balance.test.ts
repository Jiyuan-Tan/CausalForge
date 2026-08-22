import { readFile } from "node:fs/promises";
import { describe, expect, it } from "vitest";
import { assembleNeg1_2AuthorPrompt } from "../../src/discovery/stages/neg1_2_author.js";
import { shouldUseLeanRender } from "../../src/presentation/stages/p1_plan.js";

const read = (relativePath: string) => readFile(new URL(relativePath, import.meta.url), "utf8");

describe("topic opportunity contract", () => {
  it("uses one canonical term and origin-neutral ranking", async () => {
    const files = await Promise.all([
      read("../../../../.claude/skills/causalsmith-topics/SKILL.md"),
      read("../../../../.claude/skills/causalsmith-topics/reviewer-prompt-template.md"),
      read("../../../../.claude/skills/causalsmith/SKILL.md"),
      read("../../src/discovery/prompts/D-1/stage_neg1_1_lit_review.txt"),
      read("../../src/discovery/prompts/D-1/stage_neg1_2_proto_head_cold_start.txt"),
      read("../../src/discovery/prompts/D-1/stage_neg1_2_proto_core.txt"),
      read("../../src/discovery/stages/neg1_1.ts"),
    ]);
    const joined = files.join("\n");
    expect(joined).toContain("technique-derived direction");
    expect(joined).not.toMatch(/method[- ]transport|highest leverage|higher signal|transplant/i);
    expect(files[0]).toContain("Apply mode is the subset of technique-derived directions");
    expect(files[0]).toContain("evidence, mathematical depth, novelty, feasibility, and consumer value");
  });

  it("keeps the opportunity contract in prompts only, with no persisted provenance field", async () => {
    const [cold, motif, core, neg11, plan, touchup] = await Promise.all([
      read("../../src/discovery/prompts/D-1/stage_neg1_2_proto_head_cold_start.txt"),
      read("../../src/discovery/prompts/D-1/stage_neg1_2_motif_library.txt"),
      read("../../src/discovery/prompts/D-1/stage_neg1_2_proto_core.txt"),
      read("../../src/discovery/prompts/D-1/stage_neg1_1_lit_review.txt"),
      read("../../src/presentation/prompts/p1_plan.txt"),
      read("../../src/presentation/prompts/p1_touchup.txt"),
    ]);
    expect(cold).toContain("Rank all seeds by direct evidence");
    expect(motif).not.toContain("technique-derived direction");
    // The D-1.1 gates (G1/G3) carry the "first changed proof step" requirement in prose;
    // no typed bookkeeping record is threaded through core/graph/paper.
    expect(neg11).toContain("first proof step that changes");
    for (const text of [core, neg11, plan, touchup]) expect(text).not.toContain("opportunity_grounding");
    const assembled = assembleNeg1_2AuthorPrompt({
      head: cold,
      core,
      brief: "brief",
      contextBlocks: "=== STAGE -1.1 GAPS CONTEXT ===\n{}",
      corePath: "/tmp/proto_core.json",
    });
    expect(assembled).toContain("Rank all seeds by direct evidence");
    expect(assembled).toContain("STAGE -1.1 GAPS CONTEXT");
    // An undelivered remark is never rendered from a Lean signature.
    expect(shouldUseLeanRender("undelivered", true)).toBe(false);
    expect(shouldUseLeanRender("deliver", true)).toBe(true);
  });
});
