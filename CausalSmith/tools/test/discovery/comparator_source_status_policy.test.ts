import { readFile } from "node:fs/promises";
import { describe, expect, it } from "vitest";

async function prompt(relative: string): Promise<string> {
  return (await readFile(new URL(`../../src/discovery/prompts/${relative}`, import.meta.url), "utf8"))
    .replace(/\s+/g, " ");
}

describe("comparator source-status policy", () => {
  it("prevents an unavailable unpublished abstract from vetoing D0.5 novelty", async () => {
    const [decision, general] = await Promise.all([
      prompt("D0.5/stage0_5_review.txt"),
      prompt("D0.5/stage0_5_general_review.txt"),
    ]);

    expect(decision).toContain("unpublished non-archival WIP with no theorem text");
    expect(decision).toContain("do not let it alone trigger a novelty finding or block");
    expect(general).toContain("do not let it alone lower the tier or block the floor");
  });

  it("keeps published-but-unavailable results on an external-verification path", async () => {
    const decision = await prompt("D0.5/stage0_5_review.txt");

    expect(decision).toContain("published-but-inaccessible load-bearing claims");
    expect(decision).toContain("source verification");
  });

  it("applies the same distinction during proposal drafting and review", async () => {
    const [legacyReview, coreReview, drafter] = await Promise.all([
      prompt("D-0.5/stage_neg1_review.txt"),
      prompt("D-0.5/stage_neg1_review_core.txt"),
      prompt("D-1/stage_neg1_2_proto_core.txt"),
    ]);

    for (const text of [legacyReview, coreReview]) {
      expect(text).toContain("unpublished non-archival WIP");
      expect(text).toContain("article or preprint");
      expect(text).toContain("source verification");
    }
    expect(drafter).toContain("does not require a promise row");
    expect(drafter).toContain("published-but-inaccessible result is not ignored");
  });
});
