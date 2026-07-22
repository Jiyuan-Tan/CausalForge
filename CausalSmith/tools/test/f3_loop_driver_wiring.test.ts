import { describe, expect, it } from "vitest";
import { readFile } from "node:fs/promises";
import path from "node:path";

describe("standalone F3 proof-loop driver", () => {
  it("forwards the shared state and persistent filler directive", async () => {
    const source = await readFile(path.join(process.cwd(), "bin/f3_loop.ts"), "utf8");

    expect(source).toMatch(/runProofReviewLoop\(\{[\s\S]*?\n\s+state,/);
    expect(source).toContain(
      "fillerDirective: state.flags.f3_filler_directive ?? null",
    );
  });
});
