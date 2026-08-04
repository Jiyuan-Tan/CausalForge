import { describe, expect, it } from "vitest";
import { frontMatterBibKeys, frontMatterCacheKey } from "../src/presentation/stages/p2_draft.js";

describe("P2 front-matter prompt cache inputs", () => {
  it("invalidates the cache when the allowed bibliography-key prompt input changes", () => {
    const base = frontMatterCacheKey("model", "body", "revision", "related work", "old2020");
    const changedPool = frontMatterCacheKey("model", "body", "revision", "related work", "new2021");
    expect(changedPool).not.toBe(base);
  });

  it("rejects a missing or unparseable bibliography pool instead of telling the model to cite nothing", () => {
    expect(() => frontMatterBibKeys("")).toThrow(/non-empty, parseable references\.bib/);
    expect(() => frontMatterBibKeys("not BibTeX")).toThrow(/non-empty, parseable references\.bib/);
    expect(frontMatterBibKeys("@article{keep2021, title = {Kept}}"))
      .toBe("keep2021");
  });
});
