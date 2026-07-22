// Shared argv-reader contracts.
//
// The behaviours pinned here are the ones the 40 hand-rolled parsers got wrong:
// swallowing a following flag as a value, and disagreeing on whether a flag name
// carries its own leading dashes.

import { describe, expect, it } from "vitest";
import { ArgReader, CliArgsError, readArgs } from "../../src/shared/cli_args.js";

const read = (...argv: string[]) => new ArgReader(argv);

describe("value", () => {
  it("reads the token after the flag", () => {
    expect(read("--out", "/tmp/x").value("--out")).toBe("/tmp/x");
  });

  it("returns undefined for an absent flag", () => {
    expect(read("--other", "1").value("--out")).toBeUndefined();
  });

  it("refuses to swallow a following flag as the value", () => {
    // `d0_directive.ts --directive --require-core-changes` used to set the directive
    // to the literal string "--require-core-changes" AND lose the boolean flag.
    expect(() => read("--directive", "--require-core-changes").value("--directive"))
      .toThrow(CliArgsError);
    expect(() => read("--directive", "--require-core-changes").value("--directive"))
      .toThrow(/looks like another flag/);
  });

  it("refuses a flag given no value at all", () => {
    expect(() => read("--out").value("--out")).toThrow(/requires a value/);
  });

  it("allows a flag-like value when the caller opts in", () => {
    const r = new ArgReader(["--directive", "--verbatim-text"], { allowFlagLikeValues: ["--directive"] });
    expect(r.value("--directive")).toBe("--verbatim-text");
  });
});

describe("values", () => {
  it("collects every occurrence in argv order", () => {
    expect(read("--t", "a", "--t", "b", "--t", "c").values("--t")).toEqual(["a", "b", "c"]);
  });

  it("skips occurrences with a missing or flag-like value", () => {
    expect(read("--t", "a", "--t", "--other", "--t", "b").values("--t")).toEqual(["a", "b"]);
  });
});

describe("positionals", () => {
  it("separates positionals from flags and their values", () => {
    expect(read("qid", "spec", "--out", "/tmp/x", "--force").positionals()).toEqual(["qid", "spec"]);
  });

  it("does not treat a boolean flag's successor as consumed", () => {
    expect(read("--force", "qid", "spec").positionals()).toEqual(["spec"]);
  });
});

describe("bool", () => {
  it("reports presence only", () => {
    expect(read("--force").bool("--force")).toBe(true);
    expect(read("--other").bool("--force")).toBe(false);
  });
});

describe("readArgs", () => {
  it("defaults to process.argv minus node and script", () => {
    expect(readArgs(["a", "--b", "c"]).positionals()).toEqual(["a"]);
  });
});
