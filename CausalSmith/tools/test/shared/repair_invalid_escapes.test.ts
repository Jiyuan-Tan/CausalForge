import { describe, it, expect } from "vitest";
import { repairInvalidStringEscapes, expectStringJsonOutput } from "../../src/shared/codex_json.js";

describe("repairInvalidStringEscapes", () => {
  it("repairs LaTeX inline math, the case that killed a completed D0.5.G verdict", () => {
    // Both referees had already PASSED; the general review was lost at position 213 to
    // `\(` — a legal LaTeX delimiter and an illegal JSON escape.
    const raw = String.raw`{"critique":"shells \(q_d(P)=r_n\), with the converse"}`;
    const fixed = repairInvalidStringEscapes(raw)!;
    expect(JSON.parse(fixed).critique).toBe(String.raw`shells \(q_d(P)=r_n\), with the converse`);
  });

  it("leaves an ALREADY-escaped backslash alone", () => {
    // Models mix both spellings in one string: the real payload had `\(` raw AND
    // `\\le` correctly escaped. Re-escaping the valid one would corrupt it.
    const raw = String.raw`{"critique":"c_G \\le 3/16"}`;
    expect(repairInvalidStringEscapes(raw)).toBeNull();
    expect(JSON.parse(raw).critique).toBe(String.raw`c_G \le 3/16`);
  });

  it("handles a string mixing valid and invalid escapes", () => {
    const raw = String.raw`{"critique":"\(x\) and \\le and \n done"}`;
    const parsed = JSON.parse(repairInvalidStringEscapes(raw)!);
    expect(parsed.critique).toBe("\\(x\\) and \\le and \n done");
  });

  it("repairs \\usepackage, where \\u is a valid PREFIX but not a valid escape", () => {
    const raw = String.raw`{"tex":"\usepackage{amsmath}"}`;
    expect(JSON.parse(repairInvalidStringEscapes(raw)!).tex).toBe(String.raw`\usepackage{amsmath}`);
  });

  it("preserves a genuine \\uXXXX escape", () => {
    const raw = String.raw`{"s":"é"}`;
    expect(repairInvalidStringEscapes(raw)).toBeNull();
    expect(JSON.parse(raw).s).toBe("é");
  });

  it("ignores backslashes outside string literals", () => {
    expect(repairInvalidStringEscapes(`{"a":1}`)).toBeNull();
  });

  it("cannot change structure — only string contents", () => {
    // A repair that could alter structure might make a parse succeed DIFFERENTLY,
    // which is worse than failing.
    const raw = String.raw`{"a":"\(","b":[1,2],"c":{"d":"\)"}}`;
    const parsed = JSON.parse(repairInvalidStringEscapes(raw)!);
    expect(parsed.b).toEqual([1, 2]);
    expect(parsed.c.d).toBe("\\)");
    expect(Object.keys(parsed)).toEqual(["a", "b", "c"]);
  });

  it("returns null when nothing needs repair", () => {
    expect(repairInvalidStringEscapes(`{"ok":"plain text"}`)).toBeNull();
  });
});

describe("expectStringJsonOutput — end-to-end", () => {
  it("recovers a referee verdict whose prose carries raw LaTeX", () => {
    const stdout = String.raw`{"tier":"field","salvageable":false,"critique":"rate-level minimax on \(q_d(P)=r_n\) shells with \\le 3/16","flagship_potential":false}`;
    const out = expectStringJsonOutput(stdout) as Record<string, unknown>;
    expect(out.tier).toBe("field");
    expect(out.flagship_potential).toBe(false);
    expect(out.critique).toContain("\\(q_d(P)=r_n\\)");
    expect(out.critique).toContain("\\le 3/16");
  });
});
