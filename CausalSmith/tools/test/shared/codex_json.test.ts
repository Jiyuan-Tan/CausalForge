import { describe, expect, it, beforeEach, afterEach } from "vitest";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {
  expectStringJsonOutput,
  parseAndPersist,
  persistCodexRaw,
  tryBraceBalanceRepair,
} from "../../src/shared/codex_json.js";

let tmp: string;
beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "cs-codex-json-"));
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("expectStringJsonOutput", () => {
  it("parses a well-formed object", () => {
    expect(expectStringJsonOutput('{"a":1}')).toEqual({ a: 1 });
  });

  it("slices between first { and last } when wrapped in prose / fences", () => {
    const wrapped = '```json\n{"x":[1,2,3]}\n```';
    expect(expectStringJsonOutput(wrapped)).toEqual({ x: [1, 2, 3] });
  });

  it("returns the FIRST balanced object when codex double-emits", () => {
    // Failure mode observed in research pipeline: codex emits a pretty-printed
    // object followed by a compact restatement. Previous behavior: first-{/last-}
    // slice produced the concatenation, which JSON.parse rejects.
    const double = '{"a":1,"b":[2,3]}\n{"a":1,"b":[2,3]}';
    expect(expectStringJsonOutput(double)).toEqual({ a: 1, b: [2, 3] });
  });

  it("parses a fenced JSON object followed by trailing prose", () => {
    const messy = '```json\n{"verdict":"pass","notes":"ok"}\n```\nAnd here is some commentary.';
    expect(expectStringJsonOutput(messy)).toEqual({ verdict: "pass", notes: "ok" });
  });

  it("repairs a 1-char truncation (missing outer })", () => {
    // Mirror the Manski 1990 failure mode: one missing closing brace.
    const truncated = '{"insight":{"id":"x","theorems":[{"t":1}]}';
    expect(expectStringJsonOutput(truncated)).toEqual({
      insight: { id: "x", theorems: [{ t: 1 }] },
    });
  });

  it("repairs missing ] before missing }", () => {
    const truncated = '{"a":[1,2,3';
    expect(expectStringJsonOutput(truncated)).toEqual({ a: [1, 2, 3] });
  });

  it("tags unrepairable parse failures with code codex_malformed_output", () => {
    try {
      expectStringJsonOutput('{"a": "uncl');
      throw new Error("expected throw");
    } catch (err: unknown) {
      expect((err as { code?: string }).code).toBe("codex_malformed_output");
    }
  });

  it("tags missing-object as codex_malformed_output", () => {
    try {
      expectStringJsonOutput("just prose, no braces here");
      throw new Error("expected throw");
    } catch (err: unknown) {
      expect((err as { code?: string }).code).toBe("codex_malformed_output");
    }
  });

  it("does NOT 'repair' over-balanced inputs (extra closers)", () => {
    // Over-balanced: heuristic must bail out, not silently produce something.
    expect(tryBraceBalanceRepair('{"a":1}}')).toBeNull();
  });

  it("does NOT repair inputs missing more than 3 closers (likely structural)", () => {
    const tooBroken = "{".repeat(5) + '"a":1';
    expect(tryBraceBalanceRepair(tooBroken)).toBeNull();
  });

  it("ignores brackets inside strings when counting", () => {
    // Balanced object whose string content has dangling braces. Must NOT be
    // treated as needing repair.
    const s = '{"text":"some {prose with [brackets]} inside"}';
    expect(tryBraceBalanceRepair(s)).toBeNull();
    expect(expectStringJsonOutput(s)).toEqual({
      text: "some {prose with [brackets]} inside",
    });
  });
});

describe("persistCodexRaw + parseAndPersist", () => {
  it("persistCodexRaw writes the raw payload under codex_raw/", async () => {
    const written = await persistCodexRaw(tmp, "passA", "any stdout bytes");
    expect(written).not.toBeNull();
    expect(existsSync(written!)).toBe(true);
    expect(readFileSync(written!, "utf8")).toBe("any stdout bytes");
    const dir = path.join(tmp, "codex_raw");
    const entries = readdirSync(dir);
    expect(entries.length).toBe(1);
    expect(entries[0]).toMatch(/^passA__/);
  });

  it("persistCodexRaw sanitizes tag and never throws on bad run dirs", async () => {
    // Embed a NUL byte so mkdir is guaranteed to reject the path on every OS
    // (recursive mkdir is otherwise permissive — "/nonexistent/..." would
    // succeed on Windows by anchoring under the current drive).
    const written = await persistCodexRaw("bad\0dir", "tag with spaces?", "x");
    expect(written).toBeNull();
  });

  it("parseAndPersist persists the raw payload before parsing, even on parse failure", async () => {
    await expect(parseAndPersist('{"a": "uncl', tmp, "passA")).rejects.toMatchObject({
      code: "codex_malformed_output",
    });
    const dir = path.join(tmp, "codex_raw");
    expect(existsSync(dir)).toBe(true);
    const entries = readdirSync(dir);
    expect(entries.length).toBe(1);
    expect(readFileSync(path.join(dir, entries[0]), "utf8")).toBe('{"a": "uncl');
  });
});
