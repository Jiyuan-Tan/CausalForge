import { describe, expect, it, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { loadPromptTemplate, renderTemplate } from "../../src/shared/prompts.js";

let tmp: string;
beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "cs-prompts-"));
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("loadPromptTemplate", () => {
  it("reads a prompt file from the given directory", async () => {
    await writeFile(path.join(tmp, "hello.txt"), "Hello {{name}}!", "utf8");
    expect(await loadPromptTemplate(tmp, "hello.txt")).toBe("Hello {{name}}!");
  });

  it("propagates ENOENT for a missing file", async () => {
    await expect(loadPromptTemplate(tmp, "missing.txt")).rejects.toThrow(/ENOENT|no such file/i);
  });
});

describe("renderTemplate", () => {
  it("substitutes {{var}} occurrences", () => {
    expect(renderTemplate("a {{x}} b {{y}} c", { x: "1", y: "2" })).toBe("a 1 b 2 c");
  });

  it("leaves unknown {{var}} placeholders intact", () => {
    expect(renderTemplate("hi {{name}} ({{unknown}})", { name: "Alice" })).toBe(
      "hi Alice ({{unknown}})",
    );
  });

  it("substitutes repeated placeholders", () => {
    expect(renderTemplate("{{n}} + {{n}} = 2*{{n}}", { n: "x" })).toBe("x + x = 2*x");
  });

  it("does not interpret regex specials in values", () => {
    // Naive `.replace(string, replacement)` treats $1 etc in `replacement` as
    // capture refs. We use the function form to avoid that — verify.
    expect(renderTemplate("v={{v}}", { v: "$1$&" })).toBe("v=$1$&");
  });

  it("returns the template unchanged when no placeholders", () => {
    expect(renderTemplate("nothing to substitute", {})).toBe("nothing to substitute");
  });
});
