import { describe, it, expect } from "vitest";
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { parseNoteBlocks } from "../src/presentation/note_parser.js";
import { loadBankEntry } from "../src/presentation/bank.js";
import { acceptedBankEntry, causalSmithRoot } from "./helpers.js";

const fix = () => readFile(join(import.meta.dirname, "fixtures/presentation/mini_note.md"), "utf8");

describe("note parser", () => {
  it("extracts P/L/T blocks with fields", async () => {
    const blocks = parseNoteBlocks(await fix());
    expect(blocks.map((b) => b.obj_id)).toEqual(["P-1", "P-2", "L-1", "T-1"]);
    const p1 = blocks[0];
    expect(p1.title).toBe("Observable law and measurable structure");
    expect(p1.fields["Signature"]).toContain("probability space");
    const t1 = blocks[3];
    expect(t1.fields["Load-bearing hypotheses"]).toContain("H1 (A1 Identification)");
    expect(t1.fields["Conclusion"]).toContain("O(n^{-(1+κ)/(2+κ)})");
  });

  it("parses the real banked note (integration)", async () => {
    const { qid, spec } = acceptedBankEntry();
    const entry = await loadBankEntry(causalSmithRoot(), qid, spec);
    const blocks = parseNoteBlocks(entry.noteMd);
    // Structural (not paper-specific): the note parses into many P/L/T anchor blocks, each with a
    // well-formed `<PREFIX>-<n>` id and a non-empty title. The exact ids depend on the banked paper;
    // the mini_note.md fixture test above pins the precise field-parsing semantics.
    expect(blocks.length).toBeGreaterThan(20);
    const ids = blocks.map((b) => b.obj_id);
    for (const id of ids) expect(id).toMatch(/^[A-Z]+-/);
    const prefixes = new Set(ids.map((id) => id[0]));
    for (const p of ["P", "L", "T"]) expect(prefixes.has(p)).toBe(true);
    expect(blocks.every((b) => b.title.length > 0)).toBe(true);
  });
});
