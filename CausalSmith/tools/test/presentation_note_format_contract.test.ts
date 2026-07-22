import { describe, it, expect } from "vitest";
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { parseNoteBlocks } from "../src/presentation/note_parser.js";
import { buildFrozenLayer } from "../src/presentation/frozen_layer.js";
import { parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";
import { assumptionTable } from "../src/presentation/emit.js";
import type { CrosswalkEntry } from "../src/presentation/types.js";

// Guard for the causalsmith F1 -> causalsmith note-format CONTRACT. The current F1
// dialect (bold `**P-1 (…)**` / `### T-block: tN` headers, plain `- H1 (…):`
// hypotheses) broke parseNoteBlocks and the P4 assumption-table gate three times
// on the first real run (commits b3ec1f56 / 73c7dc95 / 2244fcb3). This fixes the
// contract under a fixture so a future F1 format drift fails CI here, not mid-run.
// See doc/research/PIPELINE_NOTES.md (2026-06-13).
const fixture = () =>
  readFile(join(import.meta.dirname, "fixtures/presentation/mini_note_current.md"), "utf8");

const lean = (decl: string) => ({ file: "Mock.lean", decl, decl_kind: "theorem", line: 1 });
const cw = (obj_id: string, kind: string): CrosswalkEntry => ({
  obj_id,
  kind,
  title: obj_id,
  tex: null,
  lean: lean(obj_id) as CrosswalkEntry["lean"],
  verdict: "exact",
});

describe("note-format contract (current causalsmith F1 dialect)", () => {
  it("parseNoteBlocks reads bold P/L and `### T-block: tN` headers", async () => {
    const blocks = parseNoteBlocks(await fixture());
    expect(blocks.map((b) => b.obj_id)).toEqual(["P-1", "P-2", "L-1", "T-1"]);
    const t1 = blocks.find((b) => b.obj_id === "T-1")!;
    // plain `- H1 (…):` hypotheses land in the Load-bearing field, NOT as new fields
    expect(t1.fields["Load-bearing hypotheses"]).toContain("H1 (A1 Identification");
    expect(t1.fields["Load-bearing hypotheses"]).toContain("H2 (A2 Overlap tail");
    expect(t1.fields["Statement"]).toContain("Corrected upper bound".length ? "risk" : "");
  });

  it("assumption-table totality passes: hyps found + note-only P-block counts as presented", async () => {
    const blocks = parseNoteBlocks(await fixture());
    // P-1 and T-1 are frozen (crosswalked); P-2 is deliberately note-only (no anchor).
    const crosswalk = [cw("P-1", "definition"), cw("T-1", "theorem")];
    const envs = parseAnchoredEnvs(buildFrozenLayer(blocks, crosswalk));
    const { problems } = assumptionTable(blocks, envs, {});
    // No "no load-bearing hypotheses" (plain H1/H2 parse) and no false
    // "references P-2 which is not presented" (P-2 is a note block).
    expect(problems.filter((p) => /no load-bearing hypotheses/.test(p))).toEqual([]);
    expect(problems.filter((p) => /not presented in the paper/.test(p))).toEqual([]);
  });
});
