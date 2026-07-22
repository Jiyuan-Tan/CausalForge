import { describe, it, expect } from "vitest";
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { buildFrozenLayer, envFor } from "../src/presentation/frozen_layer.js";
import { parseNoteBlocks } from "../src/presentation/note_parser.js";
import type { CrosswalkEntry } from "../src/presentation/types.js";

const cwRow = (obj_id: string, kind: string, lean: CrosswalkEntry["lean"]): CrosswalkEntry => ({
  obj_id,
  kind,
  title: "",
  tex: null,
  lean,
  verdict: "",
});

describe("frozen layer", () => {
  it("emits one anchored env per block, theorem statements from Conclusion", async () => {
    const md = await readFile(join(import.meta.dirname, "fixtures/presentation/mini_note.md"), "utf8");
    const blocks = parseNoteBlocks(md);
    const cw = [
      cwRow("P-1", "definition", { file: "Basic.lean", decl: "OverlapSetup", decl_kind: "def", line: 10 }),
      cwRow("P-2", "assumption", null),
      cwRow("L-1", "lemma", { file: "Helpers.lean", decl: "l1", decl_kind: "theorem", line: 5 }),
      cwRow("T-1", "theorem", { file: "T1.lean", decl: "t1_thm", decl_kind: "theorem", line: 9 }),
    ];
    const tex = buildFrozenLayer(blocks, cw);
    expect(tex).toContain("\\begin{definitionv}{P-1}[Observable law and measurable structure]");
    expect(tex).toContain("\\begin{assumptionv}{P-2}");
    // texSafeTitle strips development-history adjectives (self-containedness)
    expect(tex).toContain("\\begin{theoremv}{T-1}[Upper bound]");
    expect(tex).toMatch(/\\begin\{theoremv\}\{T-1\}[\s\S]*O\(n\^\{-\(1\+κ\)\/\(2\+κ\)\}\)[\s\S]*\\end\{theoremv\}/);
  });

  it("maps kinds to environments", () => {
    expect(envFor("P-2", "assumption")).toBe("assumptionv");
    expect(envFor("P-1", "definition")).toBe("definitionv");
    expect(envFor("L-3", "lemma")).toBe("lemmav");
    expect(envFor("T-2", "theorem")).toBe("theoremv");
  });
});
