import { describe, expect, it } from "vitest";
import {
  restoreAuditedProofBlocks,
  stripLatexCommentLines,
} from "../src/presentation/stages/p3_gates.js";

describe("P3 audited-proof restoration", () => {
  const audited = [
    "\\begin{proof}\nAudited first proof.\n\\end{proof}",
    "\\begin{proof}[Second]\nAudited second proof.\n\\end{proof}",
  ];

  it("keeps prose revisions while restoring proof edits in order", () => {
    const revised = [
      "Revised introduction.",
      "\\begin{proof}\nModel-edited first proof.\n\\end{proof}",
      "Revised discussion.",
      "\\begin{proof}[Second]\nModel-edited second proof.\n\\end{proof}",
    ].join("\n\n");

    const restored = restoreAuditedProofBlocks(revised, audited);
    expect(restored).not.toBeNull();
    expect(restored).toContain("Revised introduction.");
    expect(restored).toContain("Revised discussion.");
    expect(restored).toContain("Audited first proof.");
    expect(restored).toContain("Audited second proof.");
    expect(restored).not.toContain("Model-edited");
  });

  it("fails closed when a proof block is inserted or deleted", () => {
    expect(restoreAuditedProofBlocks(audited[0], audited)).toBeNull();
  });
});

describe("P3 model-facing comment stripping", () => {
  it("removes invisible provenance comments without removing escaped percentages", () => {
    const tex = [
      "% DERIVED from formal_layer.json — read-only, do not edit.",
      "Visible prose with 95\\% coverage.",
      "  % another invisible comment",
      "More visible prose.",
    ].join("\n");

    expect(stripLatexCommentLines(tex)).toBe(
      "Visible prose with 95\\% coverage.\nMore visible prose.",
    );
  });
});
