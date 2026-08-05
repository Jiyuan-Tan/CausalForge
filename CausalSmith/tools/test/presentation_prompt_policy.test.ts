import { describe, expect, it } from "vitest";
import { presentationPrompt } from "../src/presentation/prompt_io.js";

describe("global presentation prose contract", () => {
  it("is injected into drafting, TLDR, review, and holistic revision prompts", async () => {
    const prompts = await Promise.all([
      presentationPrompt("p2_intro_abstract", {
        outline: "O", frozen_layer: "F", references: "R", assumption_citation_guidance: "A",
        graph_hypotheses: "G", revision_brief: "none", related_work_brief: "W",
      }),
      presentationPrompt("p4_tldr", { title: "T", abstract: "A" }),
      presentationPrompt("p5_review", {
        paper_tex: "P", related_work_brief: "R", verification_contract: "V", prior_issue_families: "[]",
      }),
      presentationPrompt("p5_holistic_revision", {
        out_dir: "/tmp/p", revision_pass: "1", revision_mode: "local", p5_review: "{}",
        verification_contract: "{}", related_work_brief: "", editable_files: "- paper.tex",
      }),
    ]);
    for (const prompt of prompts) {
      expect(prompt).toContain("GLOBAL READER-FACING PROSE CONTRACT");
      expect(prompt).toContain("Outside an explicitly titled Limitations");
      expect(prompt).toContain("accurate affirmative account of the delivered result");
      expect(prompt).toContain("Page-facing short descriptions");
      expect(prompt).toContain("the key/main caveat is");
      expect(prompt).toContain("GLOBAL CROSS-REFERENCE CONTRACT");
      expect(prompt).toContain("Use cleveref exclusively");
      expect(prompt).toContain("every reader-facing cross-reference");
      expect(prompt).toContain("Legacy `\\ref{...}`, `\\eqref{...}`, and `\\autoref{...}` are forbidden");
    }
  });
});

describe("notation-check reviewer is told which symbols Lean already resolves", () => {
  // Two regressions pin this paragraph's shape. (1) `isLeanRealizedNotation` (p1_plan.ts)
  // suppresses synthesize-def findings for @realizes-tagged symbols whose defining equality
  // the layer already displays; when that was never communicated, the reviewer re-derived
  // the same gaps every round (q_k/p_k/\pi_k/\mu_{ak} re-reported 7/6/6/5 times across 10
  // calls). (2) The instruction must NOT be an unconditional "never report" — under that
  // rule the transported-LATE paper shipped with its central estimand θ_T Lean-linked but
  // never defined anywhere a PDF reader can see.
  it("renders the Lean-realized symbol list with no unreplaced placeholders", async () => {
    const prompt = await presentationPrompt("p1_notation_check", {
      frozen_layer: "\\begin{definitionv}{P-1}[Setup]body\\end{definitionv}",
      notation_table: "| a | p_k | mass | notation_gaps |",
      lean_realized_symbols: "- p_k\n- \\pi_k",
    });
    expect(prompt.match(/\{\{[a-z_]+\}\}/g)).toBeNull(); // no placeholder survives rendering
    expect(prompt).toContain("- p_k");
    expect(prompt).toContain("- \\pi_k");
    // The instruction must be explicit and CONDITIONAL: a displayed definition suppresses
    // a duplicate, a bare Lean link does not excuse a missing one.
    expect(prompt).toContain("@realizes");
    expect(prompt).toMatch(/a Lean link is NOT a reader-facing\s*definition/);
    expect(prompt).toMatch(/report it as `undefined` when statements USE it/);
    expect(prompt).toMatch(/Do NOT\s*report one whose definition some environment already displays/);
  });
});
