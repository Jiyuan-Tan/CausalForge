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
  // Regression: `isLeanRealizedNotation` (p1_plan.ts) drops synthesize-def findings for
  // @realizes-tagged symbols, because a paper-side duplicate would compete with the Lean
  // declaration for authority. That decision was never communicated to the reviewer, so it
  // re-derived the same gaps every round: in one run q_k/p_k/\pi_k/\mu_{ak} were re-reported
  // 7/6/6/5 times across 10 high-effort ~39.5k-char calls, none of them actionable.
  it("renders the Lean-realized symbol list with no unreplaced placeholders", async () => {
    const prompt = await presentationPrompt("p1_notation_check", {
      frozen_layer: "\\begin{definitionv}{P-1}[Setup]body\\end{definitionv}",
      notation_table: "| a | p_k | mass | notation_gaps |",
      lean_realized_symbols: "- p_k\n- \\pi_k",
    });
    expect(prompt.match(/\{\{[a-z_]+\}\}/g)).toBeNull(); // no placeholder survives rendering
    expect(prompt).toContain("- p_k");
    expect(prompt).toContain("- \\pi_k");
    // The instruction must be explicit, or the reviewer keeps reporting them as undefined.
    expect(prompt).toContain("@realizes");
    expect(prompt).toMatch(/never report them as `undefined` or `no-anchor`/);
  });
});
