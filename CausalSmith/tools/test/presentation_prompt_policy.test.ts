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
        paper_tex: "P", related_work_brief: "R", verification_contract: "V",
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

  it("makes every P5 referee draw independent of earlier issue lists", async () => {
    const prompt = await presentationPrompt("p5_review", {
      paper_tex: "CURRENT PAPER", related_work_brief: "CURRENT LITERATURE", verification_contract: "CURRENT CONTRACT",
    });
    expect(prompt).toContain("Review this submission independently from scratch");
    expect(prompt).not.toContain("immediately preceding review");
    expect(prompt).not.toContain("prior_issue_families");
    expect(prompt).not.toMatch(/reuse (?:a|the same) `?finding_id/);
  });
});

describe("appendix proofs must be self-contained, not an outline of the Lean route", () => {
  // Regression: the shipped discrete-ATE paper rendered its lemma proofs as noun phrases for the
  // Lean helpers ("X is the centered fixed-light term", "the ratio arm error is bounded by a
  // residual term") — faithful to Lean, unreadable on paper. Nothing caught it: the drafting
  // prompts capped lemma proofs at "half a page" and the audit only checked over/under-claiming.
  it("tells both drafting prompts to define every symbol and display every step", async () => {
    const prompts = await Promise.all([
      presentationPrompt("p2_proof", {
        theorem_env: "T", lean_proof_source: "L", helper_lemma_envs: "H",
        cited_dependencies: "C", informal_derivation: "D", notation_table: "N", revision_brief: "none",
      }),
      presentationPrompt("p2_lemma_proofs_batch", {
        lemmas_block: "L", citable_envs: "C", notation_table: "N", revision_brief: "none",
      }),
    ]);
    for (const prompt of prompts) {
      expect(prompt).toContain("SELF-CONTAINED ARGUMENT");
      expect(prompt).toContain("explicit defining display");
      expect(prompt).toMatch(/render that helper's CONCLUSION as a display/);
      expect(prompt).toContain("Length follows the argument, never a budget");
      expect(prompt).not.toMatch(/one paragraph to a half page/); // the cap that produced the stubs
      // The D-stage informal derivation is supplied as exposition context, SUBORDINATED to
      // the Lean route (it may be wrong or never formalized — laundering guard).
      expect(prompt).toContain("INFORMAL DERIVATION");
      expect(prompt).toMatch(/follow Lean and ignore/);
      expect(prompt).toMatch(/Never import a step, constant, or claim that has no counterpart in the Lean proof/);
    }
  });

  it("gives the proof audit a legibility verdict the refine loop can act on", async () => {
    const audit = await presentationPrompt("proof_audit", {
      obj_id: "lem:x", proof_tex: "P", lean_proof_source: "L", notation_table: "N",
    });
    expect(audit).toContain("SELF-CONTAINEDNESS");
    expect(audit).toContain('"faithful" | "unfaithful" | "incomplete"');
    const refine = await presentationPrompt("refine_proof", {
      obj_id: "lem:x", proof_tex: "P", lean_proof_source: "L",
      referenced_defs: "D", audit_issues: "I", notation_table: "N",
    });
    expect(refine).toMatch(/EXPAND when the audit flags the proof as `incomplete`/);
    expect(refine).toMatch(/REPAIR THE REASON/);
  });

  // Every defect the post-hoc review found was content-correct, so the audit's calibration
  // paragraph ("flag a mismatch only when the prose asserts CONTENT the Lean does not deliver")
  // suppressed all of them: a justification citing hypotheses that do not entail its conclusion,
  // one symbol carrying two meanings, a lattice top printed as the never-treated state.
  it("audits the prose on its own terms, not only against Lean", async () => {
    const audit = await presentationPrompt("proof_audit", {
      obj_id: "lem:x", proof_tex: "P", lean_proof_source: "L", notation_table: "N",
      paper_path: "/tmp/p/paper.tex",
    });
    expect(audit).toMatch(/THE PROSE ON ITS OWN TERMS/);
    expect(audit).toMatch(/does not entail its conclusion/);        // insufficient justification
    expect(audit).toMatch(/symbol carrying two meanings/);          // notation collision
    expect(audit).toMatch(/transliterated instead of rendered/);    // untranslated Lean object
    // The leniency clause must be scoped, or it swallows the new checks exactly as before.
    expect(audit).toMatch(/leniency governs checks 1-3 only/);
    // class 1 sub-patterns that plain "does not entail" does not name
    expect(audit).toMatch(/DIRECTION of every invoked inequality/);
    expect(audit).toMatch(/weaker condition than the step needs/);
    // class 2: claims the proof makes ABOUT other objects, checkable only by opening them
    expect(audit).toMatch(/CLAIMS ABOUT OTHER OBJECTS/);
    expect(audit).toContain("{{paper_path}}".replace("{{paper_path}}", "/tmp/p/paper.tex"));
  });

  // The proof audit runs at P2, so a P5 pass that rewrites an appendix proof is never re-audited.
  // The transported-LATE bundle shipped that way: P5 expanded two proofs and deleted every
  // `% lean:` marker, severing each step from the declaration certifying it.
  it("lets the P5 reviser expand a proof but not drop its audit markers", async () => {
    const prompt = await presentationPrompt("p5_holistic_revision", {
      out_dir: "/tmp/p", revision_pass: "1", revision_mode: "local", p5_review: "{}",
      verification_contract: "{}", related_work_brief: "", editable_files: "- paper.tex",
    });
    expect(prompt).toMatch(/appendix proof may be expanded or reorganized for readability/);
    expect(prompt).toMatch(/`% lean:` comments must survive verbatim/);
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

describe("a Proposition is a main result, not an unproved statement", () => {
  // Every proof path in p2_draft filtered on `theoremv`/`lemmav` and never mentioned
  // `propositionv`, which the anchor parser does recognize. All three propositionv envs in the
  // shipped bundles (prop:two-category-confounding, prop:oracle-regime-reduction,
  // prop:cty-a1-a2-winsorized-expected-outer-upper) therefore reached the reader with no proof
  // rendered, none audited, and none in paper.tex — each despite a verified Lean declaration.
  it("routes propositionv through the main-result proof path", async () => {
    const { isMainProofEnv } = await import("../src/presentation/stages/p2_draft.js");
    expect(isMainProofEnv("theoremv")).toBe(true);
    expect(isMainProofEnv("propositionv")).toBe(true);
    expect(isMainProofEnv("lemmav")).toBe(false);
    expect(isMainProofEnv("definitionv")).toBe(false);
    expect(isMainProofEnv("assumptionv")).toBe(false);
    expect(isMainProofEnv("remarkv")).toBe(false);
  });

  it("leaves no proof-path filter keyed on the bare string \"theoremv\"", async () => {
    const src = await import("node:fs/promises").then((fs) =>
      fs.readFile(new URL("../src/presentation/stages/p2_draft.ts", import.meta.url), "utf8"));
    // The ONLY place the bare kind may appear is inside isMainProofEnv itself; any other
    // occurrence is a proof path that would skip propositionv again.
    expect(src.match(/env === "theoremv"/g) ?? []).toHaveLength(1);
  });
});

describe("a rendered proof must reach the paper", () => {
  it("flags a rendered proof that was never placed, and passes one that was", async () => {
    const { lintProofsReachedPaper } = await import("../src/presentation/stages/p2_draft.js");
    const paper = String.raw`
\begin{lemmav}{lem:a}[A]body\end{lemmav}
\begin{proof}[Proof of \cref{obj:lem:a}]argument\end{proof}
\begin{propositionv}{prop:b}[B]body\end{propositionv}
`;
    expect(lintProofsReachedPaper(paper, ["lem:a"])).toEqual([]);
    const dropped = lintProofsReachedPaper(paper, ["lem:a", "prop:b"]);
    expect(dropped).toHaveLength(1);
    expect(dropped[0]).toMatchObject({ gate: "proof-dropped", objId: "prop:b" });
    expect(dropped[0].detail).toContain("never placed in paper.tex");
  });

  it("finds no dropped proofs in the shipped bundles", async () => {
    // Until 2026-08-25 this test asserted the historical failure set (seven dropped proofs
    // shipped live); the isolated-lemma fix wave reassembled those bundles, so the invariant
    // flips: shipped bundles must stay clean. Removing an object from a paper also deletes its
    // proofs/*.tex, so every id under proofs/ is expected to be placed — no filtering.
    const { lintProofsReachedPaper } = await import("../src/presentation/stages/p2_draft.js");
    const { readFile, readdir } = await import("node:fs/promises");
    const root = new URL("../../doc/presentation/", import.meta.url);
    const found: string[] = [];
    for (const q of ["panel_ppml_forbidden_comparison_v1",
                     "eid_lingam_direction_min_order_v1_truncated_cumulant_minimality",
                     "stat_dose_response_minimax_holder_anisotropic_converse"]) {
      const paper = await readFile(new URL(`${q}/paper.tex`, root), "utf8");
      const ids = (await readdir(new URL(`${q}/proofs/`, root)))
        .filter((n) => n.endsWith(".tex")).map((n) => n.slice(0, -4));
      found.push(...lintProofsReachedPaper(paper, ids).map((p) => p.objId!));
    }
    expect(found).toEqual([]);
  });
});
