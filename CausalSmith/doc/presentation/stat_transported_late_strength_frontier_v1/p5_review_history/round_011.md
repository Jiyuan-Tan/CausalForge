# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified results deliver a coherent and useful minimax frontier for transported complier ratios, with only remaining presentation and framing issues rather than substantive claim-fidelity defects.

The paper characterizes honest expected length for transported complier-effect ratio inference under weak transported first stages and transport-weight dispersion. The main oracle, fixed-geometry, and finite-cell feasible results are well aligned with the verified statements and the prose now largely states the contribution at the correct scope. I would support publication after a short revision that improves readability and removes a few residual ambiguities in presentation.

## Strengths
- Clear and nontrivial synthesis of transported noncompliance, weak-IV robust score inversion, and minimax expected-length analysis.
- The central rate \(\min\{1,t_0^{-1/2}\}\) is stated consistently across oracle, fixed-geometry, uniform finite-cell, and regular finite-cell settings.
- The prose generally respects the verified theorem conditions and avoids overstating beyond the formal layer.
- The distinction between model-validation evidence for receipt transport and the data used by the confidence-set procedures is now much clearer.

## Findings
- **[minor·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition repeats the full inherited checklist from \(\mathcal P_n\), making the single extra finite-cell restriction harder to see despite the preceding sentence saying the class is the compact submodel \(\mathcal N_n=\{P\in\mathcal P_n: P\text{ satisfies }\cref{obj:ass:finite-cell-source}\}\).
  - *Fix:* Keep the displayed compact definition as the main definition, state that all conditions in \(\mathcal P_n\) are inherited, and move the expanded checklist to a short parenthetical or appendix audit table if needed.
- **[minor·structure] Oracle Frontier and Score Inversion** — The theorem statement for \cref{obj:thm:oracle-score-inversion-attainment} still contains an "Admissible geometry" hypothesis, which can read as though the global oracle score rule depends on a selected geometry, even though the surrounding prose says the rule is evaluated law by law using each law's oracle inputs.
  - *Fix:* Rename this hypothesis to something like "Ambient admissible carrier" and add one sentence inside the theorem statement or immediately before it: the selected geometry is used only to certify the ambient comparison domain, while \(C_n\) uses the canonical \(w\) and \(e\) of the law under evaluation.
- **[nit·prose] global** — The manuscript uses both "least-favorable" and "least-favourable" in reader-facing prose and titles, for example \cref{obj:synth_5} uses "least-favourable" while \cref{obj:def:least-favorable-witness} uses "Least-favorable".
  - *Fix:* Choose one spelling convention throughout the manuscript, including environment titles and explanatory paragraphs.

## Questions for authors
- Can the final version state explicitly whether the finite-cell procedures require the cell partition to be known before sampling, or merely recoverable from the observed support?
- Do the authors want the appendix proof narratives to serve as a human proof, or mainly as a map to the Lean artifact? A short sentence clarifying that role would help readers calibrate the level of detail.

