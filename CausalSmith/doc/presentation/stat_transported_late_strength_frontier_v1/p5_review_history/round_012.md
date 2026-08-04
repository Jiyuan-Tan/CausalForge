# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified results deliver a clear minimax expected-length contribution, but several presentation choices still obscure scope and make the manuscript harder to referee as an econometrics paper.

The paper characterizes honest expected-length frontiers for transported complier ratios under weak transported first stages and weight dispersion, and gives matching oracle, fixed-geometry, and finite-cell feasible constructions. The contribution is interesting and plausibly publishable: it connects transported noncompliance with weak-ratio inference in a compact parameter space and the main claims are faithful to the verified statements. The remaining issues are mainly expositional and scope-clarifying rather than mathematical.

## Strengths
- The paper identifies a clean effective-strength index, \(n\mu_n^2/\kappa_n\), that combines weak compliance and transport-weight dispersion.
- The oracle lower and upper bounds, fixed-geometry frontier, and finite-cell feasible attainability results form a coherent contribution.
- The prose generally respects the verified theorem conditions and avoids overstating asymptotic strength beyond the stated model classes.
- The related-work discussion positions the paper well against transported CACE, weak-IV robust LATE, two-sample IV, and transported-ATE benchmarks.

## Findings
- **[minor·prose] Oracle Frontier and Score Inversion** — The theorem statement for \cref{obj:thm:oracle-score-inversion-attainment} still contains an "Admissible geometry" hypothesis, which can read as though the global oracle score-inversion procedure depends on a selected fixed geometry. The surrounding prose partly addresses this, but the result is still easy to misread because the theorem is presented as a global oracle attainment theorem.
  - *Fix:* Move the admissible-geometry clause into a clearly named ambient-carrier/existence condition, and add one sentence in the theorem statement or immediately before it saying that the displayed procedure is evaluated with each law's own canonical \(w\) and \(e\); the selected geometry is used to ensure the comparison domain is nonempty/admissible, not as an input to the score rule.
- **[minor·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition repeats the full inherited checklist from \(\mathcal P_n\), making the single additional finite-cell restriction harder to see despite the preceding sentence defining \(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies }\cref{obj:ass:finite-cell-source}\}\).
  - *Fix:* State \(\mathcal N_n\) as the submodel of \(\mathcal P_n\) with \cref{obj:ass:finite-cell-source}; if traceability is desired, put the inherited checklist in a compact parenthetical or footnote rather than repeating the full list in the formal definition.
- **[minor·structure] Setup, Transport, and Honest Risk** — The receipt-transport discussion is useful but disproportionately long relative to the other assumptions, and it mixes assumption interpretation, validation design, and a concrete application example before the main risk objects are introduced.
  - *Fix:* Compress the validation and appointment-reminder example to one short paragraph, or move it to the discussion after the main results; keep the setup section focused on the model restriction and its role in identifying the denominator.
- **[nit·prose] global** — The manuscript uses both "least-favorable" and "least-favourable" in reader-facing prose and titles, for example \cref{obj:synth_5} uses "least-favourable" while \cref{obj:def:least-favorable-witness} uses "Least-favorable".
  - *Fix:* Standardize to one spelling throughout, preferably "least-favorable" to match the theorem and definition names.
- **[nit·prose] appendix** — The appendix proof narratives contain implementation-flavored phrases such as "the row \(n=0\) is discharged by the empty branch" and "at row \(n=0\) take the empty branch," which are distracting in a journal manuscript and make the exposition feel closer to a formalization log than an econometric proof.
  - *Fix:* Replace these with ordinary asymptotic prose, for example by saying that finitely many initial rows are immaterial for the limiting statements.

## Questions for authors
- Can the admissible-geometry hypothesis in the oracle attainment theorem be renamed or reformulated so readers immediately see whether it is a nonemptiness/carrier condition rather than a restriction on the law-by-law oracle procedure?
- Do the authors want the receipt-transport validation discussion to be part of the model setup, or would it be clearer as an applied interpretation paragraph after the formal identification result?

