# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The paper delivers a clean and formally verified minimax frontier for a well-defined transported-CACE weak-ratio problem, with remaining issues mostly in exposition, organization, and reader-facing positioning rather than substance.

The submission studies honest confidence sets for transported complier effects when the transported first stage may be weak and transport weights may be dispersed. Its main contribution is a matched oracle lower and upper expected-length frontier indexed by \(n\mu_n^2/\kappa_n\), plus finite-cell feasible procedures that attain the same order under stated growth and overlap conditions. The formal claims appear faithfully represented overall, and the contribution is publishable after tightening several presentation points that currently make the paper harder to read than the results warrant.

## Strengths
- The effective-strength index \(n\mu_n^2/\kappa_n\) is a useful and interpretable synthesis of weak compliance and covariate-shift dispersion.
- The oracle converse and score-inversion attainment give a sharp and compact minimax message.
- The feasible finite-cell and regular-cell results connect the oracle frontier to implementable target-weight learning benchmarks.
- The manuscript is unusually careful about claim scope, theorem conditions, and verification boundaries.

## Findings
- **[minor·structure] Fixed Geometry and Feasible Cell Weight Learning** — The object titled "Geometry handle \(Q_{n,h}^{\mathfrak g}\)" is presented as a definition but contains substantive chi-square and total-variation inequalities: "the corresponding least-favorable laws satisfy..." This reads like a lemma or proposition, not a definition, and it blurs what is notation versus what is proved.
  - *Fix:* Retype this environment as a lemma/proposition such as "Least-favorable separation bound" while keeping the same label target if needed, and reserve the surrounding definition text for the construction of \(Q_{n,h}^{\mathfrak g}\) and the distance notation.
- **[minor·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition repeats the full \(\mathcal P_n\) assumption checklist immediately after the text already defines \(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies }\cref{obj:ass:finite-cell-source}\}\). This repetition obscures the simple nesting relationship.
  - *Fix:* Keep the displayed nesting as the main definition and move the expanded checklist to a short parenthetical or appendix verification note; in the main text, state that all \(\mathcal P_n\) restrictions are inherited and only the uniform finite-cell source condition is added.
- **[minor·structure] appendix** — The proof ordering is awkward: the proof of \(\cref{obj:prop:no-shift-reduction}\) invokes \(\cref{obj:thm:fixed-geometry-frontier}\), which is proved later in the appendix and stated later in the main text. This makes the no-shift result look logically prior while its proof is a corollary of the fixed-geometry theorem.
  - *Fix:* Move the no-shift reduction after the fixed-geometry frontier theorem, or explicitly label it as a corollary and place its proof after the fixed-geometry proof.
- **[minor·prose] appendix** — Some proof narratives still read like formalization control flow rather than econometric exposition, for example phrases such as "finite initial rows are asymptotically irrelevant," "rowwise coverage convention," "the finite-to-regular bridge," and "active rows on the limiting tail." These phrases are accurate but distract from the statistical argument.
  - *Fix:* Rewrite these passages in standard asymptotic language: describe eventual \(n\), nonempty model slices, support restriction, and reductions between submodels directly, without implementation-style labels.
- **[nit·prose] Oracle Frontier and Score Inversion** — The "Nonempty admissible carrier" bullet in \(\cref{obj:thm:oracle-score-inversion-attainment}\) is now explained better than in the prior version, but the phrase "admissible deterministic geometry" can still make readers think the global oracle score rule is conditional on a fixed geometry.
  - *Fix:* Rename the bullet to "Ambient carrier existence" and say that it supplies a nonempty comparison domain; keep the later sentence that the score statistic uses the \(w\) and \(e\) supplied by each evaluated law.
- **[nit·citation] Related Literature and Discussion** — The related-work section now identifies very recent papers as arXiv or journal articles, which largely resolves the earlier positioning issue. It would still help readers if the final bibliography and text gave enough detail for Chen--Huang, Ross et al., and Smucler--Lanni--Masip to be located unambiguously, since these are close and recent references.
  - *Fix:* Ensure the bibliography includes full titles, venues or arXiv identifiers, dates, and DOIs where available; for example, Ross et al. appears as Epidemiology 37(1):39--49, 2026, DOI 10.1097/EDE.0000000000001925, while Chen--Huang and Smucler--Lanni--Masip appear as 2025 arXiv papers.

## Questions for authors
- Can the finite-cell feasible construction be accompanied by brief practical guidance on when a cell partition is intended as design-given versus analyst-chosen?
- Is the no-shift result meant as a pedagogical corollary of the fixed-geometry theorem? If so, presenting it that way would make the logical structure clearer.
