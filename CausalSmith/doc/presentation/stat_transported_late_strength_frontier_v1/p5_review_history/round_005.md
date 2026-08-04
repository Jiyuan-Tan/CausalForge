# Referee review

**Recommendation:** minor_revision
**Overall score:** 8.1/10 — The paper delivers a coherent and formally verified minimax frontier for transported complier-ratio inference, with remaining revisions centered on exposition, object ordering, and sharper positioning rather than theorem validity.

The submission characterizes honest expected-length frontiers for transported complier effects under weak transported first stages and controlled transport-weight dispersion. The verified statements support the main rate claims, including oracle and finite-cell attainability. The contribution is significant for weak-IV robust transport inference, but the manuscript needs modest revision to make the closest-literature distinctions and the fixed-geometry notation easier for econometric readers to evaluate.

## Strengths
- The main effective-strength index \(n\mu_n^2/\kappa_n\) is a useful and interpretable synthesis of weak compliance and transport dispersion.
- The verified theorem layer closely supports the abstract and introduction claims about identification, compact range, oracle lower and upper bounds, and feasible finite-cell attainability.
- The Anderson--Rubin style construction is well matched to the ratio problem and gives a concrete procedure rather than only a converse.
- The paper states assumptions carefully and now gives useful substantive explanations for transport, envelope, dispersion, and cell-growth conditions.

## Findings
- **[minor·citation] Related Literature and Discussion** — The closest recent papers are still positioned mostly by topic rather than by the exact object of comparison. For example, the sentence "The closest transported-noncompliance papers study encouragement effects transported across sites, two-sample transported CACE, and trial participation that changes adherence" leaves the reader without a clear mapping from each cited paper to its estimand, sampling design, weak-identification regime, and inference guarantee.
  - *Fix:* Replace the broad list with a compact comparison paragraph or table that names each closest paper and states: estimand, source/target data structure, treatment of weak first stages, transport restriction, and inference target. Keep the final contrast affirmative by stating that this paper characterizes the honest expected-length frontier for the compact transported complier ratio under the stated \(n\mu_n^2/\kappa_n\) regime.
- **[minor·structure] Oracle Frontier and Score Inversion** — The theorem "Single-population frontier reduction" is stated before the manuscript defines the fixed-geometry class, fixed-geometry slice, and fixed-geometry value it relies on. Forward references are formally valid, but the current order makes a reader process \(\mathfrak g\), \(\mathcal P_n(\mathfrak g)\), and \(V_{\mathfrak g}^\star(t_0)\) before their econometric meaning is introduced.
  - *Fix:* Move the no-shift reduction theorem after the fixed-geometry definitions, or add a short preliminary definition block before the theorem and leave the detailed fixed-geometry discussion in the next section.
- **[minor·prose] abstract** — The sentence "The lower bound is witnessed by a unit-transport-weight submodel" is accurate but compressed: it gives the construction without explaining why a no-shift submodel establishes a transported converse.
  - *Fix:* Revise the sentence to state that the unit-weight least-favorable slice is embedded in the transported class, so its weak-ratio lower bound applies to the larger transported model.
- **[minor·prose] Setup, Transport, and Honest Risk** — The assumption interpretation has improved, but target-average receipt transport remains a high-stakes modeling condition whose empirical meaning is still somewhat abstract. The text states that it "aligns the denominator needed for the target complier share" but gives limited guidance on when this integrated condition is substantively plausible.
  - *Fix:* Add two or three sentences after \cref{obj:ass:receipt-transport} explaining that the condition equates the target-average complier share across populations while allowing covariate-specific receipt contrasts to differ, and give an applied example of what information or design feature would support that restriction.
- **[nit·prose] appendix** — The verification note says the Lean-checked layer covers formal statements and proof obligations, while the appendix also contains long proof narratives with inline Lean comments. The trust boundary is broadly clear, but the reader would benefit from a more explicit statement that the displayed prose proofs are expository companions to the checked declarations named in the comments.
  - *Fix:* In the verification note, add one sentence stating that the prose proof paragraphs are expository renderings of the checked declarations and that the cited Lean declaration comments identify the corresponding formal objects.

## Questions for authors
- Can the final related-work discussion identify the single closest transported-CACE paper and the single closest weak-IV robust LATE paper, then state precisely how the present minimax expected-length frontier differs from each?
- Is the intended reader expected to understand fixed-geometry notation before Section 3, or would moving the no-shift reduction after the fixed-geometry definitions preserve the narrative better?

