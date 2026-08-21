# Referee review

**Recommendation:** major_revision
**Overall score:** 5.6/10 — The verified fixed-separation contour result is technically novel, but the manuscript is too hard to evaluate as an econometrics paper without clearer scope, usable conditions, reproducibility support, and tighter prose fidelity.

The paper develops a contour-instrument method for partially linear models under independent, cumulant-separated treatment innovations and fixed supplied regression codes. The formal layer appears to deliver the advertised fixed-separation \(n^{-1}\) MSE characterization and the stated upper-bound comparison with ACE. As written, however, the econometric contribution is buried under formal and certified-computation machinery, several scope cues invite over-reading, and the practical meaning of the assumptions and constants is not sufficiently explained.

## Strengths
- The central zero-instrument and contour-identification idea is original in this partially linear setting.
- The manuscript is unusually explicit about fixed-code risk, treatment-code stability, and the ACE comparison being an upper-guarantee comparison.
- The verification crosswalk and theorem-local citation boundary for the imported JMS result are valuable for claim auditing.
- The mixture and Gaussian--Rademacher benchmarks help connect the complex contour construction to concrete real-valued instruments.

## Findings
- **[major·statement] main fixed-separation result** — The formal title and repeated wording "Adaptive root-n minimaxity" invite a broader adaptive interpretation than the theorem delivers. The verified result is a fixed-separation, fixed-primitive, fixed-code minimax statement with a law-blind finite contour bank and a direct \(L^1(P_X)\) treatment-code gate; it is not an adaptive local-to-Gaussian selector or adaptive switching theorem.
  - *Fix:* Retitle the theorem and surrounding discussion to something like "Fixed-separation contour minimaxity" or "Law-blind fixed-separation contour minimaxity," and reserve "adaptive" for the internal contour-bank selection if the text explicitly says what it adapts over.
- **[major·statement] setup and assumptions** — The sample-indexing convention is inconsistent: the paper writes \(O_1,\ldots,O_n\) but defines folds as \(I_0=\{i:i<\lfloor n/2\rfloor\}\) and \(I_1=\{i:i\ge\lfloor n/2\rfloor\}\), which is naturally zero-based and can make the first fold ambiguous under one-based indexing.
  - *Fix:* State explicitly that sample indices are \(0,\ldots,n-1\) for all fold definitions, or rewrite the folds in one-based notation and update all empirical-average displays accordingly.
- **[major·structure] main fixed-separation result** — The assumptions and constants that make the main theorem usable are too dispersed. The gate \(\varepsilon_{1,n}\le \{4R_1\exp(2C_gR_1)\}^{-1}\), the certified denominator floor \(a_\star\), the fixed-code convention, and the nonemptiness conditions are central, but the reader gets no consolidated interpretation of their scale or feasibility.
  - *Fix:* Add a theorem-use table immediately before or after \cref{obj:thm:adaptive-rootn-minimax} listing each gate, what object it controls, whether it is statistical or constructional, and how it enters the constants. Include at least one numerical or symbolic worked example for the mixture benchmark showing the size of the treatment-code gate.
- **[major·structure] certified construction and executable correspondence** — The manuscript makes the certified arithmetic layer a contribution, but the executable discharge remains conditional on a compiled bounded spectral adapter. A reader cannot reproduce the statistic as an executable method from the paper alone.
  - *Fix:* Either provide a runnable reference implementation with test instances for the contour bank and estimator, or demote the certified-execution material to a conditional specification and state in the introduction that the paper contributes the Borel statistic and build contract rather than an executed numerical package.
- **[major·structure] global** — The manuscript is not yet structured for a leading econometrics-journal reader. The proof and verification apparatus dominate the statistical narrative, while the estimator, assumptions, comparison class, and implications are not summarized in an accessible decision-theoretic roadmap.
  - *Fix:* Add a compact roadmap after the introduction with: model and code inputs, identification object, estimator construction in 4-5 steps, main risk theorem, ACE comparison, and diagnostic Gaussian result. Move most certified-arithmetic details further into the appendix or a supplement-facing subsection.
- **[minor·citation] related work** — The related-work section omits several canonical references identified by the paper's own context: Engle (1986), Speckman (1988), Hardle--Liang--Gao (2000), Marcinkiewicz (1939), Lukacs (1970), Shimizu et al. (2006), and Andrews (2017). This weakens the positioning of both the PLM lineage and the non-Gaussian identification lineage.
  - *Fix:* Add a short paragraph or integrate these references into the existing PLM, transform-zero, and non-Gaussian-identification paragraphs, explaining how the present fixed-separation contour construction differs from each strand.
- **[minor·prose] related work** — The sentence "Discrete-treatment designs fall outside this class because the residual innovation must satisfy both independence from covariates and cumulant separation" violates the affirmative contribution-framing rule outside the limitations/future-work section.
  - *Fix:* Delete the sentence from related work or move it to the limitations section. In related work, keep the affirmative version already present: the class covers continuous treatments generated by a covariate-free innovation with separated cumulant.
- **[minor·prose] related work** — The sentence "Rather than expanding an orthogonal score to a fixed finite order, it works with zeros of the treatment-innovation moment-generating function..." frames the contribution by negating a comparator instead of directly stating the delivered construction.
  - *Fix:* Rewrite affirmatively, for example: "The contour approach represents cumulant-separated residual variation through zeros of the treatment-innovation moment-generating function and converts those zeros into contour ratios."
- **[minor·prose] comparison with ACE and Gaussian benchmarks** — The ACE comparison is technically careful, but the manuscript should make the decision-theoretic asymmetry more visible: the spectral side has a fixed-code MSE minimax theorem, while the ACE side is imported as a published generalized-quantile upper guarantee plus a separate class minimax lower bound, not a lower bound on the ACE estimator.
  - *Fix:* Add one boxed or italicized sentence before \cref{obj:prop:jms-ace-alignment}: "The comparison below is between displayed upper guarantees on the common class; it is not a dominance theorem for the ACE estimator."
- **[nit·prose] main fixed-separation result** — There are visible placeholder or typo fragments: "Non-Gaussian fixed-code u.", "ACE fixed-code u.", and later "Its mean squared u obeys".
  - *Fix:* Replace these with "Non-Gaussian fixed-code risk", "ACE fixed-code risk", and "Its mean squared error obeys".

## Questions for authors
- Can the authors provide a small numerical example showing the contour-bank constants and the \(L^1(P_X)\) gate for a benchmark distribution?
- Is a runnable implementation of the certified contour statistic available, or is the intended contribution only the formal build contract?
- How should an applied reader obtain or validate the supplied treatment and outcome codes under the fixed-code convention before using the estimator?

