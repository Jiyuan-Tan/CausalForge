# Referee review

**Recommendation:** major_revision
**Overall score:** 6.8/10 — The verified lower-bound and conditional signed-frontier results are real and potentially useful, but the manuscript needs sharper claim calibration, cleaner assumption bookkeeping, and better exposition before publication.

The paper studies minimax expected sup-loss for boundary regression under distance-compressed experiments, proving unconditional logarithmic lower bounds for unsigned distance data and a conditional matched rate for a known-geometry signed-distance estimator. The main mathematical claims appear faithful to the verified statements, with the important qualification that the signed upper side rests on explicit analytic inputs. The contribution is promising, but several prose passages blur lower-bound sharpness, unconditionality, and information-set interpretation in ways that would mislead an econometrics reader.

## Strengths
- The paper isolates a clear statistical experiment: boundary-indexed rules using scalar distance data, with explicit law classes, decision classes, and risks.
- The verified unsigned point-indexed lower bound is a meaningful strengthening of the CTY common-map converse and directly addresses the conjectured logarithmic scale.
- The signed-distance section gives a concrete estimator and states the matched frontier with explicit conditioning on identification, bias, and maximal inputs.
- The comparison table usefully separates target, information set, decision class, and conditioning status.

## Findings
- **[major·prose] abstract** — The sentence "Thus the unsigned contribution is lower-bound sharpness" overstates the delivered unsigned result. The verified unsigned theorems provide logarithmic lower bounds, including the point-indexed strengthening, but no matching unsigned upper bound or two-sided frontier is established.
  - *Fix:* Rewrite as an affirmative lower-bound claim, for example: "Thus the unsigned contribution is the logarithmic strengthening of the CTY lower-bound scale, including the point-indexed distance-rule class."
- **[major·prose] introduction** — The sentence "The common normalization \(a_n\) therefore records a shared logarithmic lower scale, with a conditional upper side for the signed experiment" is mostly accurate, but the surrounding framing may lead readers to infer a unified frontier across both experiments. The unsigned side is lower-bound only, while the signed side is conditional two-sided.
  - *Fix:* Add one precise sentence in the introduction, before the roadmap, stating affirmatively: "For the unsigned experiment, the paper establishes lower bounds at \(a_n\); for the signed known-geometry experiment, the paper combines the lower bound with the stated analytic inputs to obtain a two-sided rate."
- **[major·structure] main results** — The proposition and matched frontier repeat the three analytic inputs in full rather than clearly tying them to \(\mathsf{AI}_{p,\nu,L}\). This makes the trust boundary hard to audit and may obscure that the signed upper bound is conditional on externally motivated analytic inputs.
  - *Fix:* State the proposition and theorem with a compact assumption line such as "Assume \(\mathsf{AI}_{p,\nu,L}\)" and then either refer to \cref{obj:synth_139} or include a short theorem-local formalization-scope note identifying the source-dependent inputs.
- **[major·prose] appendix B** — The appendix prose says the auxiliary results "support the expected outer-risk upper bound" and presents empirical-process ingredients, but the verified upper theorem treats the full expected maximal bounds as hypotheses. As written, the appendix risks suggesting the paper derives the raw-score and Gram maximal inputs self-containedly over the displayed class.
  - *Fix:* Reframe Appendix B as proving only the verified auxiliary statements and as explaining how the assumed maximal and bias inputs are used. Explicitly distinguish the proved winsorized-score maximal bound from the assumed raw-score and Gram maximal bounds in \(\mathsf{AI}_{p,\nu,L}\).
- **[minor·prose] abstract** — The sentence "The support-boundary hypercube constructs separated boundary perturbations with matching scalar-distance information at the queried point" is imprecise. The verified packing has matching unsigned-distance marginals and KL-controlled compressed distance-data laws, not identical full outcome-distance information.
  - *Fix:* Rewrite to: "The support-boundary hypercube constructs separated boundary perturbations whose unsigned-distance marginals match at the queried point and whose compressed outcome-distance laws have logarithmic KL control."
- **[minor·citation] related literature** — The sentence "The first result in the present paper sharpens the support-boundary lower-bound side on the exact full \(\mathcal P_{\mathrm{NP}}(L,q)\) law class: for integer \(q\geq1\) and \(L\geq4\), arbitrary law-independent point-indexed Borel sections already incur..." is accurate but should be integrated into the manuscript itself rather than relying on the related-work brief.
  - *Fix:* Ensure the same precise novelty statement appears in the paper's Related Literature section or introduction, with CTY cited at the point where the conjectured scale and common-map architecture are discussed.
- **[minor·prose] discussion** — The "Open questions" paragraph correctly places non-coverage in an explicitly titled section, but it uses a list of absent deliverables as the main close of the paper. This complies structurally, yet it weakens the reader-facing contribution framing.
  - *Fix:* Keep the open questions but precede them with a positive closing sentence summarizing the delivered scope: unsigned logarithmic lower bounds and a conditional signed known-geometry expected-risk frontier.
- **[minor·statement] global** — Some formal environment titles are too generic or overlapping: both signed and unsigned lower bounds are called variants of "Log Converse," and the signed theorem is titled "Point-Indexed Log Converse" although its distinctive content is fixed-geometry signed-distance treatment-effect risk.
  - *Fix:* Rename titles to make scope visible, for example "Unsigned Point-Indexed Distance Log Converse" and "Signed Known-Geometry Log Converse."
- **[nit·other] global** — The manuscript uses cleveref consistently for internal cross-references in the supplied text. No cross-reference contract violations were apparent.
  - *Fix:* Maintain the current use of \cref and \Cref when revising.

## Questions for authors
- Can you state more explicitly whether any CTY result is being invoked as an external published input in the signed upper-bound theorem, and attach a theorem-local formalization-scope note where that input is used?
- Do you intend "lower-bound sharpness" to mean a strengthened lower-bound scale only, or do you have an unsigned upper theorem elsewhere that is not included in this manuscript?

