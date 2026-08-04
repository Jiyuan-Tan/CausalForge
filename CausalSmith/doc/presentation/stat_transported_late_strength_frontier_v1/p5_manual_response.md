# P5 manual response

Date: 2026-08-02

The orchestrator manually addressed every actionable item and both questions from the post-cap referee report before rerunning P4--P5.

1. **Score-radius normalization.** The frozen inversion-handle definition now
   defines \(\widehat\kappa_n=n^{-1}\sum_i w(X_i)^2\) explicitly and displays
   the radius directly as \(L_\alpha\sqrt{\widehat\kappa_n/n}\). This is an
   algebraically equivalent clarification of the accepted definition, not a
   claim change. The frozen JSON body, its hash, the derived formal layer, the
   cached section, and the assembled paper were synchronized.
2. **Recent-literature positioning.** The related-work paragraph now separates
   transported noncompliance, weak-instrument two-sample IV, transported ATE,
   finite-population LATE, and weak-IV MTE contributions, and states precisely
   what the finite-cell frontier results add.
3. **Title style.** The seven formal result titles identified by the referee
   were converted to sentence case in the frozen layer, cached sections, and
   assembled paper.
4. **Finite-cell implementation recipe.** The finite-cell section now records
   the required source and target inputs and the concrete tabulation,
   contrast-estimation, collision-statistic, and score-inversion steps. It also
   distinguishes the known inputs in the regular-cell construction and states
   the boundary of the attainability claim.
5. **2025--2026 citation status.** The related-work discussion identifies the
   Rudolph et al., Aronow et al., and Ross et al. entries as journal articles,
   and the Chen--Huang, Zeng et al., and Ren entries as arXiv working papers,
   matching the normalized bibliography.

In addition, the abstract and oracle-frontier discussion now state the
sampling-ratio, overlap, and noncoverage dependence of constants and clarify
that the lower-bound witness is the unit-transport-weight slice, while the
attainment statements use the common strength--dispersion scale \(t_n\).

Validation before the rerun found 44 formal blocks, no stale body hashes, and
no frozen-environment mismatch in the assembled paper.

## Second terminal report

The fresh referee report retained a minor-revision disposition and raised five
new exposition items. Each was addressed before the next P4--P5 rerun:

1. The related-work comparison now identifies Chen--Huang as the closest
   transported-CACE comparison and Ma and Smucler--Lanni--Masip as the closest
   weak-identification-robust LATE comparisons, with explicit estimands,
   sample structures, transport restrictions, weak-stage treatment, and
   inference targets.
2. A preliminary fixed-geometry notation paragraph now defines
   \(\mathfrak g\), \(\mathcal P_n(\mathfrak g)\), and
   \(V_{\mathfrak g}^\star(t_0)\) before the no-shift theorem while retaining
   the detailed definitions in the following section.
3. The abstract now explains that the unit-weight least-favorable slice is
   embedded in the transported class, which is why its converse applies to the
   larger model.
4. The receipt-transport discussion now explains its aggregate, rather than
   cellwise, content and gives concrete design and validation evidence that
   could support the restriction in an encouragement application.
5. The verification note now states explicitly that the prose proofs are
   expository renderings and that adjacent Lean declaration comments identify
   the corresponding checked objects.

## Third terminal report and frozen-order adjudication

The next referee report scored the paper 8.0/10 with four remaining
organizational or expository items. Its automatic reviser attempted to move a
frozen theorem and was rejected by the frozen-order guard. The subsequent P2
reassembly placed the no-shift theorem after the four fixed-geometry
definitions while preserving each frozen environment exactly once, and the
remaining items were handled manually:

1. The receipt-transport paragraph now gives a concrete source-clinic and
   target-rollout design and names the source first-stage curve, target
   covariate law, and external target receipt contrast that diagnose the
   integrated equality.
2. The appendix opens with the requested explicit distinction between checked
   Lean declarations and expository proof narratives.
3. The closest-literature comparison is split into separate transported-
   noncompliance and weak-instrument paragraphs.
4. The P2 proof audit's sole finding was corrected: regular-cell attainment
   uses bounded overlap for the row's own propensity, while propensity \(1/2\)
   enters through the later uniform finite-cell bridge.

## Fourth terminal report

The capped terminal referee again recommended minor revision at 8.0/10 and
listed five presentation items. All five were incorporated without changing a
frozen theorem body:

1. The receipt-transport discussion now explicitly separates the target
   covariate sample used by the procedures from external target receipt
   evidence used to support the design/model restriction.
2. The finite-cell theorem is titled “Finite-cell sample-only score-inversion
   attainment,” and its lead-in states that procedural contribution directly.
3. The closest literature is presented under separate “Transported
   noncompliance” and “Weak-IV and two-sample IV inference” labels, each ending
   with the affirmative scope added here.
4. A compact equation before the finite-cell class says that it is the
   transported class plus the finite-cell source condition; the inherited
   checklist remains in the frozen display for auditability.
5. The oracle-attainment discussion now explains that admissible geometry
   supplies the ambient deterministic comparison inputs, while each law's
   oracle weight and propensity evaluate the score.

## Fifth terminal report

The next 8.0/10 minor-revision report raised five further presentation points:

1. The sentence immediately before oracle attainment now names the geometry
   bullet as an ambient-carrier existence/nonemptiness condition and states
   explicitly that the selected geometry is not a score-rule input.
2. The receipt-transport interpretation and validation example were compressed
   from three paragraphs to one short paragraph.
3. Reader-facing spelling is standardized to “least-favorable”; the two
   synthetic formal-layer occurrences were repinned after this orthographic,
   claim-neutral change.
4. Implementation-flavored initial-row language in the fixed-geometry proof
   was replaced with ordinary asymptotic prose explaining that the single
   initial row is immaterial.
5. The request to remove the inherited checklist from the finite-cell formal
   definition was manually adjudicated against the frozen-layer contract. The
   accepted statement retains that checklist for Lean traceability, while the
   compact equation immediately before it makes the sole added finite-cell
   restriction explicit. Altering the frozen mathematical display solely for
   layout would weaken the accepted statement-to-Lean audit trail.

## Final capacity-limited report and adjudication

Two final capped P4--P5 attempts reached the external referee service but
failed with the same explicit model-capacity error. The last report emitted
before that capacity boundary was manually adjudicated as follows:

1. The closest recent papers now each receive an object/design/inference/status
   comparison: Chen--Huang, Rudolph--van der Laan, Ross et al., Ma,
   Smucler--Lanni--Masip, and the Choi two-sample IV papers.
2. The oracle theorem's claim-neutral bullet label is now “Nonempty admissible
   carrier,” with its body hash repinned and every frozen copy synchronized.
3. The P5-generated asymptotic proof prose already replaces the cited
   implementation phrases with statements that finite initial rows are
   immaterial for limiting coverage and risk.
4. The receipt-transport explanation is now a two-sentence denominator
   interpretation; target-sample implementation details were removed from that
   setup paragraph.
5. The verification note states that presentation-synthesized definitions are
   notation-management devices outside the top-level Lean theorem checklist
   unless the verification contract separately names a checked declaration.
6. The repeated-checklist request remains adjudicated as a frozen-statement
   traceability constraint, with the one-line submodel definition immediately
   preceding the formal checklist.

The final bundle is therefore based on the last completed referee report plus
explicit manual disposition of every finding; no prompt, model, or seed was
changed to work around the external capacity failure.

## Capacity-retry reports and frozen-order recovery

The capacity retry completed with the same configured referee, model, prompt,
and seed. It emitted a 7.0/10 report, performed one automatic prose revision,
and then emitted a 7.1/10 report. A second automatic revision attempted to
reorder anchored formal environments and was rejected by the frozen-order
guard. The useful proof-prose cleanup from the first pass was retained, while
the authored section and outline order was restored exactly before re-emission.

Every item in the 7.1/10 report has the following concrete disposition:

1. The appendix is proof-centered and contains no quoted “acquire checked
   status,” proof-audit, implementation, empty-row, or row-zero language. Its
   short verification material is now a separate `Verification scope`
   subsection after the mathematical arguments.
2. The geometry handle remains a definition because the frozen contract maps
   it to the proposition-valued Lean handle that packages construction and the
   verified separation bounds. Surrounding prose now names its mathematical
   role directly as the least-favorable separation bound/certificate.
3. The finite-cell checklist remains byte-faithful to the frozen statement.
   The immediately preceding display states the reader-facing relationship
   \(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies the finite-cell source
   condition}\}\), so the repeated list is explicitly identified as the
   anchored expansion rather than an additional model restriction.
4. The oracle-attainment discussion states that carrier existence supplies
   only a nonempty comparison domain and that the score is evaluated law by
   law with the evaluated law's canonical weight and propensity.
5. Frozen environment order requires the no-shift specialization to appear
   before the general fixed-geometry theorem. The main text now flags it as an
   orienting specialization whose frontier conclusion follows from the next
   theorem, and the appendix proves the general theorem first.
6. The closest references are bibliographically explicit in both text and
   bibliography: the Chen--Huang, Ma, and Smucler--Lanni--Masip arXiv numbers
   are printed in the comparison prose, and Ross et al.'s journal, volume,
   issue, and pages are printed there; the BibTeX entries also carry titles,
   dates, DOI/arXiv identifiers, and URLs.
7. The transport-assumption introduction now separates conventional support
   and conditional outcome-contrast transport from the paper-specific
   target-average receipt restriction.
8. `\leanref` is a source-level traceability wrapper whose PDF definition is
   `\newcommand{\leanref}[2]{#2}`; readers see only conventional notation, not
   Lean identifiers. Removing it would not change reader-facing typography and
   would discard the interactive-artifact join key.

## Terminal confirmation under the cumulative revision cap

The terminal confirmation completed with recommendation `major_revision`,
score 7.0/10, and seven findings (two labeled major). No further manuscript
revision is permitted because the cumulative P5 revision cap is exhausted.
The report contains no genuinely new actionable defect:

1. Retyping or splitting the geometry handle would change the frozen formal
   layer; its separation-bound role is already stated immediately before and
   after the anchored environment.
2. Removing or relocating the finite-cell checklist would change either the
   frozen body or frozen environment order; the one-line nesting relation
   immediately before it already supplies the requested reader-facing form.
3. The carrier bullet is frozen and already followed by the requested sentence
   that the comparison domain is nonempty while the score uses each evaluated
   law's canonical weight and propensity.
4. The cited recent comparators have full titles, dates, DOI/arXiv identifiers,
   URLs, publication status, inferential targets, and positive-scope contrasts
   in the bibliography and related-work prose.
5. The setup introduction already distinguishes conventional support and
   conditional outcome transport from the paper-specific target-average
   receipt restriction, and the receipt paragraph states its denominator role.
6. The automatic proof-prose pass removed the quoted implementation vocabulary
   and foregrounds identification, Le Cam separation, score inversion, and
   finite-cell weight learning. The remaining finite-initial-row and limsup
   steps are mathematical content needed for the stated uniform asymptotics.
7. The cleveref item is a stylistic preference rather than a correctness or
   traceability defect; the manuscript uses no forbidden manual `\ref`-style
   references.

The questions are also already answered in the manuscript: the finite-cell
section gives an implementation recipe for empirical target frequencies,
cellwise source contrasts, and the collision statistic, while the displayed
constants are presented as uniform proof constants for rate attainment rather
than calibrated practical critical values.
