# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The core minimax contribution is substantial and the verified formal layer supports the main claims, while several prose, positioning, and reproducibility edits are needed before publication.

The paper establishes a design-based minimax MSE frontier for low-order polynomial network interference under known bounded-degree graphs and common Bernoulli assignment, with matching clipped-SNIPE upper bounds, complete-block lower constructions, a bounded-outcome extension, and a sharp block-local linear benchmark. The contribution is meaningful for researchers studying design-based network experiments, especially as a calibration result for known-graph Bernoulli designs. The manuscript is largely faithful to the verified statements, but it needs sharper comparison to the closest SNIPE antecedent, a few scope and prose repairs, and clearer human-facing presentation of the formal verification layer.

## Strengths
- The main theorem delivers a clean and interpretable frontier, \(B^2\min\{1,dA_d/n\}\), with an exposed-binomial calibration that makes the degree dependence transparent.
- The two bounded classes are treated in parallel, and the strict-inclusion statement helps clarify the scope of the comparison.
- The complete-block construction and local linear benchmark give useful sharp constants in an important reference design.
- The abstract and introduction mostly state theorem conditions accurately, including fixed \((\beta,p)\), bounded degree, known graph, and Bernoulli assignment.
- The paper has an early related-work section and positions the result within design-based interference and SNIPE literatures.

## Findings
- **[minor·citation] Related work** — The closest-prior-work paragraph identifies Cortez-Rodriguez, Eichhorn, and Yu as the direct antecedent, but the comparison remains too compressed for a leading-journal reader. The sentence "their SNIPE analysis supplies design-unbiasedness and a stated worst-case variance upper bound of order \(B^2 d\binom d{k}/n\)" should pin down the actual theorem, class, degree convention, interaction order, and assignment-probability assumptions.
  - *Fix:* Add a short theorem-level comparison paragraph or table giving the prior result's bound and conditions, then state affirmatively that the present paper establishes the bounded-class minimax frontier, complete-block lower construction, clipped-SNIPE attainment, bounded-outcome counterpart, and block-local linear benchmark under the paper's fixed-\((\beta,p)\) known-graph Bernoulli conditions.
- **[minor·prose] global** — The author footnote says "results cited from the literature enter as published inputs," while the verification contract for the displayed objects records no external formal dependencies. This is a stale trust-boundary description relative to the current extracted declarations.
  - *Fix:* Rewrite the footnote and verification note to say that the displayed formal statements and proofs are Lean-verified with no external formal dependencies for the displayed objects, while the cited literature supplies econometric framing, terminology, and positioning.
- **[minor·prose] Discussion and extensions** — The sentence "This exact constant is a best-linear-unbiased statement within that class alone: it optimizes over weights satisfying the block-local moment equations against every nonempty raw monomial up to \(\bar\beta_{d_t}\), and makes no claim about estimators outside the block-local unbiased linear class" violates the affirmative contribution framing rule outside the Limitations section.
  - *Fix:* Rewrite affirmatively in place, for example: "This exact constant characterizes the block-local unbiased linear class: it optimizes over weights satisfying the block-local moment equations against every nonempty raw monomial up to \(\bar\beta_{d_t}\)." Move any genuine non-coverage statement to the Limitations and future work subsection.
- **[minor·statement] Setup and assumptions** — The SNIPE score definition sums to \(\bar\beta_d\), while later local-energy statements naturally use \(\min\{\beta,|N_i|\}\). The empty-sum convention makes these equivalent, but the definition can make the unit-level score look as if it depends on unavailable orders.
  - *Fix:* Add one sentence after \(\cref{obj:def:snipe-score}\) explaining that terms with \(r>|N_i|\) are empty, so the effective unit-level sum is over \(1\le r\le\min\{\beta,|N_i|\}\).
- **[minor·statement] Main results** — The local-linear theorem assumption says that "active units form complete directed blocks with self-loops and inactive units are isolated," but the same theorem assumes \(d_t\mid n_t\), so all units are active. This is harmless mathematically but confusing in the human statement.
  - *Fix:* Revise the assumption to say that \(V_{n_t}\) is partitioned into \(m_t=n_t/d_t\) complete directed \(d_t\)-blocks with self-loops; if the block-family wording is reused, add that there are no inactive units under \(d_t\mid n_t\).
- **[minor·statement] Appendix** — The lemma \(\cref{obj:lem:block-energy-representer}\) contains Lean-internal wording: "for any proof witnesses of \(0\le p\) and \(p\le 1\)." This distracts from the mathematical statement.
  - *Fix:* Replace this with ordinary mathematical prose, such as "under the product Bernoulli law with \(p\in(0,1)\), the program values are ..." Keep any implementation-specific witness detail in the verification note rather than in the theorem statement.
- **[minor·other] Verification note** — The manuscript says a Lean 4 development verifies the formal statements, but it gives no reader-facing reproduction pointer such as the commit, Lean version, or command used to check the development.
  - *Fix:* Add the artifact commit, Lean/toolchain version, and a one-line verification command or appendix pointer. If anonymity or submission policy prevents a public link, state how the artifact will be provided to referees and readers.
- **[nit·structure] Introduction** — The final two paragraphs both give a roadmap: "The paper next reviews related work..." followed immediately by "The remainder of the paper is organized as follows." This is repetitive.
  - *Fix:* Consolidate these into one roadmap paragraph that lists the related work, setup, main results, discussion, and appendix once.

## Questions for authors
- Can you add a precise theorem-level comparison with Cortez-Rodriguez, Eichhorn, and Yu, including whether the prior bound is a stated worst-case variance bound and how its class differs from the bounded classes here?
- Will the final version include a public or referee-accessible Lean artifact with the commit and verification command?
- Do you want the fixed-\(p\) limitation to state explicitly that constants may deteriorate as \(p\to0,1\) or as nonzero Bernoulli contrasts approach zero?

