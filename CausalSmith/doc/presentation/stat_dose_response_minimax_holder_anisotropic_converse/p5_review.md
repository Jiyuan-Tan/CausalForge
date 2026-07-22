# Referee review

**Recommendation:** reject
**Overall score:** 4/10 — The verified result is a correct but narrow one-sided lower bound, while the paper’s terminology and positioning still invite a stronger minimax/frontier interpretation than the results deliver.

The paper proves a same-class lower bound of order n^{-2alpha/(2alpha+1)} for an interior continuous-treatment partial mean and compares this algebraically with a published HOIF benchmark. The verified statements are mostly represented cautiously in the abstract and main discussion, but the contribution is substantially narrower than what a leading econometrics journal would normally require: there is no same-class upper bound, no full minimax characterization, and no resolution of the low-covariate-smoothness regime. I would not recommend publication in its current form.

## Strengths
- The manuscript clearly separates the verified same-class lower bound from the external HOIF comparator in several places.
- The target, risk, model class, and benchmark sequence are explicitly defined.
- The paper is unusually careful about verification scope and about not claiming a same-class upper bound.

## Findings
- **[major·structure] global** — The paper’s actual contribution is too narrow for the claimed econometric payoff. The verified mathematical content is a two-point lower bound obtained by perturbing the treatment regression plus algebraic comparisons of exponents; it does not establish the minimax rate, does not prove a same-class upper bound, and leaves the main low-smoothness upper frontier open.
  - *Fix:* Either add a same-class upper bound or a sharper lower bound that resolves the rate in at least one substantively new regime, or reposition the paper as a short technical note whose contribution is a limited converse benchmark rather than a leading-journal minimax result.
- **[major·structure] global** — The contribution is overstated by repeated use of sharp/minimax/frontier terminology. Examples include the theorem title "Sharp Pointwise Lower Bound", the theorem title "Smooth Covariate Minimax Floor", and the remarks titled "Beta frontier handle" and "Full beta frontier". The formal layer proves only a one-sided lower bound plus algebraic comparisons; it does not prove sharpness, a minimax rate, or a frontier.
  - *Fix:* Retitle these objects using neutral language such as "Pointwise Lower Bound", "Smooth-Covariate Lower-Bound Comparison", and "Open Beta-Dependence Question". Reserve "sharp", "minimax", and "frontier" for claims with matching lower and upper results.
- **[major·citation] main results** — The imported comparator in "Published HOIF Comparator" remains too strong as written for a self-contained econometrics paper. It introduces a bespoke Bonvini-Kennedy localized-regularity class, asserts subset relations, and summarizes their conditions in ways a reader cannot verify from the present definitions alone.
  - *Fix:* State the comparator more modestly as an external published rate under additional assumptions, give an exact citation to the theorem and assumptions being imported, and avoid asserting strict class inclusion unless the present paper proves or documents the mapping condition by condition.
- **[major·structure] setup and observed-data class** — The model class definition includes causal assumptions and iid sampling as properties of laws P, which blurs the statistical object. A single-observation observed-data law does not itself satisfy iid sampling, and potential-outcome assumptions are not properties of the observed-data law alone without specifying an augmented law.
  - *Fix:* Separate the observed-data law class from the sampling scheme and from the causal overlay. Define the statistical class for P, then state iid sampling for P^n, and separately state the augmented potential-outcome conditions used only for interpretation.
- **[major·structure] appendix / auxiliary lemmas and proofs** — The proof prose contains claims not present as independently stated assumptions or visible lemmas in the manuscript, for example the existence of a "bump Holder gate", membership of constructed witnesses in the class, and KL tensorization details. Even if covered by the verification contract, the submitted paper presents these as ordinary mathematical proofs without enough self-contained detail.
  - *Fix:* Promote the hidden construction steps to explicit lemmas with assumptions and conclusions, or shorten the appendix proof to say these steps are formalized auxiliary inputs and list their exact statements.
- **[minor·prose] introduction** — The sentence "This separation is useful because the lower bound varies with alpha, beta, s, and d through distinct approximation and testing constraints" misdescribes the verified lower bound. The exponent varies only with alpha; beta, s, and d enter assumptions, feasibility, constants, and the comparison with rho_n.
  - *Fix:* Rewrite the sentence to say that the lower-bound exponent depends on alpha, while beta, s, and d affect feasibility, constants, and benchmark comparisons.
- **[minor·statement] main results** — The proposition "Oracle Regime Reduction" states "there exists c>0 such that, for all sufficiently large n, rho_n = ..." although the equality holds for every n >= 1 under the algebra lemma. Combining an eventual lower bound with an all-n algebra identity is harmless, but the statement obscures which part is eventual and which part is exact.
  - *Fix:* Split the proposition into two clauses: first state the exact algebraic identity for all n >= 1, then state the eventual minimax lower bound involving c rho_n.
- **[minor·statement] main results** — The strict-slack baseline condition may be nontrivial or empty for some constants M, c0, epsilon0, beta, and s, but the text gives little guidance on feasibility.
  - *Fix:* Add a short lemma or example giving sufficient primitive conditions under which Assumption baseline-submodel-slack is nonempty, and state clearly how constants such as M and c0 must relate.
- **[minor·prose] verification note** — The note says the "theorem statements and their derivations are machine-checked" but later says Le Cam is used at the level of an auxiliary lemma rather than derived from measure-theoretic foundations. This is acceptable but easy to misread.
  - *Fix:* Clarify in one sentence that the verification checks the consequences of the stated Le Cam lemma, while the general decision-theoretic lemma is imported as a mathematical input.
- **[minor·structure] clarity and presentation** — The manuscript contains many Lean-oriented labels and comments in the main mathematical exposition, which reduces readability for an econometrics audience.
  - *Fix:* Move Lean labels and audit-oriented comments to a separate reproducibility appendix or footnotes, and keep the main text in standard econometrics notation.
- **[nit·prose] global** — The manuscript alternates between "Holder" and "Hölder".
  - *Fix:* Use "Hölder" consistently in prose and reserve ASCII only for code identifiers.
- **[nit·prose] abstract / introduction** — The phrase "same-class" appears very frequently and becomes distracting.
  - *Fix:* Define the term once and then use plainer alternatives such as "over this class" or "under Definition 2" where unambiguous.

## Questions for authors
- Can you provide a same-class upper bound, even under an additional transparent primitive condition, that would make the smooth-covariate case a genuine minimax result?
- What primitive restrictions on M, c0, epsilon0, beta, and s guarantee that the strict-slack baseline condition is nonempty?
- Is the Bonvini-Kennedy localized-regularity class truly a subset of your Holder dose class under the exact definitions used here, or only a related comparator under different notation and assumptions?

