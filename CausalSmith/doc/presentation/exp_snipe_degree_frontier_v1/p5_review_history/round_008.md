# Referee review

**Recommendation:** major_revision
**Overall score:** 7/10 — The verified mathematical contribution is substantial, but the manuscript as written needs substantial revision in positioning, readability, and reproducibility before it would meet the standard of a leading econometrics journal.

The paper establishes a finite-population design-based minimax MSE frontier for low-order polynomial network interference under common Bernoulli assignment, with matching clipped-SNIPE upper bounds, complete-block lower constructions, bounded-outcome extensions, and an exact local-linear block benchmark. The formal results appear strong and, under the supplied verification contract, deliver the central minimax claims. The main weaknesses are presentation and positioning: the manuscript is too theorem-dense for its stated audience, the comparison to Cortez-Rodriguez, Eichhorn, and Yu is internally inconsistent, and the Lean-backed verification needs clearer artifact-level reproducibility information.

## Strengths
- The main minimax rate is clean, interpretable, and delivered under explicit finite-population conditions.
- The paper gives both coefficient-mass and uniformly bounded-outcome frontiers, which broadens the relevance of the result.
- The complete-block construction and exact local-linear benchmark add useful sharp calibration beyond a rate-only theorem.
- The prose generally keeps theorem conditions visible and does not materially oversell the verified minimax statements.

## Findings
- **[major·citation] Related work** — The closest-competitor comparison is internally inconsistent. One paragraph says Cortez-Rodriguez, Eichhorn, and Yu provide a bound of order “\(B^2 d\binom d{k}/n\),” while the next says the present result replaces “the \(d^{\beta}\) factor carried by their stated bound.” These cannot both be the operative comparison, and the symbol \(k\) is not tied to their notation.
  - *Fix:* State the exact result from Cortez-Rodriguez, Eichhorn, and Yu once, in their notation or with a clearly defined translation, and then explain precisely what the present restricted-class theorem sharpens: the stated worst-case bound read on the known-graph bounded class, not SNIPE's actual variance on their unrestricted class.
- **[major·structure] Main results** — The main-results section mixes headline minimax theorems with auxiliary overlap identities, lower-bound construction details, exact estimator-risk equalities, and the local-linear benchmark. As written, the reader has to parse several very long theorem statements before the conceptual contribution is clear.
  - *Fix:* Split the section into a short theorem for the two-class minimax frontier, a corollary for the exposed-binomial and fair-coin specializations, and separate propositions for complete-block exact risk and the local-linear benchmark. Move construction-level identities such as the Hellinger display and overlap-count statement to the appendix, with concise references in the main text.
- **[major·other] Verification note** — The paper relies heavily on Lean verification but gives no artifact location, build instructions, or commit in the manuscript, even though the verification contract identifies a specific commit. A reader cannot reproduce the verification from the paper alone.
  - *Fix:* Add an artifact-availability paragraph giving the repository/archive, commit hash, Lean version, build command, and a short map from theorem labels in the paper to Lean files/declarations.
- **[minor·prose] abstract** — The abstract says “where \(A_d\), the complete-block score energy, is the design second moment of the complete-block score used by the score-weighted neighborhood inverse-probability estimator (SNIPE, the shifted-neighbourhood inverse-probability estimator introduced by \citet{CortezRodriguezEichhornYu2023}).” This packs a definition, acronym expansion, attribution, and estimator description into one sentence and obscures the central result.
  - *Fix:* Break this into two sentences: define \(A_d\) as the complete-block score energy, then separately state that the attaining estimator is the clipped SNIPE estimator of Cortez-Rodriguez, Eichhorn, and Yu.
- **[minor·citation] Related work** — The dedicated related-work section omits several foundational references listed in the authors' own background brief, including Fisher, Cox, Rosenbaum, and Toulis and Kao. This weakens the historical and econometric positioning even though the nearest SNIPE comparison is present.
  - *Fix:* Add a compact opening paragraph or sentence cluster covering Fisher randomization, Cox's interference discussion, Rosenbaum's randomization tests under interference, and peer-influence estimands such as Toulis and Kao, while keeping the focus on the closest SNIPE and sparse-interference literature.
- **[minor·prose] global** — The manuscript repeatedly uses the phrase “known-graph Bernoulli benchmark” but gives little concrete guidance on how a practitioner should translate \(A_d\), \(k_\star\), and the overlap factor into design choices beyond the fair-coin first-order example.
  - *Fix:* Add one short worked example or design-calibration paragraph, preferably in the introduction or discussion, showing how the rate changes for two values of \(\beta\) and \(p\), including a case with an even-order fair-coin cancellation.
- **[minor·prose] author footnote** — The author footnote says “where a result from the literature is a formal dependency, it enters as a published input,” while the current verification contract records no external formal dependencies for the displayed objects. This is stale trust-boundary prose relative to the extracted declarations.
  - *Fix:* Revise the footnote to state the current scope affirmatively: the displayed formal statements and proofs are Lean-verified for the finite-design algebra, and the cited literature supplies framing, terminology, and positioning.
- **[nit·prose] Setup and assumptions** — The notation alternates between \(P_Z\), \(D\), \(D_t\), and \(\mathbb E_Z\) for the assignment law. The formal statements are consistent, but the prose could make the convention easier to follow.
  - *Fix:* Add one sentence before the main theorems explaining that \(D\) denotes the same product Bernoulli design as \(P_Z\) when theorem statements use a generic finite-design symbol.

## Questions for authors
- Can you state precisely which theorem of Cortez-Rodriguez, Eichhorn, and Yu is being sharpened, with its original rate and assumptions?
- Will the Lean artifact be archived with a stable DOI or repository commit so that readers can reproduce the verification?
- Do you intend the paper to target theorists already familiar with SNIPE, or a broader econometrics audience? The current exposition reads closer to a formal verification report than a journal article.

