# Referee review

**Recommendation:** major_revision
**Overall score:** 7/10 — The verified minimax frontier is a meaningful contribution, but the manuscript needs substantial tightening in positioning, scope language, and exposition before it reads like a publishable econometrics paper.

The paper establishes a finite-population design-based minimax MSE frontier for bounded low-order polynomial network interference under common Bernoulli assignment, with matching clipped-SNIPE upper bounds, complete-block lower constructions, and an exact block-local linear benchmark. The formal results appear strong and are faithfully stated in the main theorem environments. The manuscript’s main weaknesses are expository: it is overly formal, sometimes blurs verified results with interpretive claims, and has several stale or overbroad prose claims about verification scope and relation to prior SNIPE work.

## Strengths
- The main frontier is clean, nonasymptotic in n and d, and gives a clear rate in terms of local score energy and overlap.
- The paper treats both coefficient-mass and uniformly bounded-outcome envelopes and identifies that they share the same minimax scale.
- The complete-block construction and the exact local linear benchmark add useful calibration beyond a rate statement.
- The fair-coin specialization gives an accessible benchmark for first-order interference.

## Findings
- **[major·prose] abstract** — The opening claim is too compressed and may overstate generality for readers: "This paper establishes a finite-population design-based minimax mean squared error frontier ... under known bounded-degree low-order polynomial interference and common-probability Bernoulli assignment." The verified frontier is for fixed beta and fixed p, with constants depending on (beta,p), and the honest-scope charter notes that constants can deteriorate as p approaches 0, 1, or a contrast zero.
  - *Fix:* Revise the abstract's first sentence to include the fixed-order and fixed-propensity scope explicitly, e.g. "For fixed interaction order beta and fixed p in (0,1), this paper establishes... up to constants depending on (beta,p)."
- **[major·prose] title page** — The author footnote is stale relative to the verification contract: "results cited from the literature enter as published inputs." The current verification contract records no external formal dependencies for the displayed objects, while the verification note says the cited literature supplies framing and terminology.
  - *Fix:* Update the footnote to say that the displayed formal statements and proofs are Lean-verified and that cited literature is used for econometric framing and positioning, not as theorem-local formal dependencies for the displayed results.
- **[major·citation] related work** — The comparison to Cortez-Rodriguez, Eichhorn, and Yu is cautious but still underdeveloped for the closest competitor. The manuscript states that their work gives a "stated worst-case variance upper bound" and that the present paper gives a bounded-class calibration, but it does not spell out the exact model differences, class restrictions, and whether the displayed d choose k scale sharpens only the stated bound rather than the actual variance behavior in that paper.
  - *Fix:* Add a focused paragraph comparing assumptions, target, estimator, class size, and bound form against Cortez-Rodriguez et al.; explicitly state that the paper sharpens their stated worst-case variance bound in the bounded known-graph class and does not claim an improvement over their unrestricted-class theorem.
- **[major·prose] discussion** — The sentence "The global upper bound therefore has the same degree dependence as the sharp complete-block calculation" risks suggesting that the complete-block calculation proves the all-measurable global minimax leading constant. The verified result gives exact unprojected SNIPE worst-case risk on complete blocks and globally for that estimator, while the exact leading constant over all measurable estimators remains outside scope.
  - *Fix:* Rewrite to distinguish rate calibration from global minimax constants, e.g. "The complete-block calculation matches the global upper bound's degree dependence and gives the exact unprojected-SNIPE worst-case risk on the block graph."
- **[minor·prose] setup and assumptions** — The SNIPE score definition uses \(\bar\beta_d\) even when a unit has \(|N_i|<d\). The inner subset sum is then empty for orders exceeding \(|N_i|\), so the formula is correct, but readers may wonder why the upper limit is global rather than local.
  - *Fix:* Add a short sentence after \cref{obj:def:snipe-score} noting that orders above \(|N_i|\) contribute zero through the empty subset sum, equivalently one may sum to \(\min\{\beta,|N_i|\}\).
- **[minor·structure] main results** — The main-results section is dominated by long formal theorem statements before the reader sees a compact explanation of which parts are minimax, estimator-risk, fixed-graph, and local-linear benchmark claims.
  - *Fix:* Before the first theorem, add a short roadmap with four bullets: coefficient-mass minimax frontier, bounded-outcome extension, exact complete-block unprojected-SNIPE risk, and local-linear benchmark. Keep the existing table but make it more interpretive.
- **[minor·prose] verification note** — The verification note says "The checked statements include the finite-design SNIPE unbiasedness and variance identities"; the theorems state worst-case MSE bounds and exact risk identities in specific settings, not a general free-standing variance identity for arbitrary network models.
  - *Fix:* Replace this with a more precise description, such as "the checked statements include the SNIPE unbiasedness claims and the displayed worst-case MSE/risk bounds and exact complete-block risk identities."
- **[minor·prose] discussion** — The sentence "At the saturation scale, the frontier identifies \(B^2\) as the constant-order minimax scale" is correct as rate language, but it should keep the fixed-(beta,p) constant qualification nearby.
  - *Fix:* Revise to "At the saturation scale, for fixed \((\beta,p)\), the frontier identifies \(B^2\) as the constant-order minimax scale."
- **[minor·prose] abstract** — The abstract introduces \(A_d\) and \(k_\star(d,\beta,p)\) before formal definitions and does give appositives, but the first use of SNIPE is not glossed.
  - *Fix:* At first abstract use, expand or briefly gloss SNIPE, e.g. "a score-weighted neighborhood inverse-probability estimator (SNIPE)" if that is the intended expansion.
- **[nit·structure] global** — The manuscript uses both "fair-coin" and "fair-coin design" consistently, but the title and several headings are more technical than reader-facing; this may reduce accessibility for econometrics readers outside the formal verification audience.
  - *Fix:* Consider simplifying some headings and adding one short intuitive paragraph near the end of the introduction explaining the rate in words before the formal setup.

## Questions for authors
- Can you state explicitly in the related-work section whether Cortez-Rodriguez et al.'s unrestricted class contains schedules outside both bounded classes studied here?
- Do you intend the verification footnote to claim theorem-local external dependencies, or should it align with the current contract's no-external-formal-dependencies scope?
- Would an empirical or numerical illustration of A_d across p and beta be possible, even if not necessary for the theorem?

