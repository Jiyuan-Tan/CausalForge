# Referee review

**Recommendation:** major_revision
**Overall score:** 5.8/10 — The verified mathematical core is coherent and potentially useful, but the paper is too narrowly delivered relative to its econometric framing and several prose claims and objects around interference, exact rollout risk, and covariance structure need substantial tightening before publication.

The paper reduces a low-budget rollout scheduling problem to minimum-l1 polynomial extrapolation weights and proves a Chebyshev-Lobatto rate-minimax result for a diagonal covariance-envelope criterion. This is a clean translation of classical Chebyshev optimal-recovery ideas into a rollout-design criterion, and the authors are unusually careful in distinguishing the envelope result from exact nested-rollout optimality. As written, however, the econometric contribution is still thin relative to a leading-journal standard because the low-order interference and exact covariance problems are mostly assumed or left symbolic rather than derived from a primitive design.

## Strengths
- The main envelope criterion is clearly stated and the distinction between envelope minimaxity and exact nested-rollout optimality is mostly honest.
- The Chebyshev-Lobatto schedule result is mathematically clean and gives a usable design prescription under the stated criterion.
- The paper repeatedly warns that the polynomial mean restriction and variance envelope are imposed rather than derived, which improves claim fidelity.
- The duality between l1 weights and bounded polynomial extrapolation is a strong organizing device and makes the argument easy to follow.

## Findings
- **[major·prose] global** — The title and some framing oversell the result as an interference result. The title is "Chebyshev Rollout Schedules for Polynomial Extrapolation under Low-Order Interference," but the formal layer proves results under an imposed polynomial mean curve and diagonal variance envelope, not under a primitive low-order interference model.
  - *Fix:* Retitle and reframe around the actual assumptions, e.g. "Chebyshev Rollout Schedules for Polynomial Extrapolation Motivated by Low-Order Interference," and state early that the main theorem is an optimal-design result for the polynomial-envelope problem rather than a theorem derived from low-order interference primitives.
- **[major·structure] setup and discussion** — The exact nested covariance object is not self-contained. The setup says "The specific assignment law... is not further specified here" and that the exact covariance is "not part of the verified formal layer," but Remark oe:q later refers to "the true design covariance matrix of the monotone Bernoulli rollout," which has not been defined.
  - *Fix:* Either define the monotone Bernoulli rollout law, its covariance matrix, and the corresponding law class precisely, or remove references to a "true" monotone Bernoulli covariance and present R_exact only as a symbolic placeholder for future work.
- **[major·prose] contribution and significance** — The delivered contribution is narrower than the econometric motivation suggests. The paper solves the diagonal-envelope linear-unbiased polynomial extrapolation design problem, while exact covariance optimality, primitive interference derivation, finite-population rounding effects, and misspecification risk are outside the formal contribution.
  - *Fix:* Revise the introduction to make the contribution a sharply scoped design theorem for the envelope criterion, or add substantive econometric content: primitive examples deriving the polynomial curve and variance envelope, simulations under exact rollout covariance, or partial results showing when the envelope prescription remains close to exact-risk optimal.
- **[major·structure] setup** — The notation for the law class suppresses important dependence on the schedule, design, and variance scale. Definition P_beta pins E[bar Y_j]=m_P(p_j), so the class changes with p, yet R_exact writes sup_{P in P_beta} while p is being optimized.
  - *Fix:* Introduce notation such as P_beta(p, pi, sigma0) or P_beta(p), and rewrite R_exact and all exact-risk lemmas with that dependence explicit.
- **[major·statement] setup and assumptions** — The round-mean variance envelope is central but only heuristically justified. The text says it holds under "weak" or "bounded-neighborhood" dependence, but no formal sufficient condition or citation is provided, and bounded outcomes alone are correctly noted to be insufficient.
  - *Fix:* Add at least one worked primitive example proving Var_pi(bar Y_j) <= sigma0^2/n, such as independent Bernoulli assignment with bounded dependency neighborhoods, and cite the relevant dependency-graph variance result.
- **[minor·prose] main results** — The equal-spacing comparison can mislead because only an upper bound is available. The table labels an "equal-spacing upper-bound base beta/q" and compares it visually to the Chebyshev base, but this does not establish equal spacing has that rate or is worse.
  - *Fix:* Make the table caption and surrounding paragraph more explicit: the equal-spacing column is only the base of a crude certified upper bound and should not be interpreted as an actual performance rate or lower bound for equal spacing.
- **[minor·prose] main results** — Some prose drops the qualifications "linear unbiased" and "diagonal-envelope." For example, "the statistical problem becomes a polynomial extrapolation problem" and "where should measurement fractions be placed to minimize the worst-case variance" are broader than the formal statements.
  - *Fix:* Wherever the design problem is summarized, add the qualifiers "among linear unbiased estimators" and "under the PSD diagonal variance envelope."
- **[minor·prose] main results** — The static rollout consistency assumption is repeatedly paired with the polynomial identity, but the displayed identity uses only the polynomial mean expansion once the target m_P(1)-m_P(0) is defined.
  - *Fix:* Clarify that static consistency gives the causal interpretation of the round means, while the algebraic endpoint identity follows from the polynomial mean restriction.
- **[minor·citation] positioning** — The approximation-theory and optimal-recovery lineage is under-cited relative to how much work it does. The text invokes "classical optimal-recovery pairing" and Chebyshev endpoint extrapolation but cites mainly broad sources.
  - *Fix:* Add precise citations for the l1/l_infinity optimal-recovery duality, Chebyshev-Lobatto norming/Ehlich-Zeller, and polynomial extrapolation at exterior points.
- **[minor·structure] verification note** — The verification note is useful but blurs what is displayed as a formal result versus what is an external or separately discharged approximation fact. The paper states the oversampled norming lemma conditionally, then says the Ehlich-Zeller inequality is discharged in Lean but not displayed.
  - *Fix:* Provide a short verification table mapping each displayed theorem to the exact Lean declaration and indicate whether Ehlich-Zeller is an imported theorem, a proved auxiliary theorem, or an assumption in that declaration.
- **[nit·prose] setup** — Finite-population rounding is mentioned but left vague: "any gap between a target fraction and the realized fraction is a finite-sample perturbation... outside the formal scope." This is important for actual rollout implementation.
  - *Fix:* Add a short bound or diagnostic recommendation for rounding error, or move the caveat to a limitations paragraph so readers do not mistake the real-valued schedule theorem for an exact finite-n implementation rule.

## Questions for authors
- Do you intend R_exact to refer to a specific monotone Bernoulli rollout law, or is it only a placeholder for any future covariance-restricted problem?
- Can you give primitive sufficient conditions under which both the degree-beta polynomial mean and the sigma0^2/n variance envelope hold simultaneously in a finite population?
- Is there numerical evidence that the Chebyshev schedule remains near-optimal under an actual nested-rollout covariance, not only under the diagonal envelope?

