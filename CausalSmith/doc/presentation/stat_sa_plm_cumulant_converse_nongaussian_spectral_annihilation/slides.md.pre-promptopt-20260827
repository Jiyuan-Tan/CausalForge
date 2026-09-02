# Contour Instruments for Learned Treatment Residuals

TL;DR: Under fixed cumulant separation and stable supplied treatment codes, transform zeros give contour instruments that identify \(\theta_0\) and attain fixed-code minimax mean-squared error at most \(C/n\).

---

## The Punchline

- The paper estimates the partially linear coefficient \(\theta_0\), the treatment coefficient, after residualizing treatment with a supplied code \(\bar g_n\).
- Non-Gaussian treatment noise supplies a complex zero of its moment-generating function.
- That zero becomes an instrument that survives real shifts from treatment-code error.
- A finite contour bank finds a stable zero region from data and averages an observable transform ratio.
- The resulting fixed-code statistic has minimax mean-squared error bounded between \(c/n\) and \(C/n\).
- Two names recur: ACE is the published order-\(r\) higher-order orthogonal estimator of Jin, Mackey, and Syrgkanis (JMS), used here as the comparison benchmark, and a class is *fixed-code* when all of its laws share the same supplied codes \(\bar g_n,\bar q_n\).

@informal thm:adaptive-rootn-minimax: Under fixed primitive constants, a stable \(L^1(P_X)\) treatment-code gate, and nonempty fixed-code classes, the contour statistic has non-Gaussian and ACE fixed-code mean-squared risk at most \(C/n\), with matching lower bound at least \(c/n\).

---

## Why This Question Matters

- Partially linear models estimate a low-dimensional treatment effect while allowing flexible covariate adjustment.
- In practice, \(g_0\), the treatment regression, is often replaced by a learned or supplied code \(\bar g_n\).
- Standard residualization leaves bias terms when the treatment code is imperfect.
- The paper asks how much extra information is available when the treatment residual is non-Gaussian.
- Running example: the treatment innovation is a symmetric two-component Gaussian mixture, so its transform has a known imaginary zero.

---

## The Running Example

- Suppose treatment shocks come from \(\tfrac12 N(-1,1)+\tfrac12 N(1,1)\).
- This noise is centered, independent of covariates, and has a fourth cumulant equal to \(-2\).
- Its moment-generating function vanishes at \(i\pi/2\).
- The zero turns the residual \(Z_n=T-\bar g_n(X)\) into a sine-weighted instrument.
- In this example, the full contour search collapses to one empirical sine ratio.

@informal prop:symmetric-mixture-reduction: For the symmetric Gaussian mixture, the sine-ratio estimator has mean-squared error at most \(C/n\) when the stated independence, range, tail, sampling, and \(L^1(P_X)\) treatment-code conditions hold.

---

## Setup: What Is Observed

- Each observation is \(O=(X,T,Y)\): covariates, treatment, and outcome.
- The partially linear coefficient is \(\theta_0\), the coefficient on residualized treatment.
- The treatment innovation is \(\eta=T-g_0(X)\).
- The outcome innovation is \(\xi=Y-q_0(X)-\theta_0\eta\).
- The estimator uses the supplied clipped treatment code \(\bar g_n\), giving the code residual \(Z_n=T-\bar g_n(X)\).

---

## Assumptions in Plain Language

- Sampling is i.i.d. from the law under evaluation.
- The treatment innovation \(\eta\) is independent of \(X\).
- The outcome innovation has mean zero conditional on \(X,T\).
- The coefficient, treatment regression, and outcome regression live in fixed bounded ranges.
- The treatment and outcome innovations satisfy the stated sub-Gaussian envelopes.
- The treatment innovation has a fixed nonzero cumulant: \(|\kappa_k(\eta)|\ge\delta\).

@formal ass:cumulant-separation

---

## The Stability Gate

- The contour class controls the treatment-code error in \(L^1(P_X)\).
- In words: the supplied treatment code is close enough on average under the covariate distribution.
- This condition preserves the zero geometry of the residual transform.
- In the running mixture example, it keeps the sine denominator bounded away from zero.
- The main theorem uses the explicit gate \(\varepsilon_{1,n}\le \{4R_1\exp(2C_gR_1)\}^{-1}\).

@formal ass:l1-treatment-code-radius

---

## Key Idea: Zeros Survive Residual Shifts

- A zero of the innovation transform creates a weight \(J\) with zero expectation.
- Treatment-code error shifts the innovation by a real covariate-dependent amount.
- The zero-based weight annihilates every real shift \(d\), so it also works after conditioning on \(X\).
- That gives an instrument for \(Z_n=T-\bar g_n(X)\), even when \(\bar g_n\) differs from \(g_0\).
- The denominator is a product of the zero derivative and a nuisance transform, so stability means keeping that product nonzero.

@informal thm:known-zero-instrument: Given a zero of the treatment-innovation transform with nonzero denominator, the zero-based instrument identifies \(\theta_0\) from the population ratio.

---

## From a Known Zero to a Contour

- The estimator usually does not know the exact zero.
- The observable treatment-residual transform \(F_n\) carries the same zeros after multiplying by a nuisance factor.
- The observable outcome-weighted transform \(G_n\) carries the numerator information.
- A contour enclosing at least one zero averages \(G_n/F_n\) over the enclosed zero structure.
- The contour ratio equals the partially linear coefficient under residual zero-freeness, nuisance zero-freeness, and positive zero count.

@formal thm:exact-contour-identification

---

## Where the Literature Stands

- Classical partially linear estimation residualizes \(T\) and \(Y\) to estimate \(\theta_0\).
- Double/debiased machine learning stabilizes first-order nuisance error through orthogonal scores.
- Higher-order orthogonality and the JMS order-\(r\) ACE estimator use finite-order expansions under non-Gaussian treatment residuals.
- Transform and zero methods are classical tools for identification and spectral estimation.
- This paper uses complex MGF zeros directly for learned-residual contamination in a fixed-code PLM decision problem.

---

## The Finite Contour Statistic

- Cumulant separation localizes at least one transform zero inside radius \(R_0=A_k(\psi_\eta^2/\delta)^{1/(k-2)}\).
- The contour bank searches circles between \(R_0\) and \(R_1=R_0+1\).
- The pilot fold selects a circle using a winding count and an empirical lower-modulus check.
- The evaluation fold computes the contour average of \(\widehat G/\widehat F\).
- The final output is the real midpoint clipped to \([-C_\theta,C_\theta]\).

@figure contour-estimator-pipeline: The diagram shows observations split into pilot and evaluation folds, residualized treatments \(Z_n\), empirical transforms, pilot contour selection, evaluation-fold contour averaging, and clipping to \([-C_\theta,C_\theta]\).

---

## Main Result: Fixed-Separation Minimaxity

@formal thm:adaptive-rootn-minimax

- The contour statistic is a measurable function of the sample.
- Its certified exact-arithmetic implementation, run on rational-record inputs, returns the same number under the stated adapter specification.
- The non-Gaussian fixed-code risk is bounded above by \(C/n\) and below by \(c/n\).
- The ACE fixed-code class receives the same \(C/n\) upper guarantee and \(c/n\) lower guarantee.
- The generalized lower \((1-\gamma)\)-quantile of absolute error is at most \(\sqrt{C/(\gamma n)}\).

---

## Why the Novelty Wins

- The naive plug-in residual moment inherits treatment-code contamination through \(D_n(X)=g_0(X)-\bar g_n(X)\).
- A finite-order ACE expansion carries nuisance terms \(\varepsilon_{1,n}^r\varepsilon_{2,n}\) and \(C_\theta\varepsilon_{1,n}^{r+1}\), plus sampling.
- The contour statistic uses transform zeros to remove the real-shift contamination from the identifying moment.
- The \(L^1(P_X)\) gate controls the nuisance factor \(H_n\), preserving the zero count and denominator separation.
- Under fixed separation, the displayed contour upper guarantee is governed by \((\gamma n)^{-1/2}\) in quantile scale.
- Call a sequence *nuisance-dominant* when the ACE nuisance terms \(\varepsilon_{1,n}^r\varepsilon_{2,n}+C_\theta\varepsilon_{1,n}^{r+1}\) grow large relative to the sampling scale \(n^{-1/2}\); those are the sequences the comparison below tracks.

@informal prop:jms-ace-alignment: On the aligned ACE class, the contour quantile upper bound is at most \(\sqrt{C_{\mathrm{spec}}/(\gamma n)}\), while the published ACE upper bound carries the stated finite-order nuisance terms, and their ratio tends to zero along nuisance-dominant sequences.

---

## Also in the Paper

@informal thm:common-experiment-dichotomy: Along fixed-primitive non-Gaussian sequences, the same transported contour bank gives fixed-code minimax risk between \(c/n_j\) and \(C/n_j\), and the bounded-outcome Gaussian comparison class has zero fixed-code Gaussian risks.

@informal prop:bounded-outcome-gaussian-degeneracy: In the bounded-outcome Gaussian JMS comparison class, every law has \(\theta_0(P)=0\), and nonempty fixed-code intersections have zero Gaussian minimax MSE and quantile risk.

@informal thm:local-to-gaussian-partial-benchmarks: For shrinking cumulant thresholds, the paper gives a Gaussian--Rademacher sine benchmark with the explicit mean-squared-error bound and records the local ACE oracle envelope under the published ACE handle assumptions.

---

## Why It Is True: Population Geometry

- Cumulant separation forces the innovation transform away from the Gaussian case strongly enough to guarantee a zero in a fixed disk.
- Independence from \(X\) factors the residual transform into the innovation transform times the treatment-code nuisance transform.
- The \(L^1(P_X)\) gate keeps the nuisance transform uniformly close to one on the search disk.
- Therefore the observable residual transform has the same relevant zero geometry as the innovation transform.
- A contour enclosing those zeros converts the transform identity into the coefficient \(\theta_0\).

---

## Why It Is True: Statistical Control

- The contour bank is finite once the primitive constants are fixed.
- Split sampling separates contour selection from contour evaluation.
- Uniform empirical-transform bounds control \(\widehat F-F\) and \(\widehat G-G\) on the search disk.
- The selected contour has a certified denominator buffer, so ratio perturbations are linear in transform errors.
- The final \(1/n\) rational integration tolerance is smaller than the statistical scale.

---

## Takeaways

- Non-Gaussian treatment innovations provide usable zeros of the treatment-innovation transform.
- Zero-based instruments identify the partially linear coefficient after residualizing with a stable supplied treatment code.
- A finite bank of circles between \(R_0\) and \(R_1\) turns the population zero argument into a statistic defined on every sample.
- Under fixed cumulant separation and the stated fixed-code conditions, the contour statistic attains minimax mean-squared error of order \(n^{-1}\).
- The ACE comparison identifies regimes where the contour upper guarantee removes the finite-order nuisance terms from the displayed ACE bound.
