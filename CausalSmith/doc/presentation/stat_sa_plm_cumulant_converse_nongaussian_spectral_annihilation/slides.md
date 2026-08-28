# Contour Instruments for Partially Linear Models

We use zeros of the treatment-innovation transform to build contour instruments that identify and estimate the partially linear treatment coefficient at fixed-separation root-\(n\) scale.

---

## Overview

- We study a partially linear model with a supplied treatment code.
- The target is \(\theta_0\), the treatment coefficient after residualizing treatment on covariates.
- The key resource is non-Gaussian treatment noise with a fixed nonzero cumulant.
- A zero of the treatment-innovation moment-generating function creates an instrument that survives treatment-code error.
- A finite contour bank turns that population identity into a fixed-code estimator with minimax mean-squared error of order \(n^{-1}\).

@informal thm:adaptive-rootn-minimax: Under fixed cumulant separation and the stated fixed-code stability and boundedness conditions, the contour statistic has minimax mean-squared error between \(c/n\) and \(C/n\), and its generalized quantile error is at most \(\sqrt{C/(\gamma n)}\).

---

## Motivation

- Partially linear models estimate a low-dimensional treatment effect while allowing flexible covariate adjustment.
- Robinson (1988) gives the classical root-\(n\) residualized construction.
- Modern double/debiased machine learning keeps the same target stable under learned nuisance functions; see Chernozhukov et al. (2018).
- Here the supplied treatment code may have residual error.
- Think of \(T\) as an endogenous exposure whose predictable part is learned from covariates.
- We observe \(Z_n=T-\bar g_n(X)\), the residualized treatment formed with the supplied clipped treatment code.
- The code error shifts the true treatment innovation by \(D_n(X)=g_0(X)-\bar g_n(X)\).
- Non-Gaussian treatment noise gives complex transform zeros that can protect estimation from these real shifts.

---

## Setup

- We observe \(O=(X,T,Y)\).
- The conditional treatment and outcome regressions are \(g_0(X)=E[T\mid X]\) and \(q_0(X)=E[Y\mid X]\).
- The treatment innovation is \(\eta=T-g_0(X)\).
- The outcome innovation is \(\xi=Y-q_0(X)-\theta_0\eta\).
- The supplied treatment and outcome codes are clipped to fixed ranges before use.
- The sample is i.i.d. and split into a pilot fold and an evaluation fold.

@formal def:plm-model

---

## Assumptions

- The treatment innovation is independent of covariates.
- The outcome innovation has conditionally mean zero given \(X,T\).
- The coefficient and regression functions are bounded.
- Treatment and outcome innovations are sub-Gaussian under our fixed envelope convention.
- The \(k\)th cumulant of the treatment innovation is separated from zero by \(\delta\), the cumulant-separation level.
- The treatment-code radius \(\varepsilon_{1,n}\) controls \(\|\bar g_n-g_0\|_{L^1(P_X)}\).

@formal ass:cumulant-separation

---

## Key idea

- Let \(M(z)=E[e^{z\eta}]\) be the treatment-innovation moment-generating function.
- If \(M\) has a zero \(z_0\), a polynomial-exponential weight built from \(z_0\) annihilates every real shift of \(\eta\).
- Conditioning on \(X\), that same weight becomes an instrument for the code residual \(Z_n\).
- The resulting ratio identifies \(\theta_0\) whenever the denominator is separated from zero.

@informal thm:known-zero-instrument: A zero of the treatment-innovation transform yields a valid shifted-residual instrument and identifies \(\theta_0\) through a population ratio when the denominator is nonzero.

---

## Contour identification

- A known zero gives one instrument; a contour handles the zeros without naming them one by one.
- \(F_n\) is the observable transform of the residualized treatment.
- \(G_n\) is the observable outcome-weighted transform.
- A contour enclosing at least one zero averages \(G_n/F_n\) over the enclosed zero structure.
- Nuisance zero-freeness keeps the treatment-code error from creating spurious denominator zeros.

@figure contour-identification: Box-and-arrow schematic showing supplied code and data forming residuals, observable treatment and outcome transforms, a zero-free nuisance factor, a selected contour, a contour average, and the identified coefficient.

@informal thm:exact-contour-identification: On a contour where \(F_n\) is zero-free at the boundary, the nuisance factor is zero-free inside, and at least one zero is enclosed, the normalized contour ratio equals \(\theta_0(P)\).

---

## Estimator

- The estimator uses a finite translated-dyadic bank of circles between the zero-localization radius and an outer radius.
- The pilot fold selects a circle with a positive winding count and a certified denominator margin.
- The evaluation fold computes the normalized contour average on the selected circle.
- The real midpoint is clipped to the known coefficient range.
- Every empirical branch returns a value, so the estimator is always well defined.

@figure contour-estimator-pipeline: Box-and-arrow schematic showing observations split into pilot and evaluation folds, residualization, empirical transforms, zero-radius bank construction, pilot contour selection, evaluation contour averaging, and clipped output.

@formal def:adaptive-contour-estimator

---

## Main result

- Fixed cumulant separation localizes a transform zero in a fixed search region.
- The \(L^1(P_X)\) treatment-code gate preserves the zero geometry of the residual transform.
- Uniform empirical transform control gives root-\(n\) accuracy on the selected contour.
- The lower bound comes from a one-dimensional submodel with fixed treatment law and \(1/\sqrt n\) target separation.

@formal thm:adaptive-rootn-minimax

---

## Sequence result

- Along a sequence of experiments with the same primitive constants, one contour bank serves the sequence.
- On the cumulant-separated non-Gaussian fixed-code class, the minimax mean-squared risk stays between constants times \(n_j^{-1}\).
- On the bounded-outcome Gaussian comparison class of Jin, Mackey, and Syrgkanis (JMS), the target degenerates to zero under the stated simultaneous restrictions.

@informal thm:common-experiment-dichotomy: Along fixed-constant non-Gaussian experiment sequences, the same contour bank gives minimax mean-squared risk of order \(n_j^{-1}\), while the bounded-outcome Gaussian JMS fixed-code risks are zero.

---

## Related literature

- Partially linear models trace to Engle et al. (1986), Robinson (1988), Speckman (1988), and Härdle et al. (2000).
- Orthogonal and debiased learning build on semiparametric stability; see Chernozhukov et al. (2018) and Newey and Robins (2018).
- Higher-order orthogonality is the closest methodological comparison, including Mackey et al. (2018) and Jin et al. (2025).
- Transform-based estimation and zero arguments connect to Feuerverger and McDunnough (1981), Carrasco (2017), Kagan et al. (1973), Mattner (1992), and Hu and Shiu (2022).
- Non-Gaussian identification also appears in ICA and structural-equation work, including Comon (1994), Lanne et al. (2017), Lee and Mesters (2024), and Reizinger et al. (2025).

---

## ACE comparison

- Jin et al. (2025) provide the published comparison through their finite-order ACE estimator for cumulant-separated partially linear models.
- The ACE guarantee uses \(L^r(P_X)\) treatment and outcome code radii and the JMS eligibility condition.
- The contour guarantee uses the common clipped-code experiment and the \(L^1(P_X)\) treatment-code gate.
- On the aligned class, ACE carries finite-order nuisance terms, while the contour upper guarantee is governed by \((\gamma n)^{-1/2}\).
- When the ACE nuisance terms dominate \(n^{-1/2}\), the ratio of the contour upper guarantee to the ACE upper guarantee tends to zero.

@formal prop:jms-ace-alignment

---

## Gaussian benchmark

- The JMS Gaussian comparison imposes Gaussian treatment noise and bounded observed outcomes.
- Under those simultaneous restrictions, the target coefficient is forced to zero.
- The fixed-code Gaussian minimax mean-squared risk and generalized-quantile risk are therefore zero whenever the clipped-code intersection is nonempty.

@informal prop:bounded-outcome-gaussian-degeneracy: In the bounded-outcome Gaussian JMS comparison class, every admissible law has \(\theta_0(P)=0\), and the fixed-code Gaussian risks are zero when the class intersection is nonempty.

---

## Explicit mixtures

- A symmetric two-component Gaussian mixture has a known imaginary transform zero.
- The contour construction collapses to a sine-ratio estimator using \(Y\sin(\pi Z_n/2)\) and \(Z_n\sin(\pi Z_n/2)\).
- The \(L^1(P_X)\) treatment-code bound keeps the sine denominator bounded away from zero.
- The resulting clipped ratio attains mean-squared error at most \(C/n\).

@informal prop:symmetric-mixture-reduction: For the symmetric Gaussian mixture treatment innovation with the stated independence, range, tail, sampling, and treatment-code conditions, the clipped sine-ratio estimator has mean-squared error at most \(C/n\).

---

## Local benchmarks

- The Gaussian--Rademacher path makes weak non-Gaussianity explicit through the amplitude \(a\).
- Its fourth cumulant magnitude is \(\Delta_a=2a^4\), and the first positive transform zero determines the sine frequency.
- The mean-squared error bound grows with the reciprocal denominator scale as the path approaches Gaussian noise.
- The local ACE oracle envelope records the published ACE upper bound with shrinking cumulant threshold \(\delta_n\).

@formal thm:local-to-gaussian-partial-benchmarks

---

## Also in the paper

@informal lem:jms-ace-class-relations: The JMS ACE class is contained in the non-Gaussian contour class, the \(L^s(P_X)\)-restricted contour subclass is contained in the JMS ACE class, and the two coincide when \(s=r\).

@informal lem:non-gaussian-hard-submodel: A one-dimensional fixed-code submodel gives an \(n^{-1}\) minimax lower bound on the non-Gaussian and ACE classes.

@informal lem:gaussian-rademacher-l1-benchmark: Along the Gaussian--Rademacher path, the sine denominator and cumulant scale are explicit, and the clipped sine estimator satisfies the displayed mean-squared-error bound.

---

## Future work

- The fixed-separation theorem holds with \(\delta\), the cumulant-separation level, fixed across the experiment.
- A local-to-Gaussian frontier lets the cumulant threshold \(\delta_n\) shrink with \(n\).
- The open statistical object is the sharp minimax mean-squared-error rate as a function of \((n,\varepsilon_{1,n},\varepsilon_{2,n},\delta_n)\).
- A full selector would compare ordinary debiased machine learning, the finite-order ACE estimator, and global-contour procedures under a uniform inference criterion.

@formal oeq:local-to-gaussian-frontier

---

## Conclusion

- We construct contour instruments from zeros of the treatment-innovation transform.
- The population contour ratio identifies the partially linear treatment coefficient under zero-free boundary, zero-free nuisance, and positive-count conditions.
- The finite contour statistic attains fixed-code minimax mean-squared error of order \(n^{-1}\) under fixed cumulant separation and the stated stability and boundedness conditions.
- The ACE alignment places the contour guarantee and the published finite-order guarantee on a common clipped-code comparison class.
- The mixture benchmarks show the same mechanism in explicit sine-ratio form.
