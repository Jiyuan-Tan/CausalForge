# Chebyshev Schedules for Low-Budget Rollouts

With a polynomial rollout mean curve and a sharp round-mean variance envelope, Chebyshev-Lobatto measurement fractions attain the minimax exponential variance-amplification rate for extrapolating from partial rollout \(q<1\) to full adoption.

---

## Overview

- We want the full-adoption contrast, but the experiment observes treated fractions only up to \(q<1\).
- Low-order interference motivates a degree-\(\beta\) polynomial mean curve along the rollout path.
- Linear unbiased estimation becomes polynomial extrapolation from \([0,q]\) to \(1\).
- Under the variance envelope, schedule quality is exactly a weight-amplification problem.
- Chebyshev-Lobatto schedules attain the minimax amplification rate up to constants.

@informal thm:chebyshev-minimax: Under low-budget rollout and oversampling \(k\ge c\beta\), Chebyshev-Lobatto schedules have amplification at most the same exponential order that every admissible schedule must face.

---

## Motivation

- Rollout experiments often stop before universal adoption.
- In networked settings, partial adoption can still move outcomes through spillovers.
- The target is the endpoint contrast between no adoption and full adoption.
- The design question is where to measure along the rollout path before the budget \(q\).
- Example: a platform can expose at most 20 percent of users during the experiment, but wants the full-launch effect.

@figure rollout-pipeline: Box-and-arrow schematic showing rollout fractions from 0 through intermediate measurement rounds to budget q, followed by extrapolation to the full-adoption target 1.

---

## Research question

- The econometrician chooses \(k+1\) treated fractions \(0=p_0<\cdots<p_k=q\).
- At each fraction, we observe a finite-population round mean.
- We combine the round means linearly to estimate the endpoint contrast.
- The question is: which measurement fractions minimize worst-case variance amplification?

---

## Setup

- \(U_n\) is the finite population of \(n\) units.
- \(Z_j\) is the assignment vector at rollout measurement \(j\).
- \(\bar Y_j\) is the observed finite-population mean at that measurement.
- The schedule \(p=(p_0,\ldots,p_k)\) records target treated fractions from 0 to \(q\).
- The endpoint contrast is \(\tau_P=m_P(1)-m_P(0)\).

@formal ass:static-rollout-consistency

---

## Polynomial structure

- The rollout mean curve \(m_P(u)\), the mean response at treated fraction \(u\), is assumed polynomial.
- The order \(\beta\) is the maximum degree of the rollout mean curve.
- In the running example, \(\beta\) summarizes how many low-order exposure interactions are carried by the mean path.
- Once \(m_P\) is polynomial, the full-adoption contrast is a coefficient functional.

@formal ass:beta-order-polynomial

@informal prop:rollout-polynomial-identity: Under static rollout consistency and the degree-\(\beta\) mean restriction, the endpoint treatment contrast is the sum of the nonconstant polynomial coefficients.

---

## Variance envelope

- The variance scale \(\sigma_0^2/n\) bounds each round mean.
- The envelope allows any positive-semidefinite cross-round covariance matrix consistent with that diagonal bound.
- This isolates the cost of treated-fraction placement from model-specific covariance restrictions.
- In the platform example, the condition is read as a common bound on the noise of each rollout mean.

@formal ass:round-mean-variance-envelope

@formal ass:low-budget-cap

---

## Linear unbiased estimation

- We estimate \(\tau_P\) with a weighted sum of the observed round means.
- The weights are chosen to be exact for every polynomial of degree at most \(\beta\).
- The intercept weight sums to zero; every nonconstant monomial contributes one unit to the endpoint contrast.
- With at least \(\beta+1\) distinct nodes, such weights exist.

@informal lem:unbiased-weight-set-nonempty: When \(k\ge\beta\) and the schedule is admissible, there exists a linear weight vector that is unbiased for every degree-\(\beta\) rollout mean curve.

---

## Design criterion

- The variance envelope turns risk into the squared total variation of the weights.
- A fixed schedule is good when it admits unbiased weights with small \(\ell^1\) norm.
- The minimax design chooses the schedule with the smallest attainable amplification.
- This is the optimal-design problem behind the talk.

@formal thm:tv-envelope-design

---

## Key idea

- Polynomial extrapolation is controlled by the largest endpoint movement compatible with bounded values at the observed nodes.
- Weight minimization and polynomial extremality are dual views of the same object.
- Chebyshev polynomials are extremal for this endpoint problem.
- Lobatto nodes discretize the interval while preserving that extremal control under oversampling.

@informal lem:amplification-dual-norm: The minimum \(\ell^1\) norm of unbiased weights equals the largest possible endpoint contrast of a degree-\(\beta\) polynomial bounded at the schedule nodes.

---

## Chebyshev schedule

- Shifted Chebyshev-Lobatto nodes put more measurements near 0 and \(q\).
- Mechanism: use \(k+1\) Lobatto points on \([0,q]\), with \(k\ge c\beta\).
- Intuition: endpoint clustering controls the polynomial near the observed interval boundaries, where extrapolation to 1 is most sensitive.
- In the running example, this means spending more measurement rounds near no adoption and near the maximum feasible rollout.

@informal lem:chebyshev-schedule-admissible: For every \(k\ge1\) and \(q\in(0,1]\), the shifted Chebyshev-Lobatto schedule is admissible.

@figure chebyshev-schedule: Box-and-arrow schematic from the budget interval \([0,q]\) through endpoint-dense shifted Chebyshev--Lobatto nodes and oversampling \(k\ge c\beta\) to unbiased weights, endpoint extrapolation, and the minimax amplification scale.

---

## Main result

@formal thm:chebyshev-minimax

- The base \(\left(\frac{(1+\sqrt{1-q})^2}{q}\right)^{2\beta}\) is the unavoidable low-budget extrapolation scale under the envelope.
- Chebyshev-Lobatto placement attains this scale up to constants depending only on \(q_{\max}\) and \(c\).
- The schedule problem is solved at the level of the exponential rate.

---

## Benchmarks

- Equal spacing gives a simple feasible design with exactly \(\beta+1\) nodes.
- Its bound is useful as a scale comparison, since the displayed upper bound grows with \(\beta/q\).
- At \(q=1\), extrapolation disappears and the endpoint rule has bounded amplification.
- These benchmarks separate feasibility from minimax low-budget control.

@informal prop:equal-spacing-benchmark: For equally spaced \(\beta+1\) nodes on \([0,q]\), amplification is at most \(9(\beta/q)^{2\beta}\).

@informal prop:no-extrapolation-boundary: At \(q=1\), the baseline and final round means give an unbiased endpoint contrast with amplification at most 4.

---

## Proof sketch

- The envelope theorem reduces variance to \(\ell^1\) weight amplification.
- Duality converts weight amplification into an extremal polynomial problem.
- Chebyshev extremality gives the lower bound any schedule must respect.
- Oversampled Lobatto norming transfers continuous Chebyshev control to the finite measurement grid.
- The endpoint bound converts the exterior point \(1\) into the low-budget base.

@informal lem:chebyshev-exterior-extremal: A degree-\(\beta\) polynomial bounded by 1 on \([-1,1]\) is bounded at any exterior point by the corresponding Chebyshev value.

@informal lem:oversampled-chebyshev-lobatto-norming: With \(k\ge c\beta\), values on the Lobatto grid control the full interval sup norm up to a constant depending only on \(c\).

@informal lem:continuous-chebyshev-endpoint-bound: Uniformly for \(0<q\le q_{\max}<1\), the endpoint extrapolation size is controlled above and below by constants times \(\lambda(q)^\beta\).

---

## Exact covariance

- The envelope problem allows all positive-semidefinite covariance matrices with the same diagonal bound.
- The exact nested rollout problem uses the covariance matrix generated by the rollout law.
- The envelope comparison gives an exact-risk upper bound at every admissible schedule.
- Chebyshev-Lobatto schedules therefore give a feasible finite-population exact-risk rate.

@informal lem:exact-risk-envelope-upper: For every admissible schedule, the exact nested risk is at most the envelope amplification bound \((\sigma_0^2/n)A_\beta(p)\).

@informal lem:exact-chebyshev-rate-feasible: With \(k=\lceil c\beta\rceil\), the Chebyshev-Lobatto schedule has exact finite-population variance at most the same low-budget exponential upper rate as in the envelope theorem.

---

## Also in the paper

@informal lem:variance-envelope-sharpness: The round-mean variance envelope yields the \((\sigma_0^2/n)(\sum_j |w_j|)^2\) upper bound, and a positive-semidefinite covariance matrix attains that value.

@informal oeq:exact-nested-minimax: The exact covariance question asks whether Chebyshev-Lobatto placement attains the nested exact-risk infimum, separately from the proved rate-feasibility bound.

---

## Related literature

- Rubin (1974) and Imbens and Rubin (2015) frame the potential-outcomes baseline.
- Manski (1993, 2013) motivates spillovers and social interactions as identification targets.
- Horvitz and Thompson (1952) provide the linear-unbiased design template.
- Aronow and Samii (2017), Sävje et al. (2017), Eckles et al. (2017), and Ugander et al. (2013) develop design-based interference tools.
- Cortez et al. (2022), Cortez-Rodriguez et al. (2022), Cortez-Rodriguez et al. (2024), Eichhorn et al. (2024), Jiang and Wang (2023), Cai et al. (2023), and Fan et al. (2025) develop the low-order and network-interference design lineage.
- Smith (1918), Kiefer and Wolfowitz (1959), Kiefer (1974), Pukelsheim (1993), and Karlin and Studden (1966) supply the optimal-design and Chebyshev-system foundation.

---

## Conclusion

- We turn low-budget rollout placement into a polynomial extrapolation design problem.
- Under static rollout consistency, degree-\(\beta\) polynomial means, and the round-mean variance envelope, worst-case variance equals a total-variation amplification criterion.
- Chebyshev-Lobatto schedules attain the minimax low-budget exponential rate when \(k\ge c\beta\).
- For the exact nested rollout covariance problem, the same schedule is proved rate-feasible through the envelope upper bound.
- The remaining design question is covariance-specific exact optimality for the true nested rollout risk.
