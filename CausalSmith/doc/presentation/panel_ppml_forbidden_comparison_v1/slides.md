# Forbidden Comparisons in Fixed-Effect Poisson Difference-in-Differences

We characterize when pooled fixed-effect Poisson pseudo-maximum likelihood (PPML) in staggered-adoption difference-in-differences (DiD) delivers a negative population treatment coefficient under strictly positive proportional effects.

---

## Overview

- The object is \(\beta^\star(\delta)\), the limiting pooled PPML treatment coordinate.
- Under heterogeneous proportional effects, \(\beta^\star(\delta)\) is a misspecified projection.
- Its sign is governed by fitted-mean-weighted residualized treatment comparisons.
- We give an explicit four-cohort design with \(\beta^\star(\delta)<0\) while every treated cohort-time proportional effect is positive.
- The counterfactual-share proportional treatment-on-the-treated target (PTT) remains positive in the same population environment.

---

## Motivation

- Staggered adoption makes a single treatment indicator tempting.
- Linear DiD taught us that pooled two-way fixed effects can compare already-treated and newly treated cohorts in hard-to-interpret ways.
- Goodman-Bacon (2021) gives the linear decomposition.
- de Chaisemartin and D'Haultfoeuille (2020) show how heterogeneous effects can receive signed weights.
- Many applied settings use multiplicative means and PPML, especially trade and count outcomes.
- We ask how the same concern appears on the PPML scale.

---

## Running example

- Think of a trade policy adopted by different country pairs at different dates.
- Outcomes are nonnegative flows, so applied work often uses PPML with high-dimensional fixed effects.
- The policy effect is naturally proportional: a treated cell has a multiplicative change relative to its untreated mean.
- A single pooled PPML coefficient is often read as the policy direction.
- Our results characterize the population object behind that coefficient.

@figure staggered-adoption-panel: Boxes for cohorts 2, 3, 4, and never-treated, arrows from each cohort box to its treated cohort-period cells, and arrows from all cells into one pooled PPML coefficient.

---

## Setup

- Units belong to adoption cohorts \(G_i\), including the never-treated cohort \(\infty\).
- Treatment is absorbing, so cohort \(g\) is treated in period \(t\) when \(D_{gt}=1\).
- The untreated mean has a unit baseline and a calendar component.
- Treated outcomes follow cohort-time proportional log multipliers \(\delta_{gt}\).
- Cohort shares stay positive in the large-array limit.
- Within-cohort baseline averages converge, so the panel collapses to cohort-time cells.

---

## Assumptions

The load-bearing structure is multiplicative untreated means, proportional treatment effects, and a full-rank collapsed fixed-effect design.

@formal ass:unit-untreated-exponential-mean

@formal ass:proportional-effects

@formal ass:collapsed-design-rank

---

## Positive-effect scope

- The sign-reversal question is asked under the strongest sign benchmark.
- Every treated cohort-time cell has a positive proportional log multiplier.
- The multicohort scope contains early, middle, late, and never-treated cohorts.

@formal ass:strict-positive-effects

@formal ass:multicohort-frontier-scope

---

## Projection target

- We study the population PPML projection, evaluated at cohort-time means.
- The fitted mean \(\mu^\star_{gt}(\delta)\) is the PPML fit in the collapsed cohort-time table.
- The treatment coordinate \(\beta^\star(\delta)\) is the single coefficient produced by pooling.
- The key comparison object is \(\widetilde W_{gt}(\delta)\), the fitted-mean-weighted residual of treatment after partialling out cohort and time fixed effects.
- A cell with negative \(\widetilde W_{gt}(\delta)\) acts like an already-treated comparison cell in the PPML projection.

---

## Related literature

- Classical DiD builds untreated counterfactual trends from repeated observations: Ashenfelter and Card (1985), Angrist and Pischke (2009), and Imbens and Wooldridge (2009).
- Modern staggered DiD clarifies heterogeneous-effect aggregation: Goodman-Bacon (2021), Callaway and Sant'Anna (2021), Sun and Abraham (2021), and Borusyak et al. (2024).
- Nonlinear DiD and functional-form work frame the multiplicative setting: Wooldridge (2023) and Roth and Sant'Anna (2023).
- PPML practice is central in multiplicative mean models: Santos Silva and Tenreyro (2006, 2011), Correia et al. (2020), and Yotov et al. (2016).
- Moreau-Kastler (2025) supplies the closest positive proportional PTT benchmark.

---

## Main result: local sign

@informal thm:sharp-ppml-forbidden-sign: Under collapsed rank, increasing one treated-cell proportional effect moves \(\beta^\star(\delta)\) in the sign direction of that cell's fitted-mean-weighted residualized treatment.

@formal thm:sharp-ppml-forbidden-sign

---

## Intuition

- PPML fits cohort and time fixed effects first through the multiplicative mean score.
- The remaining treatment variation is the residual after that weighted fit.
- The weights are fitted means, so high-mean cells carry more curvature in the score.
- Increasing a treated-cell effect changes the pooled coefficient through that cell's residualized treatment value.
- A negative residual means a larger positive effect in that cell pushes the pooled coefficient downward.

---

## Homogeneous benchmark

@informal prop:homogeneous-effect-reduction: Under the untreated mean restriction, collapsed rank, and a common treated-cell log multiplier, the pooled PPML coefficient recovers that common multiplier exactly.

@formal prop:homogeneous-effect-reduction

---

## Primitive frontier

- The derivative result is local.
- We also give a global sign diagnostic.
- \(\Phi\), the primitive sign index, is built from cohort shares, untreated means, treatment timing, and proportional multipliers.
- Under the stated multicohort positive-effect conditions, \(\Phi\) has exactly the same sign as \(\beta^\star(\delta)\).
- In the same environment, \(\Phi<0\) implies \(\beta^\star(\delta)<0<PTT\).

@formal thm:primitive-global-frontier

---

## Four-cohort witness

@informal prop:four-cohort-sign-reversal: In the equal-share four-cohort witness with flat untreated means, every treated cell has a positive proportional effect, the largest effect is in cell \((2,4)\), and the primitive belongs to the sign-reversal region.

@formal prop:four-cohort-sign-reversal

---

## Proof sketch

- Collapse the unit fixed-effect population criterion to cohort-time cells using cohort shares and within-cohort baseline limits.
- Use the PPML first-order conditions to express local coefficient changes through a weighted residualized treatment.
- The full-rank condition keeps residual treatment variation positive.
- Eliminate fixed effects from the collapsed score to obtain the primitive sign index \(\Phi\).
- In the four-cohort design, the late cell of the early-treated cohort has a negative residual and the explicit primitive index is negative.

---

## Also in the paper

@informal lem:unit-fe-collapse: Under the stated support, share, untreated-mean, baseline-limit, proportional-effect, and rank conditions, the unit fixed-effect population coefficient equals the collapsed finite-array treatment coordinate and converges to \(\beta^\star(\delta)\).

@informal lem:pseudo-true-ppml-projection: Under collapsed rank, the limiting PPML projection is unique and satisfies the nuisance and treatment score equations.

---

## Interpretation

- Under common proportional effects, pooled fixed-effect PPML recovers the common log multiplier.
- Under heterogeneous proportional effects, the pooled coefficient is a projection summary shaped by fixed-effect residual comparisons.
- The four-cohort witness shows a negative limiting pooled coefficient under strictly positive granular proportional effects.
- Positive-weight proportional targets aggregate the granular effects directly.
- The sign of the pooled coefficient and the sign of the proportional PTT can therefore diverge in the same primitive environment.

---

## Takeaways

- We characterize the population coefficient targeted by pooled fixed-effect PPML in staggered-adoption multiplicative DiD.
- The sharp sign formula links local movements in \(\beta^\star(\delta)\) to fitted-mean-weighted residualized treatment.
- The primitive frontier gives an exact global sign diagnostic through \(\Phi\).
- The four-cohort witness establishes sign reversal with equal shares, flat untreated means, and strictly positive treated-cell effects.
- The empirical message is to interpret pooled PPML coefficients as projection summaries and use granular proportional effects or positive-weight proportional aggregates for causal sign statements.
