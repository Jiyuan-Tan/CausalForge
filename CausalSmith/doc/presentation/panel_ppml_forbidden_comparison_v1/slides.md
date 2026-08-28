# When Fixed-Effect Poisson DiD Gets the Sign Wrong

A pooled fixed-effect PPML coefficient can be negative even when every cohort-time proportional treatment effect is positive, because the population score uses signed residual comparisons.

---

## The coefficient is a projection, and projections can flip signs

- In staggered adoption, treated cohorts also become comparison cohorts for later-treated groups.
- In linear DiD, this creates signed comparison weights under heterogeneous effects.
- This paper gives the proportional-effect PPML analogue.
- The object is the population treatment coordinate \(\beta^\star(\delta)\), the limiting fixed-effect Poisson projection coefficient.
- Under a common proportional effect, \(\beta^\star(\delta)\) recovers that effect exactly.
- Under heterogeneous positive proportional effects, \(\beta^\star(\delta)\) can be negative.

---

## The running example is a staggered policy in a multiplicative mean model

- Think of a gravity-style policy that affects trade flows multiplicatively.
- Cohorts adopt in periods 2, 3, and 4, and one cohort is never treated.
- The empirical shortcut is a PPML regression with unit fixed effects, time fixed effects, and one treatment indicator.
- The causal primitives are cohort-time proportional effects.
- The question is what sign the single pooled PPML coefficient carries when those effects differ.

@figure staggered-ppml-panel: A box-and-arrow schematic with boxes for cohorts 2, 3, 4, and never treated, arrows from untreated mean and cohort-time proportional effects into observed cohort-time means, and an arrow from observed means into the pooled FE-PPML coefficient.

---

## Multiplicative parallel trends gives the untreated benchmark

- The untreated mean factors into a unit baseline and a calendar component.
- After cohort averaging, the untreated cohort-time mean is \(B_{gt}\), the untreated mean for cohort \(g\) in period \(t\).
- Treatment is absorbing, so \(D_{gt}\) records whether cohort \(g\) is treated in period \(t\).
- A treated cell has log proportional effect \(\delta_{gt}\), so positive \(\delta_{gt}\) means the treatment raises the mean proportionally.
- The collapsed design has enough variation to separate cohort effects, time effects, and treatment.

@formal ass:unit-untreated-exponential-mean

---

## The population target is the collapsed PPML coefficient

- The paper studies \(\beta^\star(\delta)\), the treatment coordinate selected by the limiting cohort-time PPML criterion.
- This is the deterministic population object targeted by pooling cohort-time cells with fixed effects.
- The fitted mean \(\mu^\star_{gt}(\delta)\) supplies the curvature weights that determine comparisons.
- The finite-array unit fixed-effect projection collapses to the same cohort-time object asymptotically.

@formal def:collapsed-population-projection

---

## Homogeneity is the calibration point

@informal prop:homogeneous-effect-reduction: When every treated cell has the same proportional log effect \(\delta_0\), the population PPML coefficient equals \(\delta_0\) exactly.

@formal prop:homogeneous-effect-reduction

---

## Heterogeneity makes the residual comparison decisive

- Residualized treatment means treatment after partialling out cohort and time fixed effects.
- Here residualization uses PPML fitted-mean weights, not ordinary least-squares weights.
- A treated cell with positive residualized treatment pushes \(\beta^\star(\delta)\) upward when its effect rises.
- A treated cell with negative residualized treatment pushes \(\beta^\star(\delta)\) downward when its effect rises.
- The next result gives the exact derivative sign.

---

## The local sign is sharp

@informal thm:sharp-ppml-forbidden-sign: For a treated cell, the derivative of \(\beta^\star(\delta)\) with respect to that cell’s log proportional effect has the same sign as its fitted-mean-weighted residualized treatment.

@formal thm:sharp-ppml-forbidden-sign

---

## The mechanism is the Poisson score, not averaging

- The PPML first-order condition balances observed means against fitted means.
- Fixed effects force that balance across cohort margins and time margins.
- Heterogeneous treatment effects change treated-cell observed means.
- The fixed-effect refit reallocates that change through fitted-mean-weighted residual comparisons.
- A positive effect in a negative-residual treated cell can lower the pooled coefficient.

@figure score-residual-pipeline: A box-and-arrow schematic with boxes for heterogeneous treated-cell means, PPML fixed-effect fit, fitted-mean weights, residualized treatment cells, and the sign of the pooled coefficient.

---

## A primitive index gives the global sign

- The local derivative explains how one cell moves the coefficient.
- The global characterization reduces the sign to \(\Phi\), a scalar index computed from cohort shares, untreated means, and treated-cell multipliers.
- The index uses \(h_{gt}\), the share-weighted observed mean component for cohort \(g\) in period \(t\).
- Its row sums, column sums, grand sum, and treated-cell sum determine the sign frontier.
- This turns the sign question into a primitive diagnostic.

---

## The frontier exactly matches the coefficient sign

@informal thm:primitive-global-frontier: Under the stated multicohort positive-effect conditions, \(\beta^\star(\delta)\) is negative, zero, or positive exactly when \(\Phi\) is negative, zero, or positive.

@formal thm:primitive-global-frontier

---

## The same primitives can have a positive proportional target

- The proportional treatment-on-the-treated target \(PTT\) averages granular proportional effects with counterfactual-share weights.
- Under positive granular effects, those weights are positive and sum to one.
- The frontier theorem places both summaries in the same population environment.
- When \(\Phi<0\), the pooled PPML coefficient is negative while \(PTT\) is positive.
- The contrast is between a pooled score projection and a positive-weight causal aggregate.

---

## The four-cohort witness makes the sign reversal concrete

- The support is \(\{2,3,4,\infty\}\): early, middle, late, and never-treated cohorts.
- Cohort shares are equal.
- Untreated baselines are one, and untreated time effects are flat.
- Every treated cell has a positive proportional log effect.
- The largest treated effect is in cell \((2,4)\), an early-treated cohort observed late.
- That cell has negative residualized treatment in the witness.

---

## Positive effects can produce a negative pooled coefficient

@informal prop:four-cohort-sign-reversal: In the equal-share four-cohort witness \(W_4\), every treated-cell log proportional effect is positive, the largest effect is at \((2,4)\), and the primitive tuple belongs to the sign-reversal region \(\mathcal R_4\).

@formal prop:four-cohort-sign-reversal

---

## The proof follows the fitted comparison structure

- First, unit fixed effects collapse to cohort-time cells because only cohort-average baselines enter the population criterion.
- Second, the PPML first-order conditions define a unique pseudo-true fitted mean under the rank condition.
- Third, differentiating the score gives a denominator from residual treatment variation and a numerator from the treated cell’s residual.
- Fourth, eliminating fixed effects yields the primitive sign index \(\Phi\).
- Finally, the four-cohort primitives place \(W_4\) on the negative side of that frontier.

---

## What the paper establishes

- It characterizes the deterministic population FE-PPML treatment coefficient in staggered-adoption proportional-effect designs.
- It proves exact recovery under a common proportional effect.
- It gives a sharp local sign rule through fitted-mean-weighted residualized treatment.
- It gives a primitive global sign frontier through \(\Phi\).
- It constructs an equal-share four-cohort positive-effect witness with a negative limiting pooled coefficient.
- It separates the pooled PPML projection from the positive counterfactual-share proportional \(PTT\).
