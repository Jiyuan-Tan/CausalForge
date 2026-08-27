# Forbidden Comparisons in Fixed-Effect Poisson DiD

TL;DR: In staggered-adoption DiD with proportional effects, pooled fixed-effect Poisson can have a negative population treatment coefficient even when every treated cohort-time effect is positive, because the coefficient is a misspecified projection with signed residual comparisons.

---

## The Punchline

- The paper characterizes the population treatment coefficient from pooled unit-and-time fixed-effect PPML.
- With a common proportional effect, that coefficient recovers the common log multiplier exactly.
- With heterogeneous proportional effects, the coefficient moves according to fitted-mean-weighted residualized treatment.
- Under staggered timing, some treated cells can receive negative comparison residuals.
- An explicit four-cohort design gives a negative limiting coefficient while every treated cell effect is positive.
- A positive counterfactual-share proportional ATT target remains positive in the same environment.

---

## Why This Matters

- PPML fixed-effect DiD is natural when outcomes have multiplicative means, zeros, and high-dimensional fixed effects.
- Trade gravity is the motivating case: policy adoption is staggered across pairs or cohorts, and effects may vary over event time.
- A single pooled treatment coefficient is often read as the sign of the policy effect.
- The paper asks what sign that coefficient carries as a population projection.
- The answer matters when heterogeneous positive effects are compressed into one PPML coefficient.

---

## Running Example

- Four cohorts are observed for four periods.
- Cohorts first treated in periods 2, 3, and 4 are compared with a never-treated cohort.
- Untreated means are flat and cohort shares are equal.
- Every treated cohort-time cell has a positive proportional effect.
- One late cell for the earliest cohort has the largest positive effect.
- What sign does pooled fixed-effect PPML assign to treatment?

@figure four-cohort-staggered-design: Schematic of the witness design: four cohorts crossed with four periods give the treated cells, one of which is the late cohort-2 period-4 cell carrying the largest effect, and these together with the flat-mean equal-share restrictions determine the pooled PPML sign.

---

## Setup: The Population Object

- Units belong to adoption cohorts \(g\), and periods are indexed by \(t\).
- \(D_{gt}\) records whether cohort \(g\) is treated in period \(t\).
- \(B_{gt}\) is the untreated cohort-time mean.
- \(\delta_{gt}\) is the treated-cell log proportional effect.
- \(m_{gt}(\delta)\) is the observed cohort-time mean induced by treatment, and \(q_{gt}\) is the mass of that cell.
- Collapsed means the unit-level regression is reduced to one cell per cohort-period pair, which the paper shows leaves the treatment coefficient unchanged.
- \(\beta^\star(\delta)\) is the limiting treatment coordinate from the collapsed fixed-effect PPML projection, with \(\mu^\star_{gt}(\delta)\) the fitted means it produces.

---

## Maintained Mean Restrictions

- Cohort shares have positive limits, so every cohort remains in the population comparison.
- Untreated means follow a multiplicative unit-effect and time-effect structure.
- Treatment changes treated means by cohort-time proportional log multipliers.
- In the trade example, untreated trade flows have multiplicative pair and time components, and policy effects are proportional shifts in expected flows.

@formal ass:cohort-share-limit

@formal ass:unit-untreated-exponential-mean

@formal ass:proportional-effects

---

## The Projection Needs Residual Treatment Variation

- The collapsed design has enough variation to separate cohort effects, time effects, and treatment.
- The analysis works with the deterministic population PPML score.
- The key auxiliary object is \(\widetilde W_{gt}(\delta)\): treatment residualized on cohort and time fixed effects using fitted PPML mean weights.
- A positive residual means the treated cell pushes the pooled coefficient upward.
- A negative residual means the treated cell pushes it downward.

@formal ass:collapsed-design-rank

---

## Key Idea

- Linear TWFE can create forbidden comparisons because already-treated and newly treated groups enter with signed weights.
- PPML creates an analogous issue through the curvature of the misspecified Poisson criterion.
- The comparison weight is not a simple least-squares outcome weight.
- It is the fixed-effect residual of treatment under weights \(q_{gt}\mu^\star_{gt}(\delta)\).
- The sign question becomes: which treated cells have negative weighted residualized treatment?

@figure ppml-projection-pipeline: Schematic of the mechanism: primitive cohort-time means fix the fixed-effect PPML projection and hence the fitted means, the fitted means supply the weights, and treatment residualized under those weights is what decides the sign of the pooled coefficient.

---

## Where the Literature Stands

- Classical DiD builds untreated counterfactual trends from repeated observations.
- Modern staggered-adoption work shows that linear TWFE can aggregate heterogeneous effects through problematic comparisons.
- Nonlinear DiD and PPML work justify multiplicative mean models and pseudo-likelihood projections.
- Moreau-Kastler studies positive counterfactual-share proportional ATT targets.
- This paper connects those threads by characterizing the pseudo-true pooled PPML coefficient under heterogeneous proportional effects.

---

## Benchmark: Homogeneous Effects

@informal prop:homogeneous-effect-reduction: Under the untreated exponential mean restriction, full collapsed rank, and a common treated-cell log effect, the limiting pooled PPML coefficient equals that common effect.

@formal prop:homogeneous-effect-reduction

---

## First Main Result: The Local Sign Rule

@informal thm:sharp-ppml-forbidden-sign: Under collapsed rank, increasing one treated cell’s log multiplier moves \(\beta^\star(\delta)\) in the sign direction of that cell’s fitted-mean-weighted residualized treatment.

@formal thm:sharp-ppml-forbidden-sign

---

## Why the Sign Rule Is New

- The naive intuition is that a larger positive treated-cell effect should raise the pooled treatment coefficient.
- That intuition is valid when the treated cell has positive residualized treatment.
- It breaks when the fixed effects make that treated cell a negative residual comparison cell.
- The PPML score then balances the larger observed mean against fitted means through curvature weights.
- The novel object \(\widetilde W_{gt}(\delta)\) identifies exactly which cell-level effects pull the pooled coefficient down.

---

## Global Sign Characterization

- The local derivative tells how one cell moves the coefficient.
- The next result gives a primitive scalar index \(\Phi\), built from cohort sums, period sums, the grand sum, and treated-cell sums of observed mean components.
- Its sign is exactly the sign of the limiting pooled PPML coefficient under the stated multicohort positive-effect scope.
- The same theorem compares the pooled coefficient with \(PTT\), the counterfactual-share proportional ATT: the treated cells' proportional gains averaged with positive weights that sum to one.

@informal thm:primitive-global-frontier: Under the stated multicohort positive-effect assumptions, \(\Phi\) is negative, zero, or positive exactly when \(\beta^\star(\delta)\) is negative, zero, or positive; when \(\Phi<0\), the pooled coefficient is negative while \(PTT\) is positive.

@formal thm:primitive-global-frontier

---

## The Four-Cohort Sign Reversal

- The witness uses cohorts \(2,3,4,\infty\), four periods, equal shares, unit baselines, and flat untreated time effects.
- Every treated cell has a strictly positive proportional log multiplier.
- The cohort-2 period-4 cell has the unique largest treated effect.
- Its residualized treatment is \(-1/8\) at the no-effect benchmark, and the coefficient's derivative in that cell stays negative for all small positive effect vectors.
- The sign-reversal region \(\mathcal R_T\) collects the primitives that have at least four periods, the required cohort support, strictly positive treated effects, full collapsed rank, and \(\beta^\star(\delta)<0\).
- The primitive index places the full witness in that region.

@informal prop:four-cohort-sign-reversal: In the explicit four-cohort witness, every treated supported cell has a strictly positive log multiplier, yet the primitive belongs to the sign-reversal region \(\mathcal R_4\).

@formal prop:four-cohort-sign-reversal

---

## Why the Construction Works

- Equal shares and flat untreated means remove composition and baseline scale as explanations.
- Staggered timing creates cells that are treated but resemble residual controls after cohort and time effects are partialled out.
- The largest positive effect is placed in a cell with negative residualized treatment.
- The PPML projection tries to fit all cohort-time means with one treatment coordinate.
- The fixed-effect score balance lets that large positive cell pull the common coefficient below zero.

---

## Projection Coefficient Versus Positive Target

- The pooled PPML coefficient is a pseudo-true projection coordinate: the treatment coordinate that maximizes the misspecified Poisson criterion at the population means.
- The counterfactual-share \(PTT\) aggregates granular proportional effects using positive untreated-exposure weights.
- Under positive granular effects, that target preserves the positive sign.
- In the frontier theorem’s environment, the same primitives can satisfy \(\beta^\star(\delta)<0<PTT\).
- The empirical interpretation turns on which population object the researcher wants.

---

## Takeaways

- Under the maintained mean restrictions, fixed-effect PPML exactly recovers a common proportional effect.
- With heterogeneous proportional effects, the pooled coefficient is governed by weighted residualized treatment comparisons.
- A treated cell with negative residualized treatment can push the coefficient downward as its positive effect grows.
- Within the multicohort positive-effect scope, the primitive index \(\Phi\) characterizes the sign of the limiting pooled coefficient.
- The four-cohort witness establishes sign reversal under equal shares, flat untreated means, and strictly positive treated-cell effects.
- Positive-weight proportional targets remain the natural causal summaries under the maintained mean restrictions.
