# Minimax ATE with Many Discrete Cells

TL;DR: Under fixed overlap, real outcomes, and a known bound on cell-effect heterogeneity, the paper constructs clipped estimators and gives a finite-sample minimax bracket showing how \(n\), \(d\), and \(\sigma\) determine ATE accuracy.

---

## Punchline

- The target is a scalar average treatment effect with a finite discrete adjustment variable.
- The hard case is sparse crossing: many cells contain observations from one treatment arm but few contain both.
- The paper gives a same-class lower benchmark and a constructive upper benchmark.
- The known-radius selector chooses among a rare-cell polynomial estimator, a crossed-cell collision estimator, and zero.
- The benchmarks match at exact homogeneity, unrestricted radius, fixed positive radius, saturation, and parametric-dominance elbows.

@informal thm:two-sided-minimax-bracket-all-d: The minimax risk is bracketed between an exact-homogeneity baseline plus a radius-channel rare-cell term and the selector benchmark.

---

## Motivation

- Think of an observational program evaluation with many income-demographic strata.
- The econometrician wants the average treatment effect, not a conditional-effect map.
- Fixed overlap says both treatment arms are possible in every supported stratum.
- Finite samples still create empty arm-cell combinations.
- With many sparse cells, ordinary within-cell contrasts pay a collision price.
- The question is: how much does bounded treatment-effect heterogeneity help?

---

## Running Example

- In a 401(k)-style study, \(X\) is a fine discrete adjustment cell.
- \(A\) is eligibility or participation.
- \(Y\) is a real-valued wealth outcome.
- \(d\) is the number of adjustment cells.
- \(\sigma\) is the heterogeneity radius: it bounds how far any supported cell's effect can depart from the population ATE, in units of \(M\).
- Smaller \(\sigma\) means cells can borrow more information from each other.

---

## Setup

- Each observation is \(O=(X,A,Y)\), with \(X\in\{1,\ldots,d\}\), \(A\in\{0,1\}\), and real \(Y\).
- \(p_k\) is the cell mass, \(\pi_k\) is the propensity, and \(\mu_{ak}\) is the arm-cell outcome mean.
- The cell effect is \(\tau_k=\mu_{1k}-\mu_{0k}\).
- The target \(\tau(P)\) is the population-weighted average of the cell effects.
- The radius bound controls \(\delta_k=\tau_k-\tau(P)\) on supported cells.
- Risk is mean squared error, uniformly over the model class.
- Under the potential-outcome assumptions, \(\tau(P)\) is the standard adjusted causal contrast, identified by the usual g-computation argument.

---

## Assumptions in Plain Language

- Consistency links the observed outcome to the realized treatment.
- Conditional exchangeability makes within-cell treated-control contrasts causal.
- Fixed overlap bounds every supported propensity away from zero and one.
- Mean normalization fixes the real-outcome scale \(M\).
- Second central moments are bounded by \(M^2\), giving variance control.
- Approximate homogeneity bounds supported-cell effect deviations by \(\sigma M\).

@formal ass:overlap

---

## The Radius Index

- \(\sigma=0\) is exact effect homogeneity across supported cells.
- \(\sigma=2\) coincides with the unrestricted-radius endpoint under the outcome scale.
- Interior \(\sigma\) values form one nested family of minimax problems.
- In the running example, \(\sigma\) measures how far a stratum effect can move from the population ATE.
- This turns heterogeneity into a rate parameter rather than a side condition.

@formal ass:approximate-homogeneity

---

## Key Idea

- Sparse cells create two different estimation opportunities.
- Rare cells need a large-alphabet device that estimates many small contributions without direct crossing.
- Crossed cells support direct treated-control contrasts weighted by their observed occupancy.
- The selector uses the known radius to choose the better remainder.
- The comparison is between \(u_{n,d}=d^2/\{n^2\log^2(en)\}\) and \(h_{n,d,\sigma}=\sigma^2+d/n^2\).

@figure estimator-pipeline: The diagram shows the pilot split classifying cells as heavy or light, plug-in contrasts on heavy cells and Chebyshev factorial statistics on light cells forming the polynomial branch, the crossed-cell collision branch and the zero branch in parallel, and the known-radius selector comparing \(u_{n,d}\), \(h_{n,d,\sigma}\), and 1.

---

## Where the Literature Stands

- Classical ATE theory gives fixed-dimensional efficiency under regular nuisance estimation.
- High-dimensional nuisance work uses orthogonality and rates for learned nuisance functions.
- Discrete-adjustment minimax work highlights sparse crossing as the binding finite-sample difficulty.
- Zeng, Balakrishnan, Han, and Kennedy give binary collision and lower-bound ingredients.
- This paper builds a real-outcome, radius-indexed, same-class bracket under conditional second moments.

@informal prop:zeng-class-inclusion-and-lower-transfer: Binary hard experiments embed into the real-outcome model and transfer exact-homogeneity, radius-channel, and polynomial benchmarks on the \(M\) scale.

---

## Constructive Upper Bound

- The polynomial estimator splits the sample, classifies cells as heavy or light, and uses Chebyshev factorial statistics on light cells.
- A cell is heavy when the pilot half of the sample sees it more than a fixed multiple of \(\log(en)\) times — often enough for its arm means to be reliable; every other cell is light.
- The collision estimator averages treated-control contrasts over cells where both arms appear.
- The selector chooses collision when \(h_{n,d,\sigma}\) is smallest, polynomial when \(u_{n,d}\) is smallest, and zero in the saturated fallback region.
- Clipping keeps every candidate on the natural \([-M,M]\) target scale.

@informal thm:robust-upper-construction-resolution-all-d: The polynomial branch has risk at most a constant times \(M^2\{n^{-1}+\min(1,u_{n,d})\}\), while the collision branch has risk at most a constant times \(M^2(n^{-1}+\sigma^2+d/n^2)\).

@formal thm:frontier-upper-all-d

---

## Why the Selector Wins

- The naive within-cell approach pays for cells that never contain both treatment arms.
- The collision branch shrinks that cost when heterogeneity is small, because uncrossed cells differ from the ATE by at most \(\sigma M\).
- The polynomial branch controls the unrestricted sparse-cell remainder at the large-alphabet scale \(u_{n,d}=d^2/\{n^2\log^2(en)\}\), without needing any crossed-cell evidence.
- The selector removes the larger of these two remainders at the benchmark level.
- In the 401(k) example, it uses direct crossed-cell evidence when strata are nearly homogeneous and rare-cell polynomial smoothing when heterogeneity is larger.

@figure phase-diagram: The diagram shows symbolic regions in the \(u_{n,d},\sigma^2\) plane where the polynomial branch, collision branch, and zero branch determine the selector benchmark.

---

## Lower Bounds

- The exact-homogeneity lower component comes from uniform-mass binary hard experiments.
- The radius component starts from a binary one-arm hard family.
- A hypothesis-independent channel attenuates binary differences by \(\sigma/2\).
- Scaling by \(M\) moves the source experiment into the real-outcome class.
- The target separation therefore contributes \(M^2\sigma^2\) times the rare-cell source difficulty.

@formal thm:radius-channel-converse-all-d

---

## Main Bracket

- The lower benchmark has three affirmative pieces: parametric sampling, exact-homogeneity collision, and radius-channel rare-cell difficulty.
- The upper benchmark is the selector risk from the polynomial, collision, and zero branches.
- The same \(n,d,M,\sigma,\epsilon\) index both sides of the statement.
- The bracket is finite-sample and all-alphabet.

@formal thm:two-sided-minimax-bracket-all-d

---

## Matched Regimes

- At exact homogeneity, the benchmark is \(M^2\{n^{-1}+\min(1,d/n^2)\}\).
- At radius two, the benchmark is the unrestricted large-alphabet scale.
- For every fixed positive radius, the selector benchmark is the minimax rate.
- Saturated alphabets and parametric-dominance elbows also give order matching.
- The residual shrinking-radius wedge is localized by the theorem.

@informal prop:endpoint-reductions-all-d: The exact-homogeneity and radius-two endpoints reduce to the expected collision and unrestricted large-alphabet rates.

@formal thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d

---

## Why It Is True

- For the upper bound, condition on the pilot split so heavy and light cells are fixed.
- Heavy cells use ordinary stratified mean contrasts under overlap and second moments.
- Light cells use polynomial approximation plus distinct-index factorial statistics to control bias and covariance.
- The collision branch decomposes into crossed-cell noise and uncrossed-cell bias.
- The radius bound controls the uncrossed-cell bias, and occupancy controls the random denominator.
- The selector inherits the smallest certified branch risk.

---

## Why the Converse Works

- Restricting the model to a hard subclass can only lower the statistician’s options.
- Exact homogeneous binary experiments transfer through the affine map and give the \(d/n^2\) collision baseline.
- Radius-channel alternatives keep the data-processing distance inherited from the binary source.
- The channel makes every ATE separation proportional to \(M\sigma\).
- Squaring that separation gives the radius-sensitive lower term.
- Combining the independent lower mechanisms yields the bracket’s lower benchmark.

---

## Also in the Paper

@informal thm:frontier-upper: The restricted-range selector upper bound gives the same frontier rate under the earlier finite-range calibration.

@informal thm:robust-upper-construction-resolution: The restricted robust construction supplies the polynomial and collision branch risks before all-alphabet packaging.

@informal thm:radius-channel-converse: The restricted radius-channel converse gives the same radius-sensitive lower mechanism on the finite-range regime.

@informal thm:two-sided-minimax-bracket: The restricted two-sided bracket combines the finite-range upper and lower benchmarks.

@informal prop:endpoint-reductions: The restricted endpoint algebra identifies exact-homogeneity and radius-two rates.

@informal thm:fixed-interior-tightness-and-shrinking-radius-gap: The restricted regime theorem localizes the same fixed-radius and elbow matching structure.

@informal thm:published-binary-collision-comparison: The published binary collision remainder is algebraically compared with the selector remainder.

---

## Takeaways

- The paper gives a finite-sample minimax bracket for scalar ATE estimation with many discrete adjustment cells.
- The estimators are constructive, clipped, and valid for real outcomes under conditional second moments.
- The known-radius selector balances the rare-cell polynomial scale against the crossed-cell collision scale.
- The lower bound embeds binary hard experiments into the same real-outcome class.
- The resulting phase diagram explains when \(n\), \(d\), and \(\sigma\) make the selector benchmark the minimax rate.
