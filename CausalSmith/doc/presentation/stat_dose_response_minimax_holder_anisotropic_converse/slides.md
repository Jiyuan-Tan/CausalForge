# Dose-Response Lower Bounds at an Interior Dose

Under Hölder smoothness, local positivity, bounded outcomes, and strict baseline slack, the minimax MSE for the interior dose-response partial mean is at least \(n^{-2\alpha/(2\alpha+1)}\) for every fixed treatment-density smoothness \(\beta>0\).

---

## The lower floor is the treatment-regression floor

- The target is the dose-response partial mean \(\theta_P(t_0)\), the covariate average of the conditional mean at a fixed interior dose.
- The paper studies worst-case mean-squared error over one Hölder observed-data class.
- The lower bound is driven by how hard it is to learn the regression function in the treatment coordinate near \(t_0\).
- This obstruction remains present for every fixed \(\beta>0\).
- In the smooth-covariate regime \(d\le 4s\), the lower-bound exponent matches the published HOIF benchmark exponent.

@informal thm:sharp-pointwise-lower-bound: Under the stated smoothness, positivity, boundedness, and strict-slack conditions, the minimax risk is at least a constant times \(n^{-2\alpha/(2\alpha+1)}\).

---

## A fixed dose creates a local regression problem

- Think of a continuous treatment \(A\), such as hours of training, pollution exposure, or dosage.
- The object of interest is the mean outcome if everyone were evaluated at one interior dose \(t_0\).
- The data contain observations near \(t_0\), rather than repeated observations exactly at \(t_0\).
- Smoothness in the dose direction determines how much nearby doses can teach us about the target dose.
- Local positivity supplies enough observations near \(t_0\) for the comparison to be meaningful.

---

## The estimand averages a target-dose regression surface

- One observation is \(O=(Y,A,X)\).
- \(Y\) is the outcome, \(A\in[0,1]\) is the continuous treatment dose, and \(X\in[0,1]^d\) is the covariate vector.
- The regression \(\mu_P(a,x)\) is the conditional mean of \(Y\) at dose \(a\) and covariates \(x\).
- The target \(\theta_P(t_0)\) averages \(\mu_P(t_0,X)\) over the population covariate distribution.
- Under consistency, no unmeasured confounding, and local positivity, this observed-data partial mean has the causal dose-response interpretation.

@figure observed-target-pipeline: Box-and-arrow schematic showing observed data O=(Y,A,X) feeding the regression mu_P(a,x), evaluation at the interior dose t_0, and averaging over the covariate distribution to obtain theta_P(t_0).

---

## The model separates dose and covariate smoothness

- \(\alpha\) is the Hölder smoothness of the outcome regression in the dose direction near \(t_0\).
- \(\beta\) is the Hölder smoothness of the treatment density in the dose direction near \(t_0\).
- \(s\) is the Hölder smoothness in the covariate direction.
- \(d\) is the covariate dimension.
- The outcome is bounded, the dose is interior, and the treatment density is bounded below near \(t_0\).
- The strict-slack baseline gives room to build least favorable alternatives inside the same class.

@formal ass:local-positivity

---

## The target and risk criterion are fixed by the same class

- The paper studies the same Hölder dose class throughout, rather than changing the model between lower-bound and comparison statements.
- The minimax risk is the best possible worst-case mean-squared error over that class.
- The estimator may use the full iid sample and any measurable procedure.
- The risk is evaluated at the fixed interior dose \(t_0\).

@formal def:theta-functional

@formal def:minimax-risk

---

## The comparison benchmark has two candidate rates

- The published HOIF benchmark \(\rho_n\) is the larger of two rates.
- One term is the one-dimensional treatment-regression scale \(n^{-2\alpha/(2\alpha+1)}\).
- The other term depends on covariate dimension \(d\), covariate smoothness \(s\), and treatment smoothness \(\alpha\).
- The algebraic comparison asks which term governs \(\rho_n\) in each regime.

@formal def:published-hoif-rate

---

## The construction keeps density nuisances under control

- Mechanism: start from baseline densities \(p_0\) and \(q_0\) that sit strictly inside the model class.
- Mechanism: perturb the outcome regression locally in the dose coordinate near \(t_0\).
- Mechanism: keep the treatment-density part compatible with the \(\beta\)-smoothness restriction.
- Intuition: the alternatives change the target while remaining statistically hard to distinguish.
- The best possible testing separation is set by one-dimensional smoothing in the treatment direction.

@figure least-favorable-submodel: Box-and-arrow schematic showing slack baseline densities p_0 and q_0 feeding a local regression perturbation near t_0, which creates two hard-to-distinguish laws with separated theta_P(t_0).

---

## The all-\(\beta\) lower bound is the main result

@informal thm:sharp-pointwise-lower-bound: For every fixed \(\beta>0\), the minimax risk is at least a constant times the treatment-regression rate under the theorem's stated conditions.

@formal thm:sharp-pointwise-lower-bound

---

## Smooth covariates align the lower floor with \(\rho_n\)

- When \(d\le 4s\), covariate smoothness is high enough relative to dimension.
- In that regime, the benchmark \(\rho_n\) equals the treatment-regression term.
- The same lower-bound construction therefore gives a lower floor at the benchmark scale.
- In the running example, sufficiently smooth covariate adjustment leaves the local dose-regression difficulty as the binding obstruction.

@informal prop:oracle-regime-reduction: When \(d\le 4s\), the published benchmark equals \(n^{-2\alpha/(2\alpha+1)}\), and the same-class minimax risk is at least a constant times \(\rho_n\).

@formal prop:oracle-regime-reduction

---

## The smooth-covariate theorem packages the same comparison

@informal thm:sharp-minimax-smooth-covariate: Under the smooth-covariate condition \(d\le 4s\), the same-class minimax risk is at least \(n^{-2\alpha/(2\alpha+1)}\) up to a constant, and this rate equals \(\rho_n\).

@formal thm:sharp-minimax-smooth-covariate

---

## Low covariate smoothness separates the exponents

- When \(4s<d\), the published benchmark is governed by the covariate-smoothness term.
- The lower bound remains at the treatment-regression exponent.
- The theorem gives a strict algebraic ordering between the two exponents.
- This identifies the certified same-class lower floor in the low-covariate-smoothness regime.

@informal thm:frontier-bracket-deficient: When \(4s<d\), the minimax risk is at least a constant times the treatment-regression rate, while the published benchmark has a strictly smaller exponent.

@formal thm:frontier-bracket-deficient

---

## Also in the paper

@informal lem:oracle-dose-regression-lower-all-beta: The oracle lower-bound lemma gives the same \(n^{-2\alpha/(2\alpha+1)}\) minimax floor for every fixed \(\beta>0\).

@informal lem:rho-oracle-regime-algebra: In the regime \(d\le 4s\), the published benchmark \(\rho_n\) equals the treatment-regression rate.

@informal lem:rho-deficient-regime-algebra: In the regime \(4s<d\), the published benchmark equals the covariate-smoothness term and has exponent strictly below the oracle exponent.

@informal lem:published-upper-bound-cited: Under the cited Bonvini--Kennedy localized-regularity conditions, the HOIF estimator attains at most a constant times \(\rho_n\).

---

## The proof is a two-point testing argument

- Build two observed-data laws inside the same Hölder dose class.
- Make the two laws differ only through a local bump in the treatment regression near \(t_0\).
- Choose the bump width and height at the treatment-regression scale.
- The target values separate at the same scale as the bump height.
- The sample distributions remain close enough that Le Cam's bound converts testing difficulty into MSE risk.

---

## Why \(\beta\) does not change the lower exponent

- The perturbation uses the outcome regression as the hard direction.
- The treatment-density component is held within the slack baseline envelope.
- Higher or lower fixed \(\beta\) changes the constants and feasibility margins through the baseline condition.
- The exponent comes from the local dose-regression tradeoff governed by \(\alpha\).

---

## What the comparison says

- Bonvini--Kennedy supplies the published HOIF benchmark \(\rho_n\) under its localized-regularity conditions.
- This paper supplies a same-class minimax lower floor over the Hölder dose class.
- For \(d\le 4s\), the lower-floor exponent and the benchmark exponent coincide.
- For \(4s<d\), the paper gives the strict exponent comparison between the lower floor and the published benchmark.
- The rate story is therefore anchored by a same-class lower bound and an external upper-side benchmark.

---

## The contribution is a certified lower-rate benchmark

- The paper establishes the minimax lower bound \(n^{-2\alpha/(2\alpha+1)}\) for the interior dose-response partial mean under the stated Hölder, positivity, boundedness, and slack assumptions.
- The lower-bound exponent applies for every fixed treatment-density smoothness \(\beta>0\).
- The algebraic comparison with \(\rho_n\) identifies the smooth-covariate agreement regime \(d\le 4s\).
- The low-covariate-smoothness regime \(4s<d\) has a certified same-class treatment-regression lower floor and a strictly smaller published benchmark exponent.
