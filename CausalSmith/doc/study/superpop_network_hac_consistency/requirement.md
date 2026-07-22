# Substrate requirement: superpop_network_hac_consistency

## Goal
Prove that the network-HAC variance estimator `netHACVarEst` is consistent for the variance of
the network sum of a super-population locally-dependent field, so that the m-dependent network CLT
(`networkSum_clt`) can be turned into an asymptotically valid Wald confidence interval.

## Provides (API contract)
- `netHACVarEst_variance_tendsto_zero` — along a sequence of network fields `F n` in the CLT
  regime (bounded degree `m`, summand bound `B n → 0`, `card(V n)·(B n)³ → 0`, mean-zero, unit
  total variance), the *variance of the estimator* tends to zero:
  `Tendsto (fun n => variance (fun ω => (F n).netHACVarEst ω) (μ n)) atTop (𝓝 0)`.
- `netHAC_consistent` — the estimator converges in probability to the variance of the network
  sum: for every `ε > 0`, `(μ n)({ω | |(F n).netHACVarEst ω − variance (depSum (F n).X) (μ n)| ≥ ε}) → 0`
  (equivalently `… → 1` since the total variance is normalized to one in the CLT regime). Derived
  from `netHACVarEst_integral_eq_variance` (unbiasedness) + the variance bound via Chebyshev.
- (optional) `studentized_wald_coverage` — combine `networkSum_clt` with `netHAC_consistent` (and
  Slutsky) to give asymptotic standard-normal coverage of the studentized network sum.

## Statement / milestones
1. **Estimator-variance bound** (the substantive lemma; the analog of
   `Causalean.SteinMethod.DepGraph.var_nbhd_prod_le` one order up). For a single field `F` with
   bounded summands `|F.X i| ≤ B`, bounded degree `m`, the variance of
   `V̂ = ∑ᵢ ∑_{j ∈ N i} Xᵢ Xⱼ` is bounded by a polynomial in `m` times `card(V) · B⁴`:
   `variance (fun ω => F.netHACVarEst ω) μ ≤ C(m) · (card V) · B⁴`.
   Proof shape: expand the variance as a covariance double sum over PAIRS of products
   `(Xᵢ Xⱼ, Xₖ Xₗ)`; a covariance vanishes unless the two pairs are within graph distance (use the
   m-dependence / `DepGraph` separation, mirroring `cov_mul_nbhd_eq_zero`); count the surviving
   quadruples `≤ C(m)·card(V)` and bound each covariance by a constant multiple of `B⁴`.
2. **Variance → 0**: under `B n → 0` and `card(V n)·(B n)³ → 0` (hence `card(V n)·(B n)⁴ → 0` since
   `B n` is bounded), squeeze the bound from (1) to zero — giving
   `netHACVarEst_variance_tendsto_zero`.
3. **Consistency in probability**: combine (2) with the unbiasedness identity
   `netHACVarEst_integral_eq_variance` (`E[V̂] = variance (depSum X)`) via Chebyshev to get
   `netHAC_consistent`.
4. (optional) the studentized Wald-coverage corollary.

## Standard reference
Aronow & Samii (2017, *Ann. Appl. Stat.*) §variance-estimator consistency under interference;
Kojevnikov, Marmer & Song (2021, *J. Econometrics*) network-HAC / ψ-dependence; Chen & Shao (2004)
Stein dependency-graph moment bounds. The 2nd-order analog already in this repo is
`Causalean.SteinMethod.DepGraph.var_nbhd_prod_le`.

## Intended reuse
Completes the inference half of the M15 (super-population / network-dependence) motif: any
super-population network-dependent estimator that satisfies `networkSum_clt` gets an
asymptotically valid Wald interval from a *consistent* variance estimator. Consumed by future
Experimentation-cluster papers (network / spatial design-based-vs-model-based inference) and by a
later ψ-dependence (mixing) generalization.

## May assume / must derive
- **May assume** (the CLT regime, matching `networkSum_clt`): bounded summands `|F.X i| ≤ B n`,
  bounded degree `m`, `B n → 0`, `card(V n)·(B n)³ → 0`, mean-zero summands, unit total variance,
  and `MemLp (F.X i) 2 μ` (in fact bounded ⇒ all moments). The m-dependence is the structure
  field `NetworkDependence.indep`.
- **Must derive** (NOT assume): the estimator-variance bound (1) and the consistency (3). In
  particular do NOT assume the estimator concentrates or that `Var(V̂) → 0`; derive it from the
  m-dependence (independence beyond the network) and the bounded-degree counting, exactly as the
  2nd-order `var_nbhd_prod_le` is derived. Assuming consistency is the laundering failure mode.

## Non-goals
- The decaying-dependence / ψ-mixing CLT (where far nodes are only approximately independent) — a
  separate, larger substrate run; here the m-dependence (exact independence beyond the network) of
  `NetworkDependence` is taken as given.
- Building any random-graph / graphon object; the network is fixed (observed).
- A consistent estimator of the network structure itself.

## Known building blocks
- `Causalean.Experimentation.SuperPopulation.NetworkDependence` (the field), `.netHACVarEst`
  (the estimator), `.netHACVarEst_integral_eq_variance` (unbiasedness), `.toDepGraph`, `.nbhd`,
  `.mem_nbhd_iff`.
- `Causalean.SteinMethod.DepGraph` machinery: `var_nbhd_prod_le`, `cov_mul_nbhd_eq_zero`,
  `abs_cov_locProd_le`, `indepFun_leaveOut` (the tuple→pair independence `.comp` pattern).
- Mathlib: `variance_fun_sum`, `covariance_eq_sub`, `IndepFun.covariance_eq_zero`,
  `MemLp.integrable_mul`, `Finset.sum_subset`, `Finset.card_biUnion_le`, a Chebyshev /
  `meas_ge_le_variance_div_sq`-style inequality, `squeeze_zero`.
- For the in-probability statement, follow the convergence-mode convention used in
  `Causalean/Experimentation/DesignBased/InProb.lean` / `Causalean/Stat/Limit/`.

## Target module
`Causalean.Experimentation.SuperPopulation.HACConsistency`
