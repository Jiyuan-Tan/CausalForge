# panel_ppml_forbidden_comparison — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / causalsmith bridge._

## Environment (S)

**S-1 (Deterministic triangular-array collapsed cohort-by-time P…).** Deterministic triangular-array collapsed cohort-by-time Poisson-projection world: cohorts g in C encoded as WithTop (Fin T) (never-treated = top), calendar periods t in Fin T, cohort-time cells carry positive masses q_gt / q_gtN, untreated cohort means B_gt = bar_b_g*exp(gamma_t0), observed cohort means m_gt(delta) = B_gt*exp(D_gt*delta_gt), collapsed regressor r_gt in R^(|C|+T), and the Poisson pseudo-criteria L_Nc / L. This is the ambient world of every headline statement (all six operate on the limiting/finite-array collapsed quantities). — bypass-justified: Causalean has NO Poisson/PPML world (grep 'Poisson|PPML|expMean|multiplicative' over Causalean/ returns only unrelated concentration/minimax/ML modules; grep over Causalean/Panel/ returns 0). The nonlinear pseudo-likelihood criteria L_Nc/L, their unique maximizers, strict concavity/coercivity, and the fitted means mu_star are all bespoke finite-dimensional convex analysis built over Mathlib (Fin, WithTop, Real.exp, StrictConcaveOn, IsCompact.exists_isMaxOn). REUSED building blocks: the cohort/never-treated encoding is Causalean.Panel.AdoptionPath (WithTop (Fin T), le/lt/isNeverTreated, verified present); the mean-weighted-FWL residual layer (see def:weighted-fwl-residual) reuses Causalean.Panel.Weighted.WeightedSupport.{tildeX,Q_XX,thetaHat,RankCondition} (Subspace/FWL), and thm:sharp additionally reuses WeightedSupport.scalar_fwl_of_normalEqs (ScalarFWL.lean:74) for the normal-equation FWL coefficient ratio in the IFT derivative step. No single Causalean structure realizes this world, so the world skeleton itself is define-local with those helpers imported.
**required modules.** Causalean.Panel.AdoptionPath, Causalean.Panel.Weighted.Support, Causalean.Panel.Weighted.Subspace, Causalean.Panel.Weighted.FWL, Causalean.Panel.Weighted.ScalarFWL

**S-2 (Finite-N unit-and-time fixed-effect Poisson panel with po…).** Finite-N unit-and-time fixed-effect Poisson panel with potential outcomes: units i in Fin N with deterministic cohort labels G_i in C (n_gN units per cohort), unit baselines b_iN>0, unit-time regressor v_itN in R^(N+T) (intercept, unit-FE, time-FE, treatment D_it), unit-time observed mean m_itN(delta)=b_iN*exp(gamma_t0+D_it*delta_{G_i,t}), the unit-FE Poisson criterion L_N and its beta coordinate beta_Nstar, and the extended-MLE sample coefficient hat_beta_N. Potential outcomes Y_it(d) and the array sampling law Pcal_N with expectation E_Pcal_N enter ONLY through the two mean-defining assumptions. — bypass-justified: honest_scope disclaims all sampling/inference content (no fixed-T consistency, influence function, variance, or coverage claim). The probability layer is therefore not needed at theorem level: the two PO assumptions (ass:unit-untreated-exponential-mean, ass:proportional-effects) pin E_Pcal_N[Y_it(d)] to the deterministic mean m_itN(delta), and every downstream statement consumes m_itN, not the law. E_Pcal_N is treated as an abstract linear expectation functional / the means as primitives over Mathlib (no MeasureTheory import required). REUSED: unit-time assignment/history from Causalean.Panel.PO.TreatmentPath and cohort encoding from Causalean.Panel.AdoptionPath. Causalean's PO probability spaces are at a heavier (measure-theoretic) abstraction than this purely-algebraic mean-level statement, so binding is define-local.
**required modules.** Causalean.Panel.PO.TreatmentPath, Causalean.Panel.AdoptionPath

## Assumptions (A)

**A-1 (assumption).** For every N>=|C| and every g in C, n_gN is positive and n_gN/N converges to pi_g in (0,1).

**A-2 (assumption).** E_Pcal_N[Y_it(0)]=b_iN exp(gamma_t0) for every i and t, with gamma_10=0.

**A-3 (assumption).** For every g in C, the deterministic triangular-array average bar_b_gN=n_gN^(-1)sum_{i in I_gN}b_iN converges to bar_b_g in (0,infinity).

**A-4 (assumption).** E_Pcal_N[Y_it(1)]=E_Pcal_N[Y_it(0)] exp(delta_{G_i,t}) for every i and t with D_it=1.

**A-5 (assumption).** sum_{g in C}sum_{t=1}^T q_gt r_gt r_gt' is positive definite.

**A-6 (assumption).** C contains {2,3,4,infinity}.

**A-7 (assumption).** delta_gt>0 for every (g,t) with D_gt=1.

## Definitions (P)

**P-1 (beta_Nstar(delta) is the last coordinate of argmax_{theta…).** beta_Nstar(delta) is the last coordinate of argmax_{theta_N in R^(N+T)} L_N(theta_N;delta), where L_N(theta_N;delta)=(NT)^(-1)sum_{i=1}^Nsum_{t=1}^T[m_itN(delta)v_itN'theta_N-exp(v_itN'theta_N)].

**P-2 (theta_star(delta)=argmax_{theta in R^(|C|+T)}L(theta;delt…).** theta_star(delta)=argmax_{theta in R^(|C|+T)}L(theta;delta), L(theta;delta)=sum_{g in C}sum_{t=1}^Tq_gt[m_gt(delta)r_gt'theta-exp(r_gt'theta)], beta_star(delta)=the last coordinate of theta_star(delta), and mu_star_gt(delta)=exp(r_gt'theta_star(delta)).

**P-3 (Let A_N be the argmax of sum_{i=1}^Nsum_{t=1}^T[Y_it v_it…).** Let A_N be the argmax of sum_{i=1}^Nsum_{t=1}^T[Y_it v_itN'theta_N-exp(v_itN'theta_N)] over unit-effect coordinates in R union {-infinity}, time-effect coordinates in R with the period-1 normalization, and beta in R, using exp(-infinity)=0. If A_N contains a point with finite beta, hat_beta_N is its beta coordinate after choosing the finite (time-effect,beta) coordinates of smallest Euclidean norm; otherwise hat_beta_N=0.

**P-4 (rho_star(delta)=argmin_{rho in R^(|C|+T-1)}sum_{g in C}su…).** rho_star(delta)=argmin_{rho in R^(|C|+T-1)}sum_{g in C}sum_{t=1}^Tq_gt mu_star_gt(delta)[D_gt-X_gt'rho]^2 and Wtilde_gt(delta)=D_gt-X_gt'rho_star(delta).

**P-5 (R_T={((pi_g)_{g in C},(B_gt)_{g in C,1<=t<=T},(delta_gt)_…).** R_T={((pi_g)_{g in C},(B_gt)_{g in C,1<=t<=T},(delta_gt)_{(g,t):D_gt=1}): C contains {2,3,4,infinity}; B_gt=bar_b_g exp(gamma_t0); delta_gt>0 whenever D_gt=1; sum_{g,t}q_gt r_gt r_gt' is positive definite; and beta_star(delta)<0}.

**P-6 (W4 is the cofinal triangular subsequence indexed by N=4m,…).** W4 is the cofinal triangular subsequence indexed by N=4m, m=1,2,..., with T=4, C={2,3,4,infinity}, n_2N=n_3N=n_4N=n_infinityN=m, b_iN=1 for every i, gamma_t0=0 for every t, delta_gt=log(101/100) for every treated cell except delta_2,4=log(4).

**P-7 (Starting from the limiting collapsed score equations sum_…).** Starting from the limiting collapsed score equations sum_{g,t}q_gt X_gt[m_gt(delta)-mu_star_gt(delta)]=0 and sum_{g,t}q_gt D_gt[m_gt(delta)-mu_star_gt(delta)]=0, eliminate the intercept, cohort, and time multipliers by their fitted row and column margins, then characterize the beta_star(delta)=0 zero-level set in pi_g=lim_N n_gN/N, B_gt, and delta_gt.

## Lemmas (L)

**L-1 (For every N, the unit-and-time-FE population projection i…).** For every N, the unit-and-time-FE population projection in def:unit-fe-population-projection has a unique beta_Nstar(delta). Its beta_Nstar(delta) equals the beta coordinate of the unique maximizer of L_Nc(theta;delta). Consequently, beta_Nstar(delta) converges to beta_star(delta). Thus within-cohort baseline heterogeneity (b_iN) enters the limiting unit-FE coefficient only through B_gtN=n_gN^(-1)sum_{i in I_gN}b_iN exp(gamma_t0).

**L-2 (The limiting projection theta_star(delta) is unique and s…).** The limiting projection theta_star(delta) is unique and satisfies sum_{g in C}sum_{t=1}^Tq_gt r_gt[m_gt(delta)-mu_star_gt(delta)]=0.

## Theorems (T)

### T-block: t1 — For the limiting coefficient beta_star(delta) of the unit…
**Statement.** For the limiting coefficient beta_star(delta) of the unit-and-time-FE Poisson projection, at every delta satisfying the assumptions and for every treated cell (k,s), beta_star(delta) is differentiable in delta_ks and d beta_star(delta)/d delta_ks=q_ks B_ks exp(delta_ks) Wtilde_ks(delta)/[sum_{g in C}sum_{t=1}^Tq_gt mu_star_gt(delta)Wtilde_gt(delta)^2]. The denominator is strictly positive. Hence sign{d beta_star(delta)/d delta_ks}=sign{Wtilde_ks(delta)}, and a treated cell is a forbidden comparison cell if and only if Wtilde_ks(delta)<0. Both Wtilde and its sign depend on delta through mu_star.

### T-block: t2 — The explicitly constructed W4 belongs to R_4
**Statement.** The explicitly constructed W4 belongs to R_4. In particular, every treated cell has a strictly positive proportional effect, the exceptional cell (2,4) has the largest effect, and beta_star(delta)<0. At b_iN=1 and delta_gt=0 for all treated cells, Wtilde_gt equals the matrix with rows g=2,3,4,infinity and columns t=1,2,3,4: [(-3,3,1,-1),(-1,-3,3,1),(1,-1,-3,3),(3,1,-1,-3)]/8. Thus Wtilde_2,4=-1/8 and d beta_star(delta)/d delta_2,4<0 at the homogeneous no-effect point; continuity gives an open positive-effect neighborhood in which increasing the late effect of the earliest cohort strictly lowers beta_star.

### T-block: t3 — If delta_gt=delta_0 for every treated cell, then beta_sta…
**Statement.** If delta_gt=delta_0 for every treated cell, then beta_star(delta)=delta_0 and mu_star_gt(delta)=B_gt exp(D_gt delta_0).

### T-block: t4 — For h_gt=pi_g B_gt exp(D_gt delta_gt), define R_g=sum_{t=…
**Statement.** For h_gt=pi_g B_gt exp(D_gt delta_gt), define R_g=sum_{t=1}^T h_gt, C_t=sum_{g in C}h_gt, M=sum_{g in C}sum_{t=1}^T h_gt, A=sum_{g in C}sum_{t=1}^T D_gt h_gt, and Phi=M A-sum_{g in C}sum_{t=1}^T D_gt R_g C_t. Then sign{beta_star(delta)}=sign(Phi). In particular beta_star(delta)=0 if and only if Phi=0, so the requested zero-level set is the finite primitive system Phi>=0 and -Phi>=0, with no pseudo-true intercept, cohort, or time multiplier retained; subject to the defining positive-effect, baseline, share, and rank restrictions, R_T is exactly Phi<0. In the T=4, C={2,3,4,infinity}, equal-share, unit-baseline subfamily having treated multiplier x>1 outside (2,4) and multiplier y>1 at (2,4), Phi=(5x^2+12x-2y-15)/16, so beta_star<0 if and only if y>(5x^2+12x-15)/2; at x=101/100 the sharp cutoff is 4441/4000, and W4 has y=4. Operationally, let H={(g,t):D_gt=1}, Bobs_gt=m_g1 m_infinity,t/m_infinity,1, Z=sum_H q_gt Bobs_gt, omega_gt=q_gt Bobs_gt/Z, tau_gt=m_gt/Bobs_gt-1, and PTT=sum_H omega_gt tau_gt. Under the multiplicative-parallel-trends and proportional-effect assumptions, Bobs_gt=B_gt, tau_gt=exp(delta_gt)-1, every omega_gt is positive and the weights sum to one, and PTT=(sum_H q_gt m_gt)/(sum_H q_gt Bobs_gt)-1. Thus with positive effects, Phi<0 implies beta_star<0<PTT: Phi diagnoses the pooled PPML coefficient as an unsafe causal summary, while granular tau_gt and their counterfactual-share PTT form a distinct identified causal target, not a correction or reinterpretation of beta_star. This population result makes no fixed-T sampling or inference claim for hat_beta_N.
