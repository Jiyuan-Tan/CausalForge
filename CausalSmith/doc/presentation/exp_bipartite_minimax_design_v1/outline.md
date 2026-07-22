# Title

**Graph-Adaptive Bernoulli Design for Bipartite Interference**

**Contribution statement.** The paper characterizes heterogeneous Bernoulli probability designs for bipartite experiments, establishes design-based Hájek inference, and provides a bounded-degree approximation certificate for a tractable surrogate design.

# Notation

notation_gaps: $I_n$=anchored definition of intervention-unit set, $O_n$=anchored definition of outcome-unit set, $m_n$=anchored definition of intervention-population size, $n$=anchored definition of outcome-population size, $G_n$=anchored definition of bipartite graph, $N_i(G_n)$=anchored definition of outcome neighborhood, $d_i$=anchored definition of outcome-side degree, $s_k$=anchored definition of intervention-side degree quantity, $\Delta_n$=anchored definition of outcome-overlap dependency degree, $S_{ij}(G_n)$=anchored definition of shared intervention neighborhood, $h_k(G_n)$=anchored definition of surrogate weight, $Z$=anchored definition of assignment vector, $\epsilon$=anchored definition of positivity floor, $B_n$=anchored definition of assignment budget, $T_i(Z)$=anchored definition of all-treated exposure indicator, $C_i(Z)$=anchored definition of all-control exposure indicator, $\pi_i^1(p)$=anchored definition of all-treated exposure probability, $\pi_i^0(p)$=anchored definition of all-control exposure probability, $Y_i(z_{N_i})$=anchored definition of potential-outcome schedule, $Y_i^1$=anchored definition of all-treated potential outcome, $Y_i^0$=anchored definition of all-control potential outcome, $Y_i^{\mathrm{obs}}$=anchored definition of observed outcome, $\mu_1$=anchored definition of all-treated potential-outcome mean, $\mu_0$=anchored definition of all-control potential-outcome mean, $\tau_n$=anchored definition of finite-population estimand, $r_{ij}^1(G_n,p)$=anchored definition of treated exposure covariance load, $r_{ij}^0(G_n,p)$=anchored definition of control exposure covariance load, $r_{ij}^{10}(G_n)$=anchored definition of cross-exposure covariance load, $\rho$=anchored definition of homogeneous assignment rate, $p^{\mathrm{hom}}$=anchored definition of homogeneous feasible design, $\Delta_g$=anchored definition of gradient-score spread, $\eta_{\mathrm{box}}$=anchored definition of box-direction radius, $a,b$=anchored definition of extremal gradient-score indices, $L_{ab}$=anchored definition of directional second-order modulus, $e_k$=anchored definition of coordinate vector, $\operatorname{Hess}$=anchored definition of Hessian operator, $\lambda_n,\nu_{k,n}^+,\nu_{k,n}^-$=anchored definition of KKT multipliers, $\alpha_{\mathrm{cov}}$=anchored definition of coverage level, $z_{1-\alpha_{\mathrm{cov}}/2}$=anchored definition of standard-normal quantile, $\mathbf 1\{\cdot\}$=anchored definition of indicator operator, $\operatorname{argmin}$=anchored definition of minimizer correspondence, $c_{\mathrm{disp}},C_{\mathrm{disp}}$=anchored definition of dispersion constants.

| note symbol | paper notation | defining property in one phrase | home |
|---|---|---|---|
| intervention units | $I_n$ | finite set of units receiving independently randomized interventions | notation_gaps |
| outcome units | $O_n$ | finite set of units at which outcomes are measured | notation_gaps |
| intervention-population size | $m_n$ | cardinality of the intervention-unit set | notation_gaps |
| outcome-population size | $n$ | cardinality of the outcome-unit set in the asymptotic sequence | notation_gaps |
| bipartite graph | $G_n$ | known graph linking intervention and outcome units | notation_gaps |
| outcome neighborhood | $N_i(G_n)$ | intervention units adjacent to outcome unit $i$ | notation_gaps |
| outcome-side degree | $d_i$ | cardinality of $N_i(G_n)$ | notation_gaps |
| intervention-side degree | $s_k$ | graph-derived intervention-unit degree quantity used in dispersion summaries | notation_gaps |
| shared neighborhood | $S_{ij}(G_n)$ | intervention units jointly adjacent to outcome units $i$ and $j$ | notation_gaps |
| overlap dependency degree | $\Delta_n$ | maximum degree of the induced outcome-overlap graph | notation_gaps |
| surrogate weight | $h_k(G_n)$ | graph-derived coefficient in the additive surrogate objective | notation_gaps |
| assignment vector | $Z=(Z_k)_{k\in I_n}$ | vector of intervention assignments | notation_gaps |
| assignment probability vector | $p=(p_k)_{k\in I_n}$ | intervention-specific Bernoulli assignment probabilities | def:feasible-designs |
| positivity floor | $\epsilon$ | common lower and upper margin for assignment probabilities | notation_gaps |
| assignment budget | $B_n$ | required sum of intervention assignment probabilities | notation_gaps |
| feasible design class | $P_{n,B_n,\epsilon}$ | budget-balanced probability vectors satisfying positivity constraints | def:feasible-designs |
| treated exposure indicator | $T_i(Z)$ | indicator that all interventions in $N_i(G_n)$ are treated | notation_gaps |
| control exposure indicator | $C_i(Z)$ | indicator that all interventions in $N_i(G_n)$ are untreated | notation_gaps |
| treated exposure probability | $\pi_i^1(p)$ | design probability of all-treated exposure for outcome unit $i$ | notation_gaps |
| control exposure probability | $\pi_i^0(p)$ | design probability of all-control exposure for outcome unit $i$ | notation_gaps |
| potential-outcome schedule | $Y_i(z_{N_i})$ | fixed outcome of unit $i$ under its neighborhood assignment vector | notation_gaps |
| all-treated potential outcome | $Y_i^1$ | potential outcome under all-treated exposure | notation_gaps |
| all-control potential outcome | $Y_i^0$ | potential outcome under all-control exposure | notation_gaps |
| observed outcome | $Y_i^{\mathrm{obs}}$ | realized potential outcome under the assigned neighborhood exposure | notation_gaps |
| treated potential-outcome mean | $\mu_1$ | finite-population mean of all-treated potential outcomes | notation_gaps |
| control potential-outcome mean | $\mu_0$ | finite-population mean of all-control potential outcomes | notation_gaps |
| finite-population estimand | $\tau_n$ | difference between all-treated and all-control finite-population means | notation_gaps |
| treatment denominator | $D_1(p,Z)$ | inverse-probability-weighted treated-exposure count | def:hajek-denominators |
| control denominator | $D_0(p,Z)$ | inverse-probability-weighted control-exposure count | def:hajek-denominators |
| Hájek estimator | $\widehat\tau_H(p)$ | difference of normalized treated and control exposure-weighted means | def:hetero-hajek-estimator |
| linearization summand | $\eta_i(p,Z)$ | centered first-order contribution of outcome unit $i$ | def:first-order-linearization |
| asymptotic variance scale | $\sigma_{G_n,p}^2(Y)$ | scaled design variance of the linearization average | def:variance-scale |
| treated covariance load | $r_{ij}^1(G_n,p)$ | graph-and-design load for paired treated exposures | notation_gaps |
| control covariance load | $r_{ij}^0(G_n,p)$ | graph-and-design load for paired control exposures | notation_gaps |
| cross-exposure covariance load | $r_{ij}^{10}(G_n)$ | graph-only load for paired treatment-control exposures | notation_gaps |
| graph envelope | $V_{\mathrm{env}}(G_n,p)$ | graph-only upper envelope for the variance scale | def:graph-envelope |
| envelope-optimal design | $p_n^*(G_n)$ | feasible minimizer of the graph envelope | def:optimal-design |
| envelope gradient score | $g_k(G_n,p)$ | partial derivative of one quarter of the graph envelope | def:kkt-gradient |
| conservative variance-scale bound | $\widehat V_{\mathrm{cons}}(G_n,p)$ | deterministic graph-only conservative bound for the variance scale | def:conservative-variance-estimator |
| surrogate design | $p_n^{\deg}(G_n)$ | feasible minimizer of the additive degree-surrogate objective | def:surrogate-design |
| approximation ratio | $\alpha_{\mathrm{cert}}(G_n)$ | surrogate-envelope value relative to the envelope optimum under the zero-loss convention | def:approximation-ratio |
| homogeneous assignment rate | $\rho$ | budget share $B_n/m_n$ | notation_gaps |
| homogeneous feasible design | $p^{\mathrm{hom}}$ | design assigning probability $\rho$ to every intervention unit | notation_gaps |
| gradient-score spread | $\Delta_g$ | maximum minus minimum homogeneous-point envelope gradient score | notation_gaps |
| box-direction radius | $\eta_{\mathrm{box}}$ | largest symmetric budget-feasible perturbation around $\rho$ | notation_gaps |
| directional modulus | $L_{ab}$ | supremum directional second derivative of $V_{\mathrm{env}}/4$ along $e_b-e_a$ over the feasible class | notation_gaps |
| coordinate vector | $e_k$ | Euclidean basis vector associated with intervention unit $k$ | notation_gaps |
| Hessian operator | $\operatorname{Hess}$ | matrix of second derivatives of the displayed objective | notation_gaps |
| equality multiplier | $\lambda_n$ | multiplier for the assignment-budget equality constraint | notation_gaps |
| upper box multiplier | $\nu_{k,n}^+$ | nonnegative multiplier for the upper probability constraint | notation_gaps |
| lower box multiplier | $\nu_{k,n}^-$ | nonnegative multiplier for the lower probability constraint | notation_gaps |
| outcome-degree bound | $\bar d$ | uniform upper bound on outcome-neighborhood sizes | ass:bounded-outcome-degree |
| dependency-degree bound | $\bar D$ | uniform upper bound on outcome-overlap dependency | ass:bounded-overlap-dependency |
| auxiliary summands | $X_{n,i}$ | centered random variables in the dependency-graph CLT | lem:bounded-degree-dependency-clt |
| auxiliary summand bound | $M$ | uniform absolute bound in the dependency-graph CLT | lem:bounded-degree-dependency-clt |
| auxiliary dependency degree | $D$ | maximum dependency-graph degree in the auxiliary CLT | lem:bounded-degree-dependency-clt |
| auxiliary variance sequence | $v_n$ | variance of the auxiliary centered sum | lem:bounded-degree-dependency-clt |
| auxiliary variance-growth constant | $c$ | eventual linear lower-bound constant for $v_n$ | lem:bounded-degree-dependency-clt |
| coverage level | $\alpha_{\mathrm{cov}}$ | nominal two-sided Wald noncoverage probability | notation_gaps |
| normal critical value | $z_{1-\alpha_{\mathrm{cov}}/2}$ | corresponding standard-normal quantile | notation_gaps |
| indicator operator | $\mathbf 1\{\cdot\}$ | function equal to one when its condition holds and zero otherwise | notation_gaps |
| minimizer correspondence | $\operatorname{argmin}$ | set of objective minimizers over a stated feasible set | notation_gaps |
| certificate constant | $C(\epsilon,\bar d)$ | bounded-degree upper bound for the surrogate approximation ratio | thm:surrogate-certificate |
| dispersion constants | $c_{\mathrm{disp}},C_{\mathrm{disp}}$ | thresholds in the disproved first-order dispersion conjecture | notation_gaps |

# Sections

## section: Abstract

Planned last. It will state the graph-adaptive Bernoulli design problem, the design-based inference results, and the bounded-degree surrogate certificate without presenting formal statements.

objs:

bib: LuShiFangZhangDing2025BipartiteDesign, ChattopadhyayImaiZubizarreta2023GeneralizedNetwork

## section: Introduction

Planned last. It will motivate probability design in bipartite interference experiments, position the paper relative to homogeneous Bernoulli and clustered-design approaches, state the substantive contributions, and include one factual sentence directing readers to the appendix verification note.

objs:

bib: Neyman1923, HorvitzThompson1952, Hajek1964, ZiglerPapadogeorgou2018, LuShiFangZhangDing2025BipartiteDesign, BrennanMirrokniPougetAbadie2022ClusterBipartite, HarshawSavjeEisenstatMirrokniPougetAbadie2021BipartiteERL, UganderYin2020RandomizedGCR, Viviano2026NetworkDesign

## section: Setup and assumptions

This section defines the finite-population bipartite experiment, feasible heterogeneous Bernoulli designs, exposure-weighted Hájek estimator, variance objects, and graph-only optimization criteria, then states the regularity conditions for large-sample inference. It opens with one diagram displaying the bipartite graph and its induced outcome-overlap graph, uses the notation table to distinguish $s_k$, $d_i$, $S_{ij}(G_n)$, and $\Delta_n$, and introduces the directional-modulus notation and its feasible-domain interpretation before the main-results display that uses it.

objs: ass:bipartite-interference, ass:independent-heterogeneous-bernoulli, ass:positivity-floor, ass:budget-balance, ass:bounded-outcomes, ass:bounded-outcome-degree, ass:bounded-overlap-dependency, ass:variance-nondegenerate, def:feasible-designs, def:hajek-denominators, def:hetero-hajek-estimator, def:first-order-linearization, def:variance-scale, def:graph-envelope, def:optimal-design, def:kkt-gradient, def:conservative-variance-estimator, def:surrogate-design, def:approximation-ratio

bib: HudgensHalloran2008, LiuHudgens2014, AronowSamii2017GeneralInterference, Leung2019ApproxNeighborhoodInterference, ZiglerPapadogeorgou2018, DoudchenkoEtAl2020BipartiteDesign, ChattopadhyayImaiZubizarreta2023GeneralizedNetwork, LuShiFangZhangDing2025BipartiteDesign

## section: Main results

This section presents the heterogeneous overlap variance representation, the convex graph-envelope design problem and KKT characterization, asymptotic normality, design-stage conservative Wald coverage based on a deterministic variance-scale bound, strict separation from homogeneous assignment, and positive and negative results for the surrogate certificate. Immediately before the heterogeneity-separation theorem, it displays the directional-modulus formula, its feasible-domain supremum, and the positivity-domain basis for finite application-specific bounds.

objs: prop:homogeneous-reduction, thm:hetero-envelope, thm:convex-design, thm:hetero-clt, thm:postdesign-wald, thm:heterogeneity-separation, thm:surrogate-certificate, thm:dispersion-certificate-unbounded

bib: Hajek1964, AronowSamii2017GeneralInterference, BasseAiroldi2018, SavjeAronowHudgens2021, LuShiFangZhangDing2025BipartiteDesign, HarshawMiddletonSavje2021OptimizedVariance, ParkWager2026NeymanJackknife

## section: Discussion and extensions

This section interprets the graph-only design criterion relative to clustering and outcome-model-based approaches, including the implications of the bounded-degree certificate and the immediately preceding disproved first-order dispersion conjecture. It identifies extensions without treating them as delivered results.

objs:

bib: EcklesKarrerUgander2017, UganderYin2020RandomizedGCR, BrennanMirrokniPougetAbadie2022ClusterBipartite, EichhornKhanUganderYu2024LowOrderClusteredDesigns, HarshawSavjeEisenstatMirrokniPougetAbadie2021BipartiteERL, Viviano2026NetworkDesign

## section: Appendix with proofs and auxiliary lemmas

This appendix supplies detailed proofs and auxiliary probability arguments, including denominator positivity and the bounded-degree dependency-graph CLT; the main text retains only proof sketches where they convey design intuition. It ends with a verification note consolidating the Lean machine-checking scope for the finite-design and Bernoulli-randomization components, while identifying the bipartite graph scaffolding and stated asymptotic regularity conditions as inputs to the formal development.

objs: lem:denominator-positivity, lem:bounded-degree-dependency-clt

bib: Neyman1923, HorvitzThompson1952, Hajek1964, LiuHudgens2014, LuShiFangZhangDing2025BipartiteDesign
