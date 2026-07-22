# Title

**Graph-Adaptive Bernoulli Design for Bipartite Interference**

**Contribution statement.** The paper characterizes graph-adaptive heterogeneous Bernoulli designs for bipartite experiments, establishes design-based Hájek inference, and provides a bounded-degree approximation certificate for a tractable surrogate design.

# Notation

notation_gaps: $I_n$=intervention-unit set requires an anchored definition, $O_n$=outcome-unit set requires an anchored definition, $m_n$=number of intervention units requires an anchored definition, $n$=number of outcome units requires an anchored definition, $G_n$=bipartite graph requires an anchored definition, $N_i(G_n)$=outcome neighborhood requires an anchored definition, $d_i$=outcome-side degree requires an anchored definition, $s_k$=intervention-side degree or dispersion quantity requires an anchored definition, $\Delta_n$=outcome-overlap dependency degree requires an anchored definition, $S_{ij}(G_n)$=shared intervention neighborhood requires an anchored definition, $h_k(G_n)$=surrogate weight requires an anchored definition, $Z$=assignment vector requires an anchored definition, $T_i(Z)$=all-treated exposure indicator requires an anchored definition, $C_i(Z)$=all-control exposure indicator requires an anchored definition, $\pi_i^1(p)$=all-treated exposure probability requires an anchored definition, $\pi_i^0(p)$=all-control exposure probability requires an anchored definition, $Y_i(z_{N_i})$=potential-outcome schedule requires an anchored definition, $Y_i^1$=all-treated potential outcome requires an anchored definition, $Y_i^0$=all-control potential outcome requires an anchored definition, $Y_i^{\mathrm{obs}}$=observed outcome requires an anchored definition, $\mu_1$=mean all-treated potential outcome requires an anchored definition, $\mu_0$=mean all-control potential outcome requires an anchored definition, $\tau_n$=finite-population estimand requires an anchored definition, $r_{ij}^1(G_n,p)$=treated exposure covariance load requires an anchored definition, $r_{ij}^0(G_n,p)$=control exposure covariance load requires an anchored definition, $r_{ij}^{10}(G_n)$=cross-exposure covariance load requires an anchored definition, $\mathbf 1\{\cdot\}$=indicator operator requires an anchored definition, $\operatorname{argmin}$=minimizer correspondence requires an anchored definition, $\operatorname{Hess}$=Hessian operator requires an anchored definition, $e_k$=coordinate vector requires an anchored definition, $\rho$=homogeneous assignment rate requires an anchored definition, $p^{\mathrm{hom}}$=homogeneous feasible design requires an anchored definition, $\Delta_g$=gradient-score spread requires an anchored definition, $\eta_{\mathrm{box}}$=box-direction radius requires an anchored definition, $a,b$=extremal gradient-score indices require an anchored definition, $\lambda_n,\nu_{k,n}^+,\nu_{k,n}^-$=KKT multipliers require an anchored definition, $z_{1-\alpha_{\mathrm{cov}}/2}$=standard-normal quantile requires an anchored definition, $c_{\mathrm{disp}},C_{\mathrm{disp}}$=dispersion constants require an anchored definition.

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
| positivity floor | $\epsilon$ | common lower and upper margin for assignment probabilities | def:feasible-designs |
| assignment budget | $B_n$ | required sum of intervention assignment probabilities | def:feasible-designs |
| feasible design class | $\mathcal P_{n,B_n,\epsilon}$ | budget-balanced probability vectors satisfying positivity constraints | def:feasible-designs |
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
| directional modulus | $L_{ab}$ | feasible-segment supremum of the directional second derivative of $V_{\mathrm{env}}/4$ along $e_b-e_a$ | synth_1 |
| coordinate vector | $e_k$ | Euclidean basis vector associated with intervention unit $k$ | notation_gaps |
| Hessian operator | $\operatorname{Hess}$ | matrix of second derivatives of the displayed objective | notation_gaps |
| equality multiplier | $\lambda_n$ | multiplier for the assignment-budget equality constraint | notation_gaps |
| upper box multiplier | $\nu_{k,n}^+$ | nonnegative multiplier for the upper probability constraint | notation_gaps |
| lower box multiplier | $\nu_{k,n}^-$ | nonnegative multiplier for the lower probability constraint | notation_gaps |
| outcome-degree bound | $\bar d$ | uniform upper bound on outcome-neighborhood sizes | ass:bounded-outcome-degree |
| dependency-degree bound | $\bar D$ | uniform upper bound on outcome-overlap dependency | ass:bounded-overlap-dependency |
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

This section defines the finite-population bipartite experiment, feasible heterogeneous Bernoulli designs, exposure-weighted Hájek estimator, variance objects, and graph-only optimization criteria, then states the regularity conditions for large-sample inference. It opens with one diagram displaying the bipartite graph and its induced outcome-overlap graph, uses the notation table to distinguish $s_k$, $d_i$, $S_{ij}(G_n)$, and $\Delta_n$, and introduces the directional modulus on the feasible segment, including its computable supremum and boundedness on the positivity-restricted domain.

objs: ass:bipartite-interference, ass:independent-heterogeneous-bernoulli, ass:positivity-floor, ass:budget-balance, ass:bounded-outcomes, ass:bounded-outcome-degree, ass:bounded-overlap-dependency, ass:variance-nondegenerate, def:feasible-designs, def:hajek-denominators, def:hetero-hajek-estimator, def:first-order-linearization, def:variance-scale, def:graph-envelope, def:optimal-design, def:kkt-gradient, def:conservative-variance-estimator, def:surrogate-design, def:approximation-ratio, synth_1

bib: HudgensHalloran2008, LiuHudgens2014, AronowSamii2017GeneralInterference, Leung2019ApproxNeighborhoodInterference, ZiglerPapadogeorgou2018, DoudchenkoEtAl2020BipartiteDesign, ChattopadhyayImaiZubizarreta2023GeneralizedNetwork, LuShiFangZhangDing2025BipartiteDesign

## section: Main results

This section presents the heterogeneous overlap variance representation, convex graph-envelope design problem and KKT characterization, asymptotic normality and conservative Wald inference based on the deterministic conservative variance-scale bound, strict separation from homogeneous assignment, and the bounded-degree surrogate certificate.

objs: prop:homogeneous-reduction, thm:hetero-envelope, thm:convex-design, thm:hetero-clt, thm:postdesign-wald, thm:heterogeneity-separation, thm:surrogate-certificate

bib: Hajek1964, AronowSamii2017GeneralInterference, BasseAiroldi2018, SavjeAronowHudgens2021, LuShiFangZhangDing2025BipartiteDesign, HarshawMiddletonSavje2021OptimizedVariance, ParkWager2026NeymanJackknife

## section: Discussion and extensions

This section interprets the graph-only design criterion relative to clustering and outcome-model-based approaches. It records the first-order dispersion claim only as a disproved conjecture; its negative construction uses a separate index $r$ and does not identify that index with outcome-population size.

objs: thm:dispersion-certificate-unbounded

bib: EcklesKarrerUgander2017, UganderYin2020RandomizedGCR, BrennanMirrokniPougetAbadie2022ClusterBipartite, EichhornKhanUganderYu2024LowOrderClusteredDesigns, HarshawSavjeEisenstatMirrokniPougetAbadie2021BipartiteERL, Viviano2026NetworkDesign

## section: Appendix with proofs and auxiliary lemmas

This appendix supplies proofs and auxiliary probability arguments, including denominator positivity and the bounded-degree dependency-graph CLT. It ends with a verification note consolidating the Lean machine-checking scope for the finite-design and Bernoulli-randomization components, while identifying the bipartite graph scaffolding and stated asymptotic regularity conditions as inputs to the formal development.

objs: lem:denominator-positivity, lem:bounded-degree-dependency-clt

bib: Neyman1923, HorvitzThompson1952, Hajek1964, LiuHudgens2014, LuShiFangZhangDing2025BipartiteDesign
