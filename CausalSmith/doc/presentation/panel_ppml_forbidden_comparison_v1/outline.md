# Title
**Forbidden Comparisons in Fixed-Effect Poisson Difference-in-Differences**

**Contribution statement.** The paper gives a deterministic population characterization of when a pooled fixed-effect PPML coefficient is negative under strictly positive proportional treatment effects in staggered-adoption designs.

# Notation
notation_gaps: $N$=triangular-array sample size has no anchored definition, $|\mathcal C|$=number of cohorts has no anchored definition, $\mathcal C$=cohort set has no anchored definition, $g$=cohort index has no anchored definition, $t$=calendar-period index has no anchored definition, $i$=unit index has no anchored definition, $n_{gN}$=cohort size in array $N$ has no anchored definition, $\pi_g$=limiting cohort share has no anchored definition, $E_{\mathcal P_N}$=expectation under the triangular-array law has no anchored definition, $Y_{it}(0)$=untreated potential outcome has no anchored definition, $Y_{it}(1)$=treated potential outcome has no anchored definition, $b_{iN}$=unit untreated baseline has no anchored definition, $\gamma_{t0}$=untreated time component has no anchored definition, $\bar b_{gN}$=within-cohort average baseline has no anchored definition, $I_{gN}$=cohort-$g$ unit set has no anchored definition, $\bar b_g$=limit of within-cohort average baseline has no anchored definition, $G_i$=unit cohort label has no anchored definition, $D_{it}$=unit-time treatment indicator has no anchored definition, $D_{gt}$=cohort-time treatment indicator has no anchored definition, $q_{gt}$=collapsed cohort-time cell mass has no anchored definition, $r_{gt}$=collapsed regressor vector has no anchored definition, $X_{gt}$=collapsed fixed-effect regressor vector excluding treatment has no anchored definition, $B_{gt}$=untreated cohort-time mean has no anchored definition, $\exp(-\infty)=0$=extended-MLE convention has no anchored definition, $L_{Nc}(\theta;\delta)$=collapsed finite-array Poisson criterion has no anchored definition

$\delta_{G_i,t}$ | $\delta_{G_i,t}$ | cohort-time proportional-effect log multiplier for unit $i$ in period $t$ | ass:proportional-effects
$\delta_{gt}$ | $\delta_{gt}$ | cohort-time proportional-effect log multiplier | ass:strict-positive-effects
$\theta_N$ | $\theta_N$ | finite-array PPML parameter vector | def:unit-fe-population-projection
$L_N(\theta_N;\delta)$ | $L_N(\theta_N;\delta)$ | finite-array unit-FE population Poisson criterion | def:unit-fe-population-projection
$m_{itN}(\delta)$ | $m_{itN}(\delta)$ | observed unit-time mean under proportional effects $\delta$ | def:unit-fe-population-projection
$v_{itN}$ | $v_{itN}$ | unit-time regressor vector for unit effects, time effects, and treatment | def:unit-fe-population-projection
$\beta_N^\star(\delta)$ | $\beta_N^\star(\delta)$ | treatment coordinate of the finite-array population projection | def:unit-fe-population-projection
$\theta^\star(\delta)$ | $\theta^\star(\delta)$ | maximizer of the limiting collapsed PPML criterion | def:collapsed-population-projection
$L(\theta;\delta)$ | $L(\theta;\delta)$ | limiting collapsed Poisson criterion | def:collapsed-population-projection
$m_{gt}(\delta)$ | $m_{gt}(\delta)$ | collapsed observed cohort-time mean under proportional effects $\delta$ | def:collapsed-population-projection
$\beta^\star(\delta)$ | $\beta^\star(\delta)$ | treatment coordinate of the limiting collapsed PPML projection | def:collapsed-population-projection
$\mu^\star_{gt}(\delta)$ | $\mu^\star_{gt}(\delta)$ | fitted collapsed mean from the limiting collapsed PPML projection | def:collapsed-population-projection
$A_N$ | $A_N$ | extended sample PPML argmax set | def:sample-unit-fe-ppml
$\hat\beta_N$ | $\hat\beta_N$ | selected sample unit-FE PPML treatment coefficient | def:sample-unit-fe-ppml
$\rho^\star(\delta)$ | $\rho^\star(\delta)$ | weighted least-squares coefficient from projecting treatment on fixed effects | def:weighted-fwl-residual
$\widetilde W_{gt}(\delta)$ | $\widetilde W_{gt}(\delta)$ | weighted FWL residualized treatment | def:weighted-fwl-residual
$\mathcal R_T$ | $\mathcal R_T$ | parameter region where the limiting coefficient is negative under positive effects | def:global-sign-reversal-region
$W_4$ | $W_4$ | explicit four-cohort triangular-array witness | def:four-cohort-witness
$h_{gt}$ | $h_{gt}$ | primitive observed mean component entering the sign index | def:frontier-elimination-handle
$R_g$ | $R_g$ | row sum of $h_{gt}$ over periods | def:frontier-elimination-handle
$C_t$ | $C_t$ | column sum of $h_{gt}$ over cohorts | def:frontier-elimination-handle
$M$ | $M$ | grand sum of $h_{gt}$ | def:frontier-elimination-handle
$A$ | $A$ | treated-cell sum of $h_{gt}$ | def:frontier-elimination-handle
$\Phi(\delta)$ | $\Phi(\delta)$ | primitive sign index for $\beta^\star(\delta)$ | def:frontier-elimination-handle
$\Phi$ | $\Phi$ | primitive sign index for $\beta^\star(\delta)$ | thm:primitive-global-frontier
$\delta_0$ | $\delta_0$ | common homogeneous proportional-effect log multiplier | prop:homogeneous-effect-reduction
$x$ | $x$ | common treated multiplier outside cell $(2,4)$ in the four-cohort subfamily | thm:primitive-global-frontier
$y$ | $y$ | treated multiplier at cell $(2,4)$ in the four-cohort subfamily | thm:primitive-global-frontier
$H$ | $H$ | set of treated cohort-time cells | thm:primitive-global-frontier
$B^{obs}_{gt}$ | $B^{obs}_{gt}$ | observed-data untreated mean proxy from baseline and never-treated margins | thm:primitive-global-frontier
$Z$ | $Z$ | normalizing sum for counterfactual-share weights | thm:primitive-global-frontier
$\omega_{gt}$ | $\omega_{gt}$ | counterfactual-share weight for treated cell $(g,t)$ | thm:primitive-global-frontier
$\tau_{gt}$ | $\tau_{gt}$ | proportional treatment effect in levels relative to untreated mean | thm:primitive-global-frontier
$PTT$ | $PTT$ | counterfactual-share-weighted proportional ATT target | thm:primitive-global-frontier

# Sections

## section: Abstract
The abstract will be drafted after the body. It will state the multiplicative staggered-adoption setting, the population sign-reversal result for the pooled fixed-effect PPML coefficient, the explicit four-cohort witness, and the contrast with the positive counterfactual-share proportional target.

objs: none

bib: MoreauKastler2025PTT, Wooldridge2023NonlinearDiD, GoodmanBacon2021, deChaisemartinDHaultfoeuille2020TWFE

## section: Introduction
The introduction will motivate the problem from staggered-adoption DiD with multiplicative means, explain why a single fixed-effect PPML population coefficient can be a poor causal summary under heterogeneous proportional effects, and preview the derivative sign characterization, the explicit positive-effect sign reversal, and the primitive sign index. One factual sentence will point readers to the appendix verification note for the machine-checked deterministic population scope.

objs: none

bib: AshenfelterCard1985, BertrandDufloMullainathan2004, GoodmanBacon2021, deChaisemartinDHaultfoeuille2020TWFE, Wooldridge2023NonlinearDiD, MoreauKastler2025PTT, RothSantAnna2023

## section: Related Literature
This section will position the paper within program-evaluation DiD, heterogeneous-effect staggered adoption, nonlinear and semiparametric DiD, misspecified pseudo-likelihood, fixed-effect Poisson estimation, PPML gravity practice, and proportional-effect PPML DiD. It will emphasize that the paper studies the population pseudo-true coefficient of a misspecified pooled PPML regression, not sampling inference for the estimator.

objs: none

bib: AshenfelterCard1985, Abadie2005, AtheyImbens2006, ImbensWooldridge2009, AngristPischke2009, GoodmanBacon2021, deChaisemartinDHaultfoeuille2020TWFE, CallawaySantAnna2021, SunAbraham2021, BorusyakJaravelSpiess2024, SantAnnaZhao2020, Gardner2022, Baker2025, White1982MisspecifiedML, Andrews1988LLN, GourierouxMonfortTrognon1984Theory, GourierouxMonfortTrognon1984Poisson, HausmanHallGriliches1984, CameronTrivedi2013, SantosSilvaTenreyro2006, SantosSilvaTenreyro2011, CorreiaGuimaraesZylkin2020, AndersonVanWincoop2003, HeadMayer2014, YotovPiermartiniMonteiroLarch2016, NagengastYotov2025, MoreauKastler2025PTT, Wooldridge2023NonlinearDiD, RothSantAnna2023, RothSantAnnaBilinskiPoe2023

## section: Setup and Assumptions
This section will introduce the triangular-array panel, cohort-time collapse, untreated exponential mean restriction, proportional treatment effects, rank condition, and the deterministic population PPML projections. The sample coefficient will be defined only to connect notation to the empirical regression, with the text making clear that the paper’s formal claims concern population projections rather than sampling consistency; the section will also define the weighted FWL residual, the sign-reversal region, the explicit four-cohort witness, and the elimination handle used later for the primitive sign characterization.

objs: ass:cohort-share-limit, ass:unit-untreated-exponential-mean, ass:within-cohort-baseline-limit, ass:proportional-effects, ass:collapsed-design-rank, ass:multicohort-frontier-scope, ass:strict-positive-effects, def:unit-fe-population-projection, def:collapsed-population-projection, def:sample-unit-fe-ppml, def:weighted-fwl-residual, def:global-sign-reversal-region, def:four-cohort-witness, def:frontier-elimination-handle

bib: Wooldridge2023NonlinearDiD, White1982MisspecifiedML, GourierouxMonfortTrognon1984Theory, GourierouxMonfortTrognon1984Poisson, SantosSilvaTenreyro2006, SantosSilvaTenreyro2011, CorreiaGuimaraesZylkin2020

## section: Main Results
This section will present the sharp derivative formula for the pseudo-true PPML coefficient, the forbidden-comparison sign rule through the weighted FWL residual, the homogeneous-effect benchmark, the primitive sign characterization, and the explicit four-cohort sign-reversal witness as a consequence of that characterization. It will distinguish the unsafe pooled coefficient from the positive counterfactual-share proportional target.

objs: thm:sharp-ppml-forbidden-sign, prop:homogeneous-effect-reduction, thm:primitive-global-frontier, prop:four-cohort-sign-reversal

bib: GoodmanBacon2021, deChaisemartinDHaultfoeuille2020TWFE, CallawaySantAnna2021, SunAbraham2021, BorusyakJaravelSpiess2024, MoreauKastler2025PTT, Wooldridge2023NonlinearDiD, RothSantAnna2023

## section: Discussion and Extensions
This section will interpret the results for empirical PPML DiD practice, especially in settings where multiplicative gravity-style specifications and staggered treatment timing are natural. It will discuss why the primitive sign index is a diagnostic for the pooled coefficient rather than a correction, and why granular proportional effects and their counterfactual-share average remain the relevant causal summaries under the maintained mean restrictions.

objs: none

bib: AndersonVanWincoop2003, HeadMayer2014, YotovPiermartiniMonteiroLarch2016, NagengastYotov2025, SantosSilvaTenreyro2006, SantosSilvaTenreyro2011, CorreiaGuimaraesZylkin2020, MoreauKastler2025PTT, Wooldridge2023NonlinearDiD

## section: Appendix: Proofs, Auxiliary Lemmas, and Verification Note
The appendix will collect the unit-FE collapse result, the pseudo-true projection first-order condition, and the proofs of the main results in an order that proves the primitive sign characterization before using it for the four-cohort sign-reversal result. It will end with a concise verification note stating that the displayed assumptions, definitions, lemmas, and theorems are machine-checked at the deterministic population and collapsed finite-dimensional levels, while sampling consistency, inference, and external economic identifying assumptions enter only as stated inputs.

objs: lem:unit-fe-collapse, lem:pseudo-true-ppml-projection

bib: White1982MisspecifiedML, Andrews1988LLN, GourierouxMonfortTrognon1984Theory, GourierouxMonfortTrognon1984Poisson