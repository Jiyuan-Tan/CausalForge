# Title

**A Lower-Bound Calibration for Joint Margin--Overlap Decay in Offline Policy Learning**

**Contribution statement.** The paper gives a minimax lower-bound calibration for welfare regret under joint margin-overlap decay, and a conditional analysis of a specified clipped cross-fitted AIPW empirical welfare rule with supplied nuisance estimates under explicit high-level side conditions.

# Notation

notation_gaps: $p_P(x)$=the frozen layer uses the overlap score but no definition environment states whether it is $\min\{e_P(x),1-e_P(x)\}$ or another endpoint distance; $\mathcal P_{\alpha,\gamma}$=the law class is named by `def:law-class` but its displayed set notation is not fixed there; $\eta$=the nuisance triple is used by `def:clipped-propensity` and `def:clipped-aipw-score` but only informally identified as $(\mu_0,\mu_1,e)$; $\widehat\eta^{(-k)}$=cross-fitted nuisance estimators are used in `def:feasible-erm` but their construction is not defined; $Y(a)$=potential outcomes appear in assumptions but no frozen definition introduces the potential-outcome space.

| note symbol | paper notation | defining property in one phrase | home |
|---|---|---|---|
| sample size | $n$ | number of offline observations | §Setup and assumptions |
| observations | $O_i=(X_i,A_i,Y_i)$ | i.i.d. observed data units | ass:iid |
| observed law | $P$ | probability law of one observation | §Setup and assumptions |
| observation space | $\Omega=\mathcal X\times\{0,1\}\times[-1,1]$ | support for one observed data unit | §Setup and assumptions |
| covariate | $X$ | pretreatment covariate | §Setup and assumptions |
| treatment | $A$ | binary treatment indicator | §Setup and assumptions |
| outcome | $Y$ | bounded observed outcome | ass:bounded-outcome |
| potential outcomes | $Y(a)$ | treatment-$a$ potential outcome | notation_gaps |
| covariate law | $P_X$ | marginal law of $X$ under $P$ | §Setup and assumptions |
| propensity score | $e_P(x)$ | conditional treatment probability under $P$ | ass:positivity |
| overlap score | $p_P(x)$ | propensity-boundary distance used in overlap decay | notation_gaps |
| outcome regressions | $\mu_a(x)$ | conditional mean outcome under treatment $a$ | §Setup and assumptions |
| treatment contrast | $\tau_P(x)$ | conditional treatment-effect contrast | def:welfare-regret |
| policy class | $\Pi$ | pointwise measurable finite-VC class of deterministic policies | ass:policy-class |
| policy | $\pi$ | measurable deterministic binary treatment rule | ass:policy-class |
| countable dense subclass | $\Pi_0=\{\pi_j:j\ge1\}$ | pointwise dense countable policy subclass | ass:policy-class |
| VC dimension | $d_\Pi$ | finite VC dimension of $\Pi$ | ass:policy-class |
| oracle policy | $\pi^\star_P$ | welfare-maximizing threshold rule $1\{\tau_P\ge0\}$ | def:welfare-regret |
| welfare | $V_P(\pi)$ | expected contrast-weighted policy value | def:welfare-regret |
| regret | $R_P(\pi)$ | welfare loss relative to $\pi^\star_P$ | def:welfare-regret |
| disagreement set | $D_\pi$ | covariates where $\pi$ differs from $\pi^\star_P$ | def:disagreement |
| margin exponent | $\alpha$ | exponent in the small-contrast probability bound | ass:margin |
| margin constant | $C_m$ | scale in the margin bound | ass:margin |
| margin window | $u_0$ | upper endpoint of the margin window | ass:margin-window |
| overlap-decay exponent | $\gamma$ | exponent governing one-sided overlap decay near small contrasts | ass:overlap-decay |
| overlap constants | $C_o,c_o$ | scale and admissible-window constants in overlap decay | ass:overlap-decay |
| strict-overlap endpoint | $\underline p$ | lower overlap bound for the $\gamma=0$ case | ass:strict-overlap-endpoint |
| overlap calibration exponent | $\beta_{\alpha,\gamma}$ | weak-arm exponent induced by margin and overlap decay | def:exponents |
| denominator exponent | $D_{\alpha,\gamma}$ | exponent denominator $2+\alpha+\beta_{\alpha,\gamma}$ | def:exponents |
| minimax exponent | $r_\star(\alpha,\gamma)$ | lower-bound rate exponent | def:exponents |
| classification exponent | $A_\alpha$ | strict-overlap empirical-process rate exponent | ass:vc-localized-offset-envelope |
| nuisance outcome exponent | $a$ | polynomial rate exponent for outcome nuisance error | ass:polynomial-nuisance-exponents |
| nuisance product exponent | $c$ | polynomial rate exponent for nuisance product error | ass:polynomial-nuisance-exponents |
| nuisance constants | $C_\mu,C_{\mathrm{prod}}$ | constants in polynomial nuisance-rate bounds | ass:polynomial-nuisance-exponents |
| nuisance errors | $r_{\mu,n},r_{e,n}$ | $L_2(P)$ rates for outcome and propensity nuisances | ass:nuisance-rate |
| feasible-rate objective | $\phi(s,t)$ | minimum of the four upper-bound exponent components | def:feasible-rate |
| feasible clipping exponent | $s_{\mathrm{feas}}$ | maximizing exponent for $q_n$ | def:feasible-rate |
| feasible contrast-window exponent | $t_{\mathrm{feas}}$ | maximizing exponent for $u_n$ | def:feasible-rate |
| feasible nuisance exponent | $g_{\mathrm{joint}}$ | optimized conditional feasible exponent before truncation by $r_\star$ | def:feasible-rate |
| clipping base | $q_0$ | scale constant for the clipping schedule | def:feasible-rate |
| weak-arm/clipping schedule | $q_n$ | weak-arm probability in the lower-bound witness and deterministic propensity clip in the feasible analysis | def:two-point-witness |
| contrast-window base | $\bar u$ | scale constant for the localization window | def:feasible-rate |
| contrast-window schedule | $u_n$ | deterministic contrast localization sequence | def:feasible-rate |
| feasible upper exponent | $r_{\mathrm{up}}=r_{\mathrm{feas}}$ | conditional upper-bound exponent for the feasible ERM | def:feasible-rate |
| nuisance triple | $\eta=(\mu_0,\mu_1,e)$ | plug-in regression and propensity functions | notation_gaps |
| clipped propensity | $e_q(x;\eta)$ | propensity score truncated to $[q,1-q]$ | def:clipped-propensity |
| clipped AIPW score | $\Gamma_q(O;\eta)$ | clipped doubly robust score for the treatment contrast | def:clipped-aipw-score |
| fold count | $K$ | fixed number of cross-fitting folds | ass:fixed-crossfit-fold-count |
| folds | $I_1,\ldots,I_K$ | balanced deterministic partition of observation indices | def:feasible-erm |
| fold index | $k(i)$ | evaluation fold containing observation $i$ | def:feasible-erm |
| cross-fitted nuisances | $\widehat\eta^{(-k)}$ | nuisance estimates trained away from fold $k$ | notation_gaps |
| empirical welfare criterion | $\widehat V_{n,q}(\pi)$ | clipped AIPW empirical policy value | def:feasible-erm |
| ERM selector index | $j_n$ | first near-maximizing index in $\Pi_0$ | def:feasible-erm |
| policy estimator | $\widehat\pi_n$ | generic measurable policy estimator, specialized later to the feasible $1/n$-ERM | def:minimax-regret |
| minimax regret | $M_n(\alpha,\gamma)$ | worst-case regret risk optimized over estimators | def:minimax-regret |
| law class | $\mathcal P_{\alpha,\gamma}$ | laws satisfying boundedness, positivity, margin, zero-effect, overlap decay, and endpoint conditions | def:law-class |
| conditional upper risk | $U_n(\alpha,\gamma,a,c;\widehat\eta)$ | worst-case risk of the feasible clipped AIPW ERM over the stated side-condition domain | def:upper-risk |
| lower-bound bandwidth | $h_n$ | local contrast scale in the two-point witness | def:two-point-witness |
| active block | $B_n$ | covariate block where the two witness laws differ | def:two-point-witness |
| block-size constant | $c_B$ | scale determining $P_X(B_n)$ | def:two-point-witness |
| block mass | $m_n$ | covariate probability of $B_n$ | lem:two-point-divergence |
| off-block contrast | $\tau_0$ | common strict contrast outside the active block | def:two-point-witness |
| witness sign | $\sigma\in\{+,-\}$ | index for the two least favorable laws | def:two-point-witness |
| witness laws | $P_{n,\sigma}$ | two local alternatives for the minimax lower bound | def:two-point-witness |
| chi-square constant | $C_\chi$ | upper bound on product chi-square divergence | lem:le-cam-two-point-chisq |
| test | $\psi$ | binary decision rule between the two witness laws | lem:le-cam-two-point-chisq |
| plug-in nuisance | $\bar\eta=(\bar\mu_0,\bar\mu_1,\bar e)$ | arbitrary measurable nuisance triple for drift analysis | lem:clip-bias |
| clipped plug-in propensity | $\bar e_q$ | clipped propensity formed from $\bar e$ | lem:clip-bias |
| regression errors | $\Delta_a$ | plug-in regression error $\bar\mu_a-\mu_a$ | lem:clip-bias |
| localized offset rate | $\rho_n$ | empirical-process rate $(B^2/n)^{A_\alpha}(\log n)^p$ | lem:localized-vc-self-bound |
| envelope | $B$ | uniform bound for centered policy-indexed processes | ass:vc-localized-envelope |
| logarithmic power | $p$ | finite logarithmic exponent in empirical-process bounds | ass:vc-localized-envelope |
| centered process | $z_\pi$ | centered empirical process indexed by policies | ass:vc-localized-offset-envelope |
| localized radius | $r$ | regret radius for localized process bounds | lem:localized-vc-process-bound |
| localization exponent | $\kappa$ | exponent $\alpha/(2+2\alpha)$ | lem:localized-vc-process-bound |
| increments | $g_\pi$ | centered policy-indexed functions in localized bounds | ass:vc-localized-envelope |
| i.i.d. localized supremum | $Z_m(r)$ | fixed-radius supremum over policies with regret at most $r$ | lem:localized-vc-process-bound |
| cross-fit localized supremum | $Z_{\mathrm{cf}}(r)$ | pooled cross-fit analogue of $Z_m(r)$ | lem:crossfit-localized-process-reduction |
| pooled cross-fit process | $G_{\mathrm{cf}}(\pi)$ | centered cross-fit process in the offset bound | lem:crossfit-localized-offset-control |
| clipped-score drift | $b_q(x)$ | conditional mean bias of the clipped AIPW score | lem:localized-clipped-drift-bound |

# Sections

## section: Abstract

The abstract will be drafted after the body is fixed. It should state the observed-law offline policy-learning problem, the one-sided overlap-decay condition near the treatment propensity boundary, the minimax lower exponent, and the conditional clipped-AIPW upper exponent without claiming a full matching feasible characterization where the frozen layer leaves `oeq:feasible-tight` open.

objs:

bib:

## section: Introduction

The introduction motivates welfare regret in observational policy learning, explains why near-violations of overlap alter regret rates under margin structure, and previews the lower-bound calibration and the conditional feasible upper bound. It includes one factual sentence directing readers to the final verification note for the machine-checked scope.

objs:

bib: Neyman1990, Rubin1974, Rosenbaum1983, Imbens2015, Manski2004, Manski2009, Stoye2009, Kitagawa2018, Athey2021, Luedtke2017

## section: Related Literature

This section positions the paper relative to treatment-choice and welfare-regret methods, semiparametric and doubly robust estimation, margin-based excess-risk theory, and econometric work on limited overlap and off-policy learning. It should not describe the open feasible-tightness question as a result.

objs:

bib: Bickel1993, Newey1994, Robins1994, Hahn1998, Hirano2003, VanDerLaan2011, Chernozhukov2018, Chernozhukov2022, Qian2011, Zhao2012, Zhang2012, Dudik2011, Swaminathan2015, Kallus2017, Nie2021, Sasaki2020, Sun2021, Kitagawa2022, Audibert2007, Massart2006, Tsybakov2009, LeCam1986, Li2016, DAmour2017, BenMichael2022, Hill2024, Susmann2025, Zhan2021, Chen2020, Zhao2023, Sakaguchi2024, Girard2025, Liu2026

## section: Setup and Assumptions

This section introduces the observed-law experiment, the welfare-regret target, the policy class, the margin and overlap-decay restrictions, and the law class used for the minimax analysis. It also introduces the notation whose home is the setup prose, including $P$, $O=(X,A,Y)$, $P_X$, $e_P$, $\mu_a$, and the observation space, before any formal statement uses them.

objs: ass:iid, ass:bounded-outcome, ass:positivity, ass:margin, ass:zero-effect, ass:overlap-decay, ass:policy-class, ass:optimal-in-class, ass:margin-window, ass:strict-overlap-endpoint, def:welfare-regret, def:disagreement, def:exponents, def:law-class, thm:welfare-identity, thm:margin-localization

bib: Kitagawa2018, Athey2021, Luedtke2017, Audibert2007, Massart2006, Tsybakov2009

## section: Minimax Lower Bound

This section presents the overlap-margin calibration, the two-point construction, the product-divergence control, the regret separation, and the resulting minimax lower bound. The section should emphasize that the lower bound is an observed-law statement over `def:law-class` and that the two policies used in the reduction must be available in the policy class as stated in the witness-membership lemma.

objs: def:minimax-regret, def:two-point-witness, prop:overlap-envelope, lem:witness-membership, lem:two-point-divergence, lem:regret-separation, lem:le-cam-two-point-chisq, thm:minimax-lower, thm:rate-characterization

bib: LeCam1986, Tsybakov2009, Kitagawa2018, Luedtke2017

## section: Conditional Analysis of a Clipped Cross-Fitted AIPW Rule

This section defines the clipped score, the cross-fitted empirical welfare rule, the feasible tuning schedule, and the conditional risk object. It then states the conditional achievability result for the plain clipped cross-fitted AIPW ERM under the exact nuisance, cross-fitting, and empirical-process side conditions bundled into the frozen environments.

objs: ass:vc-localized-envelope, ass:nuisance-rate, ass:bounded-crossfit-nuisances, ass:polynomial-nuisance-exponents, ass:fixed-crossfit-fold-count, ass:vc-localized-offset-envelope, def:feasible-rate, def:clipped-propensity, def:clipped-aipw-score, def:feasible-erm, def:upper-risk, lem:feasible-erm-basic-inequality, lem:crude-clipped-score-envelope, lem:localized-clipped-drift-bound, lem:crude-localized-master-bound, lem:clip-balance-exponent, oeq:feasible-upper

bib: Robins1994, Hahn1998, Hirano2003, VanDerLaan2011, Chernozhukov2018, Chernozhukov2022, Athey2021, Liu2026

## section: Discussion and Open Question

This section interprets the gap between the minimax lower exponent and the conditional feasible exponent when the nuisance regime is limiting. It records `oeq:feasible-tight` only as an explicitly open question about whether genuinely feasible procedures can attain the converse exponent in the strict-gap branch.

objs: oeq:feasible-tight

bib: Li2016, DAmour2017, BenMichael2022, Hill2024, Susmann2025, Zhao2023, Liu2026

## section: Appendix A. Algebra, Testing, and Witness-Law Details

This appendix contains proof details for the overlap-envelope calculation, witness membership, two-point divergence, regret separation, and the in-core Le Cam testing reduction. It should preserve the frozen statements and use the appendix prose only to connect their proof steps.

objs:

bib: LeCam1986, Tsybakov2009

## section: Appendix B. Empirical-Process and Cross-Fitting Details

This appendix contains the localized VC process bounds, cross-fitting reduction, offset control, and the self-bounding argument used by the feasible upper bound. The role of fixed $K$, balanced folds, and the assumed empirical-process envelopes should be stated as inputs rather than consequences of the law class.

objs: lem:localized-vc-self-bound, lem:localized-vc-process-bound, lem:crossfit-localized-process-reduction, lem:crossfit-localized-offset-control

bib: Audibert2007, Massart2006, Tsybakov2009, Chernozhukov2018

## section: Appendix C. Clipped-Score Drift and Bias Localization

This appendix gives the clipped-score drift identity and the localization steps used to control the deterministic bias from clipping and nuisance estimation. It should flag that the exact drift identity rules out any stronger cancellation claim under the frozen assumptions alone.

objs: lem:clip-bias, lem:clipped-region-localization

bib: Robins1994, Hahn1998, Hirano2003, Chernozhukov2018

## section: Appendix D. Verification Note

This final appendix consolidates the Lean machine-checking scope: the observed-law objects, exponent definitions, witness construction, lower-bound skeleton, clipped-score identities, ERM inequality, and conditional upper-bound dependencies are the verified formal layer, while nuisance-rate conditions, fixed-fold cross-fitting, VC localized envelopes, and offset-envelope controls enter as explicit assumptions. It should also note that potential-outcome interpretation is non-load-bearing for the formal observed-law regret statements.

objs:

bib:
