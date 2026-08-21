# Title
**Contour Identification and Root-\(n\) Estimation in Partially Linear Models with Cumulant-Separated Treatment Noise**

**Contribution statement.** The paper establishes exact zero-based identification and a fixed-separation root-\(n\) minimax contour estimator for partially linear models whose treatment residual has a nonzero higher cumulant and whose learned treatment code is stable in \(L^1(P_X)\).

# Notation
\(O_1,\ldots,O_n\) | \(O_1,\ldots,O_n\) | i.i.d. observations from \(P\) | ass:iid-sampling
\(P\) | \(P\) | observed-data law governing \(O=(X,T,Y)\) | def:non-gaussian-class
\(X,T,Y\) | \(X,T,Y\) | covariate, treatment, and outcome coordinates | def:non-gaussian-class
\(g_0,q_0,\eta,\xi\) | \(g_0,q_0,\eta,\xi\) | residual functionals determined by \(P\) | def:non-gaussian-class
\(\theta_0(P)\) | \(\theta_0(P)\) | partially linear target under law \(P\) | def:minimax-risks
\(\theta_0\) | \(\theta_0\) | partially linear coefficient when the law is fixed | ass:theta-range
\(\bar g_n,\bar q_n\) | \(\bar g_n,\bar q_n\) | clipped externally supplied treatment and outcome codes | def:non-gaussian-class
\(C_{\theta},C_g,C_q\) | \(C_{\theta},C_g,C_q\) | fixed range constants for target and regression functions | ass:theta-range
\(\psi_{\eta},\psi_{\xi}\) | \(\psi_{\eta},\psi_{\xi}\) | sub-Gaussian envelope constants for treatment and outcome innovations | ass:eta-subgaussian
\(\lVert W\rVert_{\psi_2}\) | \(\lVert W\rVert_{\psi_2}\) | Luxemburg sub-Gaussian norm convention | ass:eta-subgaussian
\(\kappa_k(\eta)\) | \(\kappa_k(\eta)\) | \(k\)th cumulant of treatment noise | ass:cumulant-separation
\(\delta\) | \(\delta\) | fixed cumulant-separation level | ass:cumulant-separation
\(\varepsilon_{1,n},\varepsilon_{2,n}\) | \(\varepsilon_{1,n},\varepsilon_{2,n}\) | supplied treatment-code and outcome-code radii | ass:treatment-code-radius
\(r,s\) | \(r,s\) | ACE order and comparison norm exponent | def:jms-ace-class
\(\mathcal P_{\mathrm{NG},n}\) | \(\mathcal P_{\mathrm{NG},n}\) | broad cumulant-separated spectral class with \(L^1(P_X)\) treatment-code control | def:non-gaussian-class
\(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | \(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | bounded-outcome Gaussian JMS comparison class | def:gaussian-class
\(\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}\) | \(\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}\) | published ACE cumulant-separated comparison class | def:jms-ace-class
\(\mathcal P_{\mathrm{NG},n}^{\mathrm{ACE}}\) | \(\mathcal P_{\mathrm{NG},n}^{\mathrm{ACE}}\) | \(L^s(P_X)\)-restricted subclass of \(\mathcal P_{\mathrm{NG},n}\) for ACE comparison | def:ace-comparison-subclass
\(M,H_n,F_n,G_n,B_n\) | \(M,H_n,F_n,G_n,B_n\) | treatment-noise and observable complex transform family | lem:observable-factorization
\(z_0,\ell\) | \(z_0,\ell\) | zero of \(M\) and its multiplicity | def:zero-instrument
\(J_{z_0,\ell}(w)\) | \(J_{z_0,\ell}(w)\) | zero-based instrument \(w^{\ell-1}e^{z_0w}\) | def:zero-instrument
\(C_j\) | \(C_j\) | positively oriented contour circle | def:contour-functional
\(N_{C_j}(F_n)\) | \(N_{C_j}(F_n)\) | number of zeros of \(F_n\) inside \(C_j\) | def:contour-functional
\(\Theta_{C_j}(F_n,G_n)\) | \(\Theta_{C_j}(F_n,G_n)\) | contour ratio functional identifying \(\theta_0\) | def:contour-functional
\(\mathfrak R_n^{\mathrm{NG}}\) | \(\mathfrak R_n^{\mathrm{NG}}\) | minimax MSE over \(\mathcal P_{\mathrm{NG},n}\) | def:minimax-risks
\(\mathfrak R_n^{\mathrm G}\) | \(\mathfrak R_n^{\mathrm G}\) | minimax MSE over \(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | def:minimax-risks
\(\mathfrak M_{n,1-\gamma}^{\mathrm G}\) | \(\mathfrak M_{n,1-\gamma}^{\mathrm G}\) | minimax generalized-quantile risk over \(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | def:minimax-risks
\(Q_{P,1-\gamma}\) | \(Q_{P,1-\gamma}\) | generalized \(1-\gamma\) quantile under \(P\) | def:minimax-risks
\(a_{1,n},b_{1,n},a_2,b_{2,n}\) | \(a_{1,n},b_{1,n},a_2,b_{2,n}\) | JMS eligibility quantities from condition (21) | def:jms-eligibility
\(\mathsf E_n^{\mathrm{JMS}}\) | \(\mathsf E_n^{\mathrm{JMS}}\) | JMS order-\(r\) eligibility condition | def:jms-eligibility
\(\widehat\theta_{\sin,n}\) | \(\widehat\theta_{\sin,n}\) | clipped sine-ratio estimator for symmetric Gaussian mixture noise | def:sine-estimator
\(\mathscr C_m\) | \(\mathscr C_m\) | finite deterministic library of rational circles at depth \(m\) | def:local-gaussian-handle
\(\widehat F_{a,n},\widehat G_{a,n}\) | \(\widehat F_{a,n},\widehat G_{a,n}\) | split-fold empirical transforms | def:local-gaussian-handle
\(W_{a,C}(t),V_{a,C}(t)\) | \(W_{a,C}(t),V_{a,C}(t)\) | empirical winding and contour-moment integrands | def:local-gaussian-handle
\(\widehat v_{a,C}\) | \(\widehat v_{a,C}\) | angular variance of the empirical contour-moment integrand | def:local-gaussian-handle
\(\widehat\theta_{\mathrm{ad}}\) | \(\widehat\theta_{\mathrm{ad}}\) | reserved symbol for the future adaptive selector in the open question | def:local-gaussian-handle
\(\mathsf{CCIA}_{\mathrm{build}}\) | \(\mathsf{CCIA}_{\mathrm{build}}\) | finite bounded-build specification for certified contour arithmetic | def:certified-contour-arithmetic-substrate
\(\operatorname{Name}_{+}(x)\) | \(\operatorname{Name}_{+}(x)\) | positive certified-real record for \(x\) | def:contour-bank-handle
\(\mathfrak p_{\star}\) | \(\mathfrak p_{\star}\) | fixed primitive certified-record tuple for the contour bank | def:contour-bank-handle
\(R_0,R_1\) | \(R_0,R_1\) | zero-localization radius and outer radius | def:contour-bank-handle
\(U_{\psi},U_R,N_{\mathrm{cert}},m_{\star},d_{\star},h_{\star},J\) | \(U_{\psi},U_R,N_{\mathrm{cert}},m_{\star},d_{\star},h_{\star},J\) | integer and dyadic constants defining the bank fuel and size | def:contour-bank-handle
\(\rho_q,\mathfrak\rho_q\) | \(\rho_q,\mathfrak\rho_q\) | bank radius and its certified name | def:contour-bank-handle
\(a_{\star}\) | \(a_{\star}\) | positive dyadic lower-modulus certificate for the bank | def:contour-bank-handle
\(\mathfrak c_{\theta,\star}\) | \(\mathfrak c_{\theta,\star}\) | fixed positive certified record for \(C_{\theta}\) | def:adaptive-contour-estimator
\(\mathcal I_m(x)\) | \(\mathcal I_m(x)\) | floor-dyadic observation-coordinate interval | def:adaptive-contour-estimator
\(\widehat\theta_{\mathrm{spec},n}\) | \(\widehat\theta_{\mathrm{spec},n}\) | total Borel contour statistic using fixed primitive records | def:adaptive-contour-estimator
\(\mathfrak s_{\star}\) | \(\mathfrak s_{\star}\) | represented-data input record for the transducer | def:adaptive-contour-estimator
\(\widehat F_{a,n}^{(p)}(z),\widehat G_{a,n}^{(p)}(z)\) | \(\widehat F_{a,n}^{(p)}(z),\widehat G_{a,n}^{(p)}(z)\) | empirical derivative-sum enclosures used by the transducer | def:adaptive-contour-estimator
\(W_{0j}(t),V_j(t)\) | \(W_{0j}(t),V_j(t)\) | certified pilot winding and evaluation-fold contour integrands | def:adaptive-contour-estimator
\(\widehat\theta_{\mathrm{ACE},r,n}\) | \(\widehat\theta_{\mathrm{ACE},r,n}\) | published order-\(r\) ACE estimator | prop:jms-ace-alignment
\(B_{\mathrm{ACE},n,\gamma}\) | \(B_{\mathrm{ACE},n,\gamma}\) | JMS ACE generalized-quantile upper guarantee | prop:jms-ace-alignment
\(\eta_a,t_a,A_a\) | \(\eta_a,t_a,A_a\) | Gaussian-Rademacher path, first positive zero, and denominator scale | lem:gaussian-rademacher-l1-benchmark
\(\widehat\theta_{a,n}\) | \(\widehat\theta_{a,n}\) | clipped sine-ratio estimator along the Gaussian-Rademacher path | lem:gaussian-rademacher-l1-benchmark
\(\Delta_a\) | \(\Delta_a\) | fourth-cumulant magnitude \(2a^4\) along the path | lem:gaussian-rademacher-l1-benchmark
\(\mathcal C_n(\delta_n)\) | \(\mathcal C_n(\delta_n)\) | local ACE class with cumulant threshold \(\delta_n\) | thm:local-to-gaussian-partial-benchmarks
\(\widetilde b_{2,n}\) | \(\widetilde b_{2,n}\) | local JMS eligibility quantity with \(\delta_n\) | thm:local-to-gaussian-partial-benchmarks
\(U_{\mathrm{ACE},n}^{\mathrm{loc}}\) | \(U_{\mathrm{ACE},n}^{\mathrm{loc}}\) | local oracle ACE upper benchmark | thm:local-to-gaussian-partial-benchmarks
\(U_{\mathrm{DML},n}\) | \(U_{\mathrm{DML},n}\) | separately valid ordinary-DML upper bound | thm:local-to-gaussian-partial-benchmarks
notation_gaps: none

env_overrides: prop:jms-ace-alignment=propositionv, prop:symmetric-mixture-reduction=propositionv, prop:bounded-outcome-gaussian-degeneracy=propositionv, oeq:local-to-gaussian-frontier=remarkv

# Sections
## section: Introduction
The introduction will motivate partially linear estimation with learned residuals, explain how non-Gaussian treatment residuals create usable complex-MGF zeros, and state the fixed-separation contribution: an exact contour identity and a total contour statistic attaining root-\(n\) minimax MSE under \(L^1(P_X)\) treatment-code stability. It will position the result relative to PLM, DML, higher-order orthogonality, ACE, empirical characteristic functions, and non-Gaussian identification. A single factual sentence will point readers to the appendix verification note for the machine-checked scope.
objs:
bib: Engle1986, Robinson1988, Speckman1988, HardleLiangGao2000, Hansen1982, Newey1990, Newey1994, NeweyMcFadden1994, BickelKlaassenRitovWellner1993, VanDerVaart1998, VanDerVaartWellner1996, ChernozhukovEtAl2018DML, NeweyRobins2018, MackeySyrgkanisZadik2018, JinMackeySyrgkanis2025, FeuervergerMcDunnough1981, Singleton2001, Carrasco2017, Comon1994, ShimizuHoyerHyvarinenKerminen2006, ReizingerEtAl2025

## section: Model, Classes, and Risk Criteria
This section will introduce the observed-data PLM notation, residuals, deterministic clipped codes, sampling convention, cumulant and tail assumptions, and the three law classes used in the paper. It will define the minimax MSE and generalized-quantile criteria before any formal comparison results appear.
objs: ass:iid-sampling, ass:independent-treatment-noise, ass:outcome-mean-independence, ass:theta-range, ass:g-range, ass:q-range, ass:bounded-gaussian-outcome, ass:eta-subgaussian, ass:xi-subgaussian, ass:cumulant-separation, ass:treatment-code-radius, ass:outcome-code-radius, ass:jms-treatment-code-radius, ass:jms-outcome-code-radius, ass:gaussian-treatment-noise, ass:l1-treatment-code-radius, def:non-gaussian-class, def:gaussian-class, def:jms-ace-class, def:minimax-risks, def:ace-comparison-subclass
bib: Robinson1988, ChernozhukovEtAl2018DML, MackeySyrgkanisZadik2018, JinMackeySyrgkanis2025, Vershynin2018, Wainwright2019

## section: Zero Instruments and Contour Identification
This section will develop the analytic identification mechanism. It will introduce zero instruments, the contour functional, the observable factorization, and the exact contour identity that recovers \(\theta_0\) from \(F_n\) and \(G_n\) when the contour encloses zeros and avoids boundary zeros.
objs: def:zero-instrument, def:contour-functional, thm:known-zero-instrument, lem:observable-factorization, thm:exact-contour-identification
bib: KaganLinnikRao1973, Mattner1992, DHaultfoeuille2011, DarollesFanFlorensRenault2011, HuShiu2022, FeuervergerMcDunnough1981, Singleton2001, CarrascoFlorensRenault2007, Carrasco2017

## section: The Certified Bank and the Spectral Statistic
This section will explain the fixed primitive-record convention, the finite translated-dyadic contour bank, the bounded-build substrate for certified arithmetic, and the total Borel statistic \(\widehat\theta_{\mathrm{spec},n}\). The emphasis will be on the positive statistical object: a deterministic bank and a contour statistic whose ordinary-sample risk is defined independently of the compiled represented-data transducer.
objs: def:certified-contour-arithmetic-substrate, def:contour-bank-handle, def:adaptive-contour-estimator, lem:zero-localization, lem:finite-contour-bank
bib: MichelenSahasrabudhe2019, EremenkoFryntov2021, DinhGhoshTranTran2021, Weihrauch2000, Ko1991, Moore1966

## section: Root-\(n\) Minimax Estimation at Fixed Separation
This section will state the main fixed-\(\delta\) theorem. It will combine the contour construction, the empirical transform bound, the \(L^1\) nuisance stability result, and the Le Cam lower-bound submodel to obtain matched \(\Theta(n^{-1})\) MSE over \(\mathcal P_{\mathrm{NG},n}\), plus the generalized-quantile consequence.
objs: thm:adaptive-rootn-minimax
bib: BickelKlaassenRitovWellner1993, VanDerVaart1998, VanDerVaartWellner1996, ChernozhukovEtAl2018DML, NeweyRobins2018, RobinsLiTchetgenVanDerVaart2008, LiuMukherjeeRobinsTchetgen2021, LiuMukherjeeNeweyRobins2017, MackeySyrgkanisZadik2018

## section: Comparison with ACE and Gaussian Benchmarks
This section will align the paper's classes with the published ACE class, report the ACE generalized-quantile guarantee on the common class, and compare upper guarantees under fixed separation. It will also state the bounded-outcome Gaussian diagnostic and the common-experiment conclusion that separates the spectral class result from the simultaneous Gaussian bounded-outcome intersection.
objs: def:jms-eligibility, prop:jms-ace-alignment, thm:common-experiment-dichotomy, prop:bounded-outcome-gaussian-degeneracy, lem:jms-ace-class-relations
bib: JinMackeySyrgkanis2025, MackeySyrgkanisZadik2018, ChernozhukovEtAl2018DML, NeweyRobins2018

## section: Explicit Mixture Reductions and Local Benchmarks
This section will present the computable sine estimator for the symmetric Gaussian mixture, the Gaussian-Rademacher \(k=4\) benchmark path, and the local oracle ACE benchmark with shrinking cumulant thresholds. It will frame these as constructive benchmarks for weak non-Gaussian regimes and as motivation for the open research agenda.
objs: def:sine-estimator, prop:symmetric-mixture-reduction, lem:gaussian-rademacher-l1-benchmark, thm:local-to-gaussian-partial-benchmarks
bib: LeeMesters2024, HoeschLeeMesters2024, LanneMeitzSaikkonen2017, Comon1994, HyvarinenOja1997, HyvarinenKarhunenOja2001, ReizingerEtAl2025, JinMackeySyrgkanis2025

## section: Limitations and Future Work
This section will collect the open local-to-Gaussian question and the candidate-record handle for future adaptive selectors. It will state the research agenda around sharp shrinking-\(\delta_n\) rates, data-driven switching, uniform inference, and local minimax lower bounds as open work, separately from the fixed-separation theorem.
objs: def:local-gaussian-handle, oeq:local-to-gaussian-frontier
bib: JinMackeySyrgkanis2025, MackeySyrgkanisZadik2018, ChernozhukovEtAl2018DML, NeweyRobins2018, LeeMesters2024, HoeschLeeMesters2024

## section: Appendix A: Proofs for Identification and Analytic Localization
This appendix section will prove the zero-instrument identity, observable factorization, contour identification result, and zero-localization and finite-bank lemmas, with all cross-references using cleveref commands in the manuscript stage.
objs:
bib: KaganLinnikRao1973, Mattner1992, MichelenSahasrabudhe2019, EremenkoFryntov2021, DinhGhoshTranTran2021

## section: Appendix B: Empirical Process, Stability, and Lower-Bound Lemmas
This appendix section will contain the auxiliary statistical lemmas supporting the main theorem: the empirical transform \(L^2\) bound, the \(L^1\) nuisance zero-free argument, and the non-Gaussian hard submodel lower bound.
objs: lem:empirical-transform-uniform-l2, lem:l1-nuisance-zero-free, lem:non-gaussian-hard-submodel
bib: VanDerVaart1998, VanDerVaartWellner1996, BickelKlaassenRitovWellner1993, Vershynin2018, Wainwright2019

## section: Appendix C: Verification Note
This brief appendix note will consolidate the Lean verification scope: the frozen formal statements are machine-checked under their stated external interfaces and cited comparator assumptions, while published inputs such as the JMS ACE guarantee enter through the verified citation boundary rather than being reconstructed.
objs:
bib: JinMackeySyrgkanis2025
