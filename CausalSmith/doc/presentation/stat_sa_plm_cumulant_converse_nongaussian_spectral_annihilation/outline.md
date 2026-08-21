# Title
**Contour instruments for partially linear models with cumulant-separated treatment noise**

**Contribution statement.** The paper establishes zero-based contour identification and fixed-separation \(\Theta(n^{-1})\) minimax mean-squared-error estimation for partially linear models with independent cumulant-separated treatment noise and \(L^1(P_X)\)-stable supplied treatment codes.

# Notation
| note symbol | paper notation | defining property in one phrase | home |
| --- | --- | --- | --- |
| \(n\) | \(n\ge1\) | sample size | def:model-parameters |
| \(r,k\) | \(r,k\in\mathbb N\), \(k=r+1\), \(r\ge2\) | ACE order and cumulant order | def:model-parameters |
| \(s\) | \(s\in[0,\infty]\), \(s\ge r\) | comparison norm exponent | def:model-parameters |
| \(\gamma\) | \(\gamma\in(1/2,1)\) | probability level for generalized-quantile bounds | def:model-parameters |
| \(C_{\theta},C_g,C_q,\psi_{\eta},\psi_{\xi},\delta,\sigma\) | \(C_{\theta},C_g,C_q,\psi_{\eta},\psi_{\xi},\delta,\sigma>0\) | fixed class constants | def:model-parameters |
| \(\varepsilon_1,\varepsilon_2\) | \(\varepsilon_1,\varepsilon_2:\mathbb N\to\mathbb R\) | nonnegative nonincreasing code-radius sequences | def:model-parameters |
| \(\varepsilon_{1,n},\varepsilon_{2,n}\) | \(\varepsilon_{1,n},\varepsilon_{2,n}\) | code-radius values at sample size \(n\) | def:model-parameters |
| \(N(m,v)\) | \(N(m,v)\) | Gaussian law with mean \(m\) and variance \(v\) | def:model-parameters |
| \(\mathbb P_n f\) | \(\mathbb P_n f=n^{-1}\sum_{i=1}^{n}f(O_i)\) | empirical average | def:model-parameters |
| \(I_0,I_1,I_a\) | \(I_0=\{i:i<\lfloor n/2\rfloor\}\), \(I_1=\{i:i\ge\lfloor n/2\rfloor\}\), \(I_a\) | deterministic split folds | def:model-parameters |
| \(\lVert W\rVert_{\psi_2}\) | \(\lVert W\rVert_{\psi_2}\) | Luxemburg sub-Gaussian norm convention | def:model-parameters |
| \(\lVert W\rVert_{\psi_2\mid X}\) | \(\lVert W\rVert_{\psi_2\mid X}\) | conditional Luxemburg sub-Gaussian convention | def:model-parameters |
| \(O\) | \(O=(X,T,Y)\) | observation triple | def:plm-model |
| \(X,T,Y\) | \(X,T,Y\) | covariate, treatment, and outcome coordinates | def:plm-model |
| \(P\) | \(P\) | observed-data law | def:plm-model |
| \(\theta_0\) | \(\theta_0\) | partially linear coefficient for a fixed law | def:plm-model |
| \(g_0,q_0\) | \(g_0,q_0\) | treatment and outcome regression functions | def:plm-model |
| \(\widehat g,\widehat q\) | \(\widehat g=(\widehat g_n)_{n\in\mathbb N}\), \(\widehat q=(\widehat q_n)_{n\in\mathbb N}\) | deterministic supplied code sequences | def:plm-model |
| \(\eta\) | \(\eta=T-g_0(X)\) | treatment innovation | def:plm-model |
| \(\xi\) | \(\xi=Y-q_0(X)-\theta_0\eta\) | outcome innovation | def:plm-model |
| \(\bar g_n,\bar q_n\) | \(\bar g_n,\bar q_n\) | clipped supplied treatment and outcome codes | def:plm-model |
| \(P_X\) | \(P_X\) | covariate marginal of \(P\) | def:plm-model |
| \(m\) | \(m\) | model instance | def:plm-model |
| \(\theta_0(P)\) | \(\theta_0(P)\) | partially linear coefficient under law \(P\) | def:plm-model |
| \(O_1,\ldots,O_n\) | \(O_1,\ldots,O_n\) | i.i.d. observations from \(P\) | ass:iid-sampling |
| \(\kappa_k(\eta)\) | \(\kappa_k(\eta)\) | \(k\)th cumulant of treatment noise | ass:cumulant-separation |
| \(\mathcal P_{\mathrm{NG},n}\) | \(\mathcal P_{\mathrm{NG},n}\) | cumulant-separated class with \(L^1(P_X)\) treatment-code control | def:non-gaussian-class |
| \(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | \(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | bounded-outcome Gaussian JMS comparison class | def:gaussian-class |
| \(\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}\) | \(\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}\) | published ACE cumulant-separated comparison class | def:jms-ace-class |
| \(W\) | \(W=W(O_1,\ldots,O_n)\) | real-valued sample statistic in the quantile construction | def:model-parameters |
| \(P^{\otimes n}\) | \(P^{\otimes n}\) | i.i.d. product law for \(n\) observations | def:generalized-quantile |
| \(F_W(t)\) | \(F_W(t)=\Pr(W\le t)\) | distribution function of \(W\) under \(P^{\otimes n}\) | def:generalized-quantile |
| \(Q_{P,1-\gamma}(W)\) | \(Q_{P,1-\gamma}(W)\) | generalized lower \((1-\gamma)\)-quantile | def:generalized-quantile |
| \(D_n(X)\) | \(D_n(X)=g_0(X)-\bar g_n(X)\) | treatment-code error | def:outcome-contamination |
| \(b_n(X)\) | \(b_n(X)=q_0(X)-\theta_0D_n(X)\) | outcome contamination induced by treatment-code error | def:outcome-contamination |
| \(B_n(z)\) | \(B_n(z)=E_P[b_n(X)e^{zD_n(X)}]\) | weighted exponential transform of outcome contamination | def:outcome-contamination |
| \(a_{1,n},b_{1,n},a_2,b_{2,n}\) | \(a_{1,n},b_{1,n},a_2,b_{2,n}\) | JMS eligibility quantities from condition (21) | def:jms-eligibility-quantities |
| \(M(z)\) | \(M(z)=E_P[e^{z\eta}]\) | treatment-innovation moment-generating function | thm:known-zero-instrument |
| \(z_0,\ell\) | \(z_0,\ell\) | zero of \(M\) and its multiplicity | def:zero-instrument |
| \(J_{z_0,\ell}(w)\) | \(J_{z_0,\ell}(w)=w^{\ell-1}e^{z_0w}\) | zero-based instrument | def:zero-instrument |
| \(Z_n\) | \(Z_n=T-\bar g_n(X)\) | residualized treatment using the supplied treatment code | def:contour-functional |
| \(F_n(z)\) | \(F_n(z)=E_P[e^{zZ_n}]\) | observable treatment-residual transform | def:contour-functional |
| \(G_n(z)\) | \(G_n(z)=E_P[Ye^{zZ_n}]\) | observable outcome-weighted transform | def:contour-functional |
| \(H_n(z)\) | \(H_n(z)=E_P[e^{z\{g_0(X)-\bar g_n(X)\}}]\) | nuisance transform from treatment-code error | def:contour-functional |
| \(C_j\) | \(C_j\) | positively oriented contour circle | def:contour-functional |
| \(N_{C_j}(F_n)\) | \(N_{C_j}(F_n)\) | zero count of \(F_n\) inside \(C_j\), with multiplicity | def:contour-functional |
| \(\Theta_{C_j}(F_n,G_n)\) | \(\Theta_{C_j}(F_n,G_n)\) | contour ratio functional identifying \(\theta_0\) | def:contour-functional |
| \(\mathfrak R_n^{\mathrm{NG}}\) | \(\mathfrak R_n^{\mathrm{NG}}\) | minimax MSE over \(\mathcal P_{\mathrm{NG},n}\) | def:minimax-risks |
| \(\mathfrak R_n^{\mathrm G}\) | \(\mathfrak R_n^{\mathrm G}\) | minimax MSE over \(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | def:minimax-risks |
| \(\mathfrak M_{n,1-\gamma}^{\mathrm G}\) | \(\mathfrak M_{n,1-\gamma}^{\mathrm G}\) | minimax generalized-quantile risk over \(\mathcal P_{\mathrm G,n}^{\mathrm{JMS}}\) | def:minimax-risks |
| \(\widetilde\theta(O_1,\ldots,O_n;\bar g_n,\bar q_n)\) | \(\widetilde\theta(O_1,\ldots,O_n;\bar g_n,\bar q_n)\) | estimator in class-indexed minimax criteria | def:minimax-risks |
| \(\mathcal C(p;\bar g_n,\bar q_n)\) | \(\mathcal C(p;\bar g_n,\bar q_n)\) | fixed-code restriction of a law class | def:minimax-risks |
| \(\mathfrak R_n^{\mathrm{NG}}(p;\widehat g,\widehat q)\) | \(\mathfrak R_n^{\mathrm{NG}}(p;\widehat g,\widehat q)\) | displayed-parameter non-Gaussian minimax MSE | def:minimax-risks |
| \(\mathfrak R_n^{\mathrm G}(p;\widehat g,\widehat q)\) | \(\mathfrak R_n^{\mathrm G}(p;\widehat g,\widehat q)\) | displayed-parameter Gaussian JMS minimax MSE | def:minimax-risks |
| \(\mathfrak M_{n,1-\gamma}^{\mathrm G}(p;\widehat g,\widehat q)\) | \(\mathfrak M_{n,1-\gamma}^{\mathrm G}(p;\widehat g,\widehat q)\) | displayed-parameter Gaussian JMS minimax generalized-quantile risk | def:minimax-risks |
| \(\mathsf E_n^{\mathrm{JMS}}\) | \(\mathsf E_n^{\mathrm{JMS}}\) | JMS order-\(r\) eligibility condition | def:jms-eligibility |
| \(\Pi_{[-C_{\theta},C_{\theta}]}\) | \(\Pi_{[-C_{\theta},C_{\theta}]}\) | projection onto \([-C_{\theta},C_{\theta}]\) | def:sine-estimator |
| \(\widehat\theta_{\sin,n}\) | \(\widehat\theta_{\sin,n}\) | clipped sine-ratio estimator for symmetric Gaussian-mixture treatment noise | def:sine-estimator |
| \(\mathscr C_m\) | \(\mathscr C_m\) | finite deterministic library of rational circles at depth \(m\) | def:local-gaussian-handle |
| \(\widehat F_{a,n},\widehat G_{a,n}\) | \(\widehat F_{a,n},\widehat G_{a,n}\) | split-fold empirical transforms | def:local-gaussian-handle |
| \(W_{a,C}(t),V_{a,C}(t)\) | \(W_{a,C}(t),V_{a,C}(t)\) | empirical winding and contour-moment integrands | def:local-gaussian-handle |
| \(\widehat v_{a,C}\) | \(\widehat v_{a,C}\) | angular variance of the empirical contour-moment integrand | def:local-gaussian-handle |
| \(\mathcal P_{\mathrm{NG},n}^{\mathrm{ACE}}\) | \(\mathcal P_{\mathrm{NG},n}^{\mathrm{ACE}}\) | \(L^s(P_X)\)-restricted subclass of \(\mathcal P_{\mathrm{NG},n}\) for ACE comparison | def:ace-comparison-subclass |
| \(\mathsf{CCIA}_{\mathrm{build}}\) | \(\mathsf{CCIA}_{\mathrm{build}}\) | bounded-build specification for certified contour arithmetic | def:certified-contour-arithmetic-substrate |
| \(I_m\) | \(I_m=[I_m^-,I_m^+]\) | rational closed interval in a certified-real record | def:certified-contour-arithmetic-substrate |
| \(\mu\) | \(\mu:\mathbb Q_{>0}\to\mathbb N\) | executable modulus in a certified-real record | def:certified-contour-arithmetic-substrate |
| \(p>0\) | \(p>0\) | rational positivity witness for a positive record | def:certified-contour-arithmetic-substrate |
| \(\operatorname{sq}_{-}(A),\operatorname{sq}_{+}(A)\) | \(\operatorname{sq}_{-}(A),\operatorname{sq}_{+}(A)\) | lower and upper square bounds for a real interval | def:certified-contour-arithmetic-substrate |
| \(N_{\mathrm{mesh}}\) | \(N_{\mathrm{mesh}}=\lceil L/e\rceil+1\) | mesh size used for certified contour enclosures | def:certified-contour-arithmetic-substrate |
| \(\operatorname{Name}(x)\) | \(\operatorname{Name}(x)\) | certified-real record for \(x\) | def:contour-bank-handle |
| \(\operatorname{Name}_{+}(x)\) | \(\operatorname{Name}_{+}(x)\) | positive certified-real record for \(x\) | def:contour-bank-handle |
| \(\mathfrak p_{\star}\) | \(\mathfrak p_{\star}\) | fixed primitive certified-record tuple for the contour bank | def:contour-bank-handle |
| \(k_{\star}\) | \(k_{\star}\) | exact natural-number field of \(\mathfrak p_{\star}\) | def:contour-bank-handle |
| \(\mathfrak d_{\star}\) | \(\mathfrak d_{\star}:\operatorname{Name}_{+}(\delta)\) | fixed positive name for \(\delta\) | def:contour-bank-handle |
| \(\mathfrak p_{\eta,\star}\) | \(\mathfrak p_{\eta,\star}:\operatorname{Name}_{+}(\psi_{\eta})\) | fixed positive name for \(\psi_{\eta}\) | def:contour-bank-handle |
| \(\mathfrak r_{0,\star},\mathfrak r_{1,\star}\) | \(\mathfrak r_{0,\star},\mathfrak r_{1,\star}\) | fixed positive names for \(R_0\) and \(R_1\) | def:contour-bank-handle |
| \(R_0,R_1\) | \(R_0,R_1\) | zero-localization radius and outer radius | def:contour-bank-handle |
| \(A_k\) | \(A_k=(2^{k+4}k!)^{1/(k-2)}\) | numerical factor in zero localization | def:contour-bank-handle |
| \(B\) | \(B\) | bank data assembled from \(p\) and \(\mathfrak p_{\star}\) | def:contour-bank-handle |
| \(u_{\psi},u_R\) | \(u_{\psi},u_R\) | rational upper endpoints returned by primitive moduli at error one | def:contour-bank-handle |
| \(U_{\psi},U_R,N_{\mathrm{cert}}\) | \(U_{\psi},U_R,N_{\mathrm{cert}}\) | integer bounds defining bank fuel | def:contour-bank-handle |
| \(m_{\star},d_{\star},h_{\star},J_{\mathrm{base}},J\) | \(m_{\star},d_{\star},h_{\star},J_{\mathrm{base}},J\) | dyadic mesh constants and bank size | def:contour-bank-handle |
| \(\mathfrak\rho_j\) | \(\mathfrak\rho_j\) | certified-real radius record for the \(j\)th circle | def:contour-bank-handle |
| \(e_{\star},d_{\star}^{\mathrm{den}},u_{\star},a_{\star,\mathbb Q},a_{\star}\) | \(e_{\star},d_{\star}^{\mathrm{den}},u_{\star},a_{\star,\mathbb Q},a_{\star}\) | integer fuel constants and positive dyadic lower-modulus certificate | def:contour-bank-handle |
| \(\varepsilon_{1n},\varepsilon_{2n}\) | \(\varepsilon_{1n},\varepsilon_{2n}:\mathbb N\to\mathbb R\) | nonnegative nonincreasing radius sequences in the estimator record | def:adaptive-contour-estimator |
| \(\mathfrak c_{\theta,\star}\) | \(\mathfrak c_{\theta,\star}\) | fixed represented range record for \(C_{\theta}\) | def:adaptive-contour-estimator |
| \(\mathcal I_m(x)\) | \(\mathcal I_m(x)\) | floor-dyadic observation-coordinate interval | def:adaptive-contour-estimator |
| \(\widehat\theta_{\mathrm{spec},n}\) | \(\widehat\theta_{\mathrm{spec},n}\) | total Borel contour statistic using fixed primitive records | def:adaptive-contour-estimator |
| \(\widetilde{\mathfrak s}\) | \(\widetilde{\mathfrak s}=((\mathfrak t_i,\mathfrak y_i,\mathfrak g_i)_{i=1}^n)\) | represented observation record | def:adaptive-contour-estimator |
| \(\mathfrak s_{\star}\) | \(\mathfrak s_{\star}\) | represented-data input record with fixed primitive components | def:adaptive-contour-estimator |
| \(\mathfrak t_i,\mathfrak y_i,\mathfrak g_i\) | \(\mathfrak t_i,\mathfrak y_i,\mathfrak g_i\) | certified digital records for \(T_i,Y_i,\bar g_n(X_i)\) | def:adaptive-contour-estimator |
| \(\mathfrak z_i\) | \(\mathfrak z_i=\mathfrak t_i-\mathfrak g_i\) | certified subtraction record for \(T_i-\bar g_n(X_i)\) | def:adaptive-contour-estimator |
| \(\widehat F_{a,n}^{(p)}(z),\widehat G_{a,n}^{(p)}(z)\) | \(\widehat F_{a,n}^{(p)}(z),\widehat G_{a,n}^{(p)}(z)\) | empirical derivative-sum enclosures used by the transducer | def:adaptive-contour-estimator |
| \(U_{Z,i},U_{Y,i},U_{\rho,j}\) | \(U_{Z,i},U_{Y,i},U_{\rho,j}\) | rational upper magnitude bounds for records used in mesh fuel | def:adaptive-contour-estimator |
| \(z_j(t)\) | \(z_j(t)=\rho_je^{2\pi it}\) | parametrization of the \(j\)th contour | def:adaptive-contour-estimator |
| \(W_{0j}(t),V_j(t)\) | \(W_{0j}(t),V_j(t)\) | certified pilot winding and evaluation-fold contour integrands | def:adaptive-contour-estimator |
| \(N_j,m_j\) | \(N_j,m_j\) | certified zero count and lower-modulus certificate for a candidate circle | def:adaptive-contour-estimator |
| \(y\) | \(y\in\mathbb Q\) | rational midpoint of the real contour-moment interval | def:adaptive-contour-estimator |
| \(\operatorname{clip}_{C_{\theta}}(y)\) | \(\operatorname{clip}_{C_{\theta}}(y)\) | interval-arithmetic clipping of \(y\) to \([-C_{\theta},C_{\theta}]\) | def:adaptive-contour-estimator |
| \(F,G\) | \(F,G:\mathbb C\to\mathbb C\) | population denominator and numerator maps compared with evaluation-fold empirical transforms | lem:selected-contour-perturbation-bound |
| \(d,e\) | \(d,e\) | uniform denominator and numerator errors on the selected circle | lem:selected-contour-perturbation-bound |
| \(\vartheta\) | \(\vartheta\) | real target identified by the selected contour ratio | lem:selected-contour-perturbation-bound |
| \(C_G(p)\) | \(C_G(p)\) | population envelope for \(G_n(z)\) on \(|z|\le R_1\) | lem:population-numerator-envelope |
| \(\zeta\) | \(\zeta\sim N(0,(\psi/4)^2)\) | Gaussian residual used for the Luxemburg scale calculation | lem:gaussian-exponential-square-quarter-scale |
| \(c,C\) | \(c,C\) | constants in the main fixed-separation MSE theorem | thm:adaptive-rootn-minimax |
| \(p_0\) | \(p_0\) | baseline parameter record with fixed primitive entries | thm:adaptive-rootn-minimax |
| \(\mathcal P_{\mathrm{NG},n}(p;\mathrm{base})\) | \(\mathcal P_{\mathrm{NG},n}(p;\mathrm{base})\) | fixed-code non-Gaussian class relative to a base model | thm:adaptive-rootn-minimax |
| \(\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}(p;\mathrm{base})\) | \(\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}(p;\mathrm{base})\) | fixed-code JMS ACE class relative to a base model | thm:adaptive-rootn-minimax |
| \(C_{\mathrm{spec}}\) | \(C_{\mathrm{spec}}>0\) | spectral quantile-bound constant in the ACE comparison | prop:jms-ace-alignment |
| \(\widehat\theta_{\mathrm{ACE},r,n}\) | \(\widehat\theta_{\mathrm{ACE},r,n}\) | published order-\(r\) ACE estimator | prop:jms-ace-alignment |
| \(B_{\mathrm{ACE},n,\gamma}\) | \(B_{\mathrm{ACE},n,\gamma}\) | JMS ACE generalized-quantile upper guarantee | prop:jms-ace-alignment |
| \(C_{\gamma}\) | \(C_{\gamma}\) | JMS generalized-quantile guarantee constant | prop:jms-ace-alignment |
| \((p_n)\) | \((p_n)\) | sequence of parameter records used in upper-guarantee separation | prop:jms-ace-alignment |
| \((p_j)\) | \((p_j)\) | sequence of parameter records in the common-experiment result | thm:common-experiment-dichotomy |
| \(n_j\) | \(n_j=p_j.n\) | sample size along the common-experiment sequence | thm:common-experiment-dichotomy |
| \(W,R,\theta,A,\mu_W\) | \(W,R,\theta,A,\mu_W\) | numerator, denominator, target, scale, and denominator mean in clipped-ratio algebra | lem:clipped-ratio-risk-decomposition |
| \(K\) | \(K\) | constant in the uniform empirical-transform \(L^2\) bound | lem:empirical-transform-uniform-l2 |
| \(c_0,C_0,\tau,c_{\mathrm{ACE}}\) | \(c_0,C_0,\tau,c_{\mathrm{ACE}}\) | constants in the one-dimensional lower-bound submodel | lem:non-gaussian-hard-submodel |
| \(P_{n,\vartheta}\) | \(P_{n,\vartheta}\) | one-dimensional hard submodel indexed by \(\vartheta\) | lem:non-gaussian-hard-submodel |
| \(P^{\circ}\) | \(P^{\circ}\) | starting law in \(\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}\) for the ACE-class submodel | lem:non-gaussian-hard-submodel |
| \(P_{n,\vartheta}^{\mathrm{ACE}}\) | \(P_{n,\vartheta}^{\mathrm{ACE}}\) | ACE-class one-dimensional hard submodel indexed by \(\vartheta\) | lem:non-gaussian-hard-submodel |
| \(D_{\mathrm{KL}}\) | \(D_{\mathrm{KL}}\) | product relative entropy used in the lower-bound path | lem:non-gaussian-hard-submodel |
| \(g_{\star},q_{\star}\) | \(g_{\star},q_{\star}:\mathcal X\to\mathbb R\) | fixed clipped-code functions in the ACE minimax lower bound | lem:non-gaussian-hard-submodel |
| \(G_{\circ},S\) | \(G_{\circ},S\) | standard Gaussian and symmetric Rademacher variables in the benchmark path | lem:gaussian-rademacher-l1-benchmark |
| \(t_a,A_a,\Delta_a\) | \(t_a,A_a,\Delta_a\) | first positive zero, denominator scale, and fourth-cumulant magnitude on the benchmark path | lem:gaussian-rademacher-l1-benchmark |
| \(M_a(z)\) | \(M_a(z)\) | moment-generating function along the Gaussian--Rademacher path | lem:gaussian-rademacher-l1-benchmark |
| \(\widehat\theta_{a,n}\) | \(\widehat\theta_{a,n}\) | clipped sine-ratio estimator along the Gaussian--Rademacher path | lem:gaussian-rademacher-l1-benchmark |
| \((\delta_n)_{n\in\mathbb N}\) | \((\delta_n)_{n\in\mathbb N}\) | shrinking positive cumulant-separation thresholds | thm:local-to-gaussian-partial-benchmarks |
| \(\Delta\) | \(\Delta=\delta_n\) | local cumulant threshold used in the ACE benchmark | thm:local-to-gaussian-partial-benchmarks |
| \(b_{2,n}(\Delta)\) | \(b_{2,n}(\Delta)\) | local JMS eligibility quantity with threshold \(\Delta\) | thm:local-to-gaussian-partial-benchmarks |
| \(B_{\mathrm{ACE},n,\gamma}(\Delta;C_{\gamma})\) | \(B_{\mathrm{ACE},n,\gamma}(\Delta;C_{\gamma})\) | local ACE generalized-quantile upper bound | thm:local-to-gaussian-partial-benchmarks |
| \(U_{\mathrm{DML}},U_{\mathrm{ACE}}\) | \(U_{\mathrm{DML}},U_{\mathrm{ACE}}\) | oracle upper-bound inputs in the local benchmark comparison | thm:local-to-gaussian-partial-benchmarks |

notation_gaps: none

env_overrides: prop:jms-ace-alignment=propositionv, prop:symmetric-mixture-reduction=propositionv, prop:bounded-outcome-gaussian-degeneracy=propositionv, oeq:local-to-gaussian-frontier=remarkv, def:adaptive-contour-estimator=algorithmv

# Sections
## section: Introduction
The introduction will motivate estimation of a partially linear coefficient when treatment residuals are formed with a supplied first-stage treatment code. It will explain the central mechanism: independent cumulant-separated treatment innovations generate complex transform zeros, and those zeros yield instruments and contour ratios that remain stable under sufficiently accurate \(L^1(P_X)\) treatment-code error. It will state the fixed-separation statistical contribution in reader-facing terms and close with a single factual sentence directing readers to the verification appendix for the machine-checked scope.
objs:
bib: Engle1986, Robinson1988, Speckman1988, HardleLiangGao2000

## section: Related work
This section will position the paper in the partially linear and semiparametric literature, the orthogonal-score and higher-order influence-function tradition, transform-based estimation, zero and completeness arguments, non-Gaussian identification, and certified numerical analysis. The closest competing results are \citet{MackeySyrgkanisZadik2018}, which identifies the role of non-Gaussian treatment residuals in higher-order orthogonal learning for the partially linear model, and \citet{JinMackeySyrgkanis2025}, whose order-\(r\) ACE guarantee controls the \(1-\gamma\) error quantile by a constant multiple of \(\varepsilon_{1,n}^r\varepsilon_{2,n}+C_{\theta}\varepsilon_{1,n}^{r+1}+(\gamma n)^{-1/2}\) with prefactor \(r!\,16^r\delta^{-1}\). The section will compare that published finite-order upper guarantee with the fixed-separation contour upper guarantee on the common ACE class, and will situate transform zeros as classical analytic technology applied here to learned-residual contamination.
objs:
bib: Hansen1982, Newey1990, Newey1994, NeweyMcFadden1994, BickelKlaassenRitovWellner1993, VanDerVaart1998, VanDerVaartWellner1996, ChernozhukovEtAl2018DML, NeweyRobins2018, RobinsRotnitzkyZhao1994, VanDerLaanRubin2006, ChernozhukovEscancianoIchimuraNeweyRobins2022, BelloniChernozhukovHansen2014, RobinsLiTchetgenVanDerVaart2008, LiuMukherjeeRobinsTchetgen2021, LiuMukherjeeNeweyRobins2017, MackeySyrgkanisZadik2018, JinMackeySyrgkanis2025, FeuervergerMcDunnough1981, Singleton2001, ChackoViceira2003, CarrascoFlorensRenault2007, Carrasco2017, KaganLinnikRao1973, Mattner1992, DHaultfoeuille2011, DarollesFanFlorensRenault2011, HuShiu2022, Comon1994, HyvarinenOja1997, HyvarinenKarhunenOja2001, LanneMeitzSaikkonen2017, LeeMesters2024, HoeschLeeMesters2024, ReizingerEtAl2025, Weihrauch2000, Ko1991, Moore1966, Vershynin2018, Wainwright2019

## section: Setup and assumptions
This section will introduce the parameter record, observed-data partially linear model, residuals, deterministic clipped codes, i.i.d. sampling convention, tail and cumulant restrictions, and the law classes used for the main and comparison results. It will also define generalized quantiles, minimax MSE criteria, treatment-code contamination, JMS eligibility quantities, and the \(L^s(P_X)\)-restricted subclass used to align the spectral and ACE comparisons.
objs: def:model-parameters, def:plm-model, ass:iid-sampling, ass:independent-treatment-noise, ass:outcome-mean-independence, ass:theta-range, ass:g-range, ass:q-range, ass:bounded-gaussian-outcome, ass:eta-subgaussian, ass:xi-subgaussian, ass:cumulant-separation, ass:treatment-code-radius, ass:outcome-code-radius, ass:jms-treatment-code-radius, ass:jms-outcome-code-radius, ass:gaussian-treatment-noise, ass:l1-treatment-code-radius, def:non-gaussian-class, def:gaussian-class, def:jms-ace-class, def:generalized-quantile, def:outcome-contamination, def:jms-eligibility-quantities, def:minimax-risks, def:jms-eligibility, def:ace-comparison-subclass
bib: Robinson1988, ChernozhukovEtAl2018DML, MackeySyrgkanisZadik2018, JinMackeySyrgkanis2025, Vershynin2018, Wainwright2019

## section: Zero instruments and contour identification
This section will develop the analytic identification mechanism. It will define zero instruments and observable contour functionals, state the learned-residual factorization, and show how contours enclosing zeros of the observable transform recover the partially linear coefficient under the displayed zero-free and positive-count conditions.
objs: def:zero-instrument, def:contour-functional, thm:known-zero-instrument, lem:observable-factorization, thm:exact-contour-identification
bib: KaganLinnikRao1973, Mattner1992, DHaultfoeuille2011, DarollesFanFlorensRenault2011, HuShiu2022, FeuervergerMcDunnough1981, Singleton2001, CarrascoFlorensRenault2007, Carrasco2017

## section: Main fixed-separation result
This section will present the fixed-\(\delta\) contour construction in standard statistical language: cumulant separation gives a numerical zero-localization radius, \(L^1(P_X)\) treatment-code stability preserves the relevant zero geometry, empirical transforms are controlled on the contour domain, and the resulting total Borel statistic attains \(\Theta(n^{-1})\) minimax MSE with the corresponding generalized-quantile bound. It will then give the sequence-level companion: along any sequence of parameter records sharing the fixed constants, one contour bank serves the sequence, and on the bounded-outcome Gaussian comparison class the target is degenerate. Implementation-specific certified-record clauses in the theorems will be interpreted briefly and developed in the certified-construction appendix.
objs: lem:luxemburg-mgf-envelope, lem:zero-localization, lem:population-numerator-envelope, def:adaptive-contour-estimator, thm:adaptive-rootn-minimax, thm:common-experiment-dichotomy
bib: BickelKlaassenRitovWellner1993, VanDerVaart1998, VanDerVaartWellner1996, ChernozhukovEtAl2018DML, NeweyRobins2018, RobinsLiTchetgenVanDerVaart2008, LiuMukherjeeRobinsTchetgen2021, LiuMukherjeeNeweyRobins2017, MackeySyrgkanisZadik2018, MichelenSahasrabudhe2019, EremenkoFryntov2021, DinhGhoshTranTran2021

## section: Comparison with ACE and Gaussian benchmarks
This section will align the cumulant-separated spectral class with the published ACE class, report the order-\(r\) ACE generalized-quantile upper guarantee on the common class, and compare the fixed-separation upper guarantees when the ACE nuisance terms dominate \(n^{-1/2}\). It will also state the bounded-outcome Gaussian diagnostic, where the simultaneous exact-PLM, bounded-\(Y\), and Gaussian treatment-noise restrictions force the target to be zero on the JMS Gaussian comparison class.
objs: prop:jms-ace-alignment, prop:bounded-outcome-gaussian-degeneracy, lem:jms-ace-class-relations
bib: JinMackeySyrgkanis2025, MackeySyrgkanisZadik2018, ChernozhukovEtAl2018DML, NeweyRobins2018

## section: Explicit mixture reductions and local benchmarks
This section will present constructive weak-non-Gaussian benchmarks: the computable sine-ratio estimator for the symmetric Gaussian mixture and the Gaussian--Rademacher \(k=4\) path with its explicit denominator scale and risk bound. It will also state the local ACE oracle benchmark with shrinking cumulant thresholds as an upper-envelope benchmark for comparison with ordinary DML upper bounds under their own hypotheses.
objs: def:sine-estimator, prop:symmetric-mixture-reduction, lem:clipped-ratio-risk-decomposition, lem:gaussian-rademacher-l1-benchmark, thm:local-to-gaussian-partial-benchmarks
bib: LeeMesters2024, HoeschLeeMesters2024, LanneMeitzSaikkonen2017, Comon1994, HyvarinenOja1997, HyvarinenKarhunenOja2001, ReizingerEtAl2025, JinMackeySyrgkanis2025

## section: Limitations and future work
This section will collect the adaptive-selection agenda for triangular treatment-noise laws with shrinking cumulant separation. It will frame future work around sharp minimax MSE rates as a function of \((n,\varepsilon_{1,n},\varepsilon_{2,n},\delta_n)\), uniformly valid inference, and local minimax lower bounds, keeping that agenda separate from the fixed-separation contour theorem and from the construction-specific local benchmarks.
objs: def:local-gaussian-handle, oeq:local-to-gaussian-frontier
bib: JinMackeySyrgkanis2025, MackeySyrgkanisZadik2018, ChernozhukovEtAl2018DML, NeweyRobins2018, LeeMesters2024, HoeschLeeMesters2024

## section: Appendix A: proofs for identification and analytic localization
This appendix will give the proofs for zero instruments, observable factorization, contour identification, and zero localization, and then prove the deterministic finite contour-bank guarantee in mathematical form. The appendix will use the analytic probability and complex-analysis inputs needed for the zero-radius and contour arguments.
objs: lem:finite-contour-bank
bib: KaganLinnikRao1973, Mattner1992, MichelenSahasrabudhe2019, EremenkoFryntov2021, DinhGhoshTranTran2021

## section: Appendix B: empirical process, stability, and lower-bound lemmas
This appendix will collect the statistical auxiliary results supporting the main theorem: uniform \(L^2\) control of the empirical transforms, the \(L^1(P_X)\) nuisance-stability argument that preserves zero geometry, the Gaussian exponential-square scale calculation, and the one-dimensional hard submodel that gives the \(n^{-1}\) class lower bound on the broad spectral and ACE classes.
objs: lem:empirical-transform-uniform-l2, lem:l1-nuisance-zero-free, lem:gaussian-exponential-square-quarter-scale, lem:non-gaussian-hard-submodel
bib: VanDerVaart1998, VanDerVaartWellner1996, BickelKlaassenRitovWellner1993, Vershynin2018, Wainwright2019

## section: Appendix C: certified construction and executable correspondence
This technical appendix will preserve the finite-representation contract while keeping the main statistical exposition focused on identification and risk. It will give the bounded-build specification, certified-real record conventions, dyadic bank construction, represented-data transducer, fallback behavior, and trace-level correspondence required by the executable clauses, all relative to the same fixed primitive records used by the ordinary-sample Borel statistic. It will close with the deterministic good-event accuracy bound for the statistic on a selected bank circle, which the main risk proof cites for its perturbation display.
objs: def:certified-contour-arithmetic-substrate, def:contour-bank-handle, lem:selected-contour-perturbation-bound
bib: Weihrauch2000, Ko1991, Moore1966

## section: Appendix D: verification scope and crosswalk
This brief appendix note will consolidate the Lean verification scope and map reader-facing statistical claims to their exact frozen statements. It will state that the formal results are machine-checked under their displayed external interfaces and cited comparator assumptions, while published inputs such as the JMS ACE guarantee enter through the verified citation boundary. It states no result of its own.
objs:
bib: JinMackeySyrgkanis2025