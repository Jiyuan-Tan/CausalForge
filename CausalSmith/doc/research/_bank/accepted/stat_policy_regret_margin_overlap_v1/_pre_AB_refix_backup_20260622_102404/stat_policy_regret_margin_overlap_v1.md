# stat_policy_regret_margin_overlap — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (observed-law policy-learning class over a measurable cova…).** observed-law policy-learning class over a measurable covariate space: a probability law P on O=(X,A,Y) in 𝒳×{0,1}×[-1,1] with covariate marginal P_X, propensity e_P, overlap p_P, outcome regressions mu_0/mu_1, contrast tau_P, welfare V_P, regret R_P, optimal/comparator policies over a policy class Pi. — F2.5 redirect hard constraint: PolicyRegretLaw must be an observed-law substrate, not a thin covariate-only skeleton. Include an observation type O=(X,A,Y) and an observed probability law on observations, with covariate marginal P_X, propensity e_P, outcome regressions mu0/mu1, contrast tau, support/bounded-outcome semantics, welfare/regret, and policy class hooks tied to that law. It is acceptable to keep mu0/mu1/propensity as primitive fields, but do NOT omit observedLaw/sample semantics. Do NOT model the witness over Unit. bypass-justified. Searched API.md §8h (PO/) + §9g (ATE) + §13'''(CATE) for a reusable observed-law/welfare/policy primitive carrying a contrast function and covariate marginal: grep 'policy welfare regret contrast' over ../doc/API.md and doc/API.md → only deleted STAT_PolicyRegretMarginOverlap entries (doc/API.md §3.3) match; Causalean PO/CATE worlds are SCM/counterfactual measure spaces with potential-outcome kernels, a different abstraction (no tau_P/P_X/e_P as free primitives). Define-local structure PolicyRegretLaw 𝒳 bundling covariateMeasure (Measure 𝒳, IsProbabilityMeasure), contrast, propensity (and derived overlap), the policy type Policy 𝒳 := 𝒳→Bool, lawOptimalPolicy, lawWelfare, lawRegret. This is the highest-leverage reuse decision and is intentionally bespoke.
**required modules.** 

**S-2 (i.i.d).** i.i.d. offline sampling + n-sample product experiment and minimax functional: O_1,...,O_n iid from P (Measure.pi), least-favorable two-point construction scales, minimax/feasible risk functionals over the product law. — F2.5 redirect hard constraint: the n-sample experiment is Measure.pi over the S1 observed law, and minimax/upper-risk functionals must quantify over measurable Pi-valued estimators, not arbitrary functions. Tie sampleLaw, lawClass, feasibleERM, q_n/u_n schedule, crossfit folds, and nuisance estimators together in the statements. Constants in asymptotic bounds must be chosen before n, with an all-large-n quantifier. Encode the i.i.d. n-sample experiment DIRECTLY as the product law Measure.pi (fun _ : Fin n => P) over the S1 single-observation world — no bespoke product-measure constructor and no reused world decl hosts it. The minimax/feasible regret functionals M_n (def:minimax-regret) and U_n (def:upper-risk), and the two-point construction scales h_n, q_n, B_n (def:two-point-witness), are all bespoke define-local objects over Measure.pi and the S1 PolicyRegretLaw; they are NOT supplied by any reused world. disposition=define-local accordingly (reuse=null). Causalean.Stat.iid_two_point_lower_bound is cited ONLY as ANALOGOUS minimax/Le-Cam substrate — the two-point lower-bound pattern thm:minimax-lower adapts (a packaged iid two-point reduction over Measure.pi), not the host of these functionals. The chi-square product layer is genuinely reused, but at the CHILD nodes that need it, not here: CausalSmith.Mathlib.InformationTheory.ProductChiSquared.{one_add_chiSqDiv_pi_iid_general, chiSqDiv_eq_sum_partition_of_restrict_eq_smul} and Causalean.Stat.{chiSqDiv, chiSqDiv_prod} at lem:two-point-divergence, and Causalean.Stat.{one_sub_tvDist_le_test, tvDist_le_half_sqrt_chiSqDiv} at lem:le-cam-two-point-chisq (../doc/API.md §12w.2-12w.6, §2c.3). Modules listed are the analogous/supporting layers those child reuses draw on.
**required modules.** Causalean.Stat.Minimax.MinimaxRisk, Causalean.Stat.Minimax.ChiSquared, Causalean.Stat.Minimax.TotalVariation, CausalSmith.Mathlib.InformationTheory.ProductChiSquared

## Assumptions (A)

**A-1 (assumption).** O_1, ..., O_n are i.i.d. draws from P.

**A-2 (assumption).** Y = A Y(1) + (1 - A) Y(0).

**A-3 (assumption).** (Y(0), Y(1)) is independent of A given X under P.

**A-4 (assumption).** Y(a) in [-1, 1] for a in {0,1}.

**A-5 (assumption).** 0 < e_P(X) < 1 holds P_X-almost surely.

**A-6 (assumption).** P(0 < |tau_P(X)| <= u) <= C_m u^alpha for all 0 < u <= u_0.

**A-7 (assumption).** Either P_X{tau_P(X)=0}=0, or every pi in Pi agrees with pi_star P_X-almost everywhere on {tau_P(X)=0}.

**A-8 (assumption).** P{p_P(X) <= v, 0 < |tau_P(X)| <= u} <= C_o u^alpha v^(1/gamma) for all 0 < v <= c_o u^gamma, with v^(1/gamma)=1 when gamma=0.

**A-9 (assumption).** Pi is a pointwise measurable class of measurable deterministic policies with finite VC dimension d_Pi < infinity: there is a countable subclass Pi_0 subset Pi such that every pi in Pi is the pointwise limit of a sequence from Pi_0.

**A-10 (assumption).** pi_star is an element of Pi for every law P in the class.

**A-11 (assumption).** For the pointwise measurable finite-VC policy class Pi, every centered policy-indexed process with envelope B and conditional second moment bounded by C B^2 P_X(D_pi) has fixed-radius localized supremum bounded by C B n^{-1/2} r^{alpha/(2+2 alpha)}(log n)^p under thm:margin-localization.

**A-12 (assumption).** 0 < u_0 < 2.

**A-13 (assumption).** The cross-fitted nuisance estimators satisfy ||muhat_a-mu_a||_{L2(P)} <= r_mu_n and ||ehat-e||_{L2(P)} <= r_e_n for a in {0,1}, with product-rate r_mu_n r_e_n = O(n^{-1/2}).

**A-14 (assumption).** When gamma=0, p_P(X) >= underline_p holds P_X-almost surely, for a constant underline_p in (0,1/2].

**A-15 (assumption).** The cross-fitted outcome-regression estimates muhat_0, muhat_1 take values in [-1,1].

**A-16 (assumption).** There exist a >= 0, c >= 1/2 and constants C_mu, C_prod such that r_mu_n <= C_mu n^(-a) and r_mu_n r_e_n <= C_prod n^(-c) for all large n.

**A-17 (assumption).** The number K of cross-fitting folds in def:feasible-erm is a fixed finite integer independent of n, and the deterministic fold partition is balanced as stated there.

**A-18 (assumption).** For the same pointwise measurable finite-VC policy class Pi, every centered policy-indexed empirical process z_pi=(P_n-P)g_pi built from an i.i.d. sample of size n, with envelope B and conditional second moment bounded by C B^2 P_X(D_pi), satisfies E sup_{pi in Pi}{2|z_pi|-R_P(pi)/4}_+ <= C (B^2/n)^{A_alpha}(log n)^p.

## Definitions (P)

**P-1 (V_P(pi) = E_P[pi(X) tau_P(X)]).** V_P(pi) = E_P[pi(X) tau_P(X)]; pi_star(x) = 1{tau_P(x) >= 0}; R_P(pi) = V_P(pi_star) - V_P(pi).

**P-2 (D_pi = {x in X ).** D_pi = {x in X : pi(x) != pi_star(x)}.

**P-3 (beta_ag = (0 if gamma = 0 else alpha gamma/(alpha+1))).** beta_ag = (0 if gamma = 0 else alpha gamma/(alpha+1)); D_ag = 2 + alpha + beta_ag; r_star(alpha,gamma) = (1+alpha)/D_ag.

**P-4 (For one fixed nuisance regime (a,c,C_mu,C_prod), let A_al…).** For one fixed nuisance regime (a,c,C_mu,C_prod), let A_alpha=(1+alpha)/(2+alpha). For gamma>0, fix u_bar in (0,u_0] and q_0 in (0,min{1/2,c_o u_bar^gamma}]. Define phi(s,t)=min{A_alpha(1-2s), c-s, a+s/(2 gamma)+alpha t/2, 2a-t} on the compact feasible set 0<=s<=1/2 and 0<=t<=s/gamma. Let (s_feas,t_feas) be any maximizer, set g_joint=phi(s_feas,t_feas), q_n=q_0 n^{-s_feas}, and u_n=u_bar n^{-t_feas}. Then q_n<=c_o u_n^gamma for all large n, and the solved conditional feasible upper exponent is r_up=r_feas=min{r_star(alpha,gamma),g_joint(alpha,gamma,a,c)}. For gamma=0, use fixed q_n=q_0<=underline_p/2 and set r_up=r_feas=min{A_alpha,c}.

**P-5 (e_q(x).** e_q(x; eta) = min{1-q, max{q, e(x)}} for clip q in (0,1/2] and nuisance eta=(mu_0,mu_1,e).

**P-6 (Gamma_q(O).** Gamma_q(O; eta) = mu_1(X) - mu_0(X) + (A/e_q(X;eta))(Y - mu_1(X)) - ((1-A)/(1-e_q(X;eta)))(Y - mu_0(X)).

**P-7 (Fix a countable pointwise-dense subclass Pi_0=(pi_j)_{j>=…).** Fix a countable pointwise-dense subclass Pi_0=(pi_j)_{j>=1} from ass:policy-class and a deterministic balanced K-fold partition I_1,...,I_K of {1,...,n}, where each fold has size floor(n/K) or ceil(n/K). With foldwise cross-fitted nuisances etahat^{(-k)} and clip q in (0,1/2], define Vhat_{n,q}(pi)=n^{-1} sum_i pi(X_i) Gamma_q(O_i; etahat^{(-k(i))}), where k(i) is the evaluation fold of observation i. Let j_n be the smallest index j such that Vhat_{n,q}(pi_j) >= sup_k Vhat_{n,q}(pi_k) - 1/n, and set pi_hat_n=pi_{j_n}. This measurable Pi-valued 1/n-ERM is the feasible clipped-AIPW ERM. The clip q is the analysis tuning parameter chosen by the bias-variance balance.

**P-8 (M_n(alpha,gamma) = inf over measurable data-dependent Pi-…).** M_n(alpha,gamma) = inf over measurable data-dependent Pi-valued estimators pi_hat of sup_{P in P_class} E_P R_P(pi_hat).

**P-9 (Fix one nuisance regime (a,c,C_mu,C_prod) and the determi…).** Fix one nuisance regime (a,c,C_mu,C_prod) and the deterministic schedule (q_n,u_n) selected by def:feasible-rate for that regime. Then U_n(alpha,gamma,a,c; etahat) = sup E_P R_P(pi_hat_n), where the supremum ranges over P in def:law-class for which ass:optimal-in-class holds, over supplied cross-fitted nuisance estimators satisfying ass:nuisance-rate, ass:bounded-crossfit-nuisances, and ass:polynomial-nuisance-exponents with those same exponents a,c and regime constants C_mu,C_prod, with Pi satisfying ass:policy-class, ass:vc-localized-envelope, and ass:vc-localized-offset-envelope, and with the cross-fitting scheme satisfying ass:fixed-crossfit-fold-count.

**P-10 ({ P ).** { P : ass:bounded-outcome, ass:positivity, ass:margin, ass:zero-effect, ass:overlap-decay, and ass:strict-overlap-endpoint hold at exponents (alpha,gamma) }

**P-11 (On X=[0,1] with P_X=Lebesgue, fix h_n=n^{-1/(2+alpha+beta…).** On X=[0,1] with P_X=Lebesgue, fix h_n=n^{-1/(2+alpha+beta_ag)}, q_n=(1/4 if beta_ag=0 else h_n^{beta_ag}), and an active block B_n=[0, c_B h_n^alpha] with P_X(B_n)=c_B h_n^alpha. Choose tau_0 in (u_0,2). The two laws P_{n,sigma}, sigma in {+,-}, share P_X, share the logging propensity e(x)=q_n on B_n and e(x)=1/2 off B_n, and share the off-block outcome law supported on {-1,1} with E[Y|X=x,A=1]=tau_0/2 and E[Y|X=x,A=0]=-tau_0/2 for x notin B_n, so the common off-block optimal label is 1 and the common off-block contrast is tau_0. On B_n set Y=0 almost surely when A=0, and on the active treated cell {X in B_n, A=1} let Y be supported on {-1,1} with P(Y=1 | X in B_n, A=1)=(1+sigma h_n)/2 and P(Y=-1 | X in B_n, A=1)=(1-sigma h_n)/2, so E[Y|X in B_n,A=1]=sigma h_n and tau_{P_{n,sigma}}=sigma h_n on B_n. The laws agree everywhere off the treated active cell. Constants are chosen with 8 C_B C_Q < log 5.

**P-12 (OPEN).** OPEN: In the strict-gap branch of the conditional feasible achievability bound for the regime-indexed risk U_n over def:law-class plus explicit side conditions, determine whether any genuinely feasible estimator under estimated cross-fitted nuisances can attain the converse exponent r_star(alpha,gamma), or whether weak-arm nuisance learning imposes the slower conditional exponent derived in oeq:feasible-upper.

## Lemmas (L)

**L-1 (For all large n the corrected witness laws P_{n,+}, P_{n,…).** For all large n the corrected witness laws P_{n,+}, P_{n,-} satisfy the observed-law member-properties of def:law-class, namely ass:bounded-outcome, ass:positivity, ass:margin, ass:zero-effect, ass:overlap-decay, and ass:strict-overlap-endpoint; hence P_{n,+}, P_{n,-} lie in def:law-class P_class(alpha,gamma). The two explicit witness-optimal policies are x -> 1 and x -> 1{x notin B_n}; if these policies belong to Pi, they are available as the two policy actions used by the later two-point lower-bound reduction. (Normalization: the margin window satisfies u_0<2, so an off-block contrast tau_0 in (u_0, 2) exists under bounded outcomes |Y|<=1.)

**L-2 (For the def:two-point-witness laws, the per-observation c…).** For the def:two-point-witness laws, the per-observation chi-square is chi^2(P_{n,+} || P_{n,-}) <= C m_n q_n h_n^2 with m_n=P_X(B_n)~h_n^alpha and q_n~h_n^{beta_ag}, hence ~ h_n^{2+alpha+beta_ag}; for h_n=n^{-1/(2+alpha+beta_ag)} the n-fold divergence is bounded, chi^2(P_{n,+}^{⊗n} || P_{n,-}^{⊗n}) <= C (equivalently 1+chi^2(P^{⊗n}) = (1+O(h_n^{2+alpha+beta_ag}))^n <= e^{C}).

**L-3 (For the def:two-point-witness laws, inf_{pi in Pi} max_{s…).** For the def:two-point-witness laws, inf_{pi in Pi} max_{sigma in {+,-}} R_{P_{n,sigma}}(pi) >= c h_n^(1+alpha): the optimal policies are opposite on B_n, so any pi misclassifies B_n under at least one law and pays regret >= (1/2) P_X(B_n) h_n ~ h_n^(1+alpha).

**L-4 (In-core two-point testing lemma).** In-core two-point testing lemma. If chi^2(P_+^{\otimes n} || P_-^{\otimes n}) <= C_chi, then every test psi has P_+^n(psi != +)+P_-^n(psi != -) >= c(C_chi)>0; in particular the conclusion follows from a per-observation chi-square bound <= c_0/n using the product chi-square identity. Prove this from total-variation testing risk, Cauchy-Schwarz/Pinsker-type TV <= sqrt(chi^2), and (1+x/n)^n <= exp(x), not by citation alone.

**L-5 (Exact clipped-score drift identity).** Exact clipped-score drift identity. For any measurable plug-in nuisance triple \(\bar\eta=(\bar\mu_0,\bar\mu_1,\bar e)\), with \(\bar e_q=\min\{1-q,\max\{q,\bar e\}\}\) and \(\Delta_a=\bar\mu_a-\mu_a\), the conditional mean drift satisfies \[ E_P[\Gamma_q(O;\bar\eta)\mid X=x]-\tau_P(x) =(\bar e_q(x)-e_P(x))\left(\frac{\Delta_1(x)}{\bar e_q(x)}+\frac{\Delta_0(x)}{1-\bar e_q(x)}\right). \] Hence cancellation holds only where \(\bar e_q(x)=e_P(x)\) or both regression errors vanish; it does not follow merely from \(p_P(x)>q\). Under the frozen assumptions alone, no additive clipped-region bound of the form asserted in the current lemma is derivable.

**L-6 (Under ass:policy-class, def:feasible-erm defines a measur…).** Under ass:policy-class, def:feasible-erm defines a measurable Pi-valued estimator satisfying Vhat_{n,q}(pi_hat_n) >= sup_{pi in Pi} Vhat_{n,q}(pi) - 1/n. Hence for every comparator pi^b in Pi, P_n[(pi_hat_n-pi^b) Gamma_q] >= -1/n; under ass:optimal-in-class this applies to pi^b=pi_star.

**L-7 (Let rho_n=(B^2/n)^{A_alpha}(log n)^p with B>=1).** Let rho_n=(B^2/n)^{A_alpha}(log n)^p with B>=1. For a centered Pi-indexed process z_pi whose offset positive part is controlled by the proved DAG node lem:crossfit-localized-offset-control, any Pi-indexed estimator pi_tilde satisfying R_P(pi_tilde) <= 2|z_{pi_tilde}| + delta_n obeys E_P R_P(pi_tilde) <= C{rho_n+delta_n}; if delta_n<=1/n, the delta_n term is absorbed into rho_n.

**L-8 (Under def:law-class and the estimator-side/policy conditi…).** Under def:law-class and the estimator-side/policy conditions ass:optimal-in-class, ass:nuisance-rate, ass:bounded-crossfit-nuisances, ass:polynomial-nuisance-exponents, ass:policy-class, ass:vc-localized-envelope, ass:vc-localized-offset-envelope, and ass:fixed-crossfit-fold-count, the cross-fitted clipped-AIPW 1/n-ERM of def:feasible-erm satisfies E_P R_P(pi_hat_n) <= C{n^{-r_star}+(n q^2)^{-A_alpha}+r_mu_n r_e_n/q+r_mu_n u^{alpha/2}q^{1/(2 gamma)}+r_mu_n^2/u}(log n)^p for gamma>0 whenever q<=c_o u^gamma. For gamma=0 with fixed q<=underline_p/2 it satisfies E_P R_P(pi_hat_n)<=C{n^{-A_alpha}+r_mu_n r_e_n}(log n)^p.

**L-9 (Let kappa=alpha/(2+2 alpha)).** Let kappa=alpha/(2+2 alpha). For an i.i.d. sample of size m, let Z_m(r)=sup_{pi in Pi:R_P(pi)<=r} |(P_m-P) g_pi|, where the centered increments g_pi have envelope B and conditional second moment bounded by C B^2 P_X(D_pi). Under ass:vc-localized-envelope and thm:margin-localization, E_P Z_m(r) <= C B m^(-1/2) r^kappa (log m)^p for every regret radius r.

**L-10 (Let Z_cf(r) be the pooled cross-fit localized process obt…).** Let Z_cf(r) be the pooled cross-fit localized process obtained by averaging centered evaluation-fold increments. If ass:fixed-crossfit-fold-count holds, then conditional on the training folds each balanced evaluation fold is i.i.d.; if the centered foldwise increments have envelope B and conditional second moment bounded by C B^2 P_X(D_pi), then under ass:vc-localized-envelope and thm:margin-localization, E_P[Z_cf(r) | training folds] <= C B n^(-1/2) r^(alpha/(2+2 alpha)) (log n)^p, hence the same bound unconditionally.

**L-11 (For the pooled cross-fit centered process G_cf(pi) from l…).** For the pooled cross-fit centered process G_cf(pi) from lem:crude-localized-master-bound, if the foldwise centered increments have envelope B and conditional second moment bounded by C B^2 P_X(D_pi), then under ass:iid, ass:fixed-crossfit-fold-count, ass:vc-localized-offset-envelope, and thm:margin-localization, E_P sup_{pi in Pi}{2|G_cf(pi)|-R_P(pi)/4}_+ <= C (B^2/n)^{A_alpha}(log n)^p.

**L-12 (Let b_q(x)=E_P[Gamma_q(O;etahat)|X=x]-tau_P(x), with cros…).** Let b_q(x)=E_P[Gamma_q(O;etahat)|X=x]-tau_P(x), with cross-fitted nuisances fixed on the evaluation fold. For gamma>0, any pi with r=R_P(pi) satisfies |P[(pi-pi_star)b_q]| <= C{r_mu_n r_e_n/q + r_mu_n u^{alpha/2}q^{1/(2 gamma)} + r_mu_n(r/u)^{1/2}} whenever q<=c_o u^gamma. For gamma=0 and fixed q<=underline_p/2, |P[(pi-pi_star)b_q]| <= C r_mu_n r_e_n.

**L-13 (Under ass:bounded-outcome and ass:bounded-crossfit-nuisan…).** Under ass:bounded-outcome and ass:bounded-crossfit-nuisances, for every q in (0,1/2] and every cross-fitted nuisance triple used in def:feasible-erm, the clipped AIPW score satisfies |Gamma_q(O;etahat)|<=C/q almost surely and hence E[Gamma_q(O;etahat)^2 | X]<=C/q^2.

**L-14 (For gamma>0, under ass:overlap-decay and ass:zero-effect,…).** For gamma>0, under ass:overlap-decay and ass:zero-effect, every policy pi with regret r=R_P(pi) satisfies P_X(D_pi intersect {p_P<=q}) <= C u^alpha q^{1/gamma}+r/u whenever 0<u<=u_0 and q<=c_o u^gamma.

**L-15 (For the deterministic schedule in def:feasible-rate, the…).** For the deterministic schedule in def:feasible-rate, the terms in lem:crude-localized-master-bound optimize to the exponent r_up=r_feas. For gamma>0, with A_alpha=(1+alpha)/(2+alpha), q_n=q_0 n^{-s_feas}, u_n=u_bar n^{-t_feas}, and g_joint=max_{0<=s<=1/2, 0<=t<=s/gamma} min{A_alpha(1-2s), c-s, a+s/(2 gamma)+alpha t/2, 2a-t}, the master bound is at most C{n^{-r_star}+n^{-g_joint}}(log n)^p = C n^{-min{r_star,g_joint}}(log n)^p. For gamma=0, the exponent is min{A_alpha,c}.

## Theorems (T)

### T-block: t1 — Under ass:bounded-outcome, for every deterministic pi in…
**Statement.** Under ass:bounded-outcome, for every deterministic pi in Pi, R_P(pi) = E_P[ |tau_P(X)| 1{pi(X) != pi_star(X)} ] = integral over X of |tau_P(x)| 1{pi(x) != pi_star(x)} dP_X(x).

### T-block: t2 — Under ass:margin and ass:zero-effect there is C=C(C_m,u_0…
**Statement.** Under ass:margin and ass:zero-effect there is C=C(C_m,u_0,alpha) such that for every pi in Pi, P_X(D_pi) <= C R_P(pi)^(alpha/(1+alpha)).

### T-block: t3 — For alpha >= 0, gamma > 0, h in (0,1), beta >= 0, at the…
**Statement.** For alpha >= 0, gamma > 0, h in (0,1), beta >= 0, at the tight window v=h^beta, u=h^(beta/gamma): u^alpha v^(1/gamma) = h^((alpha+1)beta/gamma), and u^alpha v^(1/gamma) >= h^alpha iff beta <= alpha gamma/(alpha+1), with equality at beta = beta_ag. Hence a block of mass ~ h^alpha, contrast ~ h, propensity ~ h^beta meets the ass:overlap-decay envelope iff beta <= beta_ag, and beta_ag is the least informative admissible weak-arm exponent.

### T-block: t4 — M_n(alpha,gamma) = inf_{pi_hat} sup_{P in P_class} E_P R_…
**Statement.** M_n(alpha,gamma) = inf_{pi_hat} sup_{P in P_class} E_P R_P(pi_hat) >= c n^{-r_star(alpha,gamma)} for all large n, with c > 0 independent of n.

### T-block: t5 — CONDITIONAL ACHIEVABILITY / CONSTRUCT-AND-DETERMINE
**Statement.** CONDITIONAL ACHIEVABILITY / CONSTRUCT-AND-DETERMINE. For the regime-indexed conditional upper risk U_n from def:upper-risk, with one fixed nuisance regime (a,c,C_mu,C_prod) and the deterministic schedule selected by def:feasible-rate for that regime, derive the honest exponent r_up for the plain cross-fit clipped-AIPW 1/n-ERM using only the crude clipped-score envelope from weights bounded by 1/q (second-moment scale q^{-2}) plus deterministic lem:clip-bias controlled by ass:overlap-decay and ass:margin/localization. This is a conditional achievability bound over def:law-class on the exact side-condition domain bundled into def:upper-risk, not a smaller law class and not a claim that nuisance rates, fixed-K cross-fitting, offset control, or optimal-in-class are implied by def:law-class.

### T-block: t6 — Lower-bound headline only
**Statement.** Lower-bound headline only. M_n(alpha,gamma) >= c n^{-r_star(alpha,gamma)} for all large n, where r_star=(1+alpha)/(2+alpha+beta_{alpha,gamma}).
