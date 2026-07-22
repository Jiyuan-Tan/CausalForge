# stat_dose_response_minimax — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (iid observational sampling).** iid observational sampling: observed unit O=(Y,A,X) in R x [0,1] x [0,1]^d, single-observation data law P (a probability Measure on the unit space) with induced marginal P_X, nuisances mu_P, pi_P, p_{X,P}; n-sample law is the i.i.d. product Measure.pi (fun _ : Fin n => P). — Direct architectural analogue: Causalean.Estimation.MinimaxATE.Model (Obs/obsLaw/productLaw/minimaxMiss/nMSE/nMiss_sq_le_nMSE) realizes exactly this i.i.d. two-point world but over a FINITE covariate (X : Fin M, Y : Bool) so all laws are finite PMFs. Here X ranges over [0,1]^d and A over [0,1] with a continuous-in-treatment bump, so the single-observation law is a genuine Measure (Mathlib MeasureTheory + Measure.pi tensorization); cannot reuse the finite-PMF Model verbatim -> define-local over Mathlib, importing the Stat.Minimax Le Cam layer. Search trace: surveyed Causalean/Stat/Minimax/{LeCam,MinimaxRisk,Pinsker,ChiSquared,TotalVariation}, Estimation/MinimaxATE; no continuous-treatment dose-response sampling world present.
**required modules.** CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic, Causalean.Stat.Minimax.MinimaxRisk, Causalean.Estimation.MinimaxATE

**S-2 (potential-outcome causal overlay on S1).** potential-outcome causal overlay on S1: the PO process a -> Y(a) on the same probability space, with consistency (Y = Y(A) a.s.) and conditional ignorability (Y(a) indep A | X); the causal target value E_P[Y(t_0)] is identified by the observed-data partial mean theta_P(t_0). — Causalean.PO (POSystem, POSystem.Consistency, counterfactual-independence) is the framework analogue but is a skeleton (sorry-bearing) and graph/regime-indexed, heavier than the scalar continuous-treatment overlay needed here. The construction supplies its own explicit PO realization (draw U ~ Unif[0,1], set Y_zeta(a) via the two-point mean channel), so consistency + ignorability are verified directly on the constructed laws rather than imported. Define-local over Mathlib with PO naming aligned to Causalean.PO. Search trace: surveyed Causalean/PO/{Core,Assumptions}; no continuous-dose PO partial-mean world to reuse verbatim.
**required modules.** CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic, Causalean.PO.Core.System, Causalean.PO.Assumptions.Consistency

**S-3 (regime constants and frontier objects).** regime constants and frontier objects: smoothness/positivity/bound scalars and the evaluation geometry, plus the minimax-risk and published-rate frontier sequences. — Plain real/nat regime parameters (alpha,beta,s,M,c_0,t_0,epsilon_0 : R>0, d,n : N) and two real-valued frontier sequences R_n (minimax MSE, def:minimax-risk) and rho_n (def:published-hoif-rate). No measure-theoretic world; bound directly in Basic.lean.
**required modules.** CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic

## Assumptions (A)

**A-1 (assumption).** O_1, ..., O_n are iid draws from P.

**A-2 (assumption).** Y = Y(A) almost surely under P.

**A-3 (assumption).** For every a in [0,1], Y(a) is independent of A conditional on X under P.

**A-4 (assumption).** |Y| <= M almost surely under P.

**A-5 (assumption).** [t_0 - epsilon_0, t_0 + epsilon_0] is contained in (0,1).

**A-6 (assumption).** pi_P(a|x) >= c_0 for every a in [t_0 - epsilon_0, t_0 + epsilon_0] and every x in [0,1]^d.

**A-7 (assumption).** For every x in [0,1]^d, the function a -> mu_P(a,x) belongs to a Holder ball of order alpha and radius M on [t_0 - epsilon_0, t_0 + epsilon_0].

**A-8 (assumption).** For every x in [0,1]^d, the function a -> pi_P(a|x) belongs to a Holder ball of order beta and radius M on [t_0 - epsilon_0, t_0 + epsilon_0].

**A-9 (assumption).** The function x -> mu_P(t_0,x) belongs to a Holder ball of order s and radius M on [0,1]^d.

**A-10 (assumption).** The function x -> pi_P(t_0|x) belongs to a Holder ball of order s and radius M on [0,1]^d.

**A-11 (assumption).** The density p_{X,P} belongs to a Holder ball of order s and radius M on [0,1]^d and is bounded above by M.

**A-12 (assumption).** There exist a density p_0 on [0,1]^d, a conditional treatment density q_0 on [0,1], and a constant eta_0>0 such that p_0 and q_0 have Holder norms at most M-eta_0 in the smoothness classes required of p_{X,P} and pi_P, q_0(a) >= c_0+eta_0 for all a in [t_0-epsilon_0,t_0+epsilon_0], and p_0 is bounded above by M-eta_0.

**A-13 (ass:mu-is-regression; defining model tie).** The nuisance `mu_P` is the observed law's actual conditional regression: `mu_P(a,x) = E_P[Y | A=a, X=x]` (in Lean, the corresponding conditional-expectation identity holds almost everywhere).

**A-14 (ass:px-is-x-density; defining model tie).** The nuisance `p_{X,P}` is the Lebesgue density of the X-marginal induced by `P`.

**A-15 (ass:pi-is-cond-treatment-density; defining model tie).** The nuisance `pi_P(a|x)` is the conditional density of `A` given `X=x` under `P`; equivalently, the `(A,X)` marginal has density `pi_P(a|x) p_{X,P}(x)` with respect to product Lebesgue measure.

## Definitions (P)

**P-1 ({P ).** {P : P satisfies ass:iid-sampling, ass:consistency, ass:no-unmeasured-confounding, ass:bounded-outcome, ass:interior-dose, ass:local-positivity, ass:mu-treatment-holder, ass:pi-treatment-holder, ass:mu-covariate-holder, ass:pi-covariate-holder, ass:px-holder, ass:mu-is-regression, ass:px-is-x-density, ass:pi-is-cond-treatment-density}. The last three clauses are the semantic law-to-nuisance ties already present in the discovery note's definitions of `mu_P`, `p_{X,P}`, and `pi_P`; they prevent the nuisance fields from floating free of the observed-data law.

**P-2 (theta_P(t_0) = int_{[0,1]^d} mu_P(t_0,x) p_{X,P}(x) dx).** theta_P(t_0) = int_{[0,1]^d} mu_P(t_0,x) p_{X,P}(x) dx

**P-3 (R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0), t_0) = inf_{ha…).** R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0), t_0) = inf_{hat_theta_n} sup_{P in P_{alpha,beta,s}(M,c_0,epsilon_0,t_0)} E_P[(hat_theta_n - theta_P(t_0))^2]

**P-4 (rho_n = n^(-2*alpha/(2*alpha+1)) vee n^(-2/(1 + d/(4*s) +…).** rho_n = n^(-2*alpha/(2*alpha+1)) vee n^(-2/(1 + d/(4*s) + 1/alpha))

**P-5 (Headline and frontier handle).** Headline and frontier handle. The delivered content is the all-beta lower floor: by a de-laundered two-point Le Cam construction perturbing only mu_P with the covariate density and treatment-density baselines fixed, the original class satisfies R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0),t_0) >= c n^{-2*alpha/(2*alpha+1)} for every beta>0. When s>=d/4, lem:rho-oracle-regime-algebra identifies the published benchmark rho_n with this same exponent, so the converse lands on the classical interior treatment-regression scale. When 0<s<d/4, rho_n = n^{-2/(1+d/(4*s)+1/alpha)} is recorded only as the published HOIF comparator, not as a same-class certified upper endpoint. The residual carried by oeq:full-beta-frontier is therefore the unrestricted upper frontier itself: can one attain rho_n on the original class, or does a genuinely beta-sensitive phase intervene?

**P-6 (Certified partial resolution of the unrestricted beta fro…).** Certified partial resolution of the unrestricted beta frontier. Under ass:baseline-submodel-slack, the original class P_{alpha,beta,s}(M,c_0,epsilon_0,t_0) satisfies the all-beta lower floor R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0),t_0) >= c n^{-2 alpha/(2 alpha+1)} for all sufficiently large n. When s>=d/4, this floor lies on the same exponent as rho_n. When 0<s<d/4, rho_n = n^{-2/(1+d/(4s)+1/alpha)} has a strictly smaller exponent and remains only a published upper-side comparator on the present note. The open question is whether the original class admits an upper bound of order rho_n, an intermediate exponent, or a genuinely beta-sensitive phase.

## Lemmas (L)

**L-1 (Fix B>0).** Fix B>0. Let Q_u and Q_v be distributions on {-B,B} with means u and v, respectively, so Q_u(B)=(1+u/B)/2 and Q_v(B)=(1+v/B)/2. If |u|<=B/2 and |v|<=B/2, then KL(Q_u,Q_v) <= 2*(u-v)^2/B^2.

**L-2 (Let Q_0 and Q_1 be two laws for the n-sample experiment a…).** Let Q_0 and Q_1 be two laws for the n-sample experiment and let theta_0,theta_1 be the corresponding values of a real parameter, with Delta=|theta_1-theta_0|. If KL(Q_0,Q_1)<=K<infinity, then every estimator T satisfies max_{i=0,1} E_{Q_i}[(T-theta_i)^2] >= c_K Delta^2 for a constant c_K>0 depending only on K.

**L-3 (If s >= d/4, then the published beta>=alpha rate rho_n sa…).** If s >= d/4, then the published beta>=alpha rate rho_n satisfies rho_n = n^{-2 alpha/(2 alpha+1)} for every n >= 1.

**L-4 (Assume ass:baseline-submodel-slack).** Assume ass:baseline-submodel-slack. For every beta>0 there is a constant c_or>0, depending only on the fixed model radii and on the slack baseline but not on n, such that for all sufficiently large n, R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0),t_0) >= c_or n^{-2 alpha/(2 alpha+1)}. The construction leaves the treatment density fixed, so the bound is independent of whether beta>=alpha.

**L-5 (If 0<s<d/4, then rho_n = n^{-2/(1+d/(4s)+1/alpha)} for ev…).** If 0<s<d/4, then rho_n = n^{-2/(1+d/(4s)+1/alpha)} for every n>=1, and 2/(1+d/(4s)+1/alpha) < 2 alpha/(2 alpha+1).

**L-6 (Classical local-polynomial input).** Classical local-polynomial input. Let A be scalar, t be an interior point, K be a compactly supported kernel or equivalent kernel of order at least floor(eta), and h be a bandwidth with h -> 0 and N h -> infinity. If the regression function is eta-Holder in A on a fixed neighborhood of t, the design density is locally bounded above and below at t, and the response has bounded second moment, then the local-polynomial estimator at t has bias O(h^eta) and stochastic L2 size O((N h)^(-1/2)). If J bounded series coefficients in x are estimated inside the same A-window, the stochastic coefficient contribution is O(sqrt(J/(N h))).

**L-7 (Classical series/sieve L2 input).** Classical series/sieve L2 input. For an s-Holder function on [0,1]^d and a bounded spline, wavelet, or tensor-product polynomial sieve of dimension L with the usual approximation property, there is a sieve element f_L with ||f-f_L||_2 <= C L^{-s/d}. Least-squares or ridge series estimation over this sieve with effective sample size N, bounded second moments, and bounded regressors has prediction L2 error O(L^{-s/d}+sqrt(L/N)). The same rate applies to projection density estimation in L2 for an s-Holder density bounded by a finite envelope.

**L-8 (Higher-order influence function projection input).** Higher-order influence function projection input. For a localized dose-response partial-mean functional with a scalar treatment localization bandwidth h and a J-dimensional covariate projection space, the cross-fitted order-m projection-HOIF estimator has the following non-remainder MSE components: treatment smoothing bias squared O(h^{2 alpha}), first-order localized variance O((n h)^(-1)), covariate projection product bias squared O(J^{-4s/d}), and degenerate projected U-statistic variance O(J/(n h)^2).

**L-9 (Higher-order nuisance-remainder input).** Higher-order nuisance-remainder input. For a cross-fitted order-m HOIF estimator, after the smoothing bias, projection bias, and degenerate U-statistic variance have been separated, the remaining estimation bias is a finite sum of products of m+1 nuisance estimation errors in L2 norm. Consequently, if the largest nuisance L2 error is delta_n, the squared contribution of this orthogonal remainder is at most C delta_n^{2(m+1)}.

**L-10 (Deterministic denominator control).** Deterministic denominator control. If f and fhat are functions on a probability space, c <= f <= C, and fhat is truncated to [c/2,2C], then ||1/fhat-1/f||_2 <= 2 c^{-2} ||fhat-f||_2 and ||fhat-f||_2 is not increased by truncation up to a universal constant. The same statement applies to conditional treatment densities and their reciprocals on the local positivity neighborhood.

**L-11 (Upper-side scope caveat).** Upper-side scope caveat. The localized pilot bounds h^alpha+L^{-s/d}+sqrt(L/(n h)) and h^beta+L^{-s/d}+sqrt(L/(n h)) used in a Bonvini-Kennedy-style HOIF argument are not consequences of the declared class P_{alpha,beta,s}(M,c_0,epsilon_0,t_0) alone: they additionally require x-regularity of the windowed nuisance objects a -> mu_P(a,.) and a -> pi_P(a|.) near t_0, together with the localized denominator-weight control used in the source analysis.

**L-12 (Upper-side scope caveat).** Upper-side scope caveat. The four-term localized HOIF risk decomposition h^{2 alpha}+(n h)^(-1)+J^{-4s/d}+J/(n h)^2 without an extra first-order window drift is valid only when the smoothed score is written with the windowed nuisances mu_P(A,X) and pi_P(A|X) and the additional localized regularity package of the source analysis; it does not follow from plugging the slices mu_P(t_0,.) and pi_P(t_0|.) into the score on the declared class.

**L-13 (Upper-side source input).** Upper-side source input. Conditional on nuisance rates delta_n from the localized pilot route, the order-m projection-HOIF remainder is a finite sum of products of m+1 nuisance errors and therefore contributes at most C delta_n^{2(m+1)}. Choosing m so that 2(m+1)lambda_* exceeds the target exponent makes this remainder o(rho_n). This is a source-side implication, not a same-class derived rate on P_{alpha,beta,s}(M,c_0,epsilon_0,t_0).

**L-14 (External comparator only).** External comparator only. In the published Bonvini-Kennedy upper-side analysis, when s>=d/4 the benchmark sequence rho_n collapses to n^{-2 alpha/(2 alpha+1)}, and their HOIF estimator attains that exponent under additional localized regularity not encoded in def:holder-dose-class. This core records that rate only as a literature comparator, not as a same-class certified upper theorem.

**L-15 (External comparator only).** External comparator only. In the published Bonvini-Kennedy upper-side analysis, when 0<s<d/4 the benchmark sequence rho_n equals n^{-2/(1+d/(4s)+1/alpha)}, and their HOIF argument targets that exponent under additional localized regularity not encoded in def:holder-dose-class. This core records that rate only as a literature comparator, not as a same-class certified upper theorem.

**L-16 (Assume ass:baseline-submodel-slack).** Assume ass:baseline-submodel-slack. For every fixed beta>0 there exists c>0 such that, for all sufficiently large n, R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0),t_0) >= c n^{-2 alpha/(2 alpha+1)}. If s>=d/4 then rho_n = n^{-2 alpha/(2 alpha+1)}. If 0<s<d/4 then rho_n = n^{-2/(1+d/(4s)+1/alpha)} and 2/(1+d/(4s)+1/alpha) < 2 alpha/(2 alpha+1). Hence the certified unrestricted beta-frontier is the all-beta oracle lower floor together with the algebraic comparison to the published rho_n benchmark.

## Theorems (T)

### T-block: t1 — Assume ass:baseline-submodel-slack
**Statement.** Assume ass:baseline-submodel-slack. Then for every beta>0 there exists a constant c > 0, depending only on the fixed model radii and the slack baseline, such that for all sufficiently large n, R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0), t_0) >= c n^(-2*alpha/(2*alpha+1)). Equivalently, uniformly over every beta>0, every estimator of theta_P(t_0) over P_{alpha,beta,s}(M,c_0,epsilon_0,t_0) has worst-case mean-squared error at least a constant multiple of the classical interior treatment-regression pointwise rate.

**Hypothesis dropped from this theorem (drift-watch).** `ass:beta-dominates-alpha` is not load-bearing: the discovery proof keeps the treatment density fixed and explicitly proves the lower floor for every `beta > 0`, whether or not `beta >= alpha`.

### T-block: t2 — Under the assumptions of thm:sharp-pointwise-lower-bound,…
**Statement.** Under the assumptions of thm:sharp-pointwise-lower-bound, if s >= d/4 then rho_n = n^(-2*alpha/(2*alpha+1)) and therefore R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0), t_0) >= c n^(-2*alpha/(2*alpha+1)) = c rho_n for some c > 0. Thus the certified lower floor reduces to the classical interior pointwise nonparametric regression barrier.

### T-block: t3 — Assume ass:baseline-submodel-slack
**Statement.** Assume ass:baseline-submodel-slack. For every fixed beta>0 and every s>=d/4, there exists c>0 such that, for all sufficiently large n, R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0),t_0) >= c n^{-2 alpha/(2 alpha+1)} = c rho_n. Thus, in the smooth-covariate regime, the certified lower floor lands on the same exponent as the published benchmark rho_n, but this core does not claim a matching same-class upper bound.

### T-block: t4 — For every fixed beta>0 and every 0<s<d/4, under the decla…
**Statement.** For every fixed beta>0 and every 0<s<d/4, under the declared same-class assumptions and ass:baseline-submodel-slack, there exists c>0 such that, for all sufficiently large n, R_n(P_{alpha,beta,s}(M,c_0,epsilon_0,t_0),t_0) >= c n^{-2 alpha/(2 alpha+1)}. Moreover rho_n = n^{-2/(1+d/(4s)+1/alpha)} has a strictly smaller exponent than the certified lower floor. The same-class upper endpoint C rho_n is not discharged on the present core.
