# stat_neyman_regret_minimax — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (Superpopulation bounded-outcome potential-outcome law).** Superpopulation bounded-outcome potential-outcome law: nu a probability measure on [0,1]^2 with i.i.d. draws (Y_t(0),Y_t(1)) ~ nu; all arm-law functionals (marginals, root second moments, tangent strengths, scores, information program, oracle allocation/curvature/complexity, local perturbation path) live over this measure world. — REUSE (round-2 correction): the i.i.d. superpopulation SAMPLING substrate is Causalean.Stat.IIDSample — it packages Z : ℕ → Ω → X with meas (measurability), indep (iIndepFun), identDist (identical distribution), and law ((μ.map (Z 0)) = P). Instantiate X = the PO pair space [0,1]^2 (Icc 0 1 × Icc 0 1) and P = nu, so the i.i.d. draws (Y_t(0),Y_t(1)) ~ nu ARE an IIDSample; do NOT rebuild i.i.d. sampling from scratch. LOCAL EXTENSION (kept local, existing decls do not provide it): the superpopulation PO law nu on [0,1]^2 itself, its arm marginals nu_0,nu_1, and all arm-law functionals (root second moments m_a, tangent strengths r_{a,nu}, L2(nu_a) score program J_{a,nu}, oracle allocation/curvature/complexity, local perturbation path nu^(u,h)) plus PO-specific bounded/support fields, scaffolded over Mathlib probability measures on top of the reused IIDSample. Causalean/PO/* and Experimentation/DesignBased are DESIGN-BASED (fixed finite POs), so those functionals stay local; only the i.i.d. sampling packaging is reused.
**required modules.** Causalean.Stat.Sample, CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Basic, Mathlib.MeasureTheory.Measure.ProbabilityMeasure, Mathlib.Probability.Moments.Basic

**S-2 (Adaptive sequential two-arm experiment / joint law).** Adaptive sequential two-arm experiment / joint law: predictable assignment probabilities pi_t (H_{t-1}-measurable), A_t | H_{t-1} ~ Bernoulli(pi_t), observed Y_t = A_t Y_t(1)+(1-A_t)Y_t(0) over horizon T, with joint law P_{nu,Alg} on ((0,1)x{0,1}x[0,1])^T and cumulative Neyman regret functional. — SUBSTRATE-REUSE + LOCAL STRICT-INTERIOR EXTENSION (round-3 correction, S2 FLAG-world-fit): reuse Causalean.Experimentation.Sequential.AdaptiveExperiment ONLY as the PREDICTABILITY SUBSTRATE — it packages a filtration ℱ : Filtration ℕ m0 (models H_{t-1}), a propensity process propensity : ℕ → Ω → ℝ (the pi_t), propensity_adapted (Adapted ℱ propensity: predictable/non-anticipating), and propensity_nonneg / propensity_le_one (CLOSED [0,1] bounds). It is NOT the full realization of the S2 world: the core binds pi_t in the OPEN interval (0,1) and P_{nu,Alg} on ((0,1)x{0,1}x[0,1])^T, and the regret denominator V_nu(pi)=m_1^2/pi+m_0^2/(1-pi) needs pi_t strictly interior. AdaptiveExperiment's closed [0,1] bounds admit pi_t=0 or 1 and do NOT host the strict-interior propensity world. Therefore the S2 world is a LOCAL EXTENSION of AdaptiveExperiment (def:algorithm-class = AdaptiveAlgorithm) that ADDS explicit strict propensity fields (0 < pi_t and pi_t < 1) — equivalently the inherited AdaptiveExperiment.HasOverlap margin (δ ≤ propensity ≤ 1-δ, propensity_pos_of_overlap) upgraded to a nonvacuous interior predicate matching (0,1). Also LOCAL (existing decls do not provide it): the Bernoulli conditional randomization A_t | H_{t-1} ~ Bernoulli(pi_t) (via Causalean.Mathlib.Probability.BernoulliMeasure.bernoulliLaw), the observed outcome map Y_t = A_t Y_t(1)+(1-A_t)Y_t(0), and the FULL sequential joint law P_{nu,Alg} on ((0,1)x{0,1}x[0,1])^T (kernel composition of the reused IIDSample draws + the strict-interior predictable propensity + Bernoulli assignment). Do NOT rebuild the filtration/adaptedness from scratch (reuse AdaptiveExperiment); do NOT treat bare AdaptiveExperiment as the S2 world (its (0,1) interior is added locally).
**required modules.** Causalean.Experimentation.Sequential.AdaptiveDesign, CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Basic, Causalean.Mathlib.Probability.BernoulliMeasure, Mathlib.Probability.Kernel.Composition.Basic

## Assumptions (A)

**A-1 (assumption).** supp(nu) subseteq [0,1]^2.

**A-2 (assumption).** ((Y_t(0), Y_t(1)))_{t=1}^T are i.i.d. with common law nu.

**A-3 (assumption).** pi_t is H_{t-1}-measurable for each t in {1, ..., T}.

**A-4 (assumption).** A_t | H_{t-1} ~ Bernoulli(pi_t) for each t in {1, ..., T}.

**A-5 (assumption).** m_a > 0 for each a in {0,1}.

**A-6 (assumption).** inf_{b_0,b_1 in R} int (y^2 - b_0 - b_1 y)^2 d nu_a(y) > 0 for each a in {0,1}.

**A-7 (assumption).** underline_m <= m_a <= overline_m for each a in {0,1}.

**A-8 (assumption).** underline_r <= inf_{b_0,b_1 in R} int (y^2 - b_0 - b_1 y)^2 d nu_a(y) for each a in {0,1}.

## Definitions (P)

**P-1 ({nu on [0,1]^2 ).** {nu on [0,1]^2 : supp(nu) subseteq [0,1]^2 and m_a(nu) > 0 for each a in {0,1}}

**P-2 ({nu in M_int ).** {nu in M_int : inf_{b_0,b_1 in R} int (y^2 - b_0 - b_1 y)^2 d nu_a(y) > 0 for each a in {0,1}}

**P-3 (The law induced by ass:superpopulation-iid, ass:predictab…).** The law induced by ass:superpopulation-iid, ass:predictable-design, and ass:bernoulli-randomization for horizon T under instance nu and adaptive design Alg.

**P-4 (pi_nu_star = m_1 / (m_0 + m_1).).** pi_nu_star = m_1 / (m_0 + m_1).
**reuse.** Causalean.Experimentation.DesignBased.neymanFraction

**P-5 (V_nu(pi) = m_1^2 / pi + m_0^2 / (1 - pi).).** V_nu(pi) = m_1^2 / pi + m_0^2 / (1 - pi).

**P-6 (g_nu(pi) = V_nu(pi) - V_nu(pi_nu_star).).** g_nu(pi) = V_nu(pi) - V_nu(pi_nu_star).

**P-7 ({Alg = (pi_1, ..., pi_T) ).** {Alg = (pi_1, ..., pi_T) : pi_t is H_{t-1}-measurable and A_t | H_{t-1} ~ Bernoulli(pi_t) for each t in {1, ..., T}}

**P-8 (mathfrak_R_T(Alg,nu) = int [sum_{t=1}^T g_nu(pi_t)] d P_{…).** mathfrak_R_T(Alg,nu) = int [sum_{t=1}^T g_nu(pi_t)] d P_{nu,Alg}.

**P-9 (For a in {0,1}, r_{a,nu} = inf_{b_0,b_1 in R} int (y^2 -…).** For a in {0,1}, r_{a,nu} = inf_{b_0,b_1 in R} int (y^2 - b_0 - b_1 y)^2 d nu_a(y).

**P-10 (For a in {0,1}, J_{a,nu}(u_a) = inf { int s_a(y)^2 d nu_a…).** For a in {0,1}, J_{a,nu}(u_a) = inf { int s_a(y)^2 d nu_a(y) : int s_a(y) d nu_a(y) = 0, int y s_a(y) d nu_a(y) = 0, int y^2 s_a(y) d nu_a(y) = u_a }.

**P-11 (J_nu(u) = pi_nu_star J_{1,nu}(u_1) + (1 - pi_nu_star) J_{…).** J_nu(u) = pi_nu_star J_{1,nu}(u_1) + (1 - pi_nu_star) J_{0,nu}(u_0).

**P-12 (dot_pi_nu(u) = (u_1 m_0 / m_1 - u_0 m_1 / m_0) / (2 (m_0…).** dot_pi_nu(u) = (u_1 m_0 / m_1 - u_0 m_1 / m_0) / (2 (m_0 + m_1)^2).

**P-13 (H_nu = (m_0 + m_1)^4 / (m_0 m_1).).** H_nu = (m_0 + m_1)^4 / (m_0 m_1).

**P-14 (U_nu = {u in R^2 ).** U_nu = {u in R^2 : 0 < J_nu(u) < infinity and dot_pi_nu(u) != 0}.

**P-15 (Let S_nu=m_0+m_1).** Let S_nu=m_0+m_1. Define kappa_nu = sup_{u in U_nu} S_nu^2 dot_pi_nu(u)^2 / J_nu(u). Equivalently, this corrected complexity equals pi_nu_star(1-pi_nu_star) times the curvature-scaled quotient previously written with H_nu.

**P-16 (Design a bounded-support path h -> nu^(u,h) through nu wi…).** Design a bounded-support path h -> nu^(u,h) through nu with nu^(u,0) = nu, int y d nu_a^(u,h)(y) = int y d nu_a(y), int y^2 d nu_a^(u,h)(y) = m_a^2 + h u_a + o(h), and KL(nu_a^(u,h), nu_a) = (h^2 / 2) J_{a,nu}(u_a) + o(h^2) for a in {0,1}.

**P-17 (h_T(nu,u) = (log T / (T J_nu(u)))^(1/2).).** h_T(nu,u) = (log T / (T J_nu(u)))^(1/2).

**P-18 ({nu in M_tan ).** {nu in M_tan : underline_m <= m_a(nu) <= overline_m and underline_r <= inf_{b_0,b_1 in R} int (y^2 - b_0 - b_1 y)^2 d nu_a(y) for each a in {0,1}}

**P-19 (K(underline_m, overline_m, underline_r) = sup_{nu in M(un…).** K(underline_m, overline_m, underline_r) = sup_{nu in M(underline_m, overline_m, underline_r)} kappa_nu.

**P-20 (For v in (0,1), set q=v^2 and let mu_v be the unique solu…).** For v in (0,1), set q=v^2 and let mu_v be the unique solution in (q,v) of mu^4-2mu^3+2qmu^2-2q^2mu+q^2=0. Define rho(v)=((mu_v-q)(q-mu_v^2))/(4mu_v(1-mu_v)) and rho(1)=0. Let F(underline_m,overline_m,underline_r)={v in [underline_m,overline_m]: rho(v)>=underline_r}. For m_0,m_1 in F define Phi(m_0,m_1)={rho(m_0)m_1^2/m_0^3+rho(m_1)m_0^2/m_1^3}/[4(m_0+m_1)]. Then K(underline_m,overline_m,underline_r)=sup_{m_0,m_1 in F(underline_m,overline_m,underline_r)} Phi(m_0,m_1). If F is nonempty, the supremum is a maximum and is attained by taking the two arm marginals to be the corresponding three-point laws on {0,x_v,1}, x_v=(mu_v^2-2mu_v q+q)/(2mu_v(1-mu_v)), with weights p_x=(mu_v-q)/(x_v(1-x_v)), p_1=(q-x_v mu_v)/(1-x_v), and p_0=(x_v+q-(1+x_v)mu_v)/x_v. If F is empty, the regular band is empty and no attainment law is asserted.

## Lemmas (L)

**L-1 (For every nu in M_tan and every direction u with 0 < J_nu…).** For every nu in M_tan and every direction u with 0 < J_nu(u) < infinity, there exists a bounded-support path h -> nu^(u,h) satisfying def:local-path-handle.

**L-2 (For every nu in M_tan, the feasible-direction set U_nu is…).** For every nu in M_tan, the feasible-direction set U_nu is nonempty and 0 < kappa_nu < infinity.

**L-3 (For every nu in M_tan, g_nu(pi_nu_star + delta) = H_nu de…).** For every nu in M_tan, g_nu(pi_nu_star + delta) = H_nu delta^2 + o(delta^2) as delta -> 0; along every path from lem:path-existence, pi_{nu^(u,h)}_star = pi_nu_star + h dot_pi_nu(u) + o(h) as h -> 0.

**L-4 (If m_0 = m_1, then pi_nu_star = 1/2 and the fixed design…).** If m_0 = m_1, then pi_nu_star = 1/2 and the fixed design pi_t = 1/2 for all t has mathfrak_R_T(Alg,nu) = 0. There exist nu in M_tan with m_0 = m_1 and kappa_nu > 0.

**L-5 (For nu in M_tan and a in {0,1}, let e_a be the L2(nu_a) r…).** For nu in M_tan and a in {0,1}, let e_a be the L2(nu_a) residual of y^2 after projection on span{1,y}. Then r_{a,nu}=int e_a^2 dnu_a>0. For every x in R, J_{a,nu}(x)=x^2/r_{a,nu}; when x is nonzero the minimizer is s_a^x=x e_a/r_{a,nu}, and for x=0 the minimizer is s_a^0=0. These scores are bounded on [0,1].

**L-6 (For nu in M_tan and every u with 0<J_nu(u)<infinity, the…).** For nu in M_tan and every u with 0<J_nu(u)<infinity, the scores from lem:arm-score-program-solution define a linear-tilt path dnu_a^h=(1+h s_a^{u_a})dnu_a for small |h|. This path has bounded support, preserves each arm mean exactly, perturbs the arm second moment as m_a(h)^2=m_a^2+h u_a, and satisfies KL(nu_a^h,nu_a)=(h^2/2)J_{a,nu}(u_a)+o(h^2).

**L-7 (For any law with m_0,m_1>0, let S=m_0+m_1 and p=pi_nu_sta…).** For any law with m_0,m_1>0, let S=m_0+m_1 and p=pi_nu_star=m_1/S. Then for every pi in (0,1), V_nu(pi)-V_nu(p)=S^2(pi-p)^2/[pi(1-pi)].

**L-8 (Fix nu in M_tan and u in U_nu).** Fix nu in M_tan and u in U_nu. For the linear-tilt path h -> nu^(u,h), with S=m_0+m_1, there exists bar_eta>0 such that for every eta in (0,bar_eta] there is T_0(eta)<infinity such that every Alg in A_T satisfies sup_{|h|<=eta} mathfrak_R_T(Alg,nu^(u,h)) >= c_0 S^2 dot_pi_nu(u)^2 J_nu(u)^{-1} log T for all T>=T_0(eta), where c_0>0 is a universal numerical constant.

**L-9 (Let nu lie in the strict interior subclass M^circ for fix…).** Let nu lie in the strict interior subclass M^circ for fixed underline_m, overline_m, underline_r. For every fixed linear-tilt direction u with finite J_nu(u), there is eta>0 such that nu^(u,h) lies in M(underline_m,overline_m,underline_r) for all |h|<=eta.

**L-10 (For every nu in M_tan, with S=m_0+m_1, p=m_1/S, and r_a=r…).** For every nu in M_tan, with S=m_0+m_1, p=m_1/S, and r_a=r_{a,nu}, J_nu(u)=p u_1^2/r_1+(1-p)u_0^2/r_0 and kappa_nu={r_0 m_1^2/m_0^3+r_1 m_0^2/m_1^3}/[4S].

**L-11 (For v in (0,1), let q=v^2).** For v in (0,1), let q=v^2. Among all laws mu on [0,1] with int y^2 dmu=q, the supremum of r(mu)=inf_{b_0,b_1} int (y^2-b_0-b_1 y)^2 dmu is rho(v)=((mu_v-q)(q-mu_v^2))/(4mu_v(1-mu_v)), where mu_v in (q,v) is the unique root of mu^4-2mu^3+2qmu^2-2q^2mu+q^2=0. The supremum is attained by the three-point law on {0,x_v,1} with the weights displayed in def:frontier-duality-handle; rho extends continuously to v=1 by rho(1)=0.

## Theorems (T)

### T-block: t1 — For every nu in M_tan and every epsilon > 0, there exists…
**Statement.** For every nu in M_tan and every epsilon > 0, there exists u_epsilon in U_nu and the bounded LINEAR-TILT path h -> nu^(u_epsilon,h) from lem:path-existence (the construction dnu_a=(1+h s_a)dnu_a, so band-continuity for linear tilts applies) with H_nu dot_pi_nu(u_epsilon)^2 / J_nu(u_epsilon) >= kappa_nu - epsilon, and there exists eta>0, such that every Alg in A_T satisfies sup_{|h|<=eta} mathfrak_R_T(Alg, nu^(u_epsilon,h)) >= (universal positive constant) * (kappa_nu - epsilon) * log T for all sufficiently large T.

### T-block: t2 — For every 0 < underline_m < overline_m <= 1 and every und…
**Statement.** For every 0 < underline_m < overline_m <= 1 and every underline_r > 0 such that the strict interior subclass M^circ={nu in M_tan: underline_m < m_a(nu) < overline_m and r_{a,nu} > underline_r for a=0,1} is nonempty, inf_{Alg in A_T} sup_{nu in M(underline_m, overline_m, underline_r)} mathfrak_R_T(Alg,nu) >= c(underline_m,overline_m,underline_r) log T for all sufficiently large T, with c=(universal constant) times sup_{nu in M^circ} kappa_nu up to a fixed numerical factor.

### T-block: t3 — K(underline_m, overline_m, underline_r) admits the algebr…
**Statement.** K(underline_m, overline_m, underline_r) admits the algebraic closed-form moment-envelope expression K=sup_{m_0,m_1 in F(underline_m,overline_m,underline_r)} Phi(m_0,m_1), where F={v in [underline_m,overline_m]: rho(v)>=underline_r}. If F is nonempty, the supremum is a maximum and is attained by the explicit finite-support extremal arm laws from def:frontier-duality-handle; if F is empty, M(underline_m,overline_m,underline_r) is empty and no attainment law is asserted. This determines the exact class-level local lower-bound complexity over M(underline_m, overline_m, underline_r). This lower-bound complexity alone does not determine the sharp universal multiplicative constant of the full minimax regret without a matching constant-sharp upper bound.
