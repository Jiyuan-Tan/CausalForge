# exp_saturation_skew_threshold — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (probability laws on the compact interval [0,1] (weak topo…).** probability laws on the compact interval [0,1] (weak topology) — Mathlib measure-theoretic world — bypass-justified: the entire law program lives over P([0,1]) with weak convergence, moments, pushforwards and convex moment images. Surveyed Causalean/Experimentation/DesignBased {Design.lean, FiniteDesignMeasure.lean, Optimality.lean, TwoStage.lean}: Causalean's world is FiniteDesign (a probability over a finite assignment space) with E/Var/Cov and IsOptimalOn — the wrong abstraction (no P([0,1]) weak-topology / moment-set machinery, no continuous saturation law nu). Model nu as `MeasureTheory.ProbabilityMeasure ℝ` supported on Icc 0 1 (or a measure with IsProbabilityMeasure on Icc), delta_x as `MeasureTheory.Measure.dirac`, m_r/V as integrals of polynomials, D_pbar as Set.Icc (-pbar) (1-pbar).
**required modules.** Mathlib.MeasureTheory.Measure.ProbabilityMeasure, Mathlib.MeasureTheory.Integral.Bochner, Mathlib.Topology.Algebra.Module.WeakDual, Mathlib.Analysis.Convex.Combination

**S-2 (finite-population two-stage randomized saturation design…).** finite-population two-stage randomized saturation design on M equal clusters of size m (deterministic saturation vector on the 1/m grid) — bypass-justified: the implementable design is a deterministic saturation vector pi : Fin M → ℝ on the grid {0,1/m,...,1} with mean pbar, and L_M(pi) is its empirical law (M^{-1} sum of diracs). The finite-attainability/rounding/empirical-law content is pure combinatorics over Fin M → ℝ and needs no probability structure on the assignment space. Surveyed Causalean/Experimentation/DesignBased {Design.lean (FiniteDesign, E/Var/Cov), TwoStage.lean (compound design), FiniteDesignMeasure.lean}: these model the randomization over assignments (a FiniteDesign over {0,1}^N), whereas our objects are the deterministic saturation vector and its empirical law — different abstraction. The estimator hat_tau_DM and its design variance enter ONLY through the gated Cai expansion (S-blocks do not re-derive them); tau is a fixed real estimand parameter. binds_sampling_model true: the two-stage saturation sampling model is named here but its variance is supplied by the Cai gate.
**required modules.** Mathlib.Data.Fintype.Basic, Mathlib.Algebra.BigOperators.Fin, Mathlib.MeasureTheory.Measure.ProbabilityMeasure

## Assumptions (A)

**A-1 (assumption).** The finite population is partitioned into M clusters C_1, ..., C_M of common size m.

**A-2 (assumption).** 0 < pbar < 1.

**A-3 (assumption).** Potential outcomes for units in cluster C_j depend only on assignments within C_j and not on assignments in C_l for l != j.

**A-4 (assumption).** Within each cluster, the working-model contribution of a realized assignment to the variance of hat_tau_DM depends on the assignment only through the cluster treatment share u.

**A-5 (assumption).** In the note's specialized working model, for each treatment state z in {0,1} the within-cluster outcome surface Y_{ji}(z,u) is approximated by an affine function of the centered share d = u - pbar, with working-model coefficients that are common across clusters in the block-fixed isolated-cluster specialization.

**A-6 (assumption).** The finite-population sequence used to define the randomized-saturation continuous-relaxation criterion is in the Cai-Pouget-Abadie-Airoldi asymptotic variance-expansion domain: M -> infinity, m -> infinity, the linear-interference potential-outcome parameters are uniformly bounded, and the regularity hypotheses of Cai, Pouget-Abadie, and Airoldi (2022, Theorem 9) hold in the homogeneous/block-fixed isolated-cluster specialization.

## Definitions (P)

**P-1 (T_pbar(u) = u - pbar.).** T_pbar(u) = u - pbar.

**P-2 (D_pbar = {d in R ).** D_pbar = {d in R : -pbar <= d <= 1 - pbar}.

**P-3 (For pbar in [0,1], N(pbar) = {nu in P([0,1]) ).** For pbar in [0,1], N(pbar) = {nu in P([0,1]) : integral_[0,1] u d nu(u) = pbar}.

**P-4 (N_s(pbar,s) = {nu in N(pbar) ).** N_s(pbar,s) = {nu in N(pbar) : m_2(nu) = s}.

**P-5 (For r in {2,3,4}, m_r(nu) = integral_[0,1] (u - pbar)^r d…).** For r in {2,3,4}, m_r(nu) = integral_[0,1] (u - pbar)^r d nu(u).

**P-6 (V(nu) = V_0 + V_1 m_2(nu) + V_3 m_3(nu) + V_4 ( m_4(nu) -…).** V(nu) = V_0 + V_1 m_2(nu) + V_3 m_3(nu) + V_4 ( m_4(nu) - m_2(nu)^2 ).

**P-7 (F(s) = inf_{nu in N_s(pbar,s)} integral_[0,1] [V_1 (u - p…).** F(s) = inf_{nu in N_s(pbar,s)} integral_[0,1] [V_1 (u - pbar)^2 + V_3 (u - pbar)^3 + V_4 (u - pbar)^4] d nu(u).

**P-8 (Q_{a,b,c}(d) = V_1 d^2 + V_3 d^3 + V_4 d^4 - a - b d - c…).** Q_{a,b,c}(d) = V_1 d^2 + V_3 d^3 + V_4 d^4 - a - b d - c d^2.

**P-9 (For the necessary-and-sufficient global certificate, the…).** For the necessary-and-sufficient global certificate, the outer certificate is the profiled value H(s) = V_0 + F(s) - V_4 s^2. The affine expression G^{lin}_{a,c}(s)=V_0+a+c s-V_4s^2 is only a sufficient lower-certificate obtained from one slice dual line; it is not necessary for global optimality.

**P-10 (For pbar in [0,1], Pi_{M,m}(pbar) = {pi in {0, 1/m, 2/m,…).** For pbar in [0,1], Pi_{M,m}(pbar) = {pi in {0, 1/m, 2/m, ..., 1}^M : M^(-1) sum_{j=1}^M pi_j = pbar}.

**P-11 (L_M(pi) = M^(-1) sum_{j=1}^M delta_{pi_j}.).** L_M(pi) = M^(-1) sum_{j=1}^M delta_{pi_j}.

**P-12 (Given a K-atomic law nu = sum_{ell=1}^K w_ell delta_{u_el…).** Given a K-atomic law nu = sum_{ell=1}^K w_ell delta_{u_ell}, first round the masses w_ell to a vector of cluster counts summing to M, then replace each support point u_ell by one or two adjacent points in {0,1/m,...,1} with mixing weights chosen to preserve the contribution of that atom to the mean constraint up to the final balancing adjustment that enforces M^(-1) sum_j pi_j = pbar.

**P-13 (Let Theta={theta=(pbar,V_1,V_3,V_4):0<=pbar<=1}).** Let Theta={theta=(pbar,V_1,V_3,V_4):0<=pbar<=1}. For k in {1,2,3}, define E_k(theta) as the set of tuples (w_1,...,w_k,d_1,...,d_k) satisfying w_i>=0, sum_i w_i=1, -pbar<=d_1<=...<=d_k<=1-pbar, and sum_i w_i d_i=0. Define the branch objective R_k^0(theta,w,d)=V_1 sum_i w_i d_i^2+V_3 sum_i w_i d_i^3+V_4{sum_i w_i d_i^4-(sum_i w_i d_i^2)^2}; equivalently one may add the common constant V_0, which does not affect argmin comparisons. This node is only notation for the finite support/contact families and exact-input branch objectives used by thm:constructive-optimal-design-algorithm: S1 is the singleton centered support {0}, S2 is the two-point centered family {-b,a} with mean-zero weights, and S3 is the three-point endpoint-interior family {-pbar,r,1-pbar} or its equivalent fixed-second-moment KKT parameterization from lem:explicit-profile-value. It does not assert a parameter-uniform semialgebraic partition or a global branch-selection map over Theta.

**P-14 (Certified delivered content plus the remaining atlas-comp…).** Certified delivered content plus the remaining atlas-compression question. For every exact algebraic or symbolic parameter point theta=(pbar, V_1, V_3, V_4) with 0 <= pbar <= 1, thm:constructive-optimal-design-algorithm gives a terminating exact optimizer/certificate for the quartic program; lem:explicit-profile-value gives a closed-form profiled outer value H(s); and prop:explicit-two-point-cell gives the complete closed-form optimizer over the singleton/two-point class. The remaining open question is whether the exact elimination/CAD output used inside that constructive theorem can be compressed into a parameter-uniform human-readable symbolic atlas, especially for globally active three-point cells.

## Lemmas (L)

**L-1 (Under ass:equal-cluster-size, ass:isolated-partial-interf…).** Under ass:equal-cluster-size, ass:isolated-partial-interference, ass:anonymous-share-specialization, ass:homogeneous-linear-share-working-model, and ass:cai-leading-expansion-domain, fix the note's chosen homogeneous/block-fixed isolated-cluster specialization of the Cai expansion, and let (V_0, V_1, V_3, V_4) denote the resulting scoped coefficient tuple after the isolated-cluster simplification V_2 = 0. For every feasible saturation vector pi in Pi_{M,m}(pbar), the corresponding o(N^{-1})-free leading comparison is exactly V(L_M(pi)). Consequently, if a feasible sequence pi^(n) in Pi_{M_n,m_n}(pbar) has empirical laws converging weakly to nu, then nu belongs to N(pbar) and the corresponding leading comparisons converge to V(nu). Moreover, along every regime M,m -> infinity with N pbar in Z, the infimum of the feasible leading criterion over Pi_{M,m}(pbar) converges to min_{nu in N(pbar)} V(nu), and this asymptotic infimum is approached by grid-split rounding of a support-at-most-three minimizer.

**L-2 (For 0 < pbar < 1, write p=pbar, q=1-p, C=pq, and A=q-p).** For 0 < pbar < 1, write p=pbar, q=1-p, C=pq, and A=q-p. For s in [0,C], let I_2(s)=[s/p-p, q-s/q] and I_3(s)=[-s/q, s/p]. Define Phi_2(s,t)=V_1 s+V_4 s^2+s(V_3 t+V_4 t^2) and Phi_3(s,r)=V_1 s+V_3(A s+(s-C)r)+V_4((1-3C)s+(s-C)(r^2+A r)). Then the fixed-second-moment profile satisfies F(0)=0 and, for all s in [0,C], F(s)=min{min_{t in I_2(s)} Phi_2(s,t), min_{r in I_3(s)} Phi_3(s,r)}; consequently H(s)=V_0+F(s)-V_4s^2. The first minimum is attained by the two-point centered law whose support points are the roots of x^2-tx-s=0. The second is attained by the endpoint-interior law on {-p,r,q} with weights (s+rq)/(p+r), (C-s)/((p+r)(q-r)), and (s-pr)/(q-r), with the endpoint limiting interpretation. Since the two displayed minimizations are quadratic over closed intervals, F and H are explicit piecewise-algebraic functions of (s,pbar,V_1,V_3,V_4).

**L-3 (If C is a compact convex subset of R^n and an open convex…).** If C is a compact convex subset of R^n and an open convex set O is disjoint from C, then there is a nonzero affine functional that weakly separates C from O; in particular, a finite-dimensional compact convex moment set has a supporting hyperplane at any exposed lower boundary point.

**L-4 (If I is a compact interval of R, then P(I) is weakly comp…).** If I is a compact interval of R, then P(I) is weakly compact.

**L-5 (If I is a compact interval of R and g:I -> R is bounded a…).** If I is a compact interval of R and g:I -> R is bounded and continuous, then mu |-> int g dmu is weakly continuous on P(I).

**L-6 (If K is compact and h:K -> R is continuous, then h attain…).** If K is compact and h:K -> R is continuous, then h attains its minimum on K.

**L-7 (Let D_pbar be the compact centered-support interval and l…).** Let D_pbar be the compact centered-support interval and let f:D_pbar -> R be continuous. Then the moment image C_f={(int 1 dmu, int d dmu, int d^2 dmu, int f(d) dmu): mu in P(D_pbar)} is a compact convex subset of R^4.

**L-8 (Fix s for which N_s(pbar,s) is nonempty and set f(d)=V_1d…).** Fix s for which N_s(pbar,s) is nonempty and set f(d)=V_1d^2+V_3d^3+V_4d^4. A law nu_star in N_s(pbar,s) minimizes int f(d) d(T_pbar)_#nu(d) over N_s(pbar,s) if and only if there exist a,b,c in R such that Q_{a,b,c}(d)=f(d)-a-bd-cd^2 is nonnegative on D_pbar and vanishes on T_pbar(supp(nu_star)).

**L-9 (For 0<pbar<1, the map T_pbar(u)=u-pbar sends each nu in N…).** For 0<pbar<1, the map T_pbar(u)=u-pbar sends each nu in N(pbar) to a probability law mu on D_pbar with int d dmu(d)=0, and m_r(nu)=int d^r dmu(d) for r=2,3,4. Conversely, each probability law mu on D_pbar with int d dmu(d)=0 pushes forward under d -> pbar+d to a law in N(pbar). For every nu in N(pbar), 0<=m_2(nu)<=pbar(1-pbar).

**L-10 (Assume 0 < pbar < 1).** Assume 0 < pbar < 1. Let f(d)=V_1 d^2+V_3 d^3+V_4 d^4 and H(s)=V_0+F(s)-V_4 s^2. For every nonempty slice N_s(pbar,s), H(s)=inf{V(nu):nu in N_s(pbar,s)}. Moreover, for every nu in N_s(pbar,s), V(nu)=V_0+int f(d)d(T_pbar)_#nu(d)-V_4 s^2.

**L-11 (For 0<pbar<1, the objective V attains a minimum over N(pbar)).** For 0<pbar<1, the objective V attains a minimum over N(pbar). For every s in [0,pbar(1-pbar)] with N_s(pbar,s) nonempty, the profile value F(s) is attained on N_s(pbar,s).

**L-12 (Let mu be a probability law on D_pbar with int d dmu(d)=0…).** Let mu be a probability law on D_pbar with int d dmu(d)=0, let s=int d^2 dmu(d)>0, m_3=int d^3 dmu(d), and m_4=int d^4 dmu(d). Then t=m_3/s lies in D_pbar and m_4-s^2>=m_3^2/s.

**L-13 (For 0<pbar<1 and every s in [0,pbar(1-pbar)], the slice N…).** For 0<pbar<1 and every s in [0,pbar(1-pbar)], the slice N_s(pbar,s) is nonempty.

**L-14 (Let 0<a<=1-pbar and 0<b<=pbar).** Let 0<a<=1-pbar and 0<b<=pbar. Let mu place mass b/(a+b) at a and mass a/(a+b) at -b, and let nu be its pushforward under d -> pbar+d. Then nu in N(pbar), m_2(nu)=ab, m_3(nu)=ab(a-b), m_4(nu)-m_2(nu)^2=ab(a-b)^2, and V(nu)-V_0=ab[V_1+V_3(a-b)+V_4(a-b)^2].

**L-15 (Let pi^(M) be saturation vectors in [0,1]^M whose empiric…).** Let pi^(M) be saturation vectors in [0,1]^M whose empirical laws L_M(pi^(M)) converge weakly to nu in P([0,1]), and let pbar be fixed. Then for r in {2,3,4}, M^(-1) sum_{j=1}^M (pi_j^(M)-pbar)^r -> integral_[0,1] (u-pbar)^r d nu(u). In particular, if nu in N(pbar), the limit is m_r(nu).

**L-16 (For every nu in N(pbar), 0 <= m_2(nu) <= pbar(1-pbar)).** For every nu in N(pbar), 0 <= m_2(nu) <= pbar(1-pbar). The lower bound is attained by delta_pbar, with equality only when nu=delta_pbar. The upper bound is attained by (1-pbar)delta_0+pbar delta_1; when 0<pbar<1, equality in the upper bound forces nu=(1-pbar)delta_0+pbar delta_1.

**L-17 (For 0<pbar<1, with p=pbar, q=1-p, A=q-p, and q_theta(t)=V…).** For 0<pbar<1, with p=pbar, q=1-p, A=q-p, and q_theta(t)=V_1+V_3t+V_4t^2, the minimum of V-V_0 over mean-zero laws supported on at most two centered points in [-p,q] equals the minimum over the singleton value 0 and the two endpoint branches g_L(t)=p(p+t)q_theta(t) for t in [-p,A] and g_R(t)=q(q-t)q_theta(t) for t in [A,q].

**L-18 (For a compact interval D_pbar and any s for which the cen…).** For a compact interval D_pbar and any s for which the centered slice {mu in P(D_pbar): integral d dmu=0, integral d^2 dmu=s} is nonempty, that slice is compact and convex in the weak topology, and every continuous affine functional on it attains its minimum.

**L-19 (Let 0<pbar<1, p=pbar, q=1-p, C=pq, A=q-p, and 0<s<C).** Let 0<pbar<1, p=pbar, q=1-p, C=pq, A=q-p, and 0<s<C. If mu is a probability law on [-p,q] with E X=0, E X^2=s, m3=E X^3, and m4=E X^4, then t=m3/s lies in I_2(s)=[s/p-p,q-s/q], r=(m3-A s)/(s-C) lies in I_3(s)=[-s/q,s/p], m4>=s^2+s t^2 with equality on the two-root law x^2-tx-s=0, and m4<=(1-3C)s+(s-C)(r^2+A r) with equality on the endpoint-interior law on {-p,r,q} with the stated weights.

**L-20 (Let nu = sum_{ell=1}^K w_ell delta_{u_ell} be in N(pbar),…).** Let nu = sum_{ell=1}^K w_ell delta_{u_ell} be in N(pbar), with K <= 3, M,m positive integers, N=Mm, and N pbar in Z. The grid-split rounding handle can be run to produce pi_rd in Pi_{M,m}(pbar) and a coupling gamma_rd of nu and L_M(pi_rd) such that integral |u-v| d gamma_rd(u,v) <= 2K/M + 2/m <= 6/M + 2/m.

**L-21 (Let eta and nu be probability laws on [0,1], and let gamm…).** Let eta and nu be probability laws on [0,1], and let gamma be any coupling of eta and nu with integral |u-v| d gamma(u,v) <= Delta. Then, for the functional V built from centered moments around pbar in [0,1], |V(eta)-V(nu)| <= (2 |V_1| + 3 |V_3| + 8 |V_4|) Delta.

**L-22 (If pbar in {0,1}, then N(pbar)={delta_pbar}.).** If pbar in {0,1}, then N(pbar)={delta_pbar}.

## Theorems (T)

### T-block: t1 — For nu_star in N(pbar), let s_star = m_2(nu_star), and wr…
**Statement.** For nu_star in N(pbar), let s_star = m_2(nu_star), and write H(s)=V_0+F(s)-V_4 s^2 for the profiled outer value from def:outer-certificate. Then nu_star belongs to argmin_{nu in N(pbar)} V(nu) if and only if there exist scalars a_star, b_star, c_star such that Q_{a_star,b_star,c_star}(d) >= 0 for all d in D_pbar, Q_{a_star,b_star,c_star}(d) = 0 for every d in T_pbar(supp(nu_star)), and H(s) >= V(nu_star) for all s in [0, pbar(1-pbar)] with equality at s = s_star.

### T-block: t2 — For the quartic saturation objective V over the admissibl…
**Statement.** For the quartic saturation objective V over the admissible law class N(pbar), there exists nu_star in argmin_{nu in N(pbar)} V(nu) such that card(supp(nu_star)) <= 3; when pbar in {0,1}, this optimizer is the unique admissible law delta_pbar.

### T-block: t3 — For all real V_1, V_3, V_4 and every 0 < pbar < 1, delta_…
**Statement.** For all real V_1, V_3, V_4 and every 0 < pbar < 1, delta_pbar belongs to argmin_{nu in N(pbar)} V(nu) if and only if min_{d in D_pbar} (V_1 + V_3 d + V_4 d^2) >= 0.

### T-block: t4 — At pbar = 1/3, V_1 = 1, V_3 = -10, and V_4 = 1, the law n…
**Statement.** At pbar = 1/3, V_1 = 1, V_3 = -10, and V_4 = 1, the law nu_w = (2/3) delta_0 + (1/3) delta_1 satisfies m_2(nu_w) = 2/9, m_3(nu_w) = 2/27, m_4(nu_w) - m_2(nu_w)^2 = 2/81, and V(nu_w) - V(delta_(1/3)) = -40/81 < 0.

### T-block: t5 — Let nu = sum_{ell=1}^K w_ell delta_{u_ell} be in N(pbar)
**Statement.** Let nu = sum_{ell=1}^K w_ell delta_{u_ell} be in N(pbar). If M w_ell is an integer for every ell and m u_ell is an integer for every ell, then there exists pi in Pi_{M,m}(pbar) such that L_M(pi) = nu. In particular, these divisibility conditions already imply N pbar in Z. For the Bernoulli vertex (1 - pbar) delta_0 + pbar delta_1, exact attainability reduces to M pbar in Z. For the within-cluster stratified law delta_pbar, exact attainability reduces to m pbar in Z.

### T-block: t6 — For every nu_star in N(pbar) with card(supp(nu_star)) <=…
**Statement.** For every nu_star in N(pbar) with card(supp(nu_star)) <= 3 and N pbar in Z, the grid-split rounding handle produces pi_rd in Pi_{M,m}(pbar) such that V(L_M(pi_rd)) <= V(nu_star) + C_rd(nu_star) (M^(-1) + m^(-1)).

### T-block: t7 — If V_3 = 0 and V_4 = 0, then V(nu) = V_0 + V_1 m_2(nu) fo…
**Statement.** If V_3 = 0 and V_4 = 0, then V(nu) = V_0 + V_1 m_2(nu) for every nu in N(pbar). Hence V_1 > 0 implies delta_pbar minimizes V over nu in N(pbar), V_1 < 0 implies (1 - pbar) delta_0 + pbar delta_1 minimizes V over nu in N(pbar), and V_1 = 0 makes every nu in N(pbar) tie in V, hence all extremal-m_2 laws tie accordingly. The exact finite realization of the Bernoulli vertex uses M pbar in Z, whereas the exact finite realization of delta_pbar uses m pbar in Z.

### T-block: t8 — Under ass:equal-cluster-size, ass:isolated-partial-interf…
**Statement.** Under ass:equal-cluster-size, ass:isolated-partial-interference, ass:anonymous-share-specialization, ass:homogeneous-linear-share-working-model, and ass:cai-leading-expansion-domain, and only within the scoped bridge transcription of lem:variance-moment-reduction, along every regime M,m -> infinity with N pbar in Z the sharp feasible asymptotic o(N^{-1})-free leading surrogate for the randomized-saturation design variance equals min_{nu in N(pbar)} V(nu). More precisely, if pi^(n) in Pi_{M_n,m_n}(pbar) is any feasible sequence along such a regime and L_{M_n}(pi^(n)) converges weakly to nu, then its asymptotic leading surrogate value is V(nu) >= min_{eta in N(pbar)} V(eta); and every minimizer nu_star with card(supp(nu_star)) <= 3 is asymptotically implementable and leading-surrogate-optimal along every such regime via thm:rounding-loss. Consequently, for 0 < pbar < 1 the interior optimal laws for this surrogate are characterized by thm:global-certificate; the stratified-law benchmark delta_pbar is asymptotically leading-surrogate-optimal if and only if min_{d in D_pbar} (V_1 + V_3 d + V_4 d^2) >= 0 by prop:positive-penalty-threshold; if pbar in {0,1}, then N(pbar) = {delta_pbar}, so the boundary benchmark is uniquely optimal for the same surrogate. The SUTVA degeneration is given by prop:sutva-corner. This is only the payoff for that one fixed homogeneous-share Cai leading surrogate; the exact non-leading finite-population variance problem and broader randomized-saturation design problems remain separate scope items.

### T-block: t9 — There is a complete, exact, terminating constructive opti…
**Statement.** There is a complete, exact, terminating constructive optimizer for the quartic saturation program at exact input. The input is theta=(pbar,V_1,V_3,V_4) with 0<=pbar<=1 together with an exact real-closed-field representation of its coordinates, for example rational, algebraic, or other exact real-closed-field data, and the output is a law nu_alg in N(pbar) minimizing V. If pbar is 0 or 1, output delta_pbar; this boundary case is certified directly because N(pbar) is then the singleton {delta_pbar}. If 0<pbar<1, write p=pbar, q=1-p, C=pq, and A=q-p, then enumerate the finite support/contact subsystems: S1, the singleton centered support {0}; S2, the two-point centered supports {-b,a}, equivalently the endpoint cubic branches g_L(t)=p(p+t)(V_1+V_3t+V_4t^2) on [-p,A] and g_R(t)=q(q-t)(V_1+V_3t+V_4t^2) on [A,q] together with their endpoint and stationary equations; and S3, the three-point endpoint-interior centered supports {-p,r,q}, equivalently the KKT systems for the explicit profile branch Phi_3 over 0<=s<=C and -s/q<=r<=s/p, including every active boundary subset. Solve these finitely many polynomial systems by exact real-algebraic elimination, cylindrical algebraic decomposition, Thom encodings, and root isolation; discard infeasible roots; construct the associated laws and exact algebraic V-values; and choose a minimum. The chosen law is certified by exact candidate comparison and, on interior contact patterns, by constructing the quartic residual Q, checking Q>=0 on D_pbar by Sturm/root isolation, and checking the outer inequality H(s)>=V(nu_alg) on [0,C] using the explicit closed-form H(s)=V_0+F(s)-V_4s^2. Exact algebraic CAD/Thom computation at exact input is the constructive method; the separate atlas question is only whether one can compress that exact-input elimination output into compact human-readable regions without claiming a standalone parameter-uniform atlas theorem here.

### T-block: t10 — The exact optimizer over the singleton/two-point saturati…
**Statement.** The exact optimizer over the singleton/two-point saturation class is closed form. Let p=pbar, q=1-p, A=q-p, and q_theta(t)=V_1+V_3t+V_4t^2. The value above V_0 is the minimum of 0, the left endpoint cubic branch g_L(t)=p(p+t)q_theta(t) on t in [-p,A], and the right endpoint cubic branch g_R(t)=q(q-t)q_theta(t) on t in [A,q]. The complete candidate set is t=-p,A,q together with the roots in [-p,A] of V_1+pV_3+2(V_3+pV_4)t+3V_4t^2=0 and the roots in [A,q] of -V_1+qV_3+2(qV_4-V_3)t-3V_4t^2=0. Choosing the candidate with smallest value gives the two-point-class optimum: value 0 gives delta_pbar; a left-branch minimizer gives centered support {-p,p+t} with weights (p+t)/(2p+t) at -p and p/(2p+t) at p+t; and a right-branch minimizer gives centered support {t-q,q} with weights q/(2q-t) at t-q and (q-t)/(2q-t) at q. The two-versus-three-point comparison is the exact algebraic comparison performed inside thm:constructive-optimal-design-algorithm; it is not a missing piece of this complete two-point result.
