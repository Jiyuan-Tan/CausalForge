# exp_bipartite_minimax_design — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (Finite-population Bernoulli randomization design (assignm…).** Finite-population Bernoulli randomization design (assignment world): probability comes from the experimenter's independent heterogeneous Bernoulli coin flips over the finite assignment space Ω = (I_n → Bool); the design variable p and its feasible class are the decision objects. — Reuse the finite-sum design layer FiniteDesign (E/Var/Cov as Finset algebra) and the product Bernoulli design bernoulliDesign p (per-unit coin flips, cross-unit independence STRUCTURAL via prodDesign). This directly realizes ass:independent-heterogeneous-bernoulli. bernoulliDesign_E_treat/_E_ctrl give the marginal treatment/control expectations feeding pi_i^1/pi_i^0. The positivity floor epsilon and budget B_n restrict p but do not change the world. Verified signatures: bernoulliDesign (Bernoulli.lean:60), FiniteDesign (Design.lean).
**required modules.** Causalean.Experimentation.DesignBased.Design, Causalean.Experimentation.UnknownInterference.Bernoulli

**S-2 (Bipartite interference graph + fixed finite-population po…).** Bipartite interference graph + fixed finite-population potential-outcome schedule: known bipartite graph G_n over I_n × O_n, outcome neighborhoods N_i(G_n), fixed bounded potential outcomes Y_i(z_{N_i}), Hajek exposure estimator and its graph-only conservative variance objects. — Search trace: grepped '## Experimentation' in ../doc/API.md + scanned Causalean/Experimentation/{DesignBased,UnknownInterference}; no BipartiteDesign / bipartite-graph structure exists (all interference substrate is one-mode: ExposureMappingInterference, UnknownInterference.Interferes/InterfDep). So the bipartite graph layer (I_n, O_n, G_n, N_i, M_k, degrees, shared sets S_ij) is new local scaffolding. It nonetheless SITS INSIDE the S1 FiniteDesign world: fixed potential outcomes Y_i as functions of the treatment subvector on N_i mirror UnknownInterference.y / y_eq_of_agree_on_interferers (analogue F3 should follow for the interference-restriction algebra), and the all-treated/all-control exposure indicators T_i/C_i are products over N_i (compare Exposure.expoInd). Define a local BipartiteExperiment structure bundling G_n and the neighborhood accessors.
**required modules.** CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Basic

## Assumptions (A)

**A-1 (assumption).** For every i in O_n and every z,z' in {0,1}^{m_n}, z_{N_i(G_n)} = z'_{N_i(G_n)} implies Y_i(z_{N_i}) = Y_i(z'_{N_i}).

**A-2 (assumption).** For every k in I_n, Z_k is Bernoulli(p_k), and the collection {Z_k : k in I_n} is mutually independent.

**A-3 (assumption).** For every k in I_n, epsilon <= p_k <= 1-epsilon.

**A-4 (assumption).** sum_{k in I_n} p_k = B_n.

**A-5 (assumption).** For every i in O_n, |Y_i^1| <= 1 and |Y_i^0| <= 1.

**A-6 (assumption).** max_{i in O_n} d_i <= dbar.

**A-7 (assumption).** Delta_n <= Dbar.

**A-8 (assumption).** liminf_{n -> infty} sigma_{G_n,p_n^*(G_n)}^2(Y) > 0.

## Definitions (P)

**P-1 (P_{n,B_n,epsilon} = {p in [0,1]^{m_n} ).** P_{n,B_n,epsilon} = {p in [0,1]^{m_n} : epsilon <= p_k <= 1-epsilon for every k in I_n, and sum_{k in I_n} p_k = B_n}

**P-2 (D_1(p,Z) = sum_{i in O_n} T_i(Z) / pi_i^1(p), D_0(p,Z) =…).** D_1(p,Z) = sum_{i in O_n} T_i(Z) / pi_i^1(p), D_0(p,Z) = sum_{i in O_n} C_i(Z) / pi_i^0(p)

**P-3 (hat_tau_H(p) = 1{D_1(p,Z) > 0}{sum_{i in O_n} T_i(Z) Y_i^…).** hat_tau_H(p) = 1{D_1(p,Z) > 0}{sum_{i in O_n} T_i(Z) Y_i^obs / pi_i^1(p)} / D_1(p,Z) - 1{D_0(p,Z) > 0}{sum_{i in O_n} C_i(Z) Y_i^obs / pi_i^0(p)} / D_0(p,Z)

**P-4 (eta_i(p,Z) = (T_i(Z)/pi_i^1(p) - 1)(Y_i^1-mu_1) - (C_i(Z)…).** eta_i(p,Z) = (T_i(Z)/pi_i^1(p) - 1)(Y_i^1-mu_1) - (C_i(Z)/pi_i^0(p) - 1)(Y_i^0-mu_0)

**P-5 (sigma_{G_n,p}^2(Y) = n Var_p(n^(-1) sum_{i in O_n} eta_i(…).** sigma_{G_n,p}^2(Y) = n Var_p(n^(-1) sum_{i in O_n} eta_i(p,Z)) = n^(-1) sum_{i,j in O_n} E_p[eta_i(p,Z) eta_j(p,Z)]

**P-6 (V_env(G_n,p) = 4 n^(-1) sum_{i,j in O_n} {r_{ij}^1(G_n,p)…).** V_env(G_n,p) = 4 n^(-1) sum_{i,j in O_n} {r_{ij}^1(G_n,p) + r_{ij}^0(G_n,p) + 2 r_{ij}^{10}(G_n)}

**P-7 (p_n^*(G_n) in argmin_{p in P_{n,B_n,epsilon}} V_env(G_n,p…).** p_n^*(G_n) in argmin_{p in P_{n,B_n,epsilon}} V_env(G_n,p), whenever the argmin set is nonempty

**P-8 (g_k(G_n,p) = partial_{p_k}(V_env(G_n,p)/4) = n^(-1) sum_{…).** g_k(G_n,p) = partial_{p_k}(V_env(G_n,p)/4) = n^(-1) sum_{i,j in O_n : k in S_{ij}(G_n)} {-(product_{ell in S_{ij}(G_n)} p_ell^(-1)) p_k^(-1) + (product_{ell in S_{ij}(G_n)} (1-p_ell)^(-1)) (1-p_k)^(-1)}

**P-9 (hat_V_cons(G_n,p) = V_env(G_n,p)).** hat_V_cons(G_n,p) = V_env(G_n,p)

**P-10 (p_n^{deg}(G_n) in argmin_{p in P_{n,B_n,epsilon}} sum_{k…).** p_n^{deg}(G_n) in argmin_{p in P_{n,B_n,epsilon}} sum_{k in I_n} h_k(G_n){p_k^(-1) + (1-p_k)^(-1)}, whenever the argmin set is nonempty

**P-11 (alpha_cert(G_n) = V_env(G_n,p_n^{deg}(G_n)) / min_{p in P…).** alpha_cert(G_n) = V_env(G_n,p_n^{deg}(G_n)) / min_{p in P_{n,B_n,epsilon}} V_env(G_n,p) when min_{p in P_{n,B_n,epsilon}} V_env(G_n,p) > 0, and alpha_cert(G_n) = 1 when min_{p in P_{n,B_n,epsilon}} V_env(G_n,p) = 0 (no-loss convention: a zero envelope minimum forces V_env(G_n,p_n^{deg}(G_n))=0 as well, since V_env is a nonnegative sum over shared-neighborhood pairs that vanishes for every feasible design precisely when there are no such pairs, so there is no relative loss). Thus alpha_cert(G_n) is a total, [1,infty)-valued observable on the admitted bounded-degree graph class.

## Lemmas (L)

**L-1 (Under ass:independent-heterogeneous-bernoulli, ass:bounde…).** Under ass:independent-heterogeneous-bernoulli, ass:bounded-outcome-degree, and ass:bounded-overlap-dependency, sup_{p in P_{n,B_n,epsilon}} P_p(D_1(p,Z) = 0 or D_0(p,Z) = 0) = O(n^{-1}).

**L-2 (Let {X_{n,i}:1<=i<=n} be centered real random variables w…).** Let {X_{n,i}:1<=i<=n} be centered real random variables with a dependency graph of maximum degree at most D, |X_{n,i}|<=M for fixed finite D and M, and Var(sum_i X_{n,i})=v_n with v_n>=c n for some c>0 eventually. Then (sum_i X_{n,i})/sqrt(v_n) converges in distribution to N(0,1).

## Theorems (T)

### T-block: t1 — Under ass:independent-heterogeneous-bernoulli, if p_k = p…
**Statement.** Under ass:independent-heterogeneous-bernoulli, if p_k = p for every k in I_n for a common scalar p in (0,1), then r_{ij}^1(G_n,p) = 1{S_{ij}(G_n) != emptyset}(p^(-|S_{ij}(G_n)|) - 1), r_{ij}^0(G_n,p) = 1{S_{ij}(G_n) != emptyset}((1-p)^(-|S_{ij}(G_n)|) - 1), r_{ij}^{10}(G_n) = 1{S_{ij}(G_n) != emptyset}, and sigma_{G_n,p}^2(Y) = n^(-1) sum_{i,j in O_n} [r_{ij}^1(G_n,p)(Y_i^1-mu_1)(Y_j^1-mu_1) + r_{ij}^0(G_n,p)(Y_i^0-mu_0)(Y_j^0-mu_0) + 2 r_{ij}^{10}(G_n)(Y_i^1-mu_1)(Y_j^0-mu_0)], which is the homogeneous Bernoulli Hajek overlap formula of Lu, Shi, Fang, Zhang, and Ding (2025).

### T-block: t2 — Under ass:independent-heterogeneous-bernoulli and ass:bou…
**Statement.** Under ass:independent-heterogeneous-bernoulli and ass:bounded-outcomes, for every p in (0,1)^{m_n}, E_p[eta_i(p,Z) eta_j(p,Z)] = r_{ij}^1(G_n,p)(Y_i^1-mu_1)(Y_j^1-mu_1) + r_{ij}^0(G_n,p)(Y_i^0-mu_0)(Y_j^0-mu_0) + r_{ij}^{10}(G_n){(Y_i^1-mu_1)(Y_j^0-mu_0) + (Y_i^0-mu_0)(Y_j^1-mu_1)} for every i,j in O_n. Consequently sigma_{G_n,p}^2(Y) = n^(-1) sum_{i,j in O_n} [r_{ij}^1(G_n,p)(Y_i^1-mu_1)(Y_j^1-mu_1) + r_{ij}^0(G_n,p)(Y_i^0-mu_0)(Y_j^0-mu_0) + r_{ij}^{10}(G_n){(Y_i^1-mu_1)(Y_j^0-mu_0) + (Y_i^0-mu_0)(Y_j^1-mu_1)}] <= V_env(G_n,p).

### T-block: t3 — The feasible set P_{n,B_n,epsilon} is a nonempty compact…
**Statement.** The feasible set P_{n,B_n,epsilon} is a nonempty compact convex subset of [0,1]^{m_n}, the map p -> V_env(G_n,p) is convex on P_{n,B_n,epsilon}, and therefore the argmin set in def:optimal-design is nonempty. For every minimizer p_n^*(G_n) there exist lambda_n in R and box multipliers nu_{k,n}^+ >= 0, nu_{k,n}^- >= 0 (k in I_n) such that the observable KKT system g_k(G_n,p_n^*(G_n)) = lambda_n - nu_{k,n}^+ + nu_{k,n}^- holds for each k in I_n, together with nu_{k,n}^+((p_n^*(G_n))_k-(1-epsilon)) = 0 and nu_{k,n}^-(epsilon-(p_n^*(G_n))_k) = 0.

### T-block: t4 — Under ass:bipartite-interference, ass:independent-heterog…
**Statement.** Under ass:bipartite-interference, ass:independent-heterogeneous-bernoulli, ass:bounded-outcomes, ass:bounded-outcome-degree, ass:bounded-overlap-dependency, and ass:variance-nondegenerate, sqrt(n){hat_tau_H(p_n^*(G_n)) - tau_n} = n^(-1/2) sum_{i in O_n} eta_i(p_n^*(G_n),Z) + o_p(1), and sqrt(n){hat_tau_H(p_n^*(G_n)) - tau_n} / sqrt(sigma_{G_n,p_n^*(G_n)}^2(Y)) ->d N(0,1).

### T-block: t5 — Under the assumptions of thm:hetero-clt, hat_V_cons(G_n,p…
**Statement.** Under the assumptions of thm:hetero-clt, hat_V_cons(G_n,p_n^*(G_n)) = V_env(G_n,p_n^*(G_n)) is conservative for sigma_{G_n,p_n^*(G_n)}^2(Y), and for every sequence of potential-outcome schedules satisfying those assumptions, liminf_{n -> infty} P_{p_n^*(G_n)}(tau_n in [hat_tau_H(p_n^*(G_n)) - z_{1-alpha_cov/2} sqrt{hat_V_cons(G_n,p_n^*(G_n)) / n}, hat_tau_H(p_n^*(G_n)) + z_{1-alpha_cov/2} sqrt{hat_V_cons(G_n,p_n^*(G_n)) / n}]) >= 1-alpha_cov.

### T-block: t6 — Does alpha_cert(G_n) remain uniformly bounded whenever su…
**Statement.** Does alpha_cert(G_n) remain uniformly bounded whenever sum_{ell in I_n} s_ell^2 > 0, max_{k in I_n} s_k^2 / sum_{ell in I_n} s_ell^2 <= c_disp, and max_{k in I_n} h_k(G_n) / min_{k in I_n : h_k(G_n) > 0} h_k(G_n) <= C_disp?

### T-block: t7 — Set rho = B_n / m_n and let p^hom denote the homogeneous…
**Statement.** Set rho = B_n / m_n and let p^hom denote the homogeneous feasible design with (p^hom)_k = rho for every k in I_n; assume rho in (epsilon, 1-epsilon) and rho != 1/2. If the homogeneous-point envelope-gradient scores {g_k(G_n, p^hom) : k in I_n} of def:kkt-gradient are not all equal, then p^hom is not a minimizer of p -> V_env(G_n,p) over P_{n,B_n,epsilon}; consequently every envelope-optimal design p_n^*(G_n) of def:optimal-design is non-homogeneous and satisfies the strict inequality V_env(G_n, p_n^*(G_n)) < V_env(G_n, p^hom), and the gap admits the explicit observable lower bound V_env(G_n,p^hom) - V_env(G_n,p_n^*(G_n)) >= 2 Delta_g min{eta_box, Delta_g / L_ab}, where Delta_g = max_{k in I_n} g_k(G_n,p^hom) - min_{k in I_n} g_k(G_n,p^hom) > 0 is the gradient-score spread, eta_box = min{rho - epsilon, 1 - epsilon - rho} > 0, a in argmax_{k in I_n} g_k(G_n,p^hom), b in argmin_{k in I_n} g_k(G_n,p^hom), and L_ab = sup_{q in P_{n,B_n,epsilon}} (e_b - e_a)^T Hess(V_env(G_n,cdot)/4)(q) (e_b - e_a) is the directional second-order modulus of the graph-only envelope along the budget-feasible direction e_b - e_a (all four quantities being observable functions of G_n, epsilon, and B_n), with the bound read as 2 Delta_g eta_box when L_ab = 0. In particular, for singleton-exposure graphs, in which each outcome unit's neighborhood is a single intervention unit so that every nonempty S_{ij}(G_n) is a singleton, the gradient scores reduce to observable per-unit degree summaries, and the hypothesis (hence the strict improvement of the optimal heterogeneous design over the homogeneous design) holds whenever those summaries are not all equal.

### T-block: t8 — Under ass:bounded-outcome-degree, which forces max_{i,j i…
**Statement.** Under ass:bounded-outcome-degree, which forces max_{i,j in O_n} |S_{ij}(G_n)| <= dbar, with the explicit constant C(epsilon, dbar) = max{1, epsilon^{-(dbar-1)}} depending only on epsilon and dbar, the observable approximation ratio of def:approximation-ratio satisfies alpha_cert(G_n) <= C(epsilon, dbar). The bound follows from a uniform sandwich, valid for every feasible p in P_{n,B_n,epsilon}, between the graph-only envelope V_env(G_n,p) of def:graph-envelope and the additive degree-surrogate objective sum_{k in I_n} h_k(G_n){p_k^{-1} + (1-p_k)^{-1}} minimized in def:surrogate-design, in which the per-pair product loads over the shared-neighborhood sets S_{ij}(G_n) are comparable to their additive per-coordinate counterparts up to a multiplicative factor controlled by the bounded shared-neighborhood size dbar and the positivity floor epsilon. This is the positive counterpart, in the paper's own sparse bounded-degree regime, of the negative first-order-summary answer proved in oeq:dispersion-certificate.
