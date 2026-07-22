# exp_ego_cluster_exposure_clt — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (Finite-population Bernoulli ego-cluster randomization design).** Finite-population Bernoulli ego-cluster randomization design: a `FiniteDesign` over the cluster-assignment space {0,1}^{m_n}, with fixed exposure-indexed potential outcomes y i h and a design probability functional Pr/E/Var/Cov. The ambient world is the design-based `Experiment` substrate (Aronow-Samii architecture) specialized so the assignment vector is the ego-cluster Bernoulli product design. — Confirmed by reading Design.lean (FiniteDesign: E/Var/Cov/Pr, Var_linear_comb, Cov_linear_comb, indicator facts), Exposure.lean (prop = generalized exposure probability = D.Pr, expoInd, propPairSame/propPairCross, Cov_expoInd_same/cross), HT/Estimator.lean (htTotal/htMean/htEffect/tauTrue/muTrue), Designs/Bernoulli.lean (bernoulliDesign with bernoulliDesign_E/Var/Cov_treatInd, independent Bernoulli cluster indicators). The cluster-assignment vector W_n is exactly the Bernoulli product design; the design-probability algebra (E/Var/Cov) is reused verbatim. The signed-incidence exposure EVENT E_ihn = 1{P_ihn>=1} is a polynomial-threshold indicator (not a single-valued exposure map f z (theta i) = h), so the exposure-event/polynomial layer is built locally over this world rather than reusing `expo`/`expoInd` definitionally; pi_ihn is reused as `FiniteDesign.Pr` of the polynomial event. One S-block binds all 35 symbols: the combinatorial probability-algebra symbols (chi/u/v, monomials, supports) live in the same finite Bernoulli world.
**required modules.** Causalean.Experimentation.DesignBased.Design, Causalean.Experimentation.DesignBased.Designs.Bernoulli, Causalean.Experimentation.DesignBased.Exposure, Causalean.Experimentation.DesignBased.PotentialOutcome, Causalean.Experimentation.DesignBased.HT.Estimator, Causalean.Experimentation.DesignBased.HT.Unbiased, Causalean.Experimentation.DesignBased.HT.Variance, Causalean.Experimentation.DesignBased.GaussianCDF

## Assumptions (A)

**A-1 (assumption).** The ego-cluster assignments W_1n, ..., W_m_nn are mutually independent Bernoulli(p_n) random variables.

**A-2 (assumption).** For every i in U_n, the observed outcome satisfies Y_in^obs = sum_{h in H_n} 1{E_ihn = 1} Y_in(h), and at most one label h has E_ihn = 1.

**A-3 (assumption).** max_{i in U_n, h in H_n} |Y_in(h)| <= M_Y.

**A-4 (assumption).** min_{i in U_n} { pi_ih_n^+n, pi_ih_n^-n } >= pi_min.

**A-5 (assumption).** sigma_n^2 >= c_sigma / n.

**A-6 (assumption).** 2 q_n kappa_n (omega_n - 1) = o(n^(1/4)) as n -> infinity.

**A-7 (assumption).** For any subclass C of def:clt-qualified-ego-incidence-array-class over which uniform coverage is claimed, rho_n(C):=sup_{array in C} 2 q_n kappa_n (omega_n - 1) / n^(1/4) -> 0.

## Definitions (P)

**P-1 ({ ((Y_in(h))_{i in U_n, h in H_n}, (W_n)_{n>=1}, (M_ihn)_…).** { ((Y_in(h))_{i in U_n, h in H_n}, (W_n)_{n>=1}, (M_ihn)_{i in U_n, h in {h_n^+, h_n^-}}) : ass:bernoulli-ego-design and ass:exposure-consistency and ass:bounded-outcomes and ass:positivity }

**P-2 ({ ((Y_in(h))_{i in U_n, h in H_n}, (W_n)_{n>=1}, (M_ihn)_…).** { ((Y_in(h))_{i in U_n, h in H_n}, (W_n)_{n>=1}, (M_ihn)_{i in U_n, h in {h_n^+, h_n^-}}) : ass:bernoulli-ego-design and ass:exposure-consistency and ass:bounded-outcomes and ass:positivity and ass:variance-nondegenerate and ass:primitive-degree-rate }

**P-3 (For each cluster index c and sign sigma in {-1,1}, L_csig…).** For each cluster index c and sign sigma in {-1,1}, L_csigma_n(W_n) = W_cn if sigma = 1 and L_csigma_n(W_n) = 1 - W_cn if sigma = -1.

**P-4 (P_ihn(W_n) = sum_{A in M_ihn} prod_{(c,sigma) in A} L_csi…).** P_ihn(W_n) = sum_{A in M_ihn} prod_{(c,sigma) in A} L_csigma_n(W_n).

**P-5 (E_ihn = 1{ P_ihn(W_n) >= 1 }.).** E_ihn = 1{ P_ihn(W_n) >= 1 }.

**P-6 (chi(A) = 1 if no cluster index c appears with both signs…).** chi(A) = 1 if no cluster index c appears with both signs +1 and -1 in the union of the signed monomials in A, and chi(A) = 0 otherwise.

**P-7 (u(A) = |{ c ).** u(A) = |{ c : (c,1) appears in the union of A and (c,-1) does not appear in the union of A }|.

**P-8 (v(A) = |{ c ).** v(A) = |{ c : (c,-1) appears in the union of A and (c,1) does not appear in the union of A }|.

**P-9 (hat_tau_HT_n = n^(-1) sum_{i=1}^n [ 1{E_ih_n^+n = 1} Y_in…).** hat_tau_HT_n = n^(-1) sum_{i=1}^n [ 1{E_ih_n^+n = 1} Y_in^obs / pi_ih_n^+n - 1{E_ih_n^-n = 1} Y_in^obs / pi_ih_n^-n ].

**P-10 (G_n^dep has vertex set U_n and edge set { {i,j} ).** G_n^dep has vertex set U_n and edge set { {i,j} : i != j and B_in intersect B_jn is nonempty }.

**P-11 (CI_n^orc(1-alpha) = [hat_tau_HT_n - z_(1-alpha/2) sigma_n…).** CI_n^orc(1-alpha) = [hat_tau_HT_n - z_(1-alpha/2) sigma_n, hat_tau_HT_n + z_(1-alpha/2) sigma_n].

**P-12 (Let R={+,-}, h_+=h_n^+, h_-=h_n^-, s_+=1, s_-=-1, pi_{ir}…).** Let R={+,-}, h_+=h_n^+, h_-=h_n^-, s_+=1, s_-=-1, pi_{ir}=pi_{i h_r n}, and E_{ir}=E_{i h_r n}. For i!=j set pi_{ij}^{rs}=pi_ij(h_r,h_s,n); for i=j set pi_{ii}^{rr}=pi_{ir} and pi_{ii}^{rs}=Pr_pi(E_{ir}=1,E_{is}=1), equal to 0 for distinct labels under exposure consistency and to pi_{ir} if the two labels coincide. Define Gamma_{ij}^{rs}=pi_{ij}^{rs}/(pi_{ir}pi_{js})-1 and Q_n(y)=n^{-2} sum_{i,j} sum_{r,s in R} s_r s_s Gamma_{ij}^{rs} y_{ir} y_{js}. Given realized exposure indicators and outcomes, let F_n^{obs}={y in [-M_Y,M_Y]^{2n}: E_{ir}=1 implies y_{ir}=Y_in^obs for every i,r}. Set Vbar_n=max_{y in F_n^{obs}} Q_n(y).

## Lemmas (L)

**L-1 (Under ass:bernoulli-ego-design, for any finite nonempty c…).** Under ass:bernoulli-ego-design, for any finite nonempty collection C of signed monomials, the probability that every literal appearing in the union of C is satisfied equals chi(C) p_n^{u(C)} (1-p_n)^{v(C)}.

**L-2 (Under ass:exposure-consistency, ass:bounded-outcomes, and…).** Under ass:exposure-consistency, ass:bounded-outcomes, and ass:positivity, E_pi[psi_in] = Y_in(h_n^+) - Y_in(h_n^-) for every i, hat_tau_HT_n is unbiased for tau_n, and |psi_in - E_pi[psi_in]| <= 4 M_Y / pi_min.

**L-3 (For the notation in def:variance-envelope-handle, define…).** For the notation in def:variance-envelope-handle, define T_n(y)=n^{-1} sum_i sum_{r in {+,-}} s_r E_{ir} y_{ir}/pi_{ir}. For every fixed y in R^{2n}, Var_pi(T_n(y))=Q_n(y). For the true target vector y^0_{i+}=Y_in(h_n^+) and y^0_{i-}=Y_in(h_n^-), T_n(y^0)=hat_tau_HT_n and Q_n(y^0)=sigma_n^2.

**L-4 (For every realized dataset generated by an array satisfyi…).** For every realized dataset generated by an array satisfying ass:exposure-consistency and ass:bounded-outcomes, the Vbar_n construction in def:variance-envelope-handle is a finite-dimensional observed-data functional and its maximum over F_n^{obs} is attained.

**L-5 (For the Vbar_n construction in def:variance-envelope-hand…).** For the Vbar_n construction in def:variance-envelope-handle, every realized dataset generated by an admissible finite-population array satisfies Vbar_n >= sigma_n^2.

**L-6 (For the Vbar_n construction in def:variance-envelope-hand…).** For the Vbar_n construction in def:variance-envelope-handle, Vbar_n is the pointwise smallest observed-data upper envelope for sigma_n^2 over bounded target-potential completions consistent with the realized target-exposure data.

**L-7 (For any subclass C of def:clt-qualified-ego-incidence-arr…).** For any subclass C of def:clt-qualified-ego-incidence-array-class satisfying ass:uniform-primitive-degree-rate and any fixed alpha in (0,1), liminf_n inf_{A in C} Pr_{pi,A}{ tau_n(A) in CI_n^orc(A;1-alpha) } >= 1-alpha.

## Theorems (T)

### T-block: t1 — Under ass:bernoulli-ego-design, for every unit i in U_n a…
**Statement.** Under ass:bernoulli-ego-design, for every unit i in U_n and target exposure label h in {h_n^+, h_n^-}, pi_ihn = sum_{emptyset != A subseteq M_ihn} (-1)^(|A|+1) chi(A) p_n^(u(A)) (1-p_n)^(v(A)). For every pair i != j and labels h, h' in {h_n^+, h_n^-}, pi_ij(h,h',n) = sum_{emptyset != A subseteq M_ihn} sum_{emptyset != B subseteq M_jh'n} (-1)^(|A|+|B|) chi(A union B) p_n^(u(A union B)) (1-p_n)^(v(A union B)).

### T-block: t2 — Under ass:bernoulli-ego-design and ass:exposure-consisten…
**Statement.** Under ass:bernoulli-ego-design and ass:exposure-consistency, let G_n^dep be as in def:dependency-graph. Then the centered raw summands psi_in - E_pi[psi_in] admit G_n^dep as a dependency graph, and Delta_n <= b_n (omega_n - 1) <= 2 q_n kappa_n (omega_n - 1).

### T-block: t3 — Under ass:bernoulli-ego-design, ass:exposure-consistency,…
**Statement.** Under ass:bernoulli-ego-design, ass:exposure-consistency, ass:bounded-outcomes, ass:positivity, ass:variance-nondegenerate, and ass:primitive-degree-rate, (hat_tau_HT_n - tau_n) / sigma_n converges in distribution to N(0,1). Consequently, for every fixed alpha in (0,1), Pr_pi{ tau_n in CI_n^orc(1-alpha) } -> 1 - alpha.

### T-block: t4 — Under ass:bernoulli-ego-design, ass:exposure-consistency,…
**Statement.** Under ass:bernoulli-ego-design, ass:exposure-consistency, ass:bounded-outcomes, ass:positivity, ass:variance-nondegenerate, and ass:primitive-degree-rate, with Vbar_n the computable functional of def:variance-envelope-handle, for every fixed alpha in (0,1), liminf_n Pr_pi{ tau_n in [hat_tau_HT_n - z_(1-alpha/2) sqrt(Vbar_n), hat_tau_HT_n + z_(1-alpha/2) sqrt(Vbar_n)] } >= 1 - alpha for each sequence in def:clt-qualified-ego-incidence-array-class, and uniformly over any subclass satisfying ass:uniform-primitive-degree-rate. Moreover Vbar_n is the pointwise smallest observed-data upper envelope for sigma_n^2 over bounded target-potential completions consistent with the realized target-exposure data, so among Wald intervals obtained from observed-data variance upper envelopes that dominate sigma_n^2 completion-wise on that bounded-completion class, the choice V_n = Vbar_n yields the pointwise shortest conservative interval.
