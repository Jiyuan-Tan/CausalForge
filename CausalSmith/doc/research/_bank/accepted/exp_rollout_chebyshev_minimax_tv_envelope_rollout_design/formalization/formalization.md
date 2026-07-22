# exp_rollout_chebyshev_minimax — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (Finite-population monotone-Bernoulli rollout DESIGN world).** Finite-population monotone-Bernoulli rollout DESIGN world: the only randomness is the experimenter's rollout randomization pi over a finite assignment space; round means bar_Y_j are real random variables of the realized assignment, and E_pi/Var_pi/Cov_pi are finite-sum design moments. This is exactly the abstraction of Causalean's FiniteDesign probability layer. — FiniteDesign Ω = PMF over a finite assignment space with FiniteDesign.E/Var/Cov as finite sums (Design.lean:45-217). bar_Y_j : Ω → ℝ are round-mean random variables; Var_pi(bar_Y_j) is FiniteDesign.Var, Gamma_P(p) is the (k+1)x(k+1) FiniteDesign.Cov matrix, hat_tau_{w,p} = ∑ w_j bar_Y_j. FiniteDesign.Var_linear_comb / Var_const_mul / Cov_* supply the design-variance algebra reused by the variance-layer lemmas. The paper takes the potential-outcome / static-rollout consistency and the per-round variance ENVELOPE as threaded Prop assumptions (inherited setup + novel envelope), so Y_i(z), Z_j, U_n, m_P, a_{P,ell}, tau_P are exposed at the abstract FiniteDesign level rather than via a bespoke PO structure — the highest-leverage reuse decision, matching the paper's honest scope (novelty is the approximation-theoretic design object, not new PO machinery). Surveyed Causalean PO substrate (PotentialOutcome.lean, Exposure.lean, HT/*): those target Horvitz–Thompson measure/measurability estimation under exposure mappings and DERIVE design variance from network structure; this paper instead ASSUMES the round-variance envelope, so the HT variance derivations (var_htMean_le, EdgeVarianceBound, CompoundVariance) are a different abstraction and not a fit — recorded as bypass-justified.
**required modules.** Causalean.Experimentation.DesignBased.Design

**S-2 (Real / polynomial ℓ¹ optimal-recovery ambient).** Real / polynomial ℓ¹ optimal-recovery ambient: budgeted node schedules, linear-unbiased weight vectors, the ℓ¹ amplification criterion and its minimax value, and the Chebyshev / equal-spacing grids are pure real-analytic objects over ℝ, Fin (k+1) → ℝ, and Polynomial ℝ (Mathlib). No design/PMF object appears in these definitions or in the approximation-theoretic lemmas. — bypass-justified: the amplification criterion A_beta(p) = inf over W_beta(p) of (∑|w_j|)² is a pure ℓ¹/ℓ∞-dual optimal-recovery quantity over polynomial-unbiased weight vectors; the Causalean design world (FiniteDesign) is at a different abstraction (measure of a randomization) and does not fit these purely algebraic-analytic objects. Searched Causalean experimentation substrate for 'amplification / minimax schedule / Chebyshev node / budgeted design' (npm search concepts, lean_local_search FiniteDesign/Optimality/Minimax/Neyman): Optimality/Minimax.lean is Neyman-allocation design minimax, not node-placement ℓ¹ amplification — not found. Mathlib supplies Polynomial.Chebyshev.T ℝ n and the Extremal/RootsExtrema Chebyshev API used by the endpoint lemmas.
**required modules.** Mathlib.RingTheory.Polynomial.Chebyshev, Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal, Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

## Assumptions (A)

**A-1 (assumption).** At each rollout measurement j, the observed round mean equals bar_Y_j = n^(-1) sum_{i in U_n} Y_i(Z_j), and the potential outcomes depend on the contemporaneous assignment vector Z_j but not on earlier rollout steps.

**A-2 (assumption).** For every law P, the rollout mean curve satisfies m_P(u) = sum_{ell=0}^beta a_{P,ell} u^ell for all u in [0,1].

**A-3 (assumption).** For every law P, every admissible schedule p, and every rollout measurement j, Var_pi(bar_Y_j) <= sigma_0^2 / n.

**A-4 (assumption).** q <= q_max < 1.

## Definitions (P)

**P-1 (S_{k,q} = { p in [0,1]^(k+1) ).** S_{k,q} = { p in [0,1]^(k+1) : p_0 = 0 and 0 < p_1 < ... < p_k = q }

**P-2 (P_beta = { P ).** P_beta = { P : ass:static-rollout-consistency and ass:beta-order-polynomial and ass:round-mean-variance-envelope }

**P-3 (W_beta(p) = { w in R^(k+1) ).** W_beta(p) = { w in R^(k+1) : sum_{j=0}^k w_j p_j^0 = 0 and sum_{j=0}^k w_j p_j^ell = 1 for ell = 1, ..., beta }

**P-4 (p_j^Ch(k,q) = q { 1 - cos(pi j / k) } / 2 for j = 0, ...,…).** p_j^Ch(k,q) = q { 1 - cos(pi j / k) } / 2 for j = 0, ..., k, and p^Ch(k,q) = (p_0^Ch(k,q), ..., p_k^Ch(k,q)).

**P-5 (A_beta(p) = inf_{w in W_beta(p)} (sum_{j=0}^k |w_j|)^2 an…).** A_beta(p) = inf_{w in W_beta(p)} (sum_{j=0}^k |w_j|)^2 and M_{beta,k,q} = inf_{p in S_{k,q}} A_beta(p).

**P-6 (R_exact(beta,k,q) = inf_{p in S_{k,q}} inf_{w in W_beta(p…).** R_exact(beta,k,q) = inf_{p in S_{k,q}} inf_{w in W_beta(p)} sup_{P in P_beta} w' Gamma_P(p) w.

**P-7 (Under ass:low-budget-cap, with beta>=1, k=ceil(c beta), q…).** Under ass:low-budget-cap, with beta>=1, k=ceil(c beta), q in (0,q_max], and the admissible Chebyshev schedule p^Ch(k,q) in S_{k,q} (lem:chebyshev-schedule-admissible), does the shifted Chebyshev-Lobatto schedule also solve the exact finite-population nested-rollout minimax problem R_exact(beta,k,q), where Gamma_P(p) is the true covariance matrix of the monotone Bernoulli rollout rather than the total-variation variance envelope? The Chebyshev schedule is rate-feasible for R_exact by thm:chebyshev-minimax (the Chebyshev-schedule amplification upper bound) together with lem:exact-risk-envelope-upper (the envelope-to-exact-risk bridge); exact optimality is open.

## Lemmas (L)

**L-1 (Under ass:static-rollout-consistency and ass:beta-order-p…).** Under ass:static-rollout-consistency and ass:beta-order-polynomial, tau_P = m_P(1) - m_P(0) = sum_{ell=1}^beta a_{P,ell}.

**L-2 (Let p^eq(beta,q) = (0, q / beta, 2 q / beta, ..., q)).** Let p^eq(beta,q) = (0, q / beta, 2 q / beta, ..., q). There exists a universal positive constant C_eq (one may take C_eq = 9) such that A_beta(p^eq(beta,q)) <= C_eq (beta / q)^(2 beta) for every integer beta >= 1 and every q in (0,1].

**L-3 (At the full-budget boundary q = 1, the equal-spacing sche…).** At the full-budget boundary q = 1, the equal-spacing schedule p^eq(beta,1) admits the endpoint rule w_0 = -1, w_beta = 1, and w_j = 0 for j = 1, ..., beta - 1; hence w belongs to W_beta(p^eq(beta,1)) and A_beta(p^eq(beta,1)) <= 4.

**L-4 (For a schedule p with distinct nodes and with W_beta(p) n…).** For a schedule p with distinct nodes and with W_beta(p) nonempty, inf_{w in W_beta(p)} sum_j |w_j| equals sup{|r(1)-r(0)| : r is a real polynomial of degree at most beta and max_j |r(p_j)|<=1}. Consequently A_beta(p) is the square of this dual norm.

**L-5 (Assume beta>=1).** Assume beta>=1. For every real polynomial P of degree at most beta with sup_{x in [-1,1]} |P(x)|<=1 and every x_0>1, one has |P(x_0)| <= T_beta(x_0).

**L-6 (For each c>1 there is a finite constant K(c) such that, f…).** For each c>1 there is a finite constant K(c) such that, for every beta>=1, every integer k>=c beta, and every real polynomial R of degree at most beta, sup_{x in [-1,1]} |R(x)| <= K(c) max_{0<=j<=k} |R(-cos(pi j/k))|.

**L-7 (Let q in (0,1), x_q=2/q-1, lambda(q)=x_q+sqrt(x_q^2-1), a…).** Let q in (0,1), x_q=2/q-1, lambda(q)=x_q+sqrt(x_q^2-1), and rho(q)=q lambda(q)=(1+sqrt(1-q))^2. For every degree-beta polynomial R with sup_{x in [-1,1]}|R(x)|<=1, |R(x_q)-R(-1)| <= C(q_max) lambda(q)^beta uniformly over q in (0,q_max]; and the Chebyshev polynomial T_beta gives the matching lower order T_beta(x_q)-1 >= c(q_max) lambda(q)^beta.

**L-8 (For every integer k>=1 and q in (0,1], the shifted Chebys…).** For every integer k>=1 and q in (0,1], the shifted Chebyshev-Lobatto schedule p^Ch(k,q) belongs to S_{k,q}.

**L-9 (Assume beta>=1 and k>=beta).** Assume beta>=1 and k>=beta. For every schedule p in S_{k,q}, the unbiased linear weight set W_beta(p) is nonempty.

**L-10 (If X_0,...,X_k are square-integrable rollout-round statis…).** If X_0,...,X_k are square-integrable rollout-round statistics with Var_pi(X_j)<=sigma_0^2/n for every j, then Var_pi(sum_j w_j X_j) <= sigma_0^2 n^(-1) (sum_j |w_j|)^2 for every real w. Moreover this bound is sharp over covariance matrices whose diagonal entries are bounded by sigma_0^2/n.

**L-11 (Assume beta>=1 and k>=beta).** Assume beta>=1 and k>=beta. For every q in (0,1] and every p in S_{k,q}, inf_{w in W_beta(p)} sup_{P in P_beta} w' Gamma_P(p) w <= (sigma_0^2/n) A_beta(p). Consequently R_exact(beta,k,q) <= (sigma_0^2/n) M_{beta,k,q}.

**L-12 (Fix c>1, beta>=1, k=ceil(c beta), q in (0,q_max], and rho…).** Fix c>1, beta>=1, k=ceil(c beta), q in (0,q_max], and rho(q)=(1+sqrt(1-q))^2. The admissible shifted Chebyshev-Lobatto schedule satisfies inf_{w in W_beta(p^Ch(k,q))} sup_{P in P_beta} w' Gamma_P(p^Ch(k,q)) w <= (sigma_0^2/n) C_+(c,q_max) (rho(q)/q)^(2 beta). Consequently R_exact(beta,k,q) <= (sigma_0^2/n) C_+(c,q_max) (rho(q)/q)^(2 beta).

## Theorems (T)

### T-block: t1 — Assume beta>=1 and k>=beta
**Statement.** Assume beta>=1 and k>=beta. For every schedule p in S_{k,q} and every weight vector w in W_beta(p), the estimator hat_tau_{w,p} is design-unbiased for tau_P over P in P_beta, and Var_pi(hat_tau_{w,p}) <= sigma_0^2 n^(-1) (sum_{j=0}^k |w_j|)^2. Consequently, since W_beta(p) is nonempty for every p in S_{k,q}, over the sharp total-variation variance envelope the best achievable design variance for a fixed schedule p is sigma_0^2 n^(-1) A_beta(p); the dimensionless minimax amplification value over budgeted schedules is M_{beta,k,q}=inf_{p in S_{k,q}} A_beta(p); the corresponding minimax design variance over budgeted schedules is sigma_0^2 n^(-1) M_{beta,k,q}; and an optimal schedule for the variance envelope is any minimizer p^* in S_{k,q} attaining A_beta(p^*)=M_{beta,k,q}.

### T-block: t2 — Fix c > 1 and q_max in (0,1), and define the pointwise Ch…
**Statement.** Fix c > 1 and q_max in (0,1), and define the pointwise Chebyshev base rho(q)=(1+sqrt(1-q))^2. There exist positive constants C_-(q_max) and C_+(c,q_max) such that, for every beta>=1, every integer k >= c beta, and every q in (0,q_max], every schedule p in S_{k,q} satisfies A_beta(p) >= C_-(q_max) (rho(q)/q)^(2 beta), while the shifted Chebyshev-Lobatto schedule satisfies A_beta(p^Ch(k,q)) <= C_+(c,q_max) (rho(q)/q)^(2 beta). Hence M_{beta,k,q} has pointwise low-budget exponential base rho(q)/q; as q downarrow 0 this is 4/q, the intrinsic exponent is 2 beta, and the equal-spacing beta/q factor is not minimax in beta once the rollout uses more than beta+1 nodes.
