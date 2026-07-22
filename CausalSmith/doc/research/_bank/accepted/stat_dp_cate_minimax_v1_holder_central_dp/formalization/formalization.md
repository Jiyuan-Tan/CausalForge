# stat_dp_cate_minimax_v1 — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (i.i.d).** i.i.d. observational CATE law with potential-outcome overlay (single-observation Measure over O=(Y,A,X) on ([-1,1]x{0,1}x[0,1]^d), law-side nuisances pi_P, mu_{0,P}, mu_{1,P}, tau_P, covariate marginal P_X with density p_P, and the PO process Y(.)) — Define-local `CateObs d`/`CateLaw d` world DIRECTLY analogous to CausalSmith.Stat.DoseResponseMinimax.{DoseObs,DoseLaw} (adapt: binary A in {0,1} and two outcome-regression fields mu0,mu1 with tau=mu1-mu0, vs the continuous-dose single mu). The i.i.d. n-sample content of ass:iid reuses Causalean.Stat.IIDSample (Causalean.Stat.Sample) exactly as DoseResponseMinimax's IidSampling does; the n-fold product law is Measure.pi (fun _:Fin n => P.dataMeasure). Search trace: grepped ../doc/API.md for 'observed_data_unit / PO system / Measure DoseObs'; Causalean.PO.POSystem is a heavier graph/regime-indexed PO skeleton (bypass-justified, same call as DoseResponseMinimax) - consistency+exchangeability kept as threaded Props on the constructed law. No exact Causalean CATE-law world exists -> define-local.
**required modules.** Causalean.Stat.Sample

**S-2 (central approximate-(epsilon_n,delta_n)-differential-priv…).** central approximate-(epsilon_n,delta_n)-differential-privacy release overlay: a randomized mechanism M_n as a measurable/Markov map from samples in (([-1,1]x{0,1}x[0,1]^d))^n to Borel R, with neighboring datasets D,D' (differing in one record), output events B, and the deterministic privacy-budget sequences epsilon_n in [n^-1,1], delta_n in (0,n^-2] — Search trace: grepped ../doc/API.md and doc/API.md for 'DifferentialPrivacy|Privacy|Laplace|epsilon.*delta|central DP' -> NOT FOUND (no DP substrate in Causalean/CausalSmith). Overlay is build-inline over Mathlib MeasureTheory: M_n modeled as a measurable kernel / randomized map (Fin n -> CateObs d) -> Measure R. The central-DP predicate ass:central-dp is one named Prop. Novel infrastructure for the stat cluster but elementary (a Prop over measures) - build-inline, not Defer.
**required modules.**

**S-3 (regime constants + Holder regularity classes and derived…).** regime constants + Holder regularity classes and derived rate/class objects (plain real/nat binders enforced by a standing RegimeConstants well-formedness predicate; Holder ball realized by a define-local standard-convention multivariate Holder-ball def `HolderBallStd`; the derived objects are realized by their own def nodes) — CONVENTION FIX (round 3): the Holder-ball symbol H^s([0,1]^d,L) is DEFINE-LOCAL, NOT a reuse of CausalSmith.Stat.DoseResponseMinimax.HolderBallND. Confronted HolderBallND (CausalSmith/Stat/STAT_DoseResponseMinimax_Research/Basic.lean:87): it bounds iteratedFDeriv up to k=floor(order) and makes the k-th derivative (order-floor(order))-Holder. At INTEGER order s (floor s = s) this collapses to a 0-exponent condition on the s-th derivative (i.e. C^{s,0}), whereas the core + proof_tex use the STANDARD nonparametric convention C^{ceil(s)-1, s-(ceil(s)-1)}: derivatives up to k=ceil(s)-1 bounded, and the k-th derivative (s-k)-Holder with exponent s-k in (0,1] (lem:holder-point-l1-interpolation proof_tex: 'For integer gamma, use the degree gamma-1 Taylor polynomial and the Lipschitz remainder in the integer-order Holder definition'). The two conventions DISAGREE at every integer smoothness order, so HolderBallND is NOT an exact reusable realization for the unrestricted positive alpha,beta,gamma here. Search trace: lean_local_search 'Holder'/'HolderBall' + grep ../doc/API.md,doc/API.md 'HolderBall|HolderClass|holderNorm' -> only HolderBallND (floor convention, wrong at integers) and Mathlib HolderWith/HolderOnWith (single-exponent (0,1]-Holder CONTINUITY, no higher-derivative ball) -> NO standard ceil(s)-1-convention multivariate Holder ball exists in Causalean/CausalSmith/Mathlib. DEFINE-LOCAL `HolderBallStd {d}(f:(Fin d->R)->R)(order M:R)(S:Set (Fin d->R)):Prop` in Basic.lean: iteratedFDeriv up to k:=Nat.ceil(order)-1 bounded by M on S, and the k-th derivative (order-k)-Holder with exponent (order-(k:R)) in (0,1] and constant M (C^{ceil s -1, s-ceil s +1}). HolderBallND's proof-level lemmas do NOT transfer (different convention); prove the small analogues (HolderBallStd_const for zero seminorm, monotone-radius) inline as needed. The remaining derived symbols kappa (inlined in def:nonprivate-cate-rate), R_n^DP (def:dp-minimax-risk), r_n^CATE (def:nonprivate-cate-rate), r_n^regDP (def:private-regression-calibration), and the class P_{alpha,beta,gamma} (def:holder-cate-class) are bound here with authoritative realizers in those def/structure nodes; the free constants x_0,r_0,alpha,beta,gamma,L,e_0,f_0,f_1 are pinned by a threaded RegimeConstants predicate (pattern from DoseResponseMinimax.RegimeConstants). Block is define-local: Holder primitive + derived/constant realizers all new.
**required modules.**

## Assumptions (A)

**A-1 (assumption).** (O_i)_{i=1}^n ~ P^n.

**A-2 (assumption).** Y=Y(A) a.s.

**A-3 (assumption).** (Y(0),Y(1)) independent of A conditional on X.

**A-4 (assumption).** e_0 <= pi_P(x) <= 1-e_0 for all x in [0,1]^d.

**A-5 (assumption).** pi_P in H^alpha([0,1]^d,L).

**A-6 (assumption).** mu_{0,P},mu_{1,P} in H^beta([0,1]^d,L).

**A-7 (assumption).** tau_P in H^gamma([0,1]^d,L).

**A-8 (assumption).** 0<beta<=gamma.

**A-9 (assumption).** f_0 <= p_P(x) <= f_1 for all x in {u in [0,1]^d: ||u-x_0||_infinity<=r_0}.

**A-10 (assumption).** Pr{M_n(D) in B} <= exp(epsilon_n) Pr{M_n(D') in B}+delta_n for all D,D',B.

**A-11 (assumption).** P_{alpha,beta,gamma}(L,e_0,f_0,f_1,r_0,x_0) is nonempty.

## Definitions (P)

**P-1 ({P ).** {P : P satisfies ass:consistency, ass:exchangeability, ass:overlap, ass:pi-holder, ass:mu-holder, ass:tau-holder, ass:smoothness-order, and ass:local-density}

**P-2 (inf_{M_n).** inf_{M_n: M_n satisfies ass:central-dp} sup_{P in P_{alpha,beta,gamma}(L,e_0,f_0,f_1,r_0,x_0)} E_P[|M_n(O_1,...,O_n)-tau_P(x_0)|]

**P-3 (n^(-min{1/(2+d/gamma),1/(1+d/(2 gamma)+d/(2(alpha+beta)))})).** n^(-min{1/(2+d/gamma),1/(1+d/(2 gamma)+d/(2(alpha+beta)))})

**P-4 (inf_{0<h<=r_0}{h^gamma+(n h^d)^(-1/2)+1/(n epsilon_n h^d)}).** inf_{0<h<=r_0}{h^gamma+(n h^d)^(-1/2)+1/(n epsilon_n h^d)}

**P-5 (Let q=alpha+beta and define the formal algebraic objectiv…).** Let q=alpha+beta and define the formal algebraic objective E_n^alg(h,k)=h^gamma+(h/k^{1/d})^q+(n h^d)^(-1/2)+sqrt(k)/(n h^d)+k/(n epsilon_n h^d), over 0<h<=r_0 and 1<=k<=n h^d. Its exactly optimized value is rho_n^alg=r_n^CATE vee (n epsilon_n)^(-gamma/(gamma+d)) vee (n epsilon_n)^(-q/(q+d)); with s=min(gamma,q), this is n^(-kappa) vee (n epsilon_n)^(-s/(s+d)), and epsilon_n^alg=n^(-1+kappa(s+d)/s) is only its algebraic crossing. Neither E_n^alg nor rho_n^alg is a proved risk envelope, attainable rate, minimax frontier, or minimax elbow. The only certified full-class statement is lem:certified-private-cate-bracket, with sharp corollaries lem:equal-smoothness-sharp-private-rate and lem:bounded-effective-private-sample-risk. A private-HOIF upper program must separately privatize or globally stabilize nuisance-pilot, Gram, first-order-score, and second-order folds and retain the KBRW Gram/density third-order remainder. For q<gamma, a positive-density fuzzy family plus an approximate-DP hypercube inequality is one possible converse program, but lem:general-two-point-barrier proves only that a two-point argument certifying indistinguishability through n{exp(epsilon_n)-1+delta_n}TV(P,Q)<=eta<1 cannot exceed the gamma privacy branch; it does not show that every route to the q branch must use fuzzy cancellation. When n epsilon_n=1 the formal q and gamma privacy powers coincide; the q power is strictly larger only when n epsilon_n>1. The KBRW nonprivate expression is not asserted as the established frontier of the full positive-density class: its published lower construction and upper attainability conditions concern different density scopes, with matching on a density/Gram-stable submodel.

**P-6 (For deterministic sequences epsilon_n in [n^(-1),1] and 0…).** For deterministic sequences epsilon_n in [n^(-1),1] and 0<delta_n<=n^(-2), determine the sharp central-(epsilon_n,delta_n)-DP pointwise CATE risk R_n^DP(P_{alpha,beta,gamma},epsilon_n,delta_n,x_0) over P_{alpha,beta,gamma}(L,e_0,f_0,f_1,r_0,x_0). Establish a two-sided rate and phase diagram; determine whether the privacy-free limit over this full positive-density class reduces to r_n^CATE (open here; the Kennedy--Balakrishnan--Robins--Wasserman match uses a density/Gram-stable submodel), and decide whether the pointwise-regression calibration r_n^regDP and private estimation of pi_P, mu_{0,P}, and mu_{1,P} generate one or more additional leading regimes. Prove any lower bound using a causal localized family rather than a regression stand-in.

## Lemmas (L)

**L-1 (For any two one-observation laws P,Q and any central-(eps…).** For any two one-observation laws P,Q and any central-(epsilon_n,delta_n)-DP mechanism M_n, TV(L_{P^n}(M_n),L_{Q^n}(M_n)) <= n TV(P,Q){exp(epsilon_n)-1+delta_n}.

**L-2 (An explicit armwise privatized local-polynomial estimator…).** An explicit armwise privatized local-polynomial estimator satisfies R_n^DP <= C{n^{-beta/(2 beta+d)} vee (n epsilon_n)^{-beta/(beta+d)}} uniformly over the frozen law class.

**L-3 (The frozen regression calibration satisfies r_n^regDP asy…).** The frozen regression calibration satisfies r_n^regDP asymp n^{-gamma/(2 gamma+d)} vee (n epsilon_n)^{-gamma/(gamma+d)}, with constants depending only on the fixed regularity parameters.

**L-4 (Let P,Q lie in the frozen class, g=tau_P-tau_Q, Delta=|g(…).** Let P,Q lie in the frozen class, g=tau_P-tau_Q, Delta=|g(x_0)|, r_*=(1/2)min{r_0,x_{0,1},1-x_{0,1},...,x_{0,d},1-x_{0,d}}, and C_*={x:||x-x_0||_infinity<=r_*}. There is c_H>0 such that integral_{C_*}|g(x)|dx >= c_H Delta^{1+d/gamma}.

**L-5 (For constants 0<c<C and all sufficiently large n, c{n^{-g…).** For constants 0<c<C and all sufficiently large n, c{n^{-gamma/(2 gamma+d)} vee (n epsilon_n)^{-gamma/(gamma+d)}} <= R_n^DP <= C{n^{-beta/(2 beta+d)} vee (n epsilon_n)^{-beta/(beta+d)}}.

**L-6 (If beta=gamma, then over the full frozen class R_n^DP asy…).** If beta=gamma, then over the full frozen class R_n^DP asymp n^{-gamma/(2 gamma+d)} vee (n epsilon_n)^{-gamma/(gamma+d)} asymp r_n^regDP, with r_n^CATE=n^{-gamma/(2 gamma+d)} and proved boundary epsilon_n asymp n^{-gamma/(2 gamma+d)}.

**L-7 (There is c>0 such that, for all sufficiently large n, R_n…).** There is c>0 such that, for all sufficiently large n, R_n^DP >= c{n^{-gamma/(2 gamma+d)} vee (n epsilon_n)^{-gamma/(gamma+d)}}; both branches are witnessed by explicit localized causal two-point families in the frozen Holder class.

**L-8 (When beta=gamma, the sharp full-class central-DP CATE rat…).** When beta=gamma, the sharp full-class central-DP CATE rate in lem:equal-smoothness-sharp-private-rate is inherited, at the level of rates, from one-server private pointwise regression: the upper mechanism is the clipped difference of two armwise private local-polynomial regressions, while the causal lower family fixes mu_0=0 and a constant overlapping propensity and embeds a single pointwise-regression subproblem in mu_1. Overlap and the two-arm structure affect only constants.

## Theorems (T)

### T-block: t1 — Let r_*=(1/2)min{r_0,x_{0,1},1-x_{0,1},...,x_{0,d},1-x_{0…
**Statement.** Let r_*=(1/2)min{r_0,x_{0,1},1-x_{0,1},...,x_{0,d},1-x_{0,d}}. There is c_TV>0 such that for every P,Q in the frozen observational Holder CATE class, with Delta=|tau_P(x_0)-tau_Q(x_0)|, TV(P,Q)>=c_TV Delta^{1+d/gamma}. Hence, for every eta in (0,1), any central-(epsilon_n,delta_n)-DP causal two-point lower-bound argument that certifies output indistinguishability through n{exp(epsilon_n)-1+delta_n}TV(P,Q)<=eta must have Delta<=C_eta(n epsilon_n)^{-gamma/(gamma+d)}. In particular, if q=alpha+beta<gamma and n epsilon_n>1, the ordinary two-point/TV-contraction method cannot establish a lower bound of the larger formal order (n epsilon_n)^{-q/(q+d)}; at n epsilon_n=1 the two powers coincide.
