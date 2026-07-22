# eid_lingam_direction_min_order_v1 — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / papersmith bridge._

## Environment (S)

**S-1 (Observational law on R^2 with centered independent non-Ga…).** Observational law on R^2 with centered independent non-Gaussian latent sources (bivariate LvLiNGAM data world) — bypass-justified: Causalean's PO/SCM worlds (POManskiIVSystem, Backdoor, SCM.Do.*, SWIGGraph) are exchangeability/graph-native potential-outcomes abstractions; this world is a linear-non-Gaussian source-mixing law with joint-cumulant coordinates, a strictly different abstraction. Search trace: local_search 'cumulant' -> []; local_search over Causalean/PO/ID/Exact catalogue (ATE/ATT/DID/DTR/LATE/RDD/Frontdoor/Proximal/MultipleInstrumentIV) shows no non-Gaussian-source / ICA / mixing-law world; not found. SURVEYED-AND-REJECTED (bypass-justified, concrete Causalean candidate): Causalean.Discovery.LiNGAM.Kurtosis.cross_fourth_cumulant_eq_sum -- the nearest existing cumulant-identity decl in Causalean. REJECT / abstraction mismatch: it is a fixed SINGLE-ORDER (fourth-order / two-moment, kurtosis) cross-cumulant summation identity over a determinate LiNGAM mixing, whereas this world requires the OVERCOMPLETE ALL-ORDER LvLiNGAM truncation T_L(P) (every joint cumulant order 2<=r<=L=2m+2 simultaneously, with m+2 > 2 latent-plus-idiosyncratic sources and Zariski-generic loadings). The decl's finite-order two-moment scope cannot express the simultaneous binary-form / apolar higher-order structure the maps Phi^b range over; reusing it would silently truncate the observation vector to r=4. Search trace: local_search 'cross_fourth_cumulant_eq_sum' -> [] (sibling-pkg index miss, not absence); confronted via directive-named Causalean.Discovery.LiNGAM.Kurtosis; bypass-justified. Sources S_j as centered real RVs over a common probability space; P as pushforward on R^2; sampling_model = population identification from P (no estimation).
**required modules.** CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic, Mathlib.MeasureTheory.Measure.Typeclasses, Mathlib.Probability.Independence.Basic

**S-2 (Complexified structural-parameter and cumulant-coordinate…).** Complexified structural-parameter and cumulant-coordinate world: affine C-spaces of loadings and source-cumulant weights, the truncated joint-cumulant coordinate space C^{q_L}, and the simultaneous binary-form (divided-power) polynomial maps between them — bypass-justified: no Causalean world models complexified algebraic parameter spaces C^{m+1} x C^{n(L-1)}, Zariski-open genericity loci, polynomial cumulant maps, or their image varieties. Search trace: local_search 'ZariskiClosure' -> [], 'catalecticant' -> []; leansearch/loogle unavailable in this environment; grep of doc/API.md for cumulant|apolar|catalecticant|Zariski|semialgebraic|quantifier|Vandermonde|Waring|LiNGAM -> no matches; not found. Loadings as Fin-indexed C^2 vectors; weights c_{jr},d_{jr} as C-valued families; Phi maps as MvPolynomial-valued simultaneous binary forms indexed by (r,a).
**required modules.** CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic, Mathlib.Data.Complex.Basic, Mathlib.LinearAlgebra.Vandermonde, Mathlib.RingTheory.MvPolynomial.Basic, Mathlib.Algebra.MonoidAlgebra.Basic

## Assumptions (A)

**A-1 (assumption).** S_0 perp S_1 perp ... perp S_{m+1}

**A-2 (assumption).** for every 0<=j<=m+1, E|S_j|^K<infty

**A-3 (assumption).** for every 0<=j<=m+1, S_j is not Gaussian

**A-4 (assumption).** (X,Y)^T=sum_{j=0}^{m+1}u_j S_j

**A-5 (assumption).** (X,Y)^T=sum_{j=0}^{m+1}v_j S_j

**A-6 (assumption).** |{gamma,rho_i:1<=i<=m}|=m+1

**A-7 (assumption).** |{delta,sigma_i:1<=i<=m}|=m+1

**A-8 (assumption).** gamma!=0

**A-9 (assumption).** delta!=0

## Definitions (P)

**P-1 ({P in Laws(R^2) ).** {P in Laws(R^2) : there exist centered S_0,...,S_{m+1} such that ass:independent-sources, ass:finite-cumulants, ass:source-nongaussianity, ass:forward-axis-model, ass:forward-noncollinearity, and ass:forward-nonzero-edge hold}

**P-2 ({P in Laws(R^2) ).** {P in Laws(R^2) : there exist centered S_0,...,S_{m+1} such that ass:independent-sources, ass:finite-cumulants, ass:source-nongaussianity, ass:reverse-axis-model, ass:reverse-noncollinearity, and ass:reverse-nonzero-edge hold}

**P-3 (T_L(P)=(kappa_{r,a}(P):2<=r<=L,0<=a<=r), where kappa_{r,a…).** T_L(P)=(kappa_{r,a}(P):2<=r<=L,0<=a<=r), where kappa_{r,a}(P)=Cum_P(X repeated r-a times,Y repeated a times) and q_L=L(L+3)/2-2.

**P-4 ([Phi^right_{m,L}(gamma,rho,c)]_{r,a}=sum_{j=0}^{m+1}c_{jr…).** [Phi^right_{m,L}(gamma,rho,c)]_{r,a}=sum_{j=0}^{m+1}c_{jr}(u_{j1})^(r-a)(u_{j2})^a for 2<=r<=L and 0<=a<=r, with u_0=(1,gamma), u_j=(1,rho_j) for 1<=j<=m, and u_{m+1}=(0,1).

**P-5 ([Phi^left_{m,L}(delta,sigma,d)]_{r,a}=sum_{j=0}^{m+1}d_{j…).** [Phi^left_{m,L}(delta,sigma,d)]_{r,a}=sum_{j=0}^{m+1}d_{jr}(v_{j1})^(r-a)(v_{j2})^a for 2<=r<=L and 0<=a<=r, with v_0=(1,0), v_j=(sigma_j,1) for 1<=j<=m, and v_{m+1}=(delta,1).

**P-6 (C^right_{m,L}=ZariskiClosure(Phi^right_{m,L}(Theta^right_…).** C^right_{m,L}=ZariskiClosure(Phi^right_{m,L}(Theta^right_{m,L})) and C^left_{m,L}=ZariskiClosure(Phi^left_{m,L}(Theta^left_{m,L})) in C^{q_L}.

**P-7 (Theta^{right,circ}_{m,L}={(gamma,rho,c) in Theta^right_{m,L}).** Theta^{right,circ}_{m,L}={(gamma,rho,c) in Theta^right_{m,L}: gamma product_{i=1}^m(gamma-rho_i) product_{1<=i<ell<=m}(rho_i-rho_ell) product_{j=0}^{m+1}product_{r=2}^L c_{jr} !=0}; Theta^{left,circ}_{m,L}={(delta,sigma,d) in Theta^left_{m,L}: delta product_{i=1}^m(delta-sigma_i) product_{1<=i<ell<=m}(sigma_i-sigma_ell) product_{j=0}^{m+1}product_{r=2}^L d_{jr} !=0}.

**P-8 (R^right_{m,L}(t)={theta in Theta^right_{m,L}).** R^right_{m,L}(t)={theta in Theta^right_{m,L}: Phi^right_{m,L}(theta)=t} and R^left_{m,L}(t)={eta in Theta^left_{m,L}: Phi^left_{m,L}(eta)=t}.

**P-9 (For pi in G_m, pi.(gamma,(rho_i)_{i=1}^m,(c_{jr})_{j,r})=…).** For pi in G_m, pi.(gamma,(rho_i)_{i=1}^m,(c_{jr})_{j,r})=(gamma,(rho_{pi(i)})_{i=1}^m,(c_{pi(i),r})_{i=1}^m,c_{0r},c_{m+1,r}); the left action replaces rho,c,gamma by sigma,d,delta. Indices 0 and m+1 are fixed.

**P-10 (E_m={t in C^{q_K}).** E_m={t in C^{q_K}: [R^right_{m,K}(t) intersects Theta^{right,circ}_{m,K} is nonempty and R^left_{m,K}(t) is nonempty] or [R^left_{m,K}(t) intersects Theta^{left,circ}_{m,K} is nonempty and R^right_{m,K}(t) is nonempty]}; barE_m=ZariskiClosure(E_m); H^right_m=Theta^{right,circ}_{m,K} intersects (Phi^right_{m,K})^{-1}(E_m) and H^left_m=Theta^{left,circ}_{m,K} intersects (Phi^left_{m,K})^{-1}(E_m).

**P-11 (F^right_{m,L}={(gamma,rho,c) in R^{m+1} x R^{n(L-1)}).** F^right_{m,L}={(gamma,rho,c) in R^{m+1} x R^{n(L-1)}: gamma!=0, rho_1,...,rho_m,gamma are pairwise distinct, and for every 0<=j<=m+1 there exists a centered non-Gaussian real S_j with E|S_j|^L<infty and Cum(S_j repeated r times)=c_{jr} for every 2<=r<=L}; F^left_{m,L} is the analogous set with delta!=0 and (delta,sigma,d).

**P-12 (K^star(m)=min{L>=2).** K^star(m)=min{L>=2: for b in {right,left}, outside a proper real algebraic subset of F^b_{m,L}, the value Phi^b_{m,L}(theta) has no representation in F^{opposite(b)}_{m,L}}; set K^star(m)=infinity if the set is empty.

**P-13 (For b in {right,left} and t in R^{q_K}, let FeasFiber^b_m…).** For b in {right,left} and t in R^{q_K}, let FeasFiber^b_m(t) assert that there exist the b-loading and source-cumulant coordinates lambda and, for each 0<=j<=m+1, atomic witnesses (w_{jh},z_{jh})_{h=1}^{m+2}, such that Phi^b_{m,K}(lambda)=t; the b direct slope is nonzero; its finite loading slopes are pairwise distinct; and, writing k_{jr} for the source cumulants in lambda and mu_{jr}=B_r(0,k_{j2},...,k_{jr}), one has sum_h w_{jh}=1, w_{jh}>=0, sum_h w_{jh}z_{jh}^r=mu_{jr} for 1<=r<=K, and mu_{j2}>0. Decide each formula by real quantifier elimination (equivalently a sign-invariant cylindrical algebraic decomposition) with variables ordered t, lambda, then witnesses. Its truth value is exactly the nonemptiness of R^b_{m,K}(t) intersects F^b_{m,K}. On the apolar rank-open locus, factoring the recovered degree-n support annihilator Q_D from the contractions of the divided-power forms f_{n+k} gives the same arrow decision directly from the vertical-versus-horizontal fixed axis.

**P-14 (Evaluate the two finite formulas FeasFiber^right_m(t) and…).** Evaluate the two finite formulas FeasFiber^right_m(t) and FeasFiber^left_m(t) from def:global-feasible-fiber-decision. Set S_m(t)=X->Y when the former is true and the latter false; set S_m(t)=Y->X when the latter is true and the former false; and leave S_m(t) undefined otherwise. Thus S_m is a globally finite semialgebraic decision procedure on its declared separated domain, with apolar support-annihilator factorization as its direct generic implementation.

**P-15 (M^{sep}_{m,K}={M).** M^{sep}_{m,K}={M: M has a forward representation with theta in F^right_{m,K} and R^left_{m,K}(T_K(P_M)) intersects F^left_{m,K} is empty, or M has a reverse representation with eta in F^left_{m,K} and R^right_{m,K}(T_K(P_M)) intersects F^right_{m,K} is empty}.

**P-16 (For m=1 and K=4, A_1 is the 12-equation incidence system…).** For m=1 and K=4, A_1 is the 12-equation incidence system t_{r,a}=c_{0r}gamma^a+c_{1r}rho^a+c_{2r}1{a=r}=d_{0r}1{a=0}+d_{1r}sigma^(r-a)+d_{2r}delta^(r-a), for r=2,3,4 and 0<=a<=r, with the generic-locus disjunction; its common-axis subfamily is rho=sigma=0, delta gamma=1, d_{0r}=c_{1r}, d_{1r}=c_{2r}, d_{2r}=c_{0r}gamma^r. For m=2 and K=6, A_2 is the 25-equation system t_{r,a}=c_{0r}gamma^a+c_{1r}rho_1^a+c_{2r}rho_2^a+c_{3r}1{a=r}=d_{0r}1{a=0}+d_{1r}sigma_1^(r-a)+d_{2r}sigma_2^(r-a)+d_{3r}delta^(r-a), for r=2,...,6 and 0<=a<=r, with the generic-locus disjunction; its common-axis subfamily is rho_1=sigma_1=0, delta gamma=1, sigma_2 rho_2=1, d_{0r}=c_{1r}, d_{1r}=c_{3r}, d_{2r}=c_{2r}rho_2^r, d_{3r}=c_{0r}gamma^r.

**P-17 (Compare the simultaneous binary-form decompositions Phi^r…).** Compare the simultaneous binary-form decompositions Phi^right_{m,K}(theta)=Phi^left_{m,K}(eta) after quotienting each same-arrow fiber by G_m, using the axis directions fixed in the two maps and the Jacobian ranks of the resulting quotient-fiber equations.

**P-18 (Solve the two axis-conditioned Waring systems through K_-…).** Solve the two axis-conditioned Waring systems through K_-=2m+1 over distinct real loading directions, then realize the resulting finite source-cumulant lists by compactly supported non-Gaussian laws through a truncated-moment-matrix perturbation.

**P-19 (Put d=m+1, K=2d, and n=d+1).** Put d=m+1, K=2d, and n=d+1. Convert each source cumulant list k=(k_2,...,k_K) to raw moments mu_r=B_r(0,k_2,...,k_r), and impose the finite atomic certificate Q_K(k): there exist w_h>=0,z_h in R (1<=h<=n) with sum_h w_h=1, sum_h w_h z_h^r=mu_r for 1<=r<=K, and mu_2>0. Compute defining equations J_m for barE_m by saturating the simultaneous equations Phi^right(theta)=t=Phi^left(eta) separately by the right and left genericity products, eliminating the parameter variables, and intersecting the two resulting t-ideals. Form Gamma_b={(t,lambda):J_m(t)=0, Phi^b(lambda)=t, the b-loading inequalities hold, and Q_K holds for every source list}. Run a simultaneous sign-invariant cylindrical algebraic decomposition, using coefficients, discriminants, and principal subresultants, with t ordered before lambda and atomic witnesses. The induced t-cells stratify barE_m(R); label each cell by whether its right and left Gamma_b stacks are nonempty, and output every selected section/sector stack as the local description of R^b_{m,K}(t) intersect F^b_{m,K}.

**P-20 (For every m>=1, does there exist a Zariski-open dense sub…).** For every m>=1, does there exist a Zariski-open dense subset of each Theta^{right,circ}_{m,K} and Theta^{left,circ}_{m,K} whose images have no full opposite-arrow fiber, while each same-arrow fiber is a single G_m-orbit, and do these subsets meet F^right_{m,K} and F^left_{m,K} in nonempty relatively Euclidean-open sets? A positive answer gives generic real direction recovery from T_K modulo admissible source swaps.

**P-21 (For every m>=1, is barE_m of codimension m in each C^righ…).** For every m>=1, is barE_m of codimension m in each C^right_{m,K} and C^left_{m,K}, and are H^right_m and H^left_m exactly the respective generic parameter points that retain a full opposite-arrow representation? Can the resulting full-fiber equations be made explicit for m=1 at K=4 and m=2 at K=6?

**P-22 (Is K^star(m)=2m+2 for every m>=1? This requires both a po…).** Is K^star(m)=2m+2 for every m>=1? This requires both a positive resolution of oeq:generic-separation at K=2m+2 and a Euclidean-open family of real forward and reverse laws in the stated classes with equal T_{K_-} at K_-=2m+1.

**P-23 (Can one derive a finite semialgebraic stratification of b…).** Can one derive a finite semialgebraic stratification of barE_m(R) that determines exactly which full-fiber compatibility points have independent real non-Gaussian finite-K source representations on both arrows and gives explicit local descriptions of the two feasible fiber correspondences?

## Lemmas (L)

**L-1 (For each pi in G_m, Phi^right_{m,L}(pi.theta)=Phi^right_{…).** For each pi in G_m, Phi^right_{m,L}(pi.theta)=Phi^right_{m,L}(theta) and Phi^left_{m,L}(pi.eta)=Phi^left_{m,L}(eta). If a forward structural model M has real-feasible parameter theta, relabelling its latent sources by pi gives a forward structural model with the same observational law P_M and D(M)=X->Y; the analogous reverse statement has D(M)=Y->X. Hence quotienting a same-arrow fiber by G_m identifies only source labels and never identifies opposite arrows.

## Theorems (T)

### T-block: t1 — Put n=m+2 and K=2n-2
**Statement.** Put n=m+2 and K=2n-2. There are Zariski-open dense sets U^right_m subset Theta^{right,circ}_{m,K} and U^left_m subset Theta^{left,circ}_{m,K}, each meeting its real feasible region in a nonempty relatively Euclidean-open set, such that R^left_{m,K}(Phi^right_{m,K}(theta)) is empty for every theta in U^right_m and R^right_{m,K}(Phi^left_{m,K}(eta)) is empty for every eta in U^left_m. More explicitly, from t=T_K(P) in either set one forms the divided-power blocks f_r(x,y)=sum_{a=0}^r binom(r,a)t_{r,a}x^(r-a)y^a; the common kernel of q |-> (q(partial)f_{n+k})_{0<=k<=n-2} is the line generated by the squarefree degree-n support annihilator Q_D=product_{ell in D}ell^perp. Factoring Q_D recovers the unordered loading-direction set D, and its vertical-versus-horizontal fixed axis decides the arrow against every full opposite-arrow fiber.
