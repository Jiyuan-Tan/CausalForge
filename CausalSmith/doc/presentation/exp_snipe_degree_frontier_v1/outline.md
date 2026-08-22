# Title
**Minimax mean squared error for low-order network interference under Bernoulli assignment**

**Contribution statement.** The paper characterizes design-based minimax mean squared error for total treatment effect estimation under known bounded-degree low-order polynomial network interference, constructs clipped SNIPE estimators attaining the rate over coefficient-mass and uniformly bounded-outcome classes, and solves the complete-block benchmark for local linear design-unbiased estimators.

# Notation
notation_gaps: \(\Delta_r(p)\)=order-\(r\) Bernoulli contrast coefficient used in the score and energy definitions but not introduced by a frozen definition, \(\tau_n\)=finite-population all-treated-versus-all-control total treatment effect used in the risk definitions and theorem statements but not introduced by a frozen definition, \(\mathcal P_d\)=low-order block polynomial subspace used in the perturbation program and representer lemma but not introduced by a frozen definition, \(L_d\)=all-one-versus-all-zero block contrast functional used in the perturbation program and representer lemma but not introduced by a frozen definition, \(L^2(P_Z)\)=finite design \(L^2\) space used in the weight and local-linear estimator classes but not introduced by a frozen definition, \(P_Z\)=Bernoulli assignment law used in \(L^2(P_Z)\) but not introduced by a frozen definition, \(\mathbf1_d\)=all-one block assignment used in the representer lemma but not introduced by a frozen definition, \(\mathbf0_d\)=all-zero block assignment used in the representer lemma but not introduced by a frozen definition, \(\mu_{n,d}\)=block dominating measure introduced inside an auxiliary lemma rather than an anchored definition, \(\pi_\sigma\)=sign-\(\sigma\) block prior density introduced inside an auxiliary lemma rather than an anchored definition, \(\pi_{+1}\)=positive-sign block prior density introduced inside an auxiliary lemma rather than an anchored definition, \(\pi_{-1}\)=negative-sign block prior density introduced inside an auxiliary lemma rather than an anchored definition, \(H^2(\pi_{+1},\pi_{-1})\)=unhalved squared Hellinger distance between the block prior densities introduced inside an auxiliary lemma rather than an anchored definition

\(Z_j\) | \(Z_j\) | Bernoulli treatment assignment for unit \(j\) | ass:bernoulli-design
\(p\) | \(p\in(0,1)\) | common Bernoulli treatment probability | ass:bernoulli-design
\(V_n\) | \(V_n\) | finite population of units | ass:bernoulli-design
\(d\) | \(d\) | common in-degree and out-degree bound with self-loops counted | ass:bounded-degree
\(N_i\) | \(N_i\) | directed interference neighborhood of unit \(i\) | ass:bounded-degree
\(\beta\) | \(\beta\) | maximum polynomial interaction order | ass:low-order
\(c_{i,S}\) | \(c_{i,S}\) | coefficient on assignment monomial \(S\) for unit \(i\) | ass:low-order
\(B\) | \(B\) | coefficient-mass or outcome-bound radius according to the model class | ass:bounded-coefficient-mass
\(\bar\beta_d\) | \(\bar\beta_d:=\min\{\beta,d\}\) | available interaction order at degree \(d\) | def:exposed-order
\(\bar\beta_0\) | \(\bar\beta_0=0\) | zero-degree available-order convention | def:exposed-order
\(k_\star(d,\beta,p)\) | \(k_\star(d,\beta,p)\) | largest nonzero contrast order up to \(\bar\beta_d\) | def:exposed-order
\(\binom{0}{0}\) | \(\binom{0}{0}:=1\) | empty binomial convention | def:zero-degree-conventions
\(g_0\) | \(g_0:=0\) | zero-degree score convention | def:zero-degree-conventions
\(A_0\) | \(A_0:=0\) | zero-degree energy convention | def:zero-degree-conventions
\(h_0\) | \(h_0:=0\) | zero-degree representer convention | def:zero-degree-conventions
\(\mathcal G_{n,d}\) | \(\mathcal G_{n,d}\) | graphs on \(V_n\) satisfying the bounded-degree condition | def:graph-class
\(\mathcal C_{n,d,\beta}(B)\) | \(\mathcal C_{n,d,\beta}(B)\) | low-order coefficient schedules with unitwise \(\ell_1\) mass bounded by \(B\) | def:coefficient-class
\(Y_i(z)\) | \(Y_i(z)\) | potential outcome of unit \(i\) at assignment \(z\) | def:potential-outcome
\(Y_i^{\mathrm{obs}}\) | \(Y_i^{\mathrm{obs}}:=Y_i(Z)\) | observed outcome under the realized assignment | def:potential-outcome
\(\mathcal M_{n,d,\beta}(B)\) | \(\mathcal M_{n,d,\beta}(B)\) | graph and coefficient pairs from \(\mathcal G_{n,d}\) and \(\mathcal C_{n,d,\beta}(B)\) | def:model-class
\(g_{i,\beta,p}(z)\) | \(g_{i,\beta,p}(z)\) | unit-level SNIPE score built from centered neighborhood monomials | def:snipe-score
\(\widehat\tau_n^{\mathrm{SNIPE}}\) | \(\widehat\tau_n^{\mathrm{SNIPE}}\) | unprojected SNIPE estimator | def:snipe-estimator
\(\widehat\tau_n^{\mathrm{up}}\) | \(\widehat\tau_n^{\mathrm{up}}\) | SNIPE estimator projected to \([-B,B]\) | def:snipe-estimator
\(\Pi_{[-B,B]}\) | \(\Pi_{[-B,B]}\) | Euclidean projection onto \([-B,B]\) | def:snipe-estimator
\(R_n^\star(d,\beta,p,B)\) | \(R_n^\star(d,\beta,p,B)\) | minimax design mean squared error over \(\mathcal M_{n,d,\beta}(B)\) | def:minimax-risk
\(\widehat\tau_n\) | \(\widehat\tau_n\) | generic design-based estimator measurable in graph, assignment, and observed outcomes | def:snipe-estimator
\(g_d(z)\) | \(g_d(z)\) | complete-block SNIPE score on \(d\) Bernoulli coordinates | def:block-score-energy
\(A_d\) | \(A_d\) | complete-block score energy | def:block-score-energy
\(h_d\) | \(h_d:=g_d/A_d\) | normalized complete-block representer for \(d\ge1\) | def:block-score-energy
\(h_{d,T}\) | \(h_{d,T}\) | raw-monomial coefficient of \(h_d\) | def:block-score-energy
\(m\) | \(m:=\lfloor n/d\rfloor\) | number of complete \(d\)-blocks in the least-favourable construction | def:block-family
\(q\) | \(q:=md\) | number of active block units | def:block-family
\(\rho\) | \(\rho:=q/n\) | active population fraction | def:block-family
\(V_b\) | \(V_b\) | complete directed block of size \(d\) | def:block-family
\(s\) | \(s:=B/2\) | scale for the cosine-squared baseline density | def:block-family
\(f_s(u)\) | \(f_s(u)\) | compactly supported cosine-squared density | def:block-family
\(U_1,\ldots,U_m\) | \(U_1,\ldots,U_m\) | independent baseline block coefficients drawn from \(f_s\) | def:block-family
\(H_{\beta,p}\) | \(H_{\beta,p}\) | supremum of raw-monomial \(\ell_1\) norms of block representers | def:block-family
\(\delta\) | \(\delta\) | least-favourable perturbation amplitude | def:block-family
\(\Pi_\sigma\) | \(\Pi_\sigma\) | prior over block coefficient schedules with sign \(\sigma\) | def:block-family
\(\mathsf{PerturbProg}_{d,\beta,p}\) | \(\mathsf{PerturbProg}_{d,\beta,p}\) | minimum-energy polynomial perturbation with unit contrast | def:perturbation-program
\(\mathsf{WeightProg}_{d,\beta,p}\) | \(\mathsf{WeightProg}_{d,\beta,p}\) | minimum-energy unbiased block weight program | def:weight-program
\(\mathcal M_t(G_t)\) | \(\mathcal M_t(G_t)\) | coefficient class on a fixed complete-block graph | def:local-linear-class
\(G_t\) | \(G_t\) | fixed complete-block graph at index \(t\) | def:local-linear-class
\(d_t\) | \(d_t\) | block size in the fixed complete-block sequence | def:local-linear-class
\(n_t\) | \(n_t\) | population size in the fixed complete-block sequence | def:local-linear-class
\(N_i^{G_t}\) | \(N_i^{G_t}\) | interference neighborhood of unit \(i\) in \(G_t\) | def:local-linear-class
\(\mathcal E_t^{\mathrm{loc,lin}}\) | \(\mathcal E_t^{\mathrm{loc,lin}}\) | local linear estimators satisfying blockwise unbiasedness equations | def:local-linear-estimator-class
\(\widehat\tau_{w,t}\) | \(\widehat\tau_{w,t}\) | local linear estimator with weights \(w_{i,t}\) | def:local-linear-estimator-class
\(w_{i,t}\) | \(w_{i,t}\) | block-local weight for unit \(i\) at index \(t\) | def:local-linear-estimator-class
\(Z_{b(i)}\) | \(Z_{b(i)}\) | assignment vector restricted to the block containing unit \(i\) | def:local-linear-estimator-class
\(b(i)\) | \(b(i)\) | index of the complete block containing unit \(i\) | def:local-linear-estimator-class
\(R_t^{\mathrm{loc,lin}}\) | \(R_t^{\mathrm{loc,lin}}\) | minimax risk over local linear estimators on fixed \(G_t\) | def:local-linear-risk
\(\mathcal C_{n,d,\beta}^{\infty}(B)\) | \(\mathcal C_{n,d,\beta}^{\infty}(B)\) | low-order schedules with uniformly bounded potential outcomes | def:bounded-outcome-coefficient-class
\(\mathcal M_{n,d,\beta}^{\infty}(B)\) | \(\mathcal M_{n,d,\beta}^{\infty}(B)\) | graph and coefficient pairs with uniformly bounded potential outcomes | def:bounded-outcome-model-class
\(R_{n,\ell_1}^{\star}(d,\beta,p,B)\) | \(R_{n,\ell_1}^{\star}(d,\beta,p,B)\) | minimax risk for the coefficient-mass class | def:two-class-minimax-risks
\(R_{n,\infty}^{\star}(d,\beta,p,B)\) | \(R_{n,\infty}^{\star}(d,\beta,p,B)\) | minimax risk for the uniformly bounded-outcome class | def:two-class-minimax-risks
\(\widehat\tau_{n,\infty}^{\mathrm{up}}\) | \(\widehat\tau_{n,\infty}^{\mathrm{up}}\) | SNIPE estimator projected to \([-2B,2B]\) | def:bounded-outcome-clipped-snipe
\(\Pi_{[-2B,2B]}\) | \(\Pi_{[-2B,2B]}\) | Euclidean projection onto \([-2B,2B]\) | def:bounded-outcome-clipped-snipe
\(Z_S\) | \(Z_S:=\prod_{j\in S}Z_j\) | block monomial assignment product | thm:sharp-local-linear-constant-and-representers
\(Z_b\) | \(Z_b:=(Z_j)_{j\in V_b}\) | assignment vector in block \(V_b\) | thm:sharp-local-linear-constant-and-representers
\(\Psi_{b,t}(w)\) | \(\Psi_{b,t}(w)\) | blockwise worst-case quadratic criterion for local linear weights | thm:sharp-local-linear-constant-and-representers
\(m_t\) | \(m_t:=n_t/d_t\) | number of complete blocks at index \(t\) | thm:sharp-local-linear-constant-and-representers
\(c_{\beta,p}\) | \(c_{\beta,p}\) | lower-bound constant depending only on \((\beta,p)\) | thm:degree-frontier
\(C_{\beta,p}\) | \(C_{\beta,p}\) | upper-bound constant depending only on \((\beta,p)\) | thm:degree-frontier
\(G_n\) | \(G_n\) | directed interference graph on \(V_n\) | ass:bounded-degree
\(\Delta_r(p)\) | \(\Delta_r(p)\) | order-\(r\) all-one-versus-all-zero Bernoulli contrast | def:exposed-order
\(\bar\beta_d\) | \(\bar\beta_d\) | exposed interaction order at degree \(d\) | def:exposed-order
\(k_\star\) | \(k_\star\) | largest exposed order with nonzero contrast | def:exposed-order
\(P_Z\) | \(P_Z\) | product-Bernoulli assignment law | ass:bernoulli-design
\(\mathbb E_Z\) | \(\mathbb E_Z\) | expectation under \(P_Z\) | ass:bernoulli-design
\(Y_i^{\mathrm{obs}}\) | \(Y_i^{\mathrm{obs}}\) | observed outcome at the realized assignment | def:potential-outcome
\(\tau_n\) | \(\tau_n\) | all-treated-versus-all-control total treatment effect | def:minimax-risk
\(g_{i,\beta,p}\) | \(g_{i,\beta,p}\) | unit-level SNIPE score | def:snipe-score
\(g_d\) | \(g_d\) | complete-block score on \(d\) coordinates | def:block-score-energy
\(h_d\) | \(h_d\) | normalized complete-block representer | def:block-score-energy
\(\mathcal P_d\) | \(\mathcal P_d\) | low-order block polynomial subspace | def:perturbation-program
\(L_d\) | \(L_d\) | all-one-versus-all-zero block contrast functional | def:perturbation-program
\(f_s\) | \(f_s\) | cosine-squared block baseline density at scale \(s\) | def:block-family
\(\rho\) | \(\rho\) | active population fraction | def:block-family
\(U_b\) | \(U_b\) | baseline coefficient draw of block \(b\) | def:block-family
\(\sigma\) | \(\sigma\) | sign index of the least-favourable pair | def:block-family
\(V_{n_t}\) | \(V_{n_t}\) | population at index \(t\) of the complete-block sequence | def:local-linear-class
\(\Psi_{b,t}\) | \(\Psi_{b,t}\) | blockwise worst-case quadratic criterion | thm:sharp-local-linear-constant-and-representers

# Sections

## section: Abstract
The abstract will be drafted after the full paper prose is in place. It will state the finite-population Bernoulli design setting, the known bounded-degree low-order polynomial interference model, the minimax mean squared error scale \(B^2\min\{1,dA_d/n\}\), the equivalent exposed-order scale \(B^2\min\{1,d\binom d{k_\star}/n\}\), the attaining clipped SNIPE estimators, the comparison between the coefficient-mass and uniformly bounded-outcome classes, the exact complete-block local linear benchmark, and the fair-coin specialization in one compact paragraph.
objs:
bib:

## section: Introduction
The introduction will motivate total treatment effect estimation under known network interference and independent Bernoulli assignment, identify degree dependence as the central finite-population design quantity, and preview the paper's characterization of minimax mean squared error through the complete-block energy \(A_d\) and the single out-degree overlap charge. It will introduce SNIPE as the attaining estimator family, state how clipped versions cover the saturated branch and the two bounded model classes, and close with a single factual sentence directing readers to the appendix verification note for the Lean machine-checking scope.
objs:
bib:

## section: Related work
This section will position the paper in design-based causal inference, interference, network experiments, sparse or local interference, and low-order SNIPE estimation. It will compare most directly with \citep{CortezRodriguezEichhornYu2023} by explaining that the present results give bounded-class minimax degree dependence \(dA_d/n\asymp_{\beta,p}d\binom d{k_\star}/n\), an attaining clipped estimator under the finite-population Bernoulli model, and an exact complete-block local linear benchmark; it will also relate the block representer geometry to Riesz and pseudoinverse perspectives and calibrate the results against recent work on unknown interference, covariate adjustment, and clustered designs.
objs:
bib: HorvitzThompson1952, Rubin1978, ImbensRubin2015, Manski1993, Sobel2006, Rosenbaum2007, HudgensHalloran2008, Graham2008, Bramoulle2009, TchetgenTchetgenVanderWeele2012, Manski2013, Bowers2013, Ugander2013, vanDerLaan2014, Liu2016, Aronow2017, Eckles2017, Ogburn2017, Swaminathan2017, Athey2018, Baird2018, Basse2018a, Basse2018b, Lin2013, Jagadeesan2020, Savje2021, Leung2022, Hu2022, VazquezBare2023, Gao2025, SussmanAiroldi2017, CortezRodriguezEichhornYu2023, HarshawSavjeWang2025, YuAiroldiBorgsChayes2022, EichhornKhanUganderYu2026, WangLi2026

## section: Setup and assumptions
This section will introduce the finite population, independent Bernoulli assignment, directed interference neighborhoods with self-loops, low-order polynomial potential outcomes, the coefficient-mass and uniformly bounded-outcome model classes, the exposed order, zero-degree conventions, SNIPE scores and clipped estimators, the minimax risk definitions, and complete-block score energy used to state the main results.
objs: ass:bernoulli-design, ass:bounded-degree, ass:low-order, ass:bounded-coefficient-mass, def:exposed-order, def:zero-degree-conventions, def:graph-class, def:coefficient-class, def:potential-outcome, def:model-class, def:snipe-score, def:snipe-estimator, def:minimax-risk, def:block-score-energy, def:bounded-outcome-coefficient-class, def:bounded-outcome-model-class, def:two-class-minimax-risks, def:bounded-outcome-clipped-snipe, def:block-family
bib: HorvitzThompson1952, Rubin1978, Aronow2017, CortezRodriguezEichhornYu2023

## section: Main results
This section will state the coefficient-mass minimax theorem, the uniformly bounded-outcome comparison with the sharp complete-block variance calculation, the exact local linear complete-block benchmark and representer characterization, and the fair-coin specialization. The prose will emphasize what each theorem characterizes under its conditions: the minimax rate, the attaining projected estimator, the equality of the \(dA_d\) and \(d\binom d{k_\star}\) scales up to constants depending on \(\beta,p\), the exact block-local risk criterion, and the \(p=1/2,\beta=1\) rate \(B^2\min\{1,d^2/n\}\).
objs: thm:degree-frontier, def:local-linear-class, def:local-linear-estimator-class, def:local-linear-risk, thm:bounded-outcome-degree-frontier, thm:sharp-local-linear-constant-and-representers, thm:fair-coin-energy-frontier
bib: CortezRodriguezEichhornYu2023, HarshawSavjeWang2025, Swaminathan2017, YuAiroldiBorgsChayes2022, EichhornKhanUganderYu2026, WangLi2026

## section: Discussion and extensions
This section will interpret the rate through the local Bernoulli representer energy \(A_d\), the exposed interaction order \(k_\star\), and the additional out-degree overlap charge. It will discuss how complete directed blocks calibrate the global SNIPE variance constant and how the uniformly bounded-outcome class shares the same degree dependence as the coefficient-mass class. A clearly labelled limitations and future-work paragraph may state open directions on exact all-measurable leading constants, heterogeneous propensities, variance estimation, studentization, limit laws, unknown graphs, clustered assignment, and covariate adjustment while preserving the theorem conditions stated in the main results.
objs:
bib: Leung2022, Savje2021, Hu2022, Gao2025, WangLi2026, EichhornKhanUganderYu2026

## section: Appendix: Proofs and auxiliary lemmas
The appendix will introduce the proof-only least-favourable block family, perturbation program, and weight program before their use in the lower-bound and complete-block arguments. It will then prove the block-energy representer lemma, the overlap-count lemma, and the block-prior density and Hellinger lemmas, followed by the theorem proofs: finite-design orthogonality and SNIPE unbiasedness, variance and overlap counting for the upper bound, the least-favourable block lower bound via total variation and affinity, the local linear complete-block program, the bounded-outcome comparison, and the fair-coin calculation.
objs: def:perturbation-program, def:weight-program, lem:block-energy-representer, lem:overlap-count, lem:block-prior-dominating-measure, lem:block-prior-hellinger-bound
bib: HorvitzThompson1952, Aronow2017, CortezRodriguezEichhornYu2023, HarshawSavjeWang2025

## section: Appendix: Verification note
This brief note will consolidate the Lean verification scope: the finite Bernoulli design algebra, polynomial-interference constructions, SNIPE unbiasedness and variance calculations, minimax-risk definitions, least-favourable block family, continuous-prior integrated-risk step, affinity-based total variation bound, block Riesz programs, and the displayed theorem statements are machine checked. It will also state that bibliographic positioning and econometric interpretation enter the manuscript as cited scholarly context.
objs:
bib: HorvitzThompson1952, Rubin1978, ImbensRubin2015, Aronow2017, CortezRodriguezEichhornYu2023, HarshawSavjeWang2025