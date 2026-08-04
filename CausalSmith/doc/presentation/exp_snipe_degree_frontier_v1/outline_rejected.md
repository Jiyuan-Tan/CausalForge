# Title
**Minimax Mean Squared Error for Low-Order Network Interference under Bernoulli Assignment**

**Contribution statement.** The paper characterizes the design-based minimax mean squared error for total treatment effect estimation under known bounded-degree network interference with low-order polynomial potential outcomes, constructs the clipped SNIPE estimator attaining the rate, and identifies the exact complete-block benchmark for local linear estimators.

# Notation

notation_gaps: \(V_n\)=finite population and unit index set are used throughout but have no anchored definition, \(N_i\)=interference neighborhood is used throughout but has no anchored definition, \(Y_i(z)\)=potential outcome schedule is used in model-class definitions but has no anchored definition, \(Y_i^{\mathrm{obs}}\)=observed outcome is used in the SNIPE estimator but has no anchored definition, \(\tau_n\)=total treatment effect target is used in risk definitions and theorems but has no anchored definition, \(\Delta_r(p)\)=contrast coefficient used in scores and energies but has no anchored definition, \(P_Z\)=Bernoulli assignment law used in block programs but has no anchored definition, \(\mathcal P_d\)=low-order block polynomial subspace used in the perturbation program but has no anchored definition, \(L_d\)=all-one-versus-all-zero block contrast functional used in \(\cref{def:perturbation-program}\) and \(\cref{lem:block-energy-representer}\) but has no anchored definition, \(L^2(P_Z)\)=finite design \(L^2\) space used in weight programs but has no anchored definition, \(Z_{b(i)}\)=assignment vector in the block containing unit \(i\) but has no anchored definition, \(b(i)\)=block membership map but has no anchored definition, \(G_t\)=fixed complete-block graph sequence is introduced inside \(\cref{thm:sharp-local-linear-constant-and-representers}\) rather than an anchored definition

\(Z_j\) | \(Z_j\) | Bernoulli treatment assignment for unit \(j\) | ass:bernoulli-design
\(p\) | \(p\in(0,1)\) | common treatment probability | ass:bernoulli-design
\(d\) | \(d\) | in-degree and out-degree bound, with self-loops counted | ass:bounded-degree
\(\beta\) | \(\beta\) | maximum polynomial interaction order | ass:low-order
\(c_{i,S}\) | \(c_{i,S}\) | coefficient on assignment monomial \(S\) for unit \(i\) | ass:low-order
\(B\) | \(B\) | coefficient-mass or outcome-bound radius, depending on class | ass:bounded-coefficient-mass
\(\bar\beta_d\) | \(\bar\beta_d:=\min\{\beta,d\}\) | exposed interaction order at degree \(d\) | def:exposed-order
\(k_\star(d,\beta,p)\) | \(k_\star(d,\beta,p)\) | largest nonzero contrast order up to \(\bar\beta_d\), with zero-degree convention | def:exposed-order
\(\binom{0}{0}\) | \(\binom{0}{0}:=1\) | empty binomial convention | def:zero-degree-conventions
\(g_0\) | \(g_0:=0\) | zero-degree score convention | def:zero-degree-conventions
\(A_0\) | \(A_0:=0\) | zero-degree energy convention | def:zero-degree-conventions
\(h_0\) | \(h_0:=0\) | zero-degree representer convention | def:zero-degree-conventions
\(\mathcal G_{n,d}\) | \(\mathcal G_{n,d}\) | graphs on \(V_n\) satisfying bounded in- and out-degree | def:graph-class
\(\mathcal C_{n,d,\beta}(B)\) | \(\mathcal C_{n,d,\beta}(B)\) | low-order coefficient schedules with unitwise \(\ell_1\) mass bounded by \(B\) | def:coefficient-class
\(\mathcal M_{n,d,\beta}(B)\) | \(\mathcal M_{n,d,\beta}(B)\) | graph and coefficient pairs from \(\mathcal G_{n,d}\) and \(\mathcal C_{n,d,\beta}(B)\) | def:model-class
\(g_{i,\beta,p}(z)\) | \(g_{i,\beta,p}(z)\) | unit-level SNIPE score built from centered neighborhood monomials | def:snipe-score
\(\widehat\tau_n^{\mathrm{SNIPE}}\) | \(\widehat\tau_n^{\mathrm{SNIPE}}\) | unprojected SNIPE estimator | def:snipe-estimator
\(\widehat\tau_n^{\mathrm{up}}\) | \(\widehat\tau_n^{\mathrm{up}}\) | SNIPE estimator projected to \([-B,B]\) | def:snipe-estimator
\(\Pi_{[-B,B]}\) | \(\Pi_{[-B,B]}\) | Euclidean projection onto \([-B,B]\) | def:snipe-estimator
\(R_n^\star(d,\beta,p,B)\) | \(R_n^\star(d,\beta,p,B)\) | minimax design mean squared error over \(\mathcal M_{n,d,\beta}(B)\) | def:minimax-risk
\(g_d(z)\) | \(g_d(z)\) | complete-block score on \(d\) Bernoulli coordinates | def:block-score-energy
\(A_d\) | \(A_d\) | complete-block score energy | def:block-score-energy
\(h_d\) | \(h_d:=g_d/A_d\) | normalized block representer for \(d\ge1\) | def:block-score-energy
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
\(d_t\) | \(d_t\) | block size in the fixed complete-block sequence | def:local-linear-class
\(\mathcal E_t^{\mathrm{loc,lin}}\) | \(\mathcal E_t^{\mathrm{loc,lin}}\) | local linear estimators satisfying blockwise unbiasedness equations | def:local-linear-estimator-class
\(\widehat\tau_{w,t}\) | \(\widehat\tau_{w,t}\) | local linear estimator with weights \(w_{i,t}\) | def:local-linear-estimator-class
\(w_{i,t}\) | \(w_{i,t}\) | block-local weight for unit \(i\) at index \(t\) | def:local-linear-estimator-class
\(R_t^{\mathrm{loc,lin}}\) | \(R_t^{\mathrm{loc,lin}}\) | minimax risk over local linear estimators on fixed \(G_t\) | def:local-linear-risk
\(\mathcal C_{n,d,\beta}^{\infty}(B)\) | \(\mathcal C_{n,d,\beta}^{\infty}(B)\) | low-order schedules with uniformly bounded potential outcomes | def:bounded-outcome-coefficient-class
\(\mathcal M_{n,d,\beta}^{\infty}(B)\) | \(\mathcal M_{n,d,\beta}^{\infty}(B)\) | graph and coefficient pairs with uniformly bounded outcomes | def:bounded-outcome-model-class
\(R_{n,\ell_1}^{\star}(d,\beta,p,B)\) | \(R_{n,\ell_1}^{\star}(d,\beta,p,B)\) | minimax risk for the coefficient-mass class | def:two-class-minimax-risks
\(R_{n,\infty}^{\star}(d,\beta,p,B)\) | \(R_{n,\infty}^{\star}(d,\beta,p,B)\) | minimax risk for the uniformly bounded-outcome class | def:two-class-minimax-risks
\(\widehat\tau_{n,\infty}^{\mathrm{up}}\) | \(\widehat\tau_{n,\infty}^{\mathrm{up}}\) | SNIPE estimator projected to \([-2B,2B]\) | def:bounded-outcome-clipped-snipe
\(\Pi_{[-2B,2B]}\) | \(\Pi_{[-2B,2B]}\) | Euclidean projection onto \([-2B,2B]\) | def:bounded-outcome-clipped-snipe
\(\Psi_{b,t}(w)\) | \(\Psi_{b,t}(w)\) | blockwise worst-case quadratic criterion for local linear weights | thm:sharp-local-linear-constant-and-representers
\(Z_S\) | \(Z_S:=\prod_{j\in S}Z_j\) | block monomial assignment product | thm:sharp-local-linear-constant-and-representers
\(Z_b\) | \(Z_b:=(Z_j)_{j\in V_b}\) | assignment vector in block \(V_b\) | thm:sharp-local-linear-constant-and-representers
\(m_t\) | \(m_t:=n_t/d_t\) | number of complete blocks at index \(t\) | thm:sharp-local-linear-constant-and-representers
\(n_t\) | \(n_t\) | population size at index \(t\) in the complete-block sequence | thm:sharp-local-linear-constant-and-representers

# Sections

## section: Abstract
The abstract will be drafted after the full paper prose is in place. It will state the Bernoulli design setting, the low-order polynomial interference model, the matched minimax mean squared error rate, the attaining clipped SNIPE estimator, the uniformly bounded-outcome extension, the complete-block local linear benchmark, and the fair-coin specialization in one compact paragraph.
objs:
bib:

## section: Introduction
The introduction will motivate total treatment effect estimation under known network interference and independent Bernoulli assignment, explain why degree dependence is the central design-based quantity, and preview the matched rate \(B^2\min\{1,dA_d/n\}\) together with the SNIPE construction and the local linear benchmark. It will place the paper in the randomized-experiment, interference, exposure-mapping, network-experiment, and low-order SNIPE literatures; a single factual sentence will point readers to the appendix verification note for the machine-checked scope.
objs:
bib: Fisher1935, Cox1958, HorvitzThompson1952, Rubin1978, ImbensRubin2015, Manski1993, Sobel2006, Rosenbaum2007, HudgensHalloran2008, Graham2008, Bramoulle2009, TchetgenTchetgenVanderWeele2012, Manski2013, Bowers2013, Ugander2013, vanDerLaan2014, Liu2016, Aronow2017, Eckles2017, Ogburn2017, Athey2018, Baird2018, Basse2018a, Basse2018b, Lin2013, Jagadeesan2020, Savje2021, Leung2022, Hu2022, VazquezBare2023, Gao2025, CortezRodriguezEichhornYu2023, HarshawSavjeWang2025, YuAiroldiBorgsChayes2022, EichhornKhanUganderYu2026, WangLi2026

## section: Setup and Assumptions
This section introduces the finite-population Bernoulli design, the bounded directed interference graph with self-loops, the low-order polynomial coefficient schedule, the coefficient-mass model class, the score and estimator notation, the minimax risk, the block score and least-favourable block construction, the local linear estimator class, and the uniformly bounded-outcome extension. The definitions are ordered so that graph and coefficient classes precede model classes, SNIPE precedes risk statements, block quantities precede the complete-block results, and the bounded-outcome class precedes its minimax comparison.
objs: ass:bernoulli-design, ass:bounded-degree, ass:low-order, ass:bounded-coefficient-mass, def:exposed-order, def:zero-degree-conventions, def:graph-class, def:coefficient-class, def:model-class, def:snipe-score, def:snipe-estimator, def:minimax-risk, def:block-score-energy, def:block-family, def:perturbation-program, def:weight-program, def:local-linear-class, def:local-linear-estimator-class, def:local-linear-risk, def:bounded-outcome-coefficient-class, def:bounded-outcome-model-class, def:two-class-minimax-risks, def:bounded-outcome-clipped-snipe
bib: HorvitzThompson1952, Rubin1978, Aronow2017, CortezRodriguezEichhornYu2023

## section: Main Results
This section states the degree-dependent minimax theorem for the coefficient-mass class, the exact complete-block local linear benchmark and representer characterization, the extension to uniformly bounded outcomes and the sharp complete-block variance calculation, and the fair-coin specialization. The prose will emphasize what each result characterizes under its stated conditions: the minimax rate, the attaining projected estimator, the least-favourable block calibration, the necessary and sufficient blockwise criterion for local linear asymptotic minimaxity, and the \(p=1/2,\beta=1\) rate \(B^2\min\{1,d^2/n\}\).
objs: thm:degree-frontier, thm:sharp-local-linear-constant-and-representers, thm:bounded-outcome-degree-frontier, thm:fair-coin-energy-frontier
bib: CortezRodriguezEichhornYu2023, HarshawSavjeWang2025, Swaminathan2017, YuAiroldiBorgsChayes2022, EichhornKhanUganderYu2026, WangLi2026

## section: Discussion and Extensions
This section interprets the rate through overlap, block energy, and interaction order; relates the complete-block benchmark to global SNIPE performance; and explains how the uniformly bounded-outcome class calibrates the same degree dependence through \(A_d\). A clearly labelled limitations and future-work paragraph may discuss extensions such as alternative designs, covariate adjustment, unknown graphs, and clustered assignment, framed as open directions rather than delivered results.
objs:
bib: Leung2022, Savje2021, Hu2022, Gao2025, WangLi2026, EichhornKhanUganderYu2026

## section: Appendix: Proofs and Auxiliary Lemmas
The appendix contains the block-energy representer lemma, the overlap-count lemma, and the proofs of all theorems. The proof organization follows the main results: first the finite-design orthogonality and variance identities, then the SNIPE upper bound and overlap counting, then the least-favourable block lower bound via total variation and affinity, then the local linear complete-block program, then the bounded-outcome comparison and fair-coin calculation.
objs: lem:block-energy-representer, lem:overlap-count
bib: HorvitzThompson1952, Aronow2017, CortezRodriguezEichhornYu2023, HarshawSavjeWang2025

## section: Appendix: Verification Note
This brief note consolidates the Lean verification scope: the finite Bernoulli design algebra, polynomial-interference constructions, SNIPE unbiasedness and variance calculations, minimax-risk definitions, least-favourable block family, continuous-prior integrated-risk step, affinity-based total variation bound, block Riesz programs, and the theorem statements are machine checked; bibliographic dependencies and econometric interpretation enter as cited inputs to the manuscript exposition.
objs:
bib: HorvitzThompson1952, Rubin1978, ImbensRubin2015, Aronow2017, CortezRodriguezEichhornYu2023, HarshawSavjeWang2025
