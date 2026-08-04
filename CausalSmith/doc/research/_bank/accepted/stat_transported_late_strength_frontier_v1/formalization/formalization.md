# stat_transported_late_strength_frontier — formalization note (bridge; rendered from core + plan)

_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / causalsmith bridge._

## Environment (S)

**S-1 (Two-population full-data potential-outcome world at index n).** Two-population full-data potential-outcome world at index n: P_n^F is a probability Measure on the explicit coordinate space FullData := Bool x X x Bool x Bool x R x R carrying (S, X, D(0), D(1), Y(0), Y(1)); the assignment potential outcome is the derived map Y^Z(z) = Y(D(z)); the forced parameter space is Theta = Set.Icc (-1 : R) 1 and the causal target theta_T is the complier-conditional contrast under S = 0. — Bypass-justified (see decisions.full_data_coordinate_space): Causalean.PO's POSystem/POIVSystem is a regime- and variable-indexed skeleton with no population indicator and no transport layer, and the least-favourable witness must be built explicitly and checked against every causal assumption, which is only tractable on an explicit coordinate law. Causalean.PO.ID.Exact.LATE.POIVSystem (late_wald and its four-step chain) is the ANALOGOUS module F3 should adapt for prop:compact-causal-range; gap to bridge = two populations + the transport change of measure. Search trace: read ../doc/API.md sections '8h. PO/' and '9f. PO/ID/Exact/LATE.lean'; grepped ../Causalean for 'transport', 'population indicator', 'S = 0', 'POIVSystem'; scanned ../Causalean/PO/{Core,Assumptions,ID/Exact} -- no two-population transported potential-outcome world: not found.
**required modules.** CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Basic, Causalean.PO.ID.Exact.LATE

**S-2 (Observed two-sample triangular-array sampling world).** Observed two-sample triangular-array sampling world: n i.i.d. source observations O_i^S = (X_i, Z_i, D_i, Y_i) ~ P_S on X x Bool x Bool x R, independently N_n i.i.d. target covariate draws X_j^T ~ P_T on X, with N_n / n -> c; the joint sample law at index n is Measure.pi (fun _ : Fin n => P_S) .prod (Measure.pi (fun _ : Fin N_n => P_T)). P_S is the observed-data law induced by P_n^F given S = 1 with source assignment propensity e, P_S^X its X-marginal, P_T the S = 0 X-marginal, and e : X -> R the source propensity taking values in [eps, 1 - eps]. — The i.i.d. primitives are reused (Causalean.Stat.IIDSample, Causalean.Stat.iidSample_infinitePi, Causalean.Stat.iidSample_finN_pushforward give the coordinate-projection sample and its Measure.pi pushforward), but the world itself is a PRODUCT of two independent samples with DIFFERENT laws (source observations vs covariate-only target draws) and an index-linked size N_n, which IIDSample does not package -- so the two-sample world is define-local over Mathlib Measure.pi/Measure.prod on top of the reused primitives. Search trace: grepped ../Causalean for 'two-sample', 'twoSample', 'target sample', 'N_n', 'covariate-only'; scanned ../Causalean/Stat/{Sample.lean,Sample/PiTransport.lean,SampleSplit} and ../doc/API.md sections 12a/12a'/12e -- no two-sample independent-product sampling world: not found.
**required modules.** CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Basic, Causalean.Stat.Sample, Causalean.Stat.Sample.PiTransport

**S-3 (Transport / overlap geometry world).** Transport / overlap geometry world: the deterministic array g = (P_S^X, w, e)_{n>=1} with w : X -> R the density ratio dP_T/dP_S^X normalized by E_S[w(X)] = 1 and capped by 0 <= w <= 2 k_n, the Kish dispersion kappa_n = E_S[w(X)^2] <= k_n, the known envelope sequence k_n, and (in the cell submodels) the known source-cell probability array q_{x,n} = P_S^X{x} with c_- / k_n <= q_{x,n} <= c_+ / k_n. — Plain measurable-function / real-scalar geometry layer over Mathlib (Measure.rnDeriv for w = dP_T/dP_S^X plus the P_T(A) = E_S[w 1_A] change-of-measure identity). Search trace: grepped ../Causalean for 'densityRatio', 'density ratio', 'covariate shift', 'Kish', 'importance weight', 'rnDeriv' in Stat/ and Estimation/; scanned ../doc/API.md sections 12/13sa/13eff -- Causalean carries Measure.rnDeriv plumbing (Stat/Minimax/ChiSquared.rnDeriv_prod_eq, Mathlib/CondDistrib) but no transport-weight / Kish-dispersion geometry object: not found.
**required modules.** CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Basic

**S-4 (Identification and effective-strength scalar world).** Identification and effective-strength scalar world: the two identified source conditional contrasts Delta_Y, Delta_D : X -> R, their transported means mu_{Y,n} = E_S[w Delta_Y] and mu_n = E_S[w Delta_D] > 0, the effective identification strength t_n = n mu_n^2 / kappa_n, the frontier argument t_0 > 0, the noncoverage level alpha in (0,1), the Le Cam calibration rho = (1 - alpha) / 8, and the frontier constants c_0, C_0, t_c. — Real-valued functionals of (P_S, w) plus plain real scalars; realized as named defs over Mathlib integrals. Search trace: grepped ../Causalean for 'effective sample size', 'firstStage', 'first stage', 'Wald ratio', 'complier share', 'identification strength'; scanned ../Causalean/PO/ID/Exact/LATE.lean and ../Causalean/Estimation/NPIV -- LATE.lean has condExpDZ/condExpYZ (single-population, no covariate conditioning, no transport weight), no transported-contrast or effective-strength index: not found.
**required modules.** CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Basic

**S-5 (Procedure and minimax-risk world).** Procedure and minimax-risk world: a confidence-set sequence is a bundled random subset C_n of Theta -- a map from the index-n sample (plus the declared oracle/known inputs) to Set R with a jointly measurable graph and C_n subset Theta -- with lambda = MeasureTheory.volume restricted to Theta as the length; on top of it the four honest procedure classes (oracle, fixed-geometry oracle, finite-cell feasible, regular-cell feasible), the four model classes / slices (P_n, N_n, N_n^reg, P_n(g)), the worst-case limiting risk R, and the three value functions V*, V*_N, V*_g. — Analogous modules, not exact fits. Causalean.Estimation.MinimaxATE.Model gives the inf-sup packaging shape (minimaxMiss = iSup over a subtype of in-class DGPs, bddAbove_nMiss_range, nMiss_le_minimaxMiss) which is copied verbatim in shape, but its risk is a finite-PMF quantile MISS probability, not honest expected SET LENGTH, and its class is a finite-X ATE nuisance ball. Causalean.PO.ID.Partial.Inference.Basic gives coverage vocabulary (RandomCoversPoint, honest_ci_set_cover) for a fixed interval-identified parameter with plug-in half-widths, not an inf over honest procedure SEQUENCES with a limsup-of-sup risk. Search trace: grepped ../Causalean for 'expectedLength', 'expected_length', 'setLength', 'ConfidenceSet', 'confidenceSet', 'Coverage', 'honest' (20 files, all coverage-of-a-fixed-interval or DR-learner 'honest sample splitting'); scanned ../Causalean/PO/ID/Partial/{Inference,RandomSet}, ../Causalean/Stat/Minimax, ../Causalean/Experimentation/UnknownInterference/Confidence.lean, and doc/API.md sections 3.1-3.10 of CausalSmith -- no honest-expected-length minimax frontier world anywhere: not found.
**required modules.** CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Frontier, Causalean.Estimation.MinimaxATE.Model, Causalean.PO.ID.Partial.Inference.Basic

## Assumptions (A)

**A-1 (assumption).** \(P_n^F\{S\in\{0,1\},D(0),D(1)\in\{0,1\},Y(0),Y(1)\in[0,1]\}=1\).

**A-2 (assumption).** \(P_n^F(S=s)>0\) for \(s\in\{0,1\}\).

**A-3 (assumption).** \((O_i^S)_{i=1}^n\sim P_S^{\otimes n}\), \((X_j^T)_{j=1}^{N_n}\sim P_T^{\otimes N_n}\), \((O_i^S)_{i=1}^n\perp(X_j^T)_{j=1}^{N_n}\), and \(N_n/n\to c\).

**A-4 (assumption).** \(\varepsilon\le e(X)\le1-\varepsilon\) \(P_S\)-almost surely.

**A-5 (assumption).** \(P(Z=1\mid X,S=1)=e(X)\), \(D=D(Z)\), and \(Y=Y(D)\) conditional on \(S=1\).

**A-6 (assumption).** \(Z\perp(Y(0),Y(1),D(0),D(1))\mid(X,S=1)\).

**A-7 (assumption).** \(Y^Z(z)=Y(D(z))\) \(P_n^F\)-almost surely conditional on \(S=s\), for \(z,s\in\{0,1\}\).

**A-8 (assumption).** \(D(1)\ge D(0)\) \(P_n^F\)-almost surely conditional on \(S=s\), for \(s\in\{0,1\}\).

**A-9 (assumption).** \(\mathbb E_{P_n^F}[Y^Z(1)-Y^Z(0)\mid X=x,S=0]=\mathbb E_{P_n^F}[Y^Z(1)-Y^Z(0)\mid X=x,S=1]\) for \(P_T\)-almost every \(x\).

**A-10 (assumption).** \(\mathbb E_{X\mid S=0}[\mathbb E_{P_n^F}[D(1)-D(0)\mid X,S=0]]=\mathbb E_{X\mid S=0}[\mathbb E_{P_n^F}[D(1)-D(0)\mid X,S=1]]\).

**A-11 (assumption).** \(P_n^F(D(1)>D(0)\mid S=0)>0\).

**A-12 (assumption).** \(P_T\ll P_S^X\) on \(\mathcal X\).

**A-13 (assumption).** \(0\le w(X)\le2k_n\) \(P_S\)-almost surely.

**A-14 (assumption).** \(\kappa_n\le k_n\).

**A-15 (assumption).** \(k_n\to\infty\), \(k_n=o(n^{1/2})\), and \(\mu_n\to0\).

**A-16 (assumption).** \(\mathcal X=\{1,\ldots,k_n\}\), \(P_S^X\) is uniform, and \(e(X)=1/2\) \(P_S\)-almost surely.

## Definitions (P)

**P-1 (\(\mathcal P_n=\{P=(P_n^F,e):P\text{ satisfies ass:full-d…).** \(\mathcal P_n=\{P=(P_n^F,e):P\text{ satisfies ass:full-data-support, ass:population-presence, ass:two-sample-array, ass:instrument-overlap, ass:source-observation, ass:iv-randomization, ass:iv-exclusion, ass:iv-monotonicity, ass:outcome-transport, ass:receipt-transport, ass:target-complier-positivity, ass:transport-domination, ass:weight-envelope, ass:weight-second-moment, and ass:degrading-array at index }n\}\).

**P-2 (\(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies ass:f…).** \(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies ass:finite-cell-source at index }n\}\).

**P-3 (\(\mathfrak C^{\mathrm{or}}=\{(C_n)_{n\ge1}:C_n=C_n((O_i^…).** \(\mathfrak C^{\mathrm{or}}=\{(C_n)_{n\ge1}:C_n=C_n((O_i^S)_{i=1}^n,(X_j^T)_{j=1}^{N_n},w,e)\subseteq\Theta,\;\liminf_{n\to\infty}\inf_{P\in\mathcal P_n}P(\theta_T\in C_n)\ge1-\alpha\}\).

**P-4 (\(R((C_n),t_0)=\limsup_{n\to\infty}\sup_{P\in\mathcal P_n…).** \(R((C_n),t_0)=\limsup_{n\to\infty}\sup_{P\in\mathcal P_n:\,t_n\ge t_0}\mathbb E_P[\lambda(C_n)]\).

**P-5 (\(V^\star(t_0)=\inf_{(C_n)\in\mathfrak C^{\mathrm{or}}}R(…).** \(V^\star(t_0)=\inf_{(C_n)\in\mathfrak C^{\mathrm{or}}}R((C_n),t_0)\).

**P-6 (\(V_{\mathcal N}^\star(t_0)=\inf_{(C_n)\in\mathfrak C^{\m…).** \(V_{\mathcal N}^\star(t_0)=\inf_{(C_n)\in\mathfrak C^{\mathrm{or}}}\limsup_{n\to\infty}\sup_{P\in\mathcal N_n:\,t_n\ge t_0}\mathbb E_P[\lambda(C_n)]\).

**P-7 (\(\mathfrak C^{\mathrm{cell}}=\{(C_n)_{n\ge1}:C_n=C_n((O_…).** \(\mathfrak C^{\mathrm{cell}}=\{(C_n)_{n\ge1}:C_n=C_n((O_i^S)_{i=1}^n,(X_j^T)_{j=1}^{N_n})\subseteq\Theta,\;\liminf_{n\to\infty}\inf_{P\in\mathcal N_n}P(\theta_T\in C_n)\ge1-\alpha\}\).

**P-8 (For every \(\vartheta\in\Theta\), form the source inverse…).** For every \(\vartheta\in\Theta\), form the source inverse-propensity score \(w(X)\{Z/e(X)-(1-Z)/(1-e(X))\}(Y-\vartheta D)\), compare its empirical mean with \(L_\alpha\{n^{-1}\sum_{i=1}^nw(X_i)^2/n\}^{1/2}\), and invert the resulting acceptance inequality over \(\Theta\). Once \(w\) and \(e\) are oracle-known, the target sample does not enter this score.

**P-9 (Hold an arbitrary admissible deterministic array \((P_S^X…).** Hold an arbitrary admissible deterministic array \((P_S^X,w,e)\) fixed, set \(\mu_n=(t_0\kappa_n/n)^{1/2}\) and the conditional complier probability \(p_n(x)=\mu_nw(x)/\kappa_n\), vary only the complier outcome mean over a continuum, and compare every member with its center by chi-square and total variation.

**P-10 (Fix \(\mathfrak g=(P_S^X,w,e)_{n\ge1}\in\mathcal G\) and…).** Fix \(\mathfrak g=(P_S^X,w,e)_{n\ge1}\in\mathcal G\) and \(t_0>0\). Set \(\mu_n=(t_0\kappa_n/n)^{1/2}\), \(p_n(x)=\mu_nw(x)/\kappa_n\), \(\rho=(1-\alpha)/8\), and \(H(t_0)=\min\{1/4,\rho t_0^{-1/2}\}\). Conditional on \(X=x\), assign compliance types \((D(0),D(1))=(0,1),(1,1),(0,0)\) probabilities \(p_n(x),(1-p_n(x))/2,(1-p_n(x))/2\). Set \(Y(0)=0\); for compliers let \(Y(1)\) be Bernoulli \((1/2+h)\), and for both always-takers and never-takers let \(Y(1)\) be Bernoulli \((1/2)\), for \(|h|\le H(t_0)\). Use this same conditional full-data law in both populations, draw source encouragement with propensity \(e(X)\), and denote the resulting joint observed-data law and fixed oracle inputs by \(Q_{n,h}^{\mathfrak g}\).

**P-11 (\(\mathcal G\) is the class of deterministic arrays \(\ma…).** \(\mathcal G\) is the class of deterministic arrays \(\mathfrak g=(P_S^X,w,e)_{n\ge1}\) such that \(P_S^X\) is a probability law on \(\mathcal X\), \(e:\mathcal X\to[\varepsilon,1-\varepsilon]\), \(w:\mathcal X\to[0,2k_n]\), \(\mathbb E_S[w(X)]=1\), \(\kappa_n=\mathbb E_S[w(X)^2]\le k_n\), and \(P_T(A)=\mathbb E_S[w(X)\mathbf 1\{X\in A\}]\) for every measurable \(A\subseteq\mathcal X\).

**P-12 (For \(\mathfrak g\in\mathcal G\), \(\mathcal P_n(\mathfra…).** For \(\mathfrak g\in\mathcal G\), \(\mathcal P_n(\mathfrak g)=\{P\in\mathcal P_n:(P_S^X,w,e)\text{ equals the index-}n\text{ component of }\mathfrak g\}\).

**P-13 (\(\mathfrak C^{\mathrm{or}}(\mathfrak g)=\{(C_n)_{n\ge1}:…).** \(\mathfrak C^{\mathrm{or}}(\mathfrak g)=\{(C_n)_{n\ge1}:C_n=C_n((O_i^S)_{i=1}^n,(X_j^T)_{j=1}^{N_n},w,e)\subseteq\Theta,\;\liminf_{n\to\infty}\inf_{P\in\mathcal P_n(\mathfrak g)}P(\theta_T\in C_n)\ge1-\alpha\}\).

**P-14 (\(V_{\mathfrak g}^\star(t_0)=\inf_{(C_n)\in\mathfrak C^{\…).** \(V_{\mathfrak g}^\star(t_0)=\inf_{(C_n)\in\mathfrak C^{\mathrm{or}}(\mathfrak g)}\limsup_{n\to\infty}\sup_{P\in\mathcal P_n(\mathfrak g):\,t_n\ge t_0}\mathbb E_P[\lambda(C_n)]\).

**P-15 (\(\mathcal N_n^{\mathrm{reg}}=\{P\in\mathcal P_n:\mathcal…).** \(\mathcal N_n^{\mathrm{reg}}=\{P\in\mathcal P_n:\mathcal X=\{1,\ldots,k_n\},\;q_{x,n}=P_S^X(X=x),\;c_-/k_n\le q_{x,n}\le c_+/k_n\text{ for every }x\}\), where \(0<c_-\le1\le c_+<\infty\) are fixed.

**P-16 (\(\mathfrak C^{\mathrm{reg}}=\{(C_n)_{n\ge1}:C_n=C_n((O_i…).** \(\mathfrak C^{\mathrm{reg}}=\{(C_n)_{n\ge1}:C_n=C_n((O_i^S)_{i=1}^n,(X_j^T)_{j=1}^{N_n},(q_{x,n})_{x=1}^{k_n},e)\subseteq\Theta,\;\liminf_{n\to\infty}\inf_{P\in\mathcal N_n^{\mathrm{reg}}}P(\theta_T\in C_n)\ge1-\alpha\}\).

## Theorems (T)

### T-block: t1 — For every \(P\in\mathcal P_n\), source randomization iden…
**Statement.** For every \(P\in\mathcal P_n\), source randomization identifies \(\Delta_Y(x)=\mathbb E_{P_n^F}[Y^Z(1)-Y^Z(0)\mid X=x,S=1]\) and \(\Delta_D(x)=\mathbb E_{P_n^F}[D(1)-D(0)\mid X=x,S=1]\). Outcome-contrast transport and integrated first-stage transport imply \(\mu_{Y,n}=\mathbb E_{P_n^F}[(Y(1)-Y(0))\mathbf 1\{D(1)>D(0)\}\mid S=0]\) and \(\mu_n=P_n^F(D(1)>D(0)\mid S=0)\). Hence \(\mu_{Y,n}/\mu_n=\theta_T=\mathbb E_{P_n^F}[Y(1)-Y(0)\mid D(1)>D(0),S=0]\in\Theta=[-1,1]\).

### T-block: t2 — There exist constants \(c_0>0\) and \(t_c>0\), depending…
**Statement.** There exist constants \(c_0>0\) and \(t_c>0\), depending only on \(\alpha\), \(\varepsilon\), and the fixed class constants, such that for every \(t_0>0\), \(V^\star(t_0)\ge c_0\min\{1,t_0^{-1/2}\}\) and \(V_{\mathcal N}^\star(t_0)\ge c_0\min\{1,t_0^{-1/2}\}\). In particular, \(V^\star(t_0)\ge c_0\) whenever \(0<t_0\le t_c\). The constants do not depend on the decomposition of \(t_0\) into \(\mu_n\) and \(\kappa_n\).

### T-block: t3 — If \(w(X)=1\) \(P_S\)-almost surely, then \(\kappa_n=1\)…
**Statement.** If \(w(X)=1\) \(P_S\)-almost surely, then \(\kappa_n=1\) and \(t_n=n\mu_n^2\); hence the frontier specializes to compact single-population weak-ratio inference.

### T-block: t4 — Let \[ H_i=\frac{Z_i}{e(X_i)}-\frac{1-Z_i}{1-e(X_i)},\qua…
**Statement.** Let \[ H_i=\frac{Z_i}{e(X_i)}-\frac{1-Z_i}{1-e(X_i)},\quad \widehat A_n=\frac1n\sum_{i=1}^nw(X_i)H_iY_i,\quad \widehat B_n=\frac1n\sum_{i=1}^nw(X_i)H_iD_i, \] and \(\widehat\kappa_n=n^{-1}\sum_{i=1}^nw(X_i)^2\). With \(L_\alpha=\{8/(\alpha\varepsilon^2)\}^{1/2}\), define the single score-inversion sequence \[ C_n=\left\{\vartheta\in\Theta: |\widehat A_n-\vartheta\widehat B_n| \le L_\alpha\sqrt{\widehat\kappa_n/n}\right\}. \] Then \((C_n)\in\mathfrak C^{\mathrm{or}}\), and, simultaneously for every \(t_0>0\), \[ R((C_n),t_0)\le C_0\min\{1,t_0^{-1/2}\}, \qquad C_0=\max\left\{2,4L_\alpha+\frac8{\varepsilon^2}\right\}. \] Consequently \(V^\star(t_0)\) has order \(\min\{1,t_0^{-1/2}\}\). The displayed upper bound holds for every admissible weight geometry and depends on a member law through \(t_n=n\mu_n^2/\kappa_n\) only, apart from the fixed constants. Combined with the fixed-geometry frontier theorem, the achievability bound and the conditional converse match in order uniformly over admissible geometries, so any two admissible geometries with the same effective strength are equally difficult up to universal constants.

### T-block: t5 — On \(\mathcal N_n\), write \[ H_i=2(2Z_i-1),\qquad \wideh…
**Statement.** On \(\mathcal N_n\), write \[ H_i=2(2Z_i-1),\qquad \widehat p_{x,n}=\frac1{N_n}\sum_{j=1}^{N_n}\mathbf 1\{X_j^T=x\}, \] and, for \(G\in\{Y,D\}\), define \[ \widehat m_{G,n}(x)=\frac{k_n}{n}\sum_{i=1}^n \mathbf 1\{X_i=x\}H_iG_i,\qquad \widehat M_{G,n}=\sum_{x=1}^{k_n}\widehat p_{x,n}\widehat m_{G,n}(x). \] For \(N_n\ge2\), let \[ \widehat\kappa_{U,n}= \frac{k_n}{N_n(N_n-1)} \sum_{j\ne\ell}\mathbf 1\{X_j^T=X_\ell^T\},\qquad \widehat K_n=1+\widehat\kappa_{U,n}. \] Put \(B_c=32(1+c^{-1})\), \(L_{\alpha,c}=\{2B_c/\alpha\}^{1/2}\), and \[ C_n=\left\{\vartheta\in\Theta: |\widehat M_{Y,n}-\vartheta\widehat M_{D,n}| \le L_{\alpha,c}\sqrt{\widehat K_n/n}\right\}, \] with \(C_n=\Theta\) at the finitely many indices for which \(N_n<2\). This sequence belongs to \(\mathfrak C^{\mathrm{cell}}\), does not use \(w\), and satisfies, simultaneously for all \(t_0>0\), \[ \limsup_{n\to\infty}\sup_{P\in\mathcal N_n:\,t_n\ge t_0} \mathbb E_P[\lambda(C_n)] \le C_0\min\{1,t_0^{-1/2}\}, \] where \[ C_0=\max\{2,4\sqrt2L_{\alpha,c}+8B_c\}. \] Moreover, the finite-cell change-of-measure family used for the oracle converse applies to every sequence in \(\mathfrak C^{\mathrm{cell}}\); hence the corresponding infimum of the displayed worst-case risk is at least \(c_0\min\{1,t_0^{-1/2}\}\). Thus estimating the target cell probabilities creates no additional minimax-order loss on \(\mathcal N_n\).

### T-block: t6 — Let \(\mathfrak g\in\mathcal G\) be any admissible determ…
**Statement.** Let \(\mathfrak g\in\mathcal G\) be any admissible deterministic geometry array. Put \(L_\alpha=\{8/(\alpha\varepsilon^2)\}^{1/2}\), \(c_\alpha=3(1-\alpha)^2/16\), and \(C_\alpha=\max\{2,4L_\alpha+8\varepsilon^{-2}\}\). Then, for every fixed \(t_0>0\), \[ c_\alpha\min\{1,t_0^{-1/2}\} \le V_{\mathfrak g}^\star(t_0) \le C_\alpha\min\{1,t_0^{-1/2}\}. \] Both constants are uniform in \(\mathfrak g\). In particular, after conditioning on any admissible source-covariate law, transport-weight array, and propensity array, geometries having the same effective strength are equally difficult up to the displayed universal constants.

### T-block: t7 — On \(\mathcal N_n^{\mathrm{reg}}\), let \(q_{x,n}=P_S^X(X…
**Statement.** On \(\mathcal N_n^{\mathrm{reg}}\), let \(q_{x,n}=P_S^X(X=x)\), let \[ H_i=\frac{Z_i}{e(X_i)}-\frac{1-Z_i}{1-e(X_i)}, \qquad \widehat p_{x,n}=\frac1{N_n}\sum_{j=1}^{N_n}\mathbf 1\{X_j^T=x\}, \] and, for \(G\in\{Y,D\}\), define \[ \widehat m_{G,n}(x)=\frac1{nq_{x,n}}\sum_{i=1}^n \mathbf 1\{X_i=x\}H_iG_i, \qquad \widehat M_{G,n}=\sum_{x=1}^{k_n}\widehat p_{x,n}\widehat m_{G,n}(x). \] For \(N_n\ge2\), set \[ \widehat\kappa_{U,n}= \frac1{N_n(N_n-1)}\sum_{j\ne\ell} \frac{\mathbf 1\{X_j^T=X_\ell^T\}}{q_{X_j^T,n}}, \qquad \widehat K_n=1+\widehat\kappa_{U,n}. \] Put \(B_{\varepsilon,c}=8(\varepsilon^{-2}+c^{-1})\). For every fixed \(L\ge\{2B_{\varepsilon,c}/\alpha\}^{1/2}\), the sequence \[ C_n^{\mathrm{reg}}=\left\{\vartheta\in\Theta: |\widehat M_{Y,n}-\vartheta\widehat M_{D,n}| \le L\sqrt{\widehat K_n/n}\right\}, \] with \(C_n^{\mathrm{reg}}=\Theta\) when \(N_n<2\), belongs to \(\mathfrak C^{\mathrm{reg}}\), does not use \(w\), and satisfies, for every fixed \(t_0>0\), \[ \limsup_{n\to\infty}\sup_{P\in\mathcal N_n^{\mathrm{reg}}:\,t_n\ge t_0} \mathbb E_P[\lambda(C_n^{\mathrm{reg}})] \le \max\{2,4\sqrt2L+8B_{\varepsilon,c}\} \min\{1,t_0^{-1/2}\}. \] The infimum of this risk over \(\mathfrak C^{\mathrm{reg}}\) is at least \(3(1-\alpha)^2\min\{1,t_0^{-1/2}\}/16\). Thus unknown target cell probabilities cause no minimax-order loss for known regular source-cell probabilities and a known cell-varying propensity bounded by \(\varepsilon\).
