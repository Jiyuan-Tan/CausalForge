# Title

**Generic Separation of Axis-Normalized Latent-Source Representations by Higher-Order Cumulants**

**Contribution statement.** Conditional on a fixed number of source slots and the paper's axis-normalized representation class, the paper proves that truncated joint cumulants generically exclude the opposite representation, characterizes the codimension-one compatibility locus, and distinguishes this representation-level result from law-space causal identification or an implementable estimator.

# Notation

notation_gaps: \(\operatorname{Laws}(\mathbb R^2)\)=ambient class of probability laws on \(\mathbb R^2\), \(\operatorname{Cum}\)=joint cumulant functional, \(\operatorname{ZariskiClosure}\)=Zariski closure operator in the ambient complex affine space, \(B_r\)=complete Bell polynomial converting cumulants to raw moments, \(P_M\)=observational law induced by a structural model \(M\), \(D(M)\)=causal direction attached to a structural model, \(\operatorname{opposite}(b)\)=opposite-arrow involution on \(\{\mathrm{right},\mathrm{left}\}\)

env_overrides: def:real-atlas-handle=remarkv, def:effective-rational-groebner-cad-interface=remarkv

\(\{S_j\}_{j=0}^{m+1}\) | \(S_0,\ldots,S_{m+1}\) | centered latent source variables | ass:independent-sources
\(S_0 \perp S_1 \perp \cdots \perp S_{m+1}\) | \(S_0 \perp S_1 \perp \cdots \perp S_{m+1}\) | mutual independence of latent sources | ass:independent-sources
\(K\) | \(K\) | working cumulant and moment truncation order | ass:finite-cumulants
\(E|S_j|^K<\infty\) | \(\mathbb E|S_j|^K<\infty\) | finite \(K\)-th absolute moment condition | ass:finite-cumulants
\(S_j\) | \(S_j\) | non-Gaussian source variable | ass:source-nongaussianity
\((X,Y)^T\) | \((X,Y)^\top\) | bivariate observed outcome vector | ass:forward-axis-model
\(u_j\) | \(u_j\) | forward loading vector | ass:forward-axis-model
\(v_j\) | \(v_j\) | reverse loading vector | ass:reverse-axis-model
\(\gamma\) | \(\gamma\) | forward direct-edge slope | ass:forward-noncollinearity
\(\rho_i\) | \(\rho_i\) | forward latent finite slope | ass:forward-noncollinearity
\(\delta\) | \(\delta\) | reverse direct-edge slope | ass:reverse-noncollinearity
\(\sigma_i\) | \(\sigma_i\) | reverse latent finite slope | ass:reverse-noncollinearity
\(\{P \in \operatorname{Laws}(\mathbb R^2):\cdots\}\) | \(\mathcal P^{\mathrm{right}}_{m,K}\) | laws admitting the forward latent linear non-Gaussian representation | def:forward-lvlingam-class
\(\{P \in \operatorname{Laws}(\mathbb R^2):\cdots\}\) | \(\mathcal P^{\mathrm{left}}_{m,K}\) | laws admitting the reverse latent linear non-Gaussian representation | def:reverse-lvlingam-class
\(T_L(P)\) | \(T_L(P)\) | joint cumulant vector from orders \(2\) through \(L\) | def:truncated-cumulant
\(\kappa_{r,a}(P)\) | \(\kappa_{r,a}(P)\) | cumulant with \(r-a\) copies of \(X\) and \(a\) copies of \(Y\) | def:truncated-cumulant
\(q_L\) | \(q_L\) | number of cumulant coordinates through order \(L\) | def:truncated-cumulant
\(\Phi^{\mathrm{right}}_{m,L}(\gamma,\rho,c)\) | \(\Phi^{\mathrm{right}}_{m,L}(\gamma,\rho,c)\) | polynomial forward cumulant map | def:forward-cumulant-map
\(c_{jr}\) | \(c_{jr}\) | order-\(r\) cumulant weight for forward source \(j\) | def:forward-cumulant-map
\(u_0=(1,\gamma)\) | \(u_0=(1,\gamma)\) | forward direct-axis loading direction | def:forward-cumulant-map
\(u_j=(1,\rho_j)\) | \(u_j=(1,\rho_j)\) | forward finite latent loading direction | def:forward-cumulant-map
\(u_{m+1}=(0,1)\) | \(u_{m+1}=(0,1)\) | forward fixed vertical-axis source direction | def:forward-cumulant-map
\(\Phi^{\mathrm{left}}_{m,L}(\delta,\sigma,d)\) | \(\Phi^{\mathrm{left}}_{m,L}(\delta,\sigma,d)\) | polynomial reverse cumulant map | def:reverse-cumulant-map
\(d_{jr}\) | \(d_{jr}\) | order-\(r\) cumulant weight for reverse source \(j\) | def:reverse-cumulant-map
\(v_0=(1,0)\) | \(v_0=(1,0)\) | reverse fixed horizontal-axis source direction | def:reverse-cumulant-map
\(v_j=(\sigma_j,1)\) | \(v_j=(\sigma_j,1)\) | reverse finite latent loading direction | def:reverse-cumulant-map
\(v_{m+1}=(\delta,1)\) | \(v_{m+1}=(\delta,1)\) | reverse direct-axis loading direction | def:reverse-cumulant-map
\(C^{\mathrm{right}}_{m,L}\) | \(C^{\mathrm{right}}_{m,L}\) | Zariski closure of the forward cumulant-map image | def:image-varieties
\(C^{\mathrm{left}}_{m,L}\) | \(C^{\mathrm{left}}_{m,L}\) | Zariski closure of the reverse cumulant-map image | def:image-varieties
\(\Theta^{\mathrm{right},\circ}_{m,L}\) | \(\Theta^{\mathrm{right},\circ}_{m,L}\) | nonzero and distinct-slope forward generic locus with nonzero source cumulants | def:generic-parameter-loci
\(\Theta^{\mathrm{left},\circ}_{m,L}\) | \(\Theta^{\mathrm{left},\circ}_{m,L}\) | nonzero and distinct-slope reverse generic locus with nonzero source cumulants | def:generic-parameter-loci
\(R^{\mathrm{right}}_{m,L}(t)\) | \(R^{\mathrm{right}}_{m,L}(t)\) | forward parameter fiber over cumulant vector \(t\) | def:fiber-correspondences
\(R^{\mathrm{left}}_{m,L}(t)\) | \(R^{\mathrm{left}}_{m,L}(t)\) | reverse parameter fiber over cumulant vector \(t\) | def:fiber-correspondences
\(G_m\) | \(G_m\) | admissible permutations of non-axis latent source labels | def:admissible-source-swaps
\(\pi\) | \(\pi\) | element of the admissible source-swap group | def:admissible-source-swaps
\(E_m\) | \(E_m\) | cumulant vectors with generic representation on one arrow and a full representation on the other | def:generic-full-fiber-compatibility
\(\overline E_m\) | \(\overline E_m\) | Zariski closure of the generic full-fiber compatibility locus | def:generic-full-fiber-compatibility
\(H^{\mathrm{right}}_m\) | \(H^{\mathrm{right}}_m\) | forward generic parameters retaining a full opposite-arrow representation | def:generic-full-fiber-compatibility
\(H^{\mathrm{left}}_m\) | \(H^{\mathrm{left}}_m\) | reverse generic parameters retaining a full opposite-arrow representation | def:generic-full-fiber-compatibility
\(F^{\mathrm{right}}_{m,L}\) | \(F^{\mathrm{right}}_{m,L}\) | real forward parameters realizable by centered non-Gaussian sources through order \(L\) | def:real-feasible-regions
\(F^{\mathrm{left}}_{m,L}\) | \(F^{\mathrm{left}}_{m,L}\) | real reverse parameters realizable by centered non-Gaussian sources through order \(L\) | def:real-feasible-regions
\(K^\star(m)\) | \(K^\star(m)\) | minimal order for generic real arrow separation when finite | def:information-order
\(b\in\{\mathrm{right},\mathrm{left}\}\) | \(b\in\{\mathrm{right},\mathrm{left}\}\) | arrow index selecting a parametrization | def:global-feasible-fiber-decision
\(t\in\mathbb R^{q_K}\) | \(t\in\mathbb R^{q_K}\) | real cumulant-coordinate vector at order \(K\) | def:global-feasible-fiber-decision
\(\lambda\) | \(\lambda\) | real loading and source-cumulant coordinates in the feasible-fiber predicate | def:global-feasible-fiber-decision
\((w_{jh},z_{jh})_{h=1}^{m+2}\) | \((w_{jh},z_{jh})_{h=1}^{m+2}\) | finite atomic moment-certificate witnesses | def:global-feasible-fiber-decision
\(k_{jr}\) | \(k_{jr}\) | source cumulant assigned to source \(j\) inside the feasible-fiber predicate | def:global-feasible-fiber-decision
\(\mu_{jr}\) | \(\mu_{jr}\) | raw moment obtained from cumulants by Bell polynomials | def:global-feasible-fiber-decision
\(\operatorname{FeasFiber}^{\mathrm{right}}_m(t)\) | \(\operatorname{FeasFiber}^{\mathrm{right}}_m(t)\) | right-arrow finite feasible-fiber formula | def:direction-selector
\(\operatorname{FeasFiber}^{\mathrm{left}}_m(t)\) | \(\operatorname{FeasFiber}^{\mathrm{left}}_m(t)\) | left-arrow finite feasible-fiber formula | def:direction-selector
\(S_m(t)\) | \(S_m(t)\) | partial direction selector from one-sided feasible-fiber truth values | def:direction-selector
\(M^{\mathrm{sep}}_{m,K}\) | \(M^{\mathrm{sep}}_{m,K}\) | models whose observed cumulants have exactly one real feasible arrow | def:separated-model-domain
\(A_1\) | \(A_1\) | explicit \(m=1,K=4\) full-fiber incidence system | def:worked-compatibility-instances
\(A_2\) | \(A_2\) | explicit \(m=2,K=6\) full-fiber incidence system | def:worked-compatibility-instances
\(K_-=2m+1\) | \(K_-=2m+1\) | lower-order truncation used in the real twin construction handle | def:real-twin-construction-handle
\(d=m+1\) | \(d=m+1\) | shifted source-count parameter in the real-atlas handle | def:real-atlas-handle
\(K=2d\) | \(K=2d\) | atlas truncation order | def:real-atlas-handle
\(n=d+1\) | \(n=d+1\) | number of atoms in the finite source-moment certificate | def:real-atlas-handle
\(Q_K(k)\) | \(Q_K(k)\) | finite atomic source-moment certificate | def:real-atlas-handle
\(Q_D\) | \(Q_D\) | squarefree homogeneous support-annihilator polynomial | def:apolar-notation
\(q(\partial)\) | \(q(\partial)\) | constant-coefficient differential operator associated with \(q(x,y)\) | def:apolar-notation
\(U^{\mathrm{right}}_m\) | \(U^{\mathrm{right}}_m\) | forward Zariski-open dense locus for apolar recovery and opposite-arrow exclusion | thm:generic-apolar-arrow-recovery
\(U^{\mathrm{left}}_m\) | \(U^{\mathrm{left}}_m\) | reverse Zariski-open dense locus for apolar recovery and opposite-arrow exclusion | thm:generic-apolar-arrow-recovery
\(n=m+2\) | \(n=m+2\) | number of loading directions in the apolar theorem | thm:generic-apolar-arrow-recovery
\(K=2n-2\) | \(K=2n-2\) | cumulant truncation order in the apolar theorem | thm:generic-apolar-arrow-recovery
\(f_r(x,y)\) | \(f_r(x,y)\) | divided-power binary form built from cumulant coordinates | thm:generic-apolar-arrow-recovery
\(D\) | \(D\) | unordered loading-direction support recovered from \(Q_D\) | thm:generic-apolar-arrow-recovery

# Sections

## section: Abstract

The abstract will be drafted after the body is fixed. It will state the bivariate latent linear non-Gaussian direction problem, the generic cumulant-based direction recovery result, the codimension-one opposite-arrow compatibility result, and the lower-order recovery statement for \(m\ge 3\), without presenting the formal layer or conditional algebraic interfaces as a contribution.

objs: none

bib: none

## section: Introduction

The introduction will motivate causal direction in bivariate latent-variable linear non-Gaussian models, place the result relative to structural causal models, graphical identification, LiNGAM, hidden-confounding, cumulant methods, and binary-form identification, and state the paper’s contribution in econometric identification terms. It will include only one factual sentence saying that the formal verification scope is summarized in the appendix verification note.

objs: none

bib: Pearl2009, SpirtesGlymourScheines2001, PetersJanzingScholkopf2017, RichardsonSpirtes2002, ZhangHyvarinen2009, MooijPetersJanzingZscheischlerScholkopf2016, Comon1994, HyvarinenOja2000, Cardoso1999, KaganLinnikRao1973, ShimizuHyvarinenKanoHoyer2006, HoyerShimizuKerminenPalviainen2008, SalehkaleybarGhassamiKiyavashZhang2020, ChenPengHuangEtAl2025Direction, CaiGaoHara2025Direction, CaiHara2026SparsestLvLiNGAM

## section: Setup and assumptions

This section introduces the bivariate latent linear non-Gaussian law, the forward and reverse axis conventions, the truncated cumulant vector, the two polynomial cumulant maps, the image varieties, the generic parameter loci, admissible source relabellings, real feasibility, and the information-order notation. It also introduces the apolar notation needed for the main theorem and treats \(K^\star(m)=2m+2\) only as a disproved conjectural benchmark rather than as a result or premise.

objs: ass:independent-sources, ass:finite-cumulants, ass:source-nongaussianity, ass:forward-axis-model, ass:reverse-axis-model, ass:forward-noncollinearity, ass:reverse-noncollinearity, ass:forward-nonzero-edge, ass:reverse-nonzero-edge, def:forward-lvlingam-class, def:reverse-lvlingam-class, def:truncated-cumulant, def:forward-cumulant-map, def:reverse-cumulant-map, def:image-varieties, def:generic-parameter-loci, def:fiber-correspondences, def:admissible-source-swaps, def:real-feasible-regions, def:information-order, def:apolar-notation

bib: Brillinger1969, McCullagh1987, Comon1994, HyvarinenOja2000, Cardoso1999, ShimizuHyvarinenKanoHoyer2006, ShimizuInazumiSogawaEtAl2011, TashiroShimizuHyvarinenWashio2014, MaedaShimizu2020, HoyerShimizuKerminenPalviainen2008, ComonMourrain1996, Landsberg2012

## section: Main results

This section presents Theorem 1 as the apolar support-recovery and separation theorem: it recovers unordered loading directions from the stated cumulant truncation and excludes a full opposite-arrow fiber on the generic loci. Theorem 2 then records only the additional same-arrow fiber facts on those same loci, including the direct-axis versus latent source-swap issue and the non-orbit obstruction; the section then states the codimension-one exceptional-locus result and the improved real information-order result as separate extensions, explicitly recording the false \(K^\star(m)=2m+2\) conjecture only as refuted.

objs: thm:generic-apolar-arrow-recovery, thm:generic-arrow-recovery-and-fiber-obstruction, def:generic-full-fiber-compatibility, def:worked-compatibility-instances, def:separation-handle, thm:exceptional-locus-codimension-one, def:real-twin-construction-handle, thm:improved-real-information-order

bib: ComonMourrain1996, KoldaBader2009, AnandkumarGeHsuKakadeTelgarsky2014, Landsberg2012, CaiHuangChenEtAl2023, ChenHuangCaiEtAl2024, SchkodaRobevaDrton2024, TramontanoKivvaSalehkaleybarDrtonKiyavash2024, TramontanoKivvaSalehkaleybarDrtonKiyavash2025, ChenPengHuangEtAl2025Direction, CaiGaoHara2025Direction, CaiHara2026SparsestLvLiNGAM

## section: Discussion and extensions

This section discusses what the theorems do and do not identify, how the exceptional locus should be interpreted, and how the results relate to econometric identification from non-Gaussian higher-order structure. It does not present the feasible-fiber predicate, selector, CAD interfaces, or atlas language as an operational method, executable algorithm, or delivered computational contribution.

objs: none

bib: MestersZwiernik2022, Virolainen2024, XieHuangChenEtAl2023, MorinishiShimizu2025, ChenGuPengEtAl2025

## section: Appendix with proofs and auxiliary lemmas

The appendix contains the proof skeletons and auxiliary invariance facts, with the source-swap lemma placed before the theorem proofs that use quotienting. It records the classical algebraic and semialgebraic interfaces as external background only, not as proved, implemented, executable, or load-bearing computational contributions.

objs: lem:admissible-swaps-preserve-direction, def:real-atlas-handle, def:effective-rational-groebner-cad-interface

bib: CoxLittleOShea2015, Collins1975, BochnakCosteRoy1998, BasuPollackRoy2006, Basu2017RAAGSurvey

## section: Appendix verification note

This final appendix note consolidates the machine-checking scope: the frozen assumptions, definitions, lemma, theorem statements, and remark statements are the verified structural layer, while the cited algebraic-decomposition interfaces, real feasibility interfaces, feasible-fiber predicate, direction selector, separated-domain notation, and atlas language are external or conditional inputs rather than delivered computations. It also records that abstract and introduction prose are not part of the verified mathematical layer.

objs: def:global-feasible-fiber-decision, def:direction-selector, def:separated-model-domain, thm:exact-real-exceptional-atlas

bib: BochnakCosteRoy1998, BasuPollackRoy2006
