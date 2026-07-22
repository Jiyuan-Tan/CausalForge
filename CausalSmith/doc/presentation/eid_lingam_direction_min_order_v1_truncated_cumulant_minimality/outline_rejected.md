# Title

**Causal Direction from Low-Order Cumulants in Latent Linear Non-Gaussian Models**

**Contribution statement.** The paper shows that, in a bivariate latent linear non-Gaussian model with \(m\) latent confounder directions, truncated joint cumulants generically recover the causal arrow, identifies the full opposite-arrow obstruction as a codimension-one exceptional locus, and refutes the proposed universal information order \(K^\star(m)=2m+2\) for \(m\ge 3\).

# Notation

notation_gaps: \(\operatorname{Laws}(\mathbb R^2)\)=ambient class of probability laws used before a dedicated anchored definition, \(\operatorname{Cum}\)=joint cumulant functional used by the cumulant truncation, \(\Theta^{\mathrm{right}}_{m,L},\Theta^{\mathrm{left}}_{m,L}\)=complex parameter spaces for the two cumulant maps, \(\operatorname{ZariskiClosure}\)=closure operator in the ambient complex affine space, \(G_m\)=admissible source-label permutation group, \(B_r\)=complete Bell polynomial converting cumulants to raw moments, \(P_M\)=observational law induced by model \(M\), \(D(M)\)=causal direction attached to a structural model, \(\operatorname{opposite}(b)\)=opposite-arrow involution on \(\{\mathrm{right},\mathrm{left}\}\), \(Q_D\)=support annihilator recovered in the apolar construction, \(D\)=unordered loading-direction set recovered from \(Q_D\), \(J_m\)=elimination ideal used only in the external real-atlas handle.

env_overrides: def:real-atlas-handle=remarkv, def:effective-rational-groebner-cad-interface=remarkv

\(\{S_j\}_{j=0}^{m+1}\) | \(S_0,\ldots,S_{m+1}\) | centered latent source variables | ass:independent-sources  
source independence | \(S_0\perp\cdots\perp S_{m+1}\) | mutual independence of latent sources | ass:independent-sources  
finite cumulant order | \(\mathbb E|S_j|^K<\infty\) | finite moments through the working truncation order | ass:finite-cumulants  
source non-Gaussianity | \(S_j\) non-Gaussian | non-Gaussianity restriction on each source | ass:source-nongaussianity  
observed vector | \((X,Y)^\top\) | bivariate observed outcome vector | ass:forward-axis-model  
forward loadings | \(u_j\) | loading vectors for the \(X\to Y\) axis convention | ass:forward-axis-model  
reverse loadings | \(v_j\) | loading vectors for the \(Y\to X\) axis convention | ass:reverse-axis-model  
forward slopes | \(\gamma,\rho_1,\ldots,\rho_m\) | direct and latent finite slopes in the forward parametrization | ass:forward-noncollinearity  
reverse slopes | \(\delta,\sigma_1,\ldots,\sigma_m\) | direct and latent finite slopes in the reverse parametrization | ass:reverse-noncollinearity  
forward class | \(\mathcal P^{\mathrm{right}}_{m,K}\) | laws admitting the forward latent linear non-Gaussian representation | def:forward-lvlingam-class  
reverse class | \(\mathcal P^{\mathrm{left}}_{m,K}\) | laws admitting the reverse latent linear non-Gaussian representation | def:reverse-lvlingam-class  
truncated cumulant vector | \(T_L(P)\) | joint cumulants of \((X,Y)\) from orders \(2\) through \(L\) | def:truncated-cumulant  
cumulant coordinates | \(\kappa_{r,a}(P)\) | cumulant with \(r-a\) copies of \(X\) and \(a\) copies of \(Y\) | def:truncated-cumulant  
coordinate dimension | \(q_L\) | number of cumulant coordinates through order \(L\) | def:truncated-cumulant  
forward cumulant map | \(\Phi^{\mathrm{right}}_{m,L}\) | polynomial map from forward loadings and source cumulants to \(T_L\) | def:forward-cumulant-map  
forward source cumulants | \(c_{jr}\) | order-\(r\) cumulant weight for forward source \(j\) | def:forward-cumulant-map  
reverse cumulant map | \(\Phi^{\mathrm{left}}_{m,L}\) | polynomial map from reverse loadings and source cumulants to \(T_L\) | def:reverse-cumulant-map  
reverse source cumulants | \(d_{jr}\) | order-\(r\) cumulant weight for reverse source \(j\) | def:reverse-cumulant-map  
forward image variety | \(C^{\mathrm{right}}_{m,L}\) | Zariski closure of the forward cumulant-map image | def:image-varieties  
reverse image variety | \(C^{\mathrm{left}}_{m,L}\) | Zariski closure of the reverse cumulant-map image | def:image-varieties  
forward generic locus | \(\Theta^{\mathrm{right},\circ}_{m,L}\) | nonzero and distinct-slope forward parameter locus | def:generic-parameter-loci  
reverse generic locus | \(\Theta^{\mathrm{left},\circ}_{m,L}\) | nonzero and distinct-slope reverse parameter locus | def:generic-parameter-loci  
forward fiber | \(R^{\mathrm{right}}_{m,L}(t)\) | forward parameters mapping to cumulant vector \(t\) | def:fiber-correspondences  
reverse fiber | \(R^{\mathrm{left}}_{m,L}(t)\) | reverse parameters mapping to cumulant vector \(t\) | def:fiber-correspondences  
source swaps | \(\pi\in G_m\) | permutations of latent source labels that fix the two axis sources | def:admissible-source-swaps  
compatibility locus | \(E_m\) | cumulant vectors with a generic representation on one arrow and some full representation on the other | def:generic-full-fiber-compatibility  
exceptional closure | \(\overline E_m\) | Zariski closure of the generic full-fiber compatibility locus | def:generic-full-fiber-compatibility  
forward exceptional preimage | \(H^{\mathrm{right}}_m\) | forward generic parameters retaining a full opposite-arrow representation | def:generic-full-fiber-compatibility  
reverse exceptional preimage | \(H^{\mathrm{left}}_m\) | reverse generic parameters retaining a full opposite-arrow representation | def:generic-full-fiber-compatibility  
forward real feasible region | \(F^{\mathrm{right}}_{m,L}\) | real forward parameters realizable by centered non-Gaussian sources through order \(L\) | def:real-feasible-regions  
reverse real feasible region | \(F^{\mathrm{left}}_{m,L}\) | real reverse parameters realizable by centered non-Gaussian sources through order \(L\) | def:real-feasible-regions  
information order | \(K^\star(m)\) | minimal truncation order giving generic real arrow separation if such an order exists | def:information-order  
feasible-fiber predicate | \(\operatorname{FeasFiber}^{b}_m(t)\) | atomic-certificate predicate for real feasible fiber nonemptiness | def:global-feasible-fiber-decision  
atomic witnesses | \((w_{jh},z_{jh})\) | finite atomic moment-certificate weights and support points | def:global-feasible-fiber-decision  
raw moments | \(\mu_{jr}\) | raw moments obtained from cumulants by Bell polynomials | def:global-feasible-fiber-decision  
direction selector | \(S_m(t)\) | partial rule selecting \(X\to Y\) or \(Y\to X\) from one-sided feasible-fiber truth values | def:direction-selector  
separated model domain | \(M^{\mathrm{sep}}_{m,K}\) | models whose observed cumulants have exactly one real feasible arrow | def:separated-model-domain  
worked incidence systems | \(A_1,A_2\) | explicit full-fiber compatibility systems for \(m=1\) and \(m=2\) | def:worked-compatibility-instances  
separation handle | quotient-fiber comparison | algebraic comparison of opposite-arrow decompositions after admissible source swaps | def:separation-handle  
real twin handle | \(K_-=2m+1\) twin construction proposition | unproved existence proposition for matching lower-order real forward and reverse parameters | def:real-twin-construction-handle  
real atlas interface | cylindrical atlas interface | cited classical semialgebraic decomposition interface, not a delivered result | def:real-atlas-handle  
effective algebra interface | rational Gröbner-CAD interface | cited general exact symbolic interface, not a delivered result | def:effective-rational-groebner-cad-interface  
generic apolar loci | \(U^{\mathrm{right}}_m,U^{\mathrm{left}}_m\) | Zariski-open dense loci for apolar loading recovery and opposite-arrow exclusion | thm:generic-apolar-arrow-recovery  
divided-power blocks | \(f_r(x,y)\) | binary forms built from cumulant coordinates | thm:generic-apolar-arrow-recovery  

# Sections

## section: Abstract

The abstract will be drafted after the body is fixed. It will state the econometric identification problem, the cumulant order used for generic arrow recovery, the codimension-one obstruction, and the refutation of the proposed universal order claim without presenting the formalization as a contribution.

objs: none

bib: none

## section: Introduction

The introduction will motivate causal direction in bivariate latent-variable linear non-Gaussian models, place the result relative to LiNGAM, hidden-confounding, cumulant, and binary-form identification work, and state the paper’s contribution in non-computational terms. It will include only one factual sentence saying that the formal verification scope is summarized in the appendix verification note.

objs: none

bib: Pearl2009, SpirtesGlymourScheines2001, PetersJanzingScholkopf2017, RichardsonSpirtes2002, HoyerJanzingMooijPetersScholkopf2009, ZhangHyvarinen2009, MooijPetersJanzingZscheischlerScholkopf2016, Comon1994, HyvarinenOja2000, Cardoso1999, KaganLinnikRao1973, ShimizuHyvarinenKanoHoyer2006, HoyerShimizuKerminenPalviainen2008, SalehkaleybarGhassamiKiyavashZhang2020, ChenPengHuangEtAl2025Direction, CaiGaoHara2025Direction, CaiHara2026SparsestLvLiNGAM

## section: Setup and assumptions

This section introduces the bivariate latent linear non-Gaussian law, the forward and reverse axis conventions, the truncated cumulant vector, the two polynomial cumulant maps, the generic parameter loci, admissible source relabellings, and real feasibility. It also fixes the information-order notation while avoiding any claim based on the refuted universal equality.

objs: ass:independent-sources, ass:finite-cumulants, ass:source-nongaussianity, ass:forward-axis-model, ass:reverse-axis-model, ass:forward-noncollinearity, ass:reverse-noncollinearity, ass:forward-nonzero-edge, ass:reverse-nonzero-edge, def:forward-lvlingam-class, def:reverse-lvlingam-class, def:truncated-cumulant, def:forward-cumulant-map, def:reverse-cumulant-map, def:image-varieties, def:generic-parameter-loci, def:fiber-correspondences, def:admissible-source-swaps, def:real-feasible-regions, def:information-order

bib: Brillinger1969, McCullagh1987, Comon1994, HyvarinenOja2000, Cardoso1999, ShimizuHyvarinenKanoHoyer2006, ShimizuInazumiSogawaEtAl2011, TashiroShimizuHyvarinenWashio2014, MaedaShimizu2020, HoyerShimizuKerminenPalviainen2008

## section: Main results

This section presents the identification theorem block as one consolidated story: apolar recovery of the unordered loading directions, generic absence of a full opposite-arrow fiber, the role of direct-axis versus latent source swaps, and the fact that same-arrow fibers are not generally single \(G_m\)-orbits. It then gives the codimension-one exceptional-locus result and the improved real information-order result as separate extensions.

objs: thm:generic-apolar-arrow-recovery, thm:generic-arrow-recovery-and-fiber-obstruction, def:generic-full-fiber-compatibility, def:worked-compatibility-instances, def:separation-handle, thm:exceptional-locus-codimension-one, def:real-twin-construction-handle, thm:improved-real-information-order

bib: Sylvester1851, ComonMourrain1996, KoldaBader2009, AnandkumarGeHsuKakadeTelgarsky2014, Landsberg2012, CaiHuangChenEtAl2023, ChenHuangCaiEtAl2024, SchkodaRobevaDrton2024, TramontanoKivvaSalehkaleybarDrtonKiyavash2024, TramontanoKivvaSalehkaleybarDrtonKiyavash2025, ChenPengHuangEtAl2025Direction, CaiGaoHara2025Direction, CaiHara2026SparsestLvLiNGAM

## section: Discussion and extensions

This section discusses what the theorems do and do not identify, how the exceptional locus should be interpreted, and how the result relates to econometric identification from non-Gaussian higher-order structure. It treats the finite semialgebraic atlas and direction-selector material only as a conditional or future verification interface, explicitly not as an operational contribution of the paper.

objs: def:global-feasible-fiber-decision, def:direction-selector, def:separated-model-domain, remark:thm:exact-real-exceptional-atlas

bib: MestersZwiernik2022, Virolainen2024, XieHuangChenEtAl2023, MorinishiShimizu2025, ChenGuPengEtAl2025, BochnakCosteRoy1998, BasuPollackRoy2006

## section: Appendix with proofs and auxiliary lemmas

The appendix contains the proof skeletons and auxiliary invariance facts, with the source-swap lemma placed before the theorem proofs that use quotienting. It also records the classical algebraic and semialgebraic interfaces as external background only, not as proved or implemented contributions.

objs: lem:admissible-swaps-preserve-direction, def:real-atlas-handle, def:effective-rational-groebner-cad-interface

bib: CoxLittleOShea2015, Collins1975, BochnakCosteRoy1998, BasuPollackRoy2006, Basu2017RAAGSurvey

## section: Appendix verification note

This final appendix note consolidates the machine-checking scope: the frozen assumptions, definitions, lemma, and theorem statements are the verified structural layer, while the cited algebraic-decomposition interfaces, real feasibility interfaces, and atlas language are external or conditional inputs rather than delivered computations. It also records that abstract and introduction prose are not part of the verified mathematical layer.

objs: none

bib: none
