# Separating Latent-Source Arrows with Cumulants

With a fixed number of middle source slots and an axis normalization, higher-order population cumulants generically separate the two bivariate latent linear non-Gaussian arrow conventions.

---

## Overview

- We study a bivariate latent linear non-Gaussian model with \(m\) middle source slots.
- The maintained input is an axis-normalized representation class for \(X\to Y\) and \(Y\to X\).
- The observable object is the truncated joint cumulant vector through order \(L\).
- The question is whether the same cumulants can arise from the opposite arrow convention.
- The main answer: generically, order \(2m+2\) recovers the loading support and excludes the opposite fiber.
- For \(m\ge3\), generic real opposite-fiber exclusion already holds at order \(2m+1\).

---

## Motivation

- In Gaussian linear models, covariance information is symmetric in ways that often leave direction unresolved.
- Non-Gaussianity supplies higher-order structure that can break that symmetry.
- LiNGAM uses this asymmetry under linear non-Gaussian disturbances; latent sources make the direction problem harder.
- We ask what the population cumulants alone establish once the number of source slots and axis convention are fixed.
- This is a representation-level identification question for a structured econometric model class.

---

## Running example

- Think of \(X\) and \(Y\) as two economic outcomes linked by one direct channel and several latent shocks.
- A forward representation assigns one direct \(X\to Y\) loading, one fixed vertical-axis source, and \(m\) middle source slots.
- A reverse representation assigns the symmetric \(Y\to X\) convention.
- The econometric question is whether the observed higher-order cumulants support both recursive specifications.
- The source count \(m\) is treated as a maintained modeling input.

@figure axis-normalized-arrows: Box-and-arrow schematic with observed boxes X and Y, a forward direct arrow X to Y, middle latent source boxes pointing to both X and Y, and fixed axis source boxes pointing to one observed variable each.

---

## Related literature

- Pearl (2009), Spirtes et al. (2001), Peters et al. (2017), and Richardson and Spirtes (2002) give the structural and graphical background.
- Shimizu et al. (2006) connect linear non-Gaussian structure to causal discovery through LiNGAM.
- Hoyer et al. (2008) and Salehkaleybar et al. (2020) study latent-variable LiNGAM settings.
- Brillinger (1969), McCullagh (1987), Comon and Mourrain (1996), and Landsberg (2012) supply the cumulant and binary-form tools.
- Chen et al. (2025) use higher-order cumulants for direction under latent confounding.
- We characterize the generic opposite-fiber geometry for the fixed-source, axis-normalized representation class.

---

## Setup

- There are \(m+2\) latent source slots \(S_0,\ldots,S_{m+1}\).
- The \(m\) middle slots have finite slopes and can load on both observed coordinates.
- The two remaining slots are fixed by the axis normalization.
- Sources are centered, mutually independent, non-Gaussian, and have finite moments through the retained order.
- Independence makes cumulants add across source slots.
- Non-Gaussianity makes higher-order cumulants informative beyond covariance.

@formal ass:independent-sources

---

## Axis conventions

- In the forward convention, the direct loading has slope \(\gamma\), the middle slopes are \(\rho_1,\ldots,\rho_m\), and the vertical-axis source is fixed.
- In the reverse convention, the direct loading has slope \(\delta\), the middle slopes are \(\sigma_1,\ldots,\sigma_m\), and the horizontal-axis source is fixed.
- Genericity means distinct finite slopes, nonzero direct slope, and nonzero retained source cumulants.
- In the running example, this rules out coincident shock directions and a zero direct channel.

@formal ass:forward-axis-model

@formal ass:reverse-axis-model

---

## Cumulant data

- \(T_L(P)\), the truncated cumulant vector, collects joint cumulants of \(X\) and \(Y\) from orders \(2\) through \(L\).
- Each source contributes its order-\(r\) cumulant weight times a monomial in its loading vector.
- The forward and reverse cumulant maps encode these contributions as polynomial maps.
- A fiber is the set of parameters that produce the same truncated cumulant vector.
- Direction separation means the opposite-arrow fiber is empty.

@figure cumulant-pipeline: Box-and-arrow schematic with boxes for latent sources and loadings, polynomial cumulant map, truncated cumulant vector, forward fiber, and reverse fiber.

---

## Key idea

- The cumulant blocks behave like a simultaneous decomposition of binary forms.
- At the apolar order \(2m+2\), the equations recover the unordered set of loading directions.
- The recovered support contains the fixed axis in a way determined by the arrow convention.
- For generic parameters, the opposite convention would require the incompatible fixed-axis pattern.
- This turns higher-order cumulants into a population separation device for the two representation fibers.

---

## Main result I

@informal thm:generic-apolar-arrow-recovery: At order \(2m+2\), generic parameters have their unordered loading-slope support recovered and their full opposite-arrow cumulant fiber empty.

- The result applies on relatively Zariski-open dense loci.
- These loci contain real feasible neighborhoods, so the algebraic statement has real model points.
- In the running example, the higher-order cumulants recover the shock-loading directions needed to rule out the competing recursive axis convention.

@formal thm:generic-apolar-arrow-recovery

---

## Main result II

@informal thm:generic-arrow-recovery-and-fiber-obstruction: At order \(2m+2\), generic opposite-arrow fibers are empty, while same-arrow fibers retain the stated direct-slot versus middle-slot ambiguity.

- The arrow is separated at the representation level.
- The unordered loading-slope multiset is pinned down.
- Same-arrow parametrization still permits ambiguity beyond admissible middle-source relabelling.
- For \(m\ge2\), the same-arrow fiber has exact relative Zariski dimension \(\frac{m(m-1)}{2}\).

@formal thm:generic-arrow-recovery-and-fiber-obstruction

---

## Exceptional locus

@informal thm:exceptional-locus-codimension-one: At order \(2m+2\), the closure of cumulant vectors compatible with both arrow conventions has codimension exactly \(1\) in each arrow image variety.

- The compatibility set is a property of the truncated cumulant vector.
- Its preimages are exactly the generic same-arrow parameters whose cumulants retain a full opposite-arrow representation.
- For \(m=1\) and \(m=2\), the theorem records explicit incidence systems.
- For \(m\ge2\), the compatibility geometry has codimension one rather than codimension \(m\).

@formal thm:exceptional-locus-codimension-one

---

## Information order

@informal thm:improved-real-information-order: For \(m\ge3\), order \(2m+1\) is sufficient for generic real exclusion of the opposite arrow, so \(K^\star(m)\le 2m+1\).

- The apolar theorem uses order \(2m+2\) to recover loading support.
- The real separation target is weaker: it asks only whether the opposite real feasible fiber is empty.
- For \(m\ge3\), generic real separation reaches that target one order earlier.
- Thus \(2m+1\) is enough for generic real arrow separation, while \(2m+2\) supports loading-support recovery.

@formal thm:improved-real-information-order

---

## Proof sketch

- First, independence converts source contributions into additive cumulant blocks.
- Second, the order-\(2m+2\) cumulants are organized as binary forms with \(m+2\) loading directions.
- Third, apolar equations identify the unique support-annihilator on the generic loci.
- Fourth, the recovered support reveals which fixed axis belongs to the representation.
- Finally, the opposite-arrow convention would impose the other fixed-axis pattern, giving an empty opposite fiber generically.

---

## Compatibility geometry

- The exceptional locus is studied by comparing simultaneous forward and reverse decompositions.
- The comparison keeps the axis slots fixed and quotients only the middle-source label symmetry.
- The resulting dimension calculation gives a single algebraic compatibility condition in each arrow image.
- For small \(m\), we record explicit incidence systems that describe the same compatibility event.
- This explains why generic separation coexists with a codimension-one family admitting both conventions.

---

## Limitations and future work

@informal thm:exact-real-exceptional-atlas: A future direction is a finite computable semialgebraic atlas that exactly labels real forward and reverse feasible fibers for every fixed \(m\).

- The current results are population statements about truncated cumulants.
- The maintained inputs are the source count \(m\) and the axis-normalized representation class.
- Empirical use requires additional work on cumulant estimation, weak higher-order signal, and near-exceptional parameters.
- The finite-sample and numerical decision problems are natural next steps.

---

## Takeaways

- Higher-order cumulants carry directional information in fixed-source latent linear non-Gaussian representations.
- At order \(2m+2\), the generic apolar equations recover unordered loading support and exclude the opposite arrow convention.
- The remaining same-arrow ambiguity is characterized separately from arrow separation.
- The opposite-arrow compatibility closure has codimension exactly one in each arrow image variety.
- For \(m\ge3\), generic real opposite-fiber exclusion already holds at order \(2m+1\).
