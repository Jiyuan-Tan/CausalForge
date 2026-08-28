# When Higher Cumulants Choose an Arrow

With fixed middle source slots and a maintained axis normalization, population cumulants generically separate the two latent-source arrow conventions.

---

## Higher cumulants can rule out the opposite representation

@informal thm:generic-apolar-arrow-recovery: At order \(2m+2\), generic cumulants recover the unordered loading support and have an empty opposite-arrow fiber.

- The paper studies a bivariate latent linear non-Gaussian model with \(m\) middle source slots.
- The target is representation-level: can the same truncated cumulants come from the opposite axis-normalized arrow?
- The answer is generically no at the apolar order \(2m+2\).
- This matters because covariance-level information is symmetric, while higher cumulants retain directional structure.
- The result is population algebra: it identifies what information is present before sampling questions enter.

---

## A concrete econometric picture

- Think of two observed outcomes, \(X\) and \(Y\), driven by independent non-Gaussian shocks.
- Some shocks load mainly through the coordinate axes; \(m\) middle source slots load on both variables.
- The analyst maintains the number \(m\) and the axis normalization.
- The competing explanations are \(X\to Y\) and \(Y\to X\), each with the same number of source slots.
- The question is whether the population cumulants can support both explanations.

@figure bivariate-latent-sources: Box-and-arrow schematic with independent source boxes feeding \(X\) and \(Y\), plus competing labeled arrows \(X\to Y\) and \(Y\to X\).

---

## The maintained class fixes the comparison

- A right-arrow representation has a direct slope \(\gamma\), middle slopes \(\rho_1,\ldots,\rho_m\), and one fixed vertical-axis source.
- A left-arrow representation has a direct slope \(\delta\), middle slopes \(\sigma_1,\ldots,\sigma_m\), and one fixed horizontal-axis source.
- The middle source slots are exchangeable; the axis slots are part of the normalization.
- Generic means distinct relevant slopes, nonzero direct slope, and nonzero retained source cumulants.
- Real feasibility means the source-cumulant coordinates come from centered non-Gaussian real sources.

---

## Cumulants turn the model into a polynomial map

- The truncated cumulant vector \(T_L(P)\) collects all joint cumulants of \(X\) and \(Y\) from orders \(2\) through \(L\).
- Independence makes each cumulant block additive across source slots.
- Each source contributes its order-\(r\) cumulant weight times a loading-direction monomial.
- Thus each arrow convention defines a polynomial map into cumulant space.
- Directional separation becomes a fiber question: does the opposite polynomial map hit the same cumulant vector?

@figure cumulant-fiber-comparison: Box-and-arrow schematic with right-arrow parameters and left-arrow parameters feeding separate cumulant-map boxes that both point to a common truncated cumulant vector box.

---

## The classical ingredient is apolar recovery

- At \(K=2m+2\), there are \(m+2\) loading directions and enough cumulant orders for binary-form apolarity.
- The apolar equations recover the unordered loading-direction support on a generic locus.
- The recovered support records which fixed axis is present.
- The two arrow conventions place the fixed axis differently.
- That axis pattern is what separates the opposite fiber.

---

## Order \(2m+2\) recovers support and separates arrows

@informal thm:generic-apolar-arrow-recovery: Under the stated generic loci and feasible real neighborhoods, order \(2m+2\) cumulants recover the unordered finite slopes and exclude the opposite arrow fiber.

@formal thm:generic-apolar-arrow-recovery

---

## Same-arrow ambiguity remains structured

@informal thm:generic-arrow-recovery-and-fiber-obstruction: At order \(2m+2\), every generic same-arrow fiber has the recovered unordered slope multiset, while direct-slot and middle-slot swaps can remain outside the admissible middle-source relabelling orbit.

- This distinguishes arrow separation from full parameter recovery.
- The admissible group \(G_m\) only permutes middle source labels.
- The cumulants can also preserve values after swapping a direct slot with a middle slot.
- For \(m\ge2\), the same-arrow fiber has exact relative Zariski dimension \(\frac{m(m-1)}{2}\).
- The recovered object is the loading support needed for directional exclusion.

---

## The same-arrow fiber statement is exact

@formal thm:generic-arrow-recovery-and-fiber-obstruction

---

## Compatibility is a hypersurface, not a generic event

@informal thm:exceptional-locus-codimension-one: At order \(2m+2\), the closure of the cumulant vectors compatible with both arrow conventions has codimension exactly \(1\) in each arrow image variety.

- The exceptional set lives in cumulant space, not only in one parametrization.
- It consists of cumulant vectors with a generic representation on one side and a full representation on the other.
- For \(m=1\) and \(m=2\), the paper records explicit incidence systems \(A_1\) and \(A_2\).
- For \(m\ge2\), the codimension is exactly \(1\), rather than \(m\).
- Econometrically, opposite-arrow compatibility is a lower-dimensional algebraic restriction.

---

## The exceptional-locus statement pins down the geometry

@formal thm:exceptional-locus-codimension-one

---

## Real separation can occur one order earlier

@informal thm:improved-real-information-order: For \(m\ge3\), at order \(2m+1\), generic real feasible parameters have no opposite real feasible representation, so \(K^\star(m)\le 2m+1\).

- The apolar theorem uses \(2m+2\) to recover the full loading support.
- The information-order theorem asks only for generic real exclusion of the opposite arrow.
- Those are different identification targets.
- For \(m\ge3\), generic real arrow separation already holds at \(2m+1\).
- The order \(2m+2\) remains the support-recovery order.

---

## The lower real information-order result is separate

@formal thm:improved-real-information-order

---

## How the proof works in words

- Higher cumulants are organized as a sequence of binary forms.
- A shared loading support produces a common annihilator across several adjacent orders.
- Generic rank conditions make that annihilator unique up to scale.
- The recovered annihilator reveals which coordinate axis belongs to the support.
- The opposite arrow would require the other fixed-axis pattern, so its fiber is empty on the generic locus.

---

## The result sits between LiNGAM and algebraic decomposition

- LiNGAM uses non-Gaussianity to extract directional information from linear structures.
- Hidden source slots make the bivariate direction problem harder than ordinary causal sufficiency.
- Existing higher-cumulant work often uses rank or tensor restrictions for latent structures.
- This paper gives a fixed-\(m\), axis-normalized, representation-level separation theorem.
- The contribution is algebraic econometric identification from population cumulants.

---

## Also in the paper

@informal thm:exact-real-exceptional-atlas: A future research direction is a finite computable semialgebraic atlas that exactly decides real two-arrow feasibility on all generic and boundary branches.

- The paper also records real feasibility language for centered non-Gaussian source cumulants.
- It separates complex generic geometry from real feasible interpretation.
- It records low-dimensional compatibility systems for \(m=1\) and \(m=2\).
- It distinguishes population information from finite-sample estimation.

---

## The takeaways are three distinct identification claims

- At order \(2m+2\), generic cumulants recover the unordered loading support and exclude the opposite axis-normalized arrow.
- At the same order, the exceptional two-arrow compatibility closure has codimension exactly \(1\) in each arrow image variety.
- Same-arrow parametrizations retain structured ambiguity beyond middle-source relabelling.
- For \(m\ge3\), generic real opposite-arrow exclusion already holds at order \(2m+1\).
- The paper establishes the population cumulant geometry for the maintained fixed-source, axis-normalized representation class.
