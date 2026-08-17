# Substrate requirement: finite_marked_poisson_partition

## Goal
Build a reusable measure-theoretic construction for a finite marked Poisson
experiment split across a finite measurable partition.  It must expose
independent cell restrictions, measurable finite superposition and mark-order
retention, and the relative-entropy calculation needed to transfer a
coordinatewise testing bound back to an exact fixed-size i.i.d. sample.

## Provides (API contract)
For a standard Borel observation space `X`, a probability measure `P` on `X`,
an intensity `lambda ≥ 0`, independent atomless real marks, and a finite
measurable partition `A₀, …, A_M`:

- A concrete probability law for the finite marked Poisson sample whose total
  count has scalar Poisson law of mean `lambda` and whose points, conditional on
  the count, are i.i.d. from `P` with independent marks.
- A measurable restriction map to each partition cell, with the joint law of
  all restrictions equal to the product of independent cell laws.  Each cell
  count must have Poisson mean `lambda * P(A_j)`, and conditional on its count
  its marked points must be i.i.d. from the normalized restriction of `P`.
- A measurable finite superposition map inverse in law to restriction, together
  with a measurable ordering by the atomless marks.  Conditional on total count
  at least `n`, retaining the `n` smallest marks and forgetting the marks must
  have exactly the product law `P^n`.
- A reusable Poisson-mixture KL lemma: for equal-mass finite measures `ν₀,ν₁`
  and common independent marks, the KL divergence of the corresponding
  intensity-`lambda` cell experiments is `lambda * klDiv ν₀ ν₁` in the
  appropriate finite-measure normalization, or a directly usable upper-bound
  form.  It must support the consequence
  `klDiv Q₀ Q₁ ≤ lambda * B` from a one-point bound `klDiv ν₀ ν₁ ≤ B`.

Equivalent canonical formulations are acceptable, but the API must compose to
all four bullets without introducing a paper-specific assumption or hiding the
desired independence/KL conclusion inside a bespoke structure.

## Statement / milestones
Deliver the construction leaves-first: the finite marked sample law; exact
partition restriction and independent cell laws; measurable superposition,
mark ordering, and retained-prefix product law; then the Poisson-mixture KL
bound.  Integrate the complete neutral dependency closure without paper imports.

## Intended reuse
The consumer partitions a bivariate observation space into finitely many
disjoint cells plus their complement, uses intensity `2*n`, retains the `n`
smallest marks, and applies a fixed Borel rule to the retained i.i.d. sample.
Adjacent laws have a common cell mass and agree off one cell.  The substrate
must let the consumer derive independent coordinate experiments, the exact
retained `P^n` law, and the cellwise KL bound `2*n*D_j`; the paper-specific
angular packing, decoder, and minimax assembly remain outside this study.

## May assume / must derive
- May assume standard-Borel instances, measurability of the finite partition,
  probability of `P`, and atomlessness/continuity of the mark law.
- Must derive Poisson splitting/thinning, restriction independence, measurable
  finite superposition and ordering, retained-prefix law, and the KL mixture
  identity from ordinary Mathlib/Causalean measure and scalar-Poisson APIs.
- No `sorry`, custom axioms, paper theorem, or substrate gate may be used.

## Non-goals
- No spatial topology, geometry, angular packing, regression law, estimator,
  minimax rate, or paper namespace.
- No locally finite infinite point-process theory beyond what the finite-count,
  finite-partition marked experiment needs.
- Do not weaken exact independence or exact retained-product-law claims to
  marginal-only statements.

## Known building blocks
- `Mathlib.Probability.Distributions.Poisson` for `poissonMeasure` and scalar
  Poisson calculations.
- `Mathlib.Probability.ProductMeasure` and
  `Mathlib.MeasureTheory.Constructions.Pi` for product and i.i.d. stream laws.
- General `Measure.map`, `Measure.prod`, finite products, kernels, and existing
  `MeasureTheory.klDiv` chain/product lemmas.
- The current run has already verified a neutral leaf construction consisting
  of a Poisson count paired with an infinite i.i.d. observation stream and the
  theorem that every finite prefix maps to the exact product law.  This may be
  reused only after extraction into a neutral temporary substrate module; the
  study must not import the paper research module.

## Standard reference
Standard marked-Poisson-process facts: independent restrictions on disjoint
measurable sets, Poisson thinning/splitting and superposition, conditional i.i.d.
points given the count, and the KL formula for Poisson point-process laws.
