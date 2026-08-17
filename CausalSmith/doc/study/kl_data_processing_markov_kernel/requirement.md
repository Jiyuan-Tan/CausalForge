# Substrate requirement: kl_data_processing_markov_kernel

## Goal

Formalize the Kullback--Leibler data-processing inequality for passing two finite input laws through the same Markov kernel.

## Provides (API contract)

- A theorem in `Causalean.Mathlib.InformationTheory.Measure` stating that, for finite measures `μ` and `ν` on a countably generated measurable space and a shared Markov kernel `κ`,

      klDiv (μ.bind κ) (ν.bind κ) ≤ klDiv μ ν.

- A composition-product/projection formulation may be the primary internal theorem if it yields the bind theorem with only routine measurable-space and finiteness hypotheses.

Names and the minimal typeclass assumptions may change to fit the existing `KLBind.lean` API, but contraction under a genuinely non-injective shared kernel is required. An injective-map invariance theorem does not satisfy the contract.

## Statement / milestones

1. Prove the KL chain rule or variational/log-sum inequality needed for a shared kernel without assuming the output records the input.
2. Deduce the shared-kernel bind contraction theorem in `ℝ≥0∞`, including the non-absolutely-continuous and infinite-KL cases.
3. Provide the smallest bridge needed for probability kernels used as Gaussian convolution/compression channels.
4. Verify the exported API with zero `sorry`, zero new axioms, a full target build, source grep, and `#print axioms`.

## Standard reference

This is the classical data-processing inequality for relative entropy under a Markov transition kernel (equivalently, monotonicity of KL divergence under stochastic maps).

## Intended reuse

The immediate consumer is `stat_bdd_uniform_log_penalty`: its angular hard-family construction first bounds KL before a common Gaussian-noise/compression channel and then needs contraction for the compressed observation law. The theorem is paper-agnostic and reusable for randomized estimators, privacy channels, coarsening, and observation kernels.

## May assume / must derive

May use Mathlib's Radon--Nikodym, conditional-distribution, `Measure.bind`, kernel composition-product, and KL APIs, plus the existing Causalean results in `Mathlib/InformationTheory/KLBind.lean`, especially the shared-base composition-product chain rule and measurable-embedding invariance. Must derive non-injective shared-kernel contraction; do not assume data processing, a log-sum inequality equivalent to the target, or the paper's angular-packing conclusion.

## Non-goals

Do not formalize the CTY regression class, angular cancellation family, Gaussian bump construction, minimax reduction, or any paper-specific rate. Do not restrict the public theorem to Gaussian kernels unless the fully general theorem is genuinely blocked and the blocker is documented.

## Known building blocks

Start from `Causalean.Mathlib.InformationTheory.KLBind`, `InformationTheory.klDiv_eq_lintegral_klFun`, `Measure.compProd`, `Measure.bind`, conditional distributions, and convexity/Jensen or conditional-expectation tools. The existing `klDiv_map_measurableEmbedding` proves only invariance for injective maps and is not the desired result.
