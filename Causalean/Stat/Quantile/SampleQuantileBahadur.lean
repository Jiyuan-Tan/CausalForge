/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bahadur representation of the sample quantile — DERIVED (umbrella)

Re-export over the three layers of the elementary Bahadur derivation:
* `.Oscillation` — L2 (Chebyshev increment) + L3 (monotone-grid oscillation, crux).
* `.Rate` — L4 (root-`n` rate).
* `.Linearity` — L5 (inversion + Taylor) + L6 (assembly): `sampleQuantile_isAsymLinear`,
  `sampleQuantile_quantileRegularity`.

Existing consumers importing `Causalean.Stat.Quantile.SampleQuantileBahadur` are unaffected.
-/

import Causalean.Stat.Quantile.SampleQuantileBahadur.Linearity

/-! # Sample-Quantile Bahadur Representation

This umbrella module re-exports the derived Bahadur representation for the
ordinary empirical sample quantile. Importing this file brings in the
oscillation, root-`n` rate, inversion, and linearization layers that culminate in
`IIDSample.sampleQuantile_isAsymLinear` and
`IIDSample.sampleQuantile_quantileRegularity`.

The result is a proof that, under `SampleQuantileReg`, the sample quantile has
the classical influence function `(τ - 1{z ≤ q₀}) / f₀` and can be consumed by
the generic `QuantileRegularity.tendsto_normal` theorem.
-/
