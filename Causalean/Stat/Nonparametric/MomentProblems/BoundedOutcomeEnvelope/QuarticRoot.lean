/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.MomentAlgebra

/-!
# Quartic root selecting the bounded-outcome residual envelope

This file proves the root facts used by `BoundedOutcomeEnvelope.Defs` to define the envelope
maximizer. The tangent-strength envelope `ρ(v) = momentEnvelope μᵥ (v²)` is selected by the
maximizing support parameter `μᵥ`, which is the unique root of the FOC quartic
`envelopeQuartic t q = t⁴ − 2t³ + 2q t² − 2q² t + q²` inside the open interval `(q, v)` with
`q = v²`.  This file proves that root exists and is unique.

The two endpoint sign facts are elementary polynomial identities:

* `envelopeQuartic q q = q² (1 − q)² > 0`  (`envelopeQuartic_pos_at_q`);
* `envelopeQuartic v (v²) = −2 v³ (v − 1)² < 0`  (`envelopeQuartic_neg_at_v`).

Because `t ↦ envelopeQuartic t q` is a continuous polynomial with `q = v² < v`, the intermediate
value theorem produces a root in `(q, v)` (`interior_quartic_exists`).  The derivative
`4 t³ − 6 t² + 4 q t − 2 q²` is strictly negative on `(q, v)`, so the quartic is strictly
antitone there; hence the root is unique (`interior_quartic_unique_root`).

These facts feed `Defs.lean`, which uses the (unique) root to define `maximizingRoot` and
`rhoEnvelope`.
-/

namespace Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope

open Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra
open Set

/-- `envelopeQuartic q q = q² (1 − q)² > 0` for `q ∈ (0,1)`. This is the positive endpoint of the
sign change that locates the interior root. -/
theorem envelopeQuartic_pos_at_q (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < envelopeQuartic q q := by
  have hid : envelopeQuartic q q = q ^ 2 * (1 - q) ^ 2 := by
    unfold envelopeQuartic; ring
  rw [hid]
  have h1 : (0 : ℝ) < 1 - q := by linarith
  positivity

/-- `envelopeQuartic v (v²) = −2 v³ (v − 1)² < 0` for `v ∈ (0,1)`. This is the negative endpoint of
the sign change (at `t = v = √q`) that locates the interior root. -/
theorem envelopeQuartic_neg_at_v (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    envelopeQuartic v (v ^ 2) < 0 := by
  have hid : envelopeQuartic v (v ^ 2) = -(2 * v ^ 3) * (v - 1) ^ 2 := by
    unfold envelopeQuartic; ring
  rw [hid]
  have hne : (v - 1) ≠ 0 := by intro h; apply absurd hv1; linarith [sub_eq_zero.mp h]
  have hsq : 0 < (v - 1) ^ 2 := by positivity
  have hpos : 0 < 2 * v ^ 3 := by positivity
  nlinarith [mul_pos hpos hsq]

/-- The continuous polynomial `t ↦ envelopeQuartic t q`. -/
theorem continuous_envelopeQuartic (q : ℝ) :
    Continuous (fun t => envelopeQuartic t q) := by
  unfold envelopeQuartic; fun_prop

/-- **Derivative of the quartic.** `d/dt envelopeQuartic t q = 4 t³ − 6 t² + 4 q t − 2 q²`. -/
theorem hasDerivAt_envelopeQuartic (t q : ℝ) :
    HasDerivAt (fun s => envelopeQuartic s q)
      (4 * t ^ 3 - 6 * t ^ 2 + 4 * q * t - 2 * q ^ 2) t := by
  unfold envelopeQuartic
  -- Sum of monomials; assemble from `hasDerivAt_pow`, `const_mul`, `add`/`sub`.
  have e1 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    simpa using hasDerivAt_pow 4 t
  have hp3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    simpa using hasDerivAt_pow 3 t
  have e2 := hp3.const_mul (2 : ℝ)
  have hp2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have e3 := hp2.const_mul (2 * q)
  have e4 : HasDerivAt (fun s : ℝ => (2 * q ^ 2) * s) (2 * q ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * q ^ 2)
  have h := (((e1.sub e2).add e3).sub e4).add_const (q ^ 2)
  convert h using 1
  ring

/-- **Interior existence.** For `v ∈ (0,1)` and `q = v²`, the quartic has a root strictly inside
`(v², v)`. Proof: the sign change `envelopeQuartic (v²) (v²) > 0`, `envelopeQuartic v (v²) < 0`
plus continuity, via the intermediate value theorem (`intermediate_value_Ioo'`). -/
theorem interior_quartic_exists (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    ∃ u ∈ Ioo (v ^ 2) v, envelopeQuartic u (v ^ 2) = 0 := by
  have hqv : v ^ 2 < v := by nlinarith
  have hpos : 0 < envelopeQuartic (v ^ 2) (v ^ 2) :=
    envelopeQuartic_pos_at_q (v ^ 2) (by positivity) (by nlinarith)
  have hneg : envelopeQuartic v (v ^ 2) < 0 := envelopeQuartic_neg_at_v v hv0 hv1
  have hcont : ContinuousOn (fun t => envelopeQuartic t (v ^ 2)) (Icc (v ^ 2) v) :=
    (continuous_envelopeQuartic (v ^ 2)).continuousOn
  have hmem : (0 : ℝ) ∈ Ioo (envelopeQuartic v (v ^ 2)) (envelopeQuartic (v ^ 2) (v ^ 2)) :=
    ⟨hneg, hpos⟩
  have hsub := intermediate_value_Ioo' (le_of_lt hqv) hcont hmem
  obtain ⟨u, hu, hfu⟩ := hsub
  exact ⟨u, hu, hfu⟩

/-- **Strict negativity of the derivative on `(v², v)`.** For `v ∈ (0,1)` and `t ∈ (v², v)`,
`4 t³ − 6 t² + 4 v² t − 2 v⁴ < 0`.  (This is the derivative of `envelopeQuartic · (v²)`.)
Proof: `nlinarith` from `v² < t`, `t < v`, `0 < v`, `v < 1`. -/
theorem envelopeQuartic_deriv_neg (v t : ℝ) (hv0 : 0 < v) (hv1 : v < 1)
    (ht1 : v ^ 2 < t) (ht2 : t < v) :
    4 * t ^ 3 - 6 * t ^ 2 + 4 * (v ^ 2) * t - 2 * (v ^ 2) ^ 2 < 0 := by
  -- nlinarith with products of the constraint slacks; strengthen hints if needed.
  have hmain :
      4 * t ^ 3 - 6 * t ^ 2 + 4 * (v ^ 2) * t - 2 * (v ^ 2) ^ 2 < 0 := by
    nlinarith [
      mul_pos (sub_pos.2 ht2) (sub_pos.2 ht1),
      mul_pos (sub_pos.2 ht2) hv0,
      mul_pos (sub_pos.2 ht1) hv0,
      mul_pos hv0 hv0,
      sq_nonneg (t - v),
      sq_nonneg (t - v ^ 2),
      mul_pos (mul_pos hv0 hv0) hv0,
      ht1,
      ht2,
      hv0]
  exact (fun _ : v < 1 => hmain) hv1

/-- `t ↦ envelopeQuartic t (v²)` is strictly antitone on `Icc (v²) v`. -/
theorem strictAntiOn_envelopeQuartic (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    StrictAntiOn (fun t => envelopeQuartic t (v ^ 2)) (Icc (v ^ 2) v) := by
  have hqv : v ^ 2 < v := by nlinarith
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_envelopeQuartic (v ^ 2)).continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(hasDerivAt_envelopeQuartic t (v ^ 2)).deriv]
  exact envelopeQuartic_deriv_neg v t hv0 hv1 ht.1 ht.2

/-- **Unique interior root of the FOC quartic.** For `v ∈ (0,1)` (write `q = v²`) there is a unique
`μᵥ ∈ (v², v)` with `envelopeQuartic μᵥ (v²) = 0`.  This `μᵥ` is the envelope maximizer selecting
`ρ(v)`. Existence is `interior_quartic_exists`; uniqueness follows from strict antitonicity
(`strictAntiOn_envelopeQuartic`), whose `InjOn` forces two roots to coincide. -/
theorem interior_quartic_unique_root (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    ∃! u, u ∈ Ioo (v ^ 2) v ∧ envelopeQuartic u (v ^ 2) = 0 := by
  obtain ⟨u, hu, hfu⟩ := interior_quartic_exists v hv0 hv1
  refine ⟨u, ⟨hu, hfu⟩, ?_⟩
  rintro w ⟨hw, hfw⟩
  have hinj := (strictAntiOn_envelopeQuartic v hv0 hv1).injOn
  exact hinj (Ioo_subset_Icc_self hw) (Ioo_subset_Icc_self hu)
    (show envelopeQuartic w (v ^ 2) = envelopeQuartic u (v ^ 2) by rw [hfw, hfu])

end Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope
