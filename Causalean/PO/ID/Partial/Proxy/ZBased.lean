/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial identification — Z-based bounds (Theorem 2 / Corollary 2)

Treatment-confounding-proxy bounds of Ghassami-Shpitser-Tchetgen Tchetgen
(arXiv 2304.04374), Section 2.2.

Under Assumptions 3-5 (consistency, latent exchangeability, `proxy_YZ`,
treatment-side bridge `q`), the off-arm potential-outcome mean is sandwiched
by a pair of envelopes for `E[Y | Z, X, A = a]`:

  E[ Lenv(a, X) | A = ¬a ] ≤ E[Y(a) | A = ¬a] ≤ E[ Uenv(a, X) | A = ¬a ]

where `Lenv` (resp. `Uenv`) lower- (resp. upper-) bounds the σ_AZX-conditional
expectation `E[Y | Z, X, A = a]` μ-a.e. on `{A = a}`. The canonical (sharp)
choices are `Lenv(a, x) = min_z E[Y | z, x, A = a]` and the corresponding
`max_z` (paper Remark 5: these automatically sit inside `[inf Y, sup Y]`,
so no clamp is needed here).

## Main results

* `condMeanYofA_Z_bounds` — Theorem 2: envelope sandwich on the conditional
                            target `E[Y(a) | A = ¬a]`.
* `meanYofA_Z_bounds`     — Corollary 2: marginal version of Theorem 2 via
                            the strata identity `meanYofA_eq_strata`.

The deep core is the bridge-substitution identity
`condIntYofA_eq_envelope_arm`, which turns `E[Y(a) | A=¬a]` into a moment of
`E[Y | Z, X, A = a]`; the downstream bounds consume that identity.
-/

import Causalean.PO.ID.Partial.Proxy.Helpers
import Causalean.PO.ID.Partial.Proxy.ZBased.ArmChain

/-! # Z-based proximal partial-identification bounds

This file proves the Z-only proximal partial-identification bounds for
off-arm and marginal counterfactual means. It consumes the arm-swap
bridge-substitution lemmas from `ZBased.ArmChain`, where the treatment bridge
`q` and the Z-outcome envelope move `∫_{A != a} Y(a)` to observable envelope
integrals.

Main declarations:
* `condMeanYofA_Z_bounds` is the Theorem 2 conditional sandwich for
  `condMeanYofA`.
* `meanYofA_Z_bounds` is the Corollary 2 marginal sandwich, using
  `meanYofA_eq_strata` to add the consistency-identified on-arm contribution.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POProximalSystem

variable {P : POSystem}
  {γ_X γ_Z γ_W γ_U : Type*}
  [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
  [MeasurableSpace γ_W] [MeasurableSpace γ_U]
  {S : POProximalSystem P γ_X γ_Z γ_W γ_U}
  {μ : Measure P.Ω} [IsFiniteMeasure μ] [StandardBorelSpace P.Ω]

/-! ### Theorem 2: conditional-target envelope sandwich -/

/-- **Theorem 2** (Ghassami-Shpitser-Tchetgen Tchetgen, arXiv 2304.04374).
Under the Z-based assumption bundle, for `a ∈ {0, 1}`,
  `E[Lenv(a, X) | A = ¬a] ≤ E[Y(a) | A = ¬a] ≤ E[Uenv(a, X) | A = ¬a]`,
where the conditional expectation `E[· | A = ¬a]` is encoded as a normalised
integral over `{A ≠ a}`. The sharp instance is
`Lenv(a,x) = min_z E[Y|z,x,A=a]`, `Uenv(a,x) = max_z E[Y|z,x,A=a]`. -/
theorem condMeanYofA_Z_bounds
    (HA : POProximalSystem.ZBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvZ μ a Lenv) (hU : S.IsUpperEnvZ μ a Uenv)
    (hLInt : Integrable (fun ω => Lenv (a, S.X ω)) μ)
    (hUInt : Integrable (fun ω => Uenv (a, S.X ω)) μ)
    (hL_q :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hU_q :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hL_L :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ)
    (hU_L :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ)
    (hμpos : 0 < (μ {ω | S.A ω ≠ a}).toReal) :
    (μ {ω | S.A ω ≠ a}).toReal⁻¹ * ∫ ω in {ω | S.A ω ≠ a}, Lenv (a, S.X ω) ∂μ
      ≤ S.condMeanYofA μ a
    ∧ S.condMeanYofA μ a ≤
      (μ {ω | S.A ω ≠ a}).toReal⁻¹ * ∫ ω in {ω | S.A ω ≠ a}, Uenv (a, S.X ω) ∂μ := by
  -- Both sides are obtained from the envelope chains by multiplying through
  -- by the positive scalar `(μ {A ≠ a}).toReal⁻¹`.
  have hinv_nn : 0 ≤ (μ {ω | S.A ω ≠ a}).toReal⁻¹ := inv_nonneg.mpr hμpos.le
  have hL_int := S.envelope_le_condIntYofA_arm HA a hAY hL hLInt hL_q hL_L
  have hU_int := S.condIntYofA_le_envelope_arm HA a hAY hU hUInt hU_q hU_L
  refine ⟨?_, ?_⟩
  · -- Lower bound: scale `hL_int` by `(μ {A ≠ a}).toReal⁻¹`.
    have := mul_le_mul_of_nonneg_left hL_int hinv_nn
    simpa [POProximalSystem.condMeanYofA] using this
  · -- Upper bound: scale `hU_int` by `(μ {A ≠ a}).toReal⁻¹`.
    have := mul_le_mul_of_nonneg_left hU_int hinv_nn
    simpa [POProximalSystem.condMeanYofA] using this

/-! ### Corollary 2: marginal-target envelope sandwich -/

/-- **Corollary 2** (Ghassami-Shpitser-Tchetgen Tchetgen, arXiv 2304.04374).
Marginal version of Theorem 2:
  `∫_{A=¬a} Lenv(a,X) dμ + ∫_{A=a} Y dμ ≤ E[Y(a)] ≤ ∫_{A=¬a} Uenv(a,X) dμ + ∫_{A=a} Y dμ`.

Obtained from `condMeanYofA_Z_bounds` by `meanYofA_eq_strata`: the
`{A = a}`-stratum integral is point-identified via consistency, so only the
`{A = ¬a}`-stratum needs the envelope. -/
theorem meanYofA_Z_bounds
    (HA : POProximalSystem.ZBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvZ μ a Lenv) (hU : S.IsUpperEnvZ μ a Uenv)
    (hLInt : Integrable (fun ω => Lenv (a, S.X ω)) μ)
    (hUInt : Integrable (fun ω => Uenv (a, S.X ω)) μ)
    (hL_q :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hU_q :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hL_L :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ)
    (hU_L :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ) :
    (∫ ω in {ω | S.A ω ≠ a}, Lenv (a, S.X ω) ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ)
      ≤ S.meanYofA μ a
    ∧ S.meanYofA μ a ≤
      (∫ ω in {ω | S.A ω ≠ a}, Uenv (a, S.X ω) ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ) := by
  -- `meanYofA = ∫_{A=¬a} Y(a) + ∫_{A=a} Y` by `meanYofA_eq_strata`.
  -- Then sandwich the off-arm `∫_{A=¬a} Y(a)` with the envelope chains.
  have hsplit := POProximalSystem.meanYofA_eq_strata (S := S) (μ := μ)
    HA.consistency a hAY (HA.integrable_YofA a)
  have hL_int := S.envelope_le_condIntYofA_arm HA a hAY hL hLInt hL_q hL_L
  have hU_int := S.condIntYofA_le_envelope_arm HA a hAY hU hUInt hU_q hU_L
  refine ⟨?_, ?_⟩
  · rw [hsplit]; linarith
  · rw [hsplit]; linarith

end POProximalSystem

end PO
end Causalean
