/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.PO.Analysis.Regression
import Causalean.PO.ID.Exact.RDD.RDDLimits

/-! # Sharp Regression Discontinuity

This file formalizes sharp regression-discontinuity identification in the
potential-outcome framework. Under consistency, the deterministic cutoff rule,
local support of the running variable on both sides of the cutoff, and
continuity of the treatment-specific regressions, the cutoff effect equals the
difference between the right and left limits of the observed outcome regression.

The proof reduces the sharp cutoff to half-line agreement between observable
and potential-outcome regressions, then invokes the shared one-sided limit
engine for regression-discontinuity designs. -/

namespace Causalean
namespace PO

open Filter MeasureTheory
open scoped Topology

/-- A sharp regression-discontinuity model in the potential-outcome framework.
A unit has a continuous running variable `X`, a deterministic treatment `D` that
switches on exactly when `X` crosses the cutoff `c` (take-up jumps from 0 to 1 at
the cutoff), and a real outcome `Y`. The jump in the outcome regression at the
cutoff identifies the cutoff-local average treatment effect
(`def:po-sharp-rdd-system`). -/
structure POSharpRDDSystem (P : POSystem) where
  /-- Running (forcing) variable `X`. -/
  Xvar : POVar P ℝ
  /-- Binary treatment `D` (deterministic given `X` at the cutoff). -/
  Dvar : POVar P Bool
  /-- Real outcome `Y`. -/
  Yvar : POVar P ℝ
  /-- Cutoff value of the running variable. -/
  c : ℝ
  hYD : Yvar.v ≠ Dvar.v

namespace POSharpRDDSystem

variable {P : POSystem} (S : POSharpRDDSystem P)

/-- Factual running variable `X`. -/
noncomputable def factualX : P.Ω → ℝ := S.Xvar.factual

/-- Factual treatment `D`. -/
noncomputable def factualD : P.Ω → Bool := S.Dvar.factual

/-- Factual outcome `Y`. -/
noncomputable def factualY : P.Ω → ℝ := S.Yvar.factual

/-- Treatment-specific potential outcome `Y(d)`. -/
noncomputable def YofD (d : Bool) : P.Ω → ℝ := S.Yvar.cfUnder S.Dvar d

/-- The factual running variable is measurable. -/
lemma measurable_factualX : Measurable S.factualX := S.Xvar.measurable_factual
/-- The factual treatment is measurable. -/
lemma measurable_factualD : Measurable S.factualD := S.Dvar.measurable_factual
/-- The factual outcome is measurable. -/
lemma measurable_factualY : Measurable S.factualY := S.Yvar.measurable_factual
/-- The treatment-specific potential outcome is measurable. -/
lemma measurable_YofD (d : Bool) : Measurable (S.YofD d) :=
  S.Yvar.measurable_cfUnder S.Dvar d

/-- Factual treatment event `{D = d}`. -/
def dEvent (d : Bool) : Set P.Ω := S.Dvar.event d

/-- The factual treatment event is measurable. -/
lemma measurableSet_dEvent (d : Bool) : MeasurableSet (S.dEvent d) :=
  S.Dvar.measurableSet_event d

/-- Sharp RDD assumptions — def:po-sharp-rdd-assumptions.

The continuity clause is asserted on the treatment-specific regression
representatives `μ_d` at the cutoff, matching the textbook statement.  Two-sided
local support is encoded by demanding that every one-sided open neighborhood
of `c` carries positive `(P.μ.map X)`-mass; this is the formal counterpart of
"`X` has support on both sides of the cutoff arbitrarily close to `c`". -/
structure Assumptions (S : POSharpRDDSystem P) where
  consistency : P.Consistency
  sharpCutoff : ∀ᵐ ω ∂P.μ, S.factualD ω ↔ S.c ≤ S.factualX ω
  mu : Bool → ℝ → ℝ
  nu : ℝ → ℝ
  mu_isReg : ∀ d, IsRegressionFunction P.μ S.factualX (S.YofD d) (mu d)
  nu_isReg : IsRegressionFunction P.μ S.factualX S.factualY nu
  mu_continuousAt : ∀ d, ContinuousAt (mu d) S.c
  support_right : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo S.c (S.c + ε)) ≠ 0
  support_left : ∀ ε > (0 : ℝ),
    (P.μ.map S.factualX) (Set.Ioo (S.c - ε) S.c) ≠ 0
  nu_right_limit_exists : ∃ L : ℝ, Tendsto nu (𝓝[>] S.c) (𝓝 L)
  nu_left_limit_exists : ∃ L : ℝ, Tendsto nu (𝓝[<] S.c) (𝓝 L)

/-- Cutoff-local RDD estimand — by definition the difference of the
treatment-specific regression representatives at the cutoff.  In the standard
reading of `μ_d c = E[Y(d) | X = c]`, this is `E[Y(1) - Y(0) | X = c]`. -/
noncomputable def tau_RDD (hA : S.Assumptions) : ℝ :=
  hA.mu true S.c - hA.mu false S.c

/-- The right-hand limit `lim_{x ↓ c} ν(x)` chosen from the existence witness
of `Assumptions`. -/
noncomputable def nu_right_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nu_right_limit_exists

/-- The left-hand limit `lim_{x ↑ c} ν(x)` chosen from the existence witness
of `Assumptions`. -/
noncomputable def nu_left_limit (hA : S.Assumptions) : ℝ :=
  Classical.choose hA.nu_left_limit_exists

/-- The chosen right-hand observable regression limit is a genuine right-hand
limit at the cutoff. -/
lemma tendsto_nu_right_limit (hA : S.Assumptions) :
    Tendsto hA.nu (𝓝[>] S.c) (𝓝 (S.nu_right_limit hA)) :=
  Classical.choose_spec hA.nu_right_limit_exists

/-- The chosen left-hand observable regression limit is a genuine left-hand
limit at the cutoff. -/
lemma tendsto_nu_left_limit (hA : S.Assumptions) :
    Tendsto hA.nu (𝓝[<] S.c) (𝓝 (S.nu_left_limit hA)) :=
  Classical.choose_spec hA.nu_left_limit_exists

/-! ### Bridge from sharp cutoff + consistency to slice-level identities -/

private lemma factualY_eq_YofD_on_dEvent
    (hC : P.Consistency) (d : Bool) :
    ∀ ω ∈ S.dEvent d, S.factualY ω = S.YofD d ω := by
  intro ω hω
  exact (POVar.cf_eq_factual_on_event hC S.Yvar S.Dvar d S.hYD hω).symm

private lemma factualY_eq_YofD_true_ae_restrict_Ici
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofD true := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.sharpCutoff, self_mem_ae_restrict hslice]
    with ω hsharp hωA
  have hx : S.c ≤ S.factualX ω := hAsub hωA
  have hDprop : S.factualD ω := hsharp.mpr hx
  have hD : S.factualD ω = true := by
    cases hDω : S.factualD ω <;> simp_all
  exact S.factualY_eq_YofD_on_dEvent hA.consistency true ω hD

private lemma factualY_eq_YofD_false_ae_restrict_Iio
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    S.factualY =ᵐ[P.μ.restrict (S.factualX ⁻¹' A)] S.YofD false := by
  have hslice : MeasurableSet (S.factualX ⁻¹' A) :=
    S.measurable_factualX hAmeas
  filter_upwards [ae_restrict_of_ae hA.sharpCutoff, self_mem_ae_restrict hslice]
    with ω hsharp hωA
  have hx : S.factualX ω < S.c := hAsub hωA
  have hnotD : ¬ S.factualD ω := by
    intro hD
    exact (not_le_of_gt hx) (hsharp.mp hD)
  have hD : S.factualD ω = false := by
    cases hDω : S.factualD ω <;> simp_all
  exact S.factualY_eq_YofD_on_dEvent hA.consistency false ω hD

/-! ### Slice-level integral bridges between `ν` and `μ_d` -/

/-- Integral bridge between the chosen observable and treated regression
representatives on right-side measurable slices. -/
private lemma regression_integral_bridge_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.mu true (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nu_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofD true ω ∂P.μ :=
          integral_congr_ae
            (S.factualY_eq_YofD_true_ae_restrict_Ici hA hAsub hAmeas)
    _ = ∫ ω in S.factualX ⁻¹' A, hA.mu true (S.factualX ω) ∂P.μ :=
          (hA.mu_isReg true).integral_preimage_eq A hAmeas

/-- Integral bridge between the chosen observable and untreated regression
representatives on left-side measurable slices. -/
private lemma regression_integral_bridge_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
      = ∫ ω in S.factualX ⁻¹' A, hA.mu false (S.factualX ω) ∂P.μ := by
  calc
    (∫ ω in S.factualX ⁻¹' A, hA.nu (S.factualX ω) ∂P.μ)
        = ∫ ω in S.factualX ⁻¹' A, S.factualY ω ∂P.μ :=
          (hA.nu_isReg.integral_preimage_eq A hAmeas).symm
    _ = ∫ ω in S.factualX ⁻¹' A, S.YofD false ω ∂P.μ :=
          integral_congr_ae
            (S.factualY_eq_YofD_false_ae_restrict_Iio hA hAsub hAmeas)
    _ = ∫ ω in S.factualX ⁻¹' A, hA.mu false (S.factualX ω) ∂P.μ :=
          (hA.mu_isReg false).integral_preimage_eq A hAmeas

/-! ### Pushforward integrability and integral identity -/

private lemma aemeasurable_factualX (S : POSharpRDDSystem P) :
    AEMeasurable S.factualX P.μ := S.measurable_factualX.aemeasurable

/-- Pushforward form of the right-side integral bridge: on every measurable
subset of `Ici c`, integrals of `ν` and `μ_1` agree under the law of `X`. -/
private lemma setIntegral_pushforward_eq_right
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Ici S.c) (hAmeas : MeasurableSet A) :
    (∫ x in A, hA.nu x ∂(P.μ.map S.factualX))
      = ∫ x in A, hA.mu true x ∂(P.μ.map S.factualX) := by
  have hnu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.nu) hAmeas
      hA.nu_isReg.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hmu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.mu true) hAmeas
      (hA.mu_isReg true).measurable.aestronglyMeasurable S.aemeasurable_factualX
  rw [hnu, hmu]
  exact S.regression_integral_bridge_right hA hAsub hAmeas

/-- Pushforward form of the left-side integral bridge. -/
private lemma setIntegral_pushforward_eq_left
    (hA : S.Assumptions) {A : Set ℝ}
    (hAsub : A ⊆ Set.Iio S.c) (hAmeas : MeasurableSet A) :
    (∫ x in A, hA.nu x ∂(P.μ.map S.factualX))
      = ∫ x in A, hA.mu false x ∂(P.μ.map S.factualX) := by
  have hnu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.nu) hAmeas
      hA.nu_isReg.measurable.aestronglyMeasurable S.aemeasurable_factualX
  have hmu :=
    setIntegral_map (μ := P.μ) (g := S.factualX) (f := hA.mu false) hAmeas
      (hA.mu_isReg false).measurable.aestronglyMeasurable S.aemeasurable_factualX
  rw [hnu, hmu]
  exact S.regression_integral_bridge_left hA hAsub hAmeas

/-! ### A.e. agreement of `ν` and `μ_d` on the half-lines -/

/-- `ν` and `μ_1` agree `(P.μ.map X)`-almost everywhere on `Ici c`. -/
private lemma nu_eq_mu_true_ae_restrict_Ici (hA : S.Assumptions) :
    hA.nu =ᵐ[(P.μ.map S.factualX).restrict (Set.Ici S.c)] hA.mu true := by
  set π := P.μ.map S.factualX
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    hA.nu (hA.mu true)
    (hA.nu_isReg.integrable_pushforward S.aemeasurable_factualX).restrict
    ((hA.mu_isReg true).integrable_pushforward S.aemeasurable_factualX).restrict
    ?_
  intro s hs _
  simp_rw [Measure.restrict_restrict (μ := π) hs]
  exact S.setIntegral_pushforward_eq_right hA Set.inter_subset_right
    (hs.inter measurableSet_Ici)

/-- `ν` and `μ_0` agree `(P.μ.map X)`-almost everywhere on `Iio c`. -/
private lemma nu_eq_mu_false_ae_restrict_Iio (hA : S.Assumptions) :
    hA.nu =ᵐ[(P.μ.map S.factualX).restrict (Set.Iio S.c)] hA.mu false := by
  set π := P.μ.map S.factualX
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    hA.nu (hA.mu false)
    (hA.nu_isReg.integrable_pushforward S.aemeasurable_factualX).restrict
    ((hA.mu_isReg false).integrable_pushforward S.aemeasurable_factualX).restrict
    ?_
  intro s hs _
  simp_rw [Measure.restrict_restrict (μ := π) hs]
  exact S.setIntegral_pushforward_eq_left hA Set.inter_subset_right
    (hs.inter measurableSet_Iio)

/-! ### Limits of `ν` at the cutoff coincide with `μ_d c`

Thin wrappers around the generic `RDDLimits.oneSidedLimit_eq_*` engine. -/

/-- Any right-limit of `ν` at `c` coincides with `μ_1 c`. -/
theorem nu_right_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nu (𝓝[>] S.c) (𝓝 L)) :
    L = hA.mu true S.c :=
  RDDLimits.oneSidedLimit_eq_right
    (S.nu_eq_mu_true_ae_restrict_Ici hA)
    (hA.mu_continuousAt true)
    hA.support_right
    h

/-- Any left-limit of `ν` at `c` coincides with `μ_0 c`. -/
theorem nu_left_limit_eq (hA : S.Assumptions) {L : ℝ}
    (h : Tendsto hA.nu (𝓝[<] S.c) (𝓝 L)) :
    L = hA.mu false S.c :=
  RDDLimits.oneSidedLimit_eq_left
    (S.nu_eq_mu_false_ae_restrict_Iio hA)
    (hA.mu_continuousAt false)
    hA.support_left
    h

/-! ### Sharp RDD identification — prop:po-sharp-rdd -/

/-- **Sharp RDD identification at the cutoff** (textbook form).  The
cutoff-local effect equals the difference of the one-sided observable
regression limits at `c`:

    τ_RDD(c) = lim_{x ↓ c} ν(x) - lim_{x ↑ c} ν(x).

The existence of both side limits is part of the `Assumptions` bundle. -/
theorem rdd_identification (hA : S.Assumptions) :
    S.tau_RDD hA = S.nu_right_limit hA - S.nu_left_limit hA := by
  rw [show S.nu_right_limit hA = hA.mu true S.c from
        S.nu_right_limit_eq hA (S.tendsto_nu_right_limit hA),
      show S.nu_left_limit hA = hA.mu false S.c from
        S.nu_left_limit_eq hA (S.tendsto_nu_left_limit hA)]
  rfl

end POSharpRDDSystem

end PO
end Causalean
