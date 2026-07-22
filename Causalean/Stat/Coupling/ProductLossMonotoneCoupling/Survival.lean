/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.FrechetHoeffding

/-!
# Survival functions of a coupling, and the survival-to-cdf bridge

For a coupling `π ∈ Π(μ, ν)` we record the two marginal *survival* functions and
the joint survival function

    `SX s = π{p | s < p.1}`,  `SY t = π{p | t < p.2}`,  `S s t = π{p | s < p.1 ∧ t < p.2}`.

Since `π` is a probability measure, complementation gives `SX = 1 - F` and
`SY = 1 - G`, and inclusion–exclusion on the two half-planes gives
`S = 1 - F - G + H_π`. The point of this file is the resulting **survival gap =
cdf gap** identity

    `S s t - SX s * SY t = H_π s t - F s * G t`,

which is what converts the Fubini computation of `Cov_π` (which naturally
produces survival functions, because the tail indicator `𝟙{s < x}` is a
*survival* indicator) into the Fréchet-gap form used by the optimality theorem.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-- The first marginal survival function of `π`: `SX s = π{p | s < p.1}`. -/
noncomputable def survFst (π : Measure (ℝ × ℝ)) (s : ℝ) : ℝ :=
  (π (Prod.fst ⁻¹' Ioi s)).toReal

/-- The second marginal survival function of `π`: `SY t = π{p | t < p.2}`. -/
noncomputable def survSnd (π : Measure (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (π (Prod.snd ⁻¹' Ioi t)).toReal

/-- The joint survival function of `π`: `S s t = π (Ioi s ×ˢ Ioi t)`, the mass
of the open upper-right quadrant. -/
noncomputable def jointSurv (π : Measure (ℝ × ℝ)) (s t : ℝ) : ℝ :=
  (π (Ioi s ×ˢ Ioi t)).toReal

/-- The first marginal survival function of a coupling is `1 - F`, where
`F = cdf μ`. Proof: `Prod.fst ⁻¹' Ioi s` is the complement of
`Prod.fst ⁻¹' Iic s`, whose `π`-mass is `μ (Iic s) = F s` by `h.map_fst`. -/
lemma survFst_eq (h : IsCoupling π μ ν) (s : ℝ) : survFst π s = 1 - cdf μ s := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  haveI : IsProbabilityMeasure μ := by
    rw [← h.map_fst]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure ν := by
    rw [← h.map_snd]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let A : Set (ℝ × ℝ) := Prod.fst ⁻¹' Iic s
  have hA_meas : MeasurableSet A := measurableSet_Iic.preimage measurable_fst
  have hsurv : Prod.fst ⁻¹' Ioi s = Aᶜ := by
    ext p
    simp [A]
  have hA : π.real A = cdf μ s := by
    rw [cdf_eq_real]
    rw [measureReal_def]
    congr 1
    calc
      π A = (π.map Prod.fst) (Iic s) := by
        rw [Measure.map_apply]
        · exact measurable_fst
        · exact measurableSet_Iic
      _ = μ (Iic s) := by rw [h.map_fst]
  have hcompl := measureReal_add_measureReal_compl (μ := π) hA_meas
  have huniv : π.real (univ : Set (ℝ × ℝ)) = 1 := by simp [Measure.real]
  unfold survFst
  change π.real (Prod.fst ⁻¹' Ioi s) = 1 - cdf μ s
  rw [hsurv]
  linarith

/-- The second marginal survival function of a coupling is `1 - G`, where
`G = cdf ν`. -/
lemma survSnd_eq (h : IsCoupling π μ ν) (t : ℝ) : survSnd π t = 1 - cdf ν t := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  haveI : IsProbabilityMeasure μ := by
    rw [← h.map_fst]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure ν := by
    rw [← h.map_snd]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let B : Set (ℝ × ℝ) := Prod.snd ⁻¹' Iic t
  have hB_meas : MeasurableSet B := measurableSet_Iic.preimage measurable_snd
  have hsurv : Prod.snd ⁻¹' Ioi t = Bᶜ := by
    ext p
    simp [B]
  have hB : π.real B = cdf ν t := by
    rw [cdf_eq_real]
    rw [measureReal_def]
    congr 1
    calc
      π B = (π.map Prod.snd) (Iic t) := by
        rw [Measure.map_apply]
        · exact measurable_snd
        · exact measurableSet_Iic
      _ = ν (Iic t) := by rw [h.map_snd]
  have hcompl := measureReal_add_measureReal_compl (μ := π) hB_meas
  have huniv : π.real (univ : Set (ℝ × ℝ)) = 1 := by simp [Measure.real]
  unfold survSnd
  change π.real (Prod.snd ⁻¹' Ioi t) = 1 - cdf ν t
  rw [hsurv]
  linarith

/-- **Inclusion–exclusion.** The joint survival function of a coupling is
`S s t = 1 - F s - G t + H_π s t`. Proof: `Ioi s ×ˢ Ioi t` is the complement of
`(Prod.fst ⁻¹' Iic s) ∪ (Prod.snd ⁻¹' Iic t)`, and the mass of that union is
`F s + G t - H_π s t` by `measureReal_union_add_inter`, the intersection being
the lower-left quadrant `Iic s ×ˢ Iic t`. -/
lemma jointSurv_eq (h : IsCoupling π μ ν) (s t : ℝ) :
    jointSurv π s t = 1 - cdf μ s - cdf ν t + jointCdf π s t := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  haveI : IsProbabilityMeasure μ := by
    rw [← h.map_fst]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure ν := by
    rw [← h.map_snd]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let A : Set (ℝ × ℝ) := Prod.fst ⁻¹' Iic s
  let B : Set (ℝ × ℝ) := Prod.snd ⁻¹' Iic t
  have hA_meas : MeasurableSet A := measurableSet_Iic.preimage measurable_fst
  have hB_meas : MeasurableSet B := measurableSet_Iic.preimage measurable_snd
  have hsurv : Ioi s ×ˢ Ioi t = (A ∪ B)ᶜ := by
    ext p
    simp [A, B, Set.mem_prod]
  have hquad : Iic s ×ˢ Iic t = A ∩ B := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, hp.2⟩
    · intro hp
      exact ⟨hp.1, hp.2⟩
  have hA : π.real A = cdf μ s := by
    rw [cdf_eq_real]
    rw [measureReal_def]
    congr 1
    calc
      π A = (π.map Prod.fst) (Iic s) := by
        rw [Measure.map_apply]
        · exact measurable_fst
        · exact measurableSet_Iic
      _ = μ (Iic s) := by rw [h.map_fst]
  have hB : π.real B = cdf ν t := by
    rw [cdf_eq_real]
    rw [measureReal_def]
    congr 1
    calc
      π B = (π.map Prod.snd) (Iic t) := by
        rw [Measure.map_apply]
        · exact measurable_snd
        · exact measurableSet_Iic
      _ = ν (Iic t) := by rw [h.map_snd]
  have hAB : π.real (A ∩ B) = jointCdf π s t := by
    unfold jointCdf
    change π.real (A ∩ B) = π.real (Iic s ×ˢ Iic t)
    rw [hquad]
  have hinc := measureReal_union_add_inter (μ := π) (s := A) (t := B) hB_meas
  have hcompl := measureReal_add_measureReal_compl (μ := π) (hA_meas.union hB_meas)
  have huniv : π.real (univ : Set (ℝ × ℝ)) = 1 := by simp [Measure.real]
  unfold jointSurv
  change π.real (Ioi s ×ˢ Ioi t) = 1 - cdf μ s - cdf ν t + jointCdf π s t
  rw [hsurv]
  linarith

/-- **Survival gap = cdf gap.** For any coupling `π` of `(μ, ν)`,

    `S s t - SX s * SY t = H_π s t - F s * G t`.

This is pure algebra from `survFst_eq`, `survSnd_eq` and `jointSurv_eq`:
`(1 - F - G + H) - (1 - F)(1 - G) = H - F·G`. It is the reason the Fubini
computation, which produces survival functions, lands on the Fréchet gap. -/
lemma surv_gap_eq (h : IsCoupling π μ ν) (s t : ℝ) :
    jointSurv π s t - survFst π s * survSnd π t
      = jointCdf π s t - cdf μ s * cdf ν t := by
  rw [survFst_eq h, survSnd_eq h, jointSurv_eq h]
  ring

end Causalean.Stat
