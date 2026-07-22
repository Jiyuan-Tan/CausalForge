/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP CATE minimax: the DP → TV contraction crux

The build-inline hybrid/coupling lemma
`lem:dp_output_tv_contraction`:
`TV(L_{P^n}(M_n), L_{Q^n}(M_n)) ≤ n·TV(P,Q)·{exp(ε_n) - 1 + δ_n}`.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContractionAux

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat

-- @node: lem:dp-output-tv-contraction
/-- **DP → TV contraction (crux).** For any two one-observation laws `P, Q` and any
central-`(ε_n, δ_n)`-DP mechanism `M_n`, the total-variation distance between the
release output laws contracts:
`TV(L_{P^n}(M_n), L_{Q^n}(M_n)) ≤ n · TV(P,Q) · {exp(ε_n) - 1 + δ_n}`,
where the output law is the mixture `(P^n).bind M_n` of the release kernel against
the `n`-fold i.i.d. sample law. -/
lemma dp_output_tv_contraction {d : ℕ} (n : ℕ) (epsN delN : ℝ)
    (P Q : CateLaw d) (M : (Fin n → CateObs d) → Measure ℝ)
    (hiidP : IidSampling P) (hiidQ : IidSampling Q)
    (hdp : CentralDP n epsN delN M) (heps : 0 ≤ epsN) :
    tvDist ((Measure.pi fun _ : Fin n => P.dataMeasure).bind M)
        ((Measure.pi fun _ : Fin n => Q.dataMeasure).bind M)
      ≤ (n : ℝ) * tvDist P.dataMeasure Q.dataMeasure * (Real.exp epsN - 1 + delN) := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hiidP.1
  letI : IsProbabilityMeasure Q.dataMeasure := hiidQ.1
  letI : ∀ s, IsProbabilityMeasure (M s) := hdp.1
  have hM : Measurable M := hdp.2.1
  refine ciSup_le fun Bout => ?_
  obtain ⟨B, hB⟩ := Bout
  let f : (Fin n → CateObs d) → ℝ := fun s => (M s).real B
  have hf : Measurable f := (Measure.measurable_coe hB).ennreal_toReal.comp hM
  let o₀ : CateObs d := ⟨0, 0, fun _ => 0⟩
  have ho₀ : o₀ ∈ sampleSpace d := by simp [o₀, sampleSpace, cube]
  let clip : CateObs d → CateObs d := fun O => if O ∈ sampleSpace d then O else o₀
  have hclip : Measurable clip :=
    Measurable.ite measurableSet_sampleSpace measurable_id measurable_const
  have hclip_mem : ∀ O, clip O ∈ sampleSpace d := by
    intro O
    by_cases hO : O ∈ sampleSpace d <;> simp [clip, hO, ho₀]
  let g : (Fin n → CateObs d) → ℝ := fun s => f (fun j => clip (s j))
  have hg : Measurable g := hf.comp (measurable_pi_lambda _ fun j =>
    hclip.comp (measurable_pi_apply j))
  have h01 : ∀ s, g s ∈ Set.Icc (0 : ℝ) 1 := fun s =>
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hosc : ∀ D D' : Fin n → CateObs d,
      (∃ k, ∀ j, j ≠ k → D j = D' j) →
        |g D - g D'| ≤ Real.exp epsN - 1 + delN := by
    intro D D' hadj
    have hadj_clip :
        ReplacementAdjacent (fun j => clip (D j)) (fun j => clip (D' j)) := by
      rcases hadj with ⟨k, hk⟩
      exact ⟨k, fun j hj => congrArg clip (hk j hj)⟩
    have hforward := hdp.2.2 (fun j => clip (D j)) (fun j => clip (D' j))
      (fun j => hclip_mem (D j)) (fun j => hclip_mem (D' j)) hadj_clip B hB
    have hreverse := hdp.2.2 (fun j => clip (D' j)) (fun j => clip (D j))
      (fun j => hclip_mem (D' j)) (fun j => hclip_mem (D j))
      (by rcases hadj_clip with ⟨k, hk⟩
          exact ⟨k, fun j hj => (hk j hj).symm⟩) B hB
    have hcoef : 0 ≤ Real.exp epsN - 1 := sub_nonneg.mpr (Real.one_le_exp heps)
    have hmul_forward :
        (Real.exp epsN - 1) * (M (fun j => clip (D' j))).real B ≤
          Real.exp epsN - 1 := by
      simpa using mul_le_mul_of_nonneg_left
        (measureReal_le_one (μ := M (fun j => clip (D' j))) (s := B)) hcoef
    have hmul_reverse :
        (Real.exp epsN - 1) * (M (fun j => clip (D j))).real B ≤
          Real.exp epsN - 1 := by
      simpa using mul_le_mul_of_nonneg_left
        (measureReal_le_one (μ := M (fun j => clip (D j))) (s := B)) hcoef
    rw [abs_le]
    constructor <;> dsimp [g, f] <;> linarith
  letI : Nonempty (CateObs d) := ⟨⟨0, 0, fun _ => 0⟩⟩
  have hhybrid := pi_integral_hybrid_tv_bound P.dataMeasure Q.dataMeasure
    g hg h01 (Real.exp epsN - 1 + delN) hosc
  have hsP : ∀ᵐ O ∂P.dataMeasure, O ∈ sampleSpace d := by
    change sampleSpace d ∈ ae P.dataMeasure
    exact mem_ae_iff.mpr (iidSampling_ae_sampleSpace hiidP)
  have hsQ : ∀ᵐ O ∂Q.dataMeasure, O ∈ sampleSpace d := by
    change sampleSpace d ∈ ae Q.dataMeasure
    exact mem_ae_iff.mpr (iidSampling_ae_sampleSpace hiidQ)
  have hsPiP : ∀ᵐ s ∂Measure.pi (fun _ : Fin n => P.dataMeasure),
      ∀ j, s j ∈ sampleSpace d :=
    ((Filter.eventually_all_finite
      (Set.finite_univ : (Set.univ : Set (Fin n)).Finite)).2 fun j _ =>
        (Measure.tendsto_eval_ae_ae
          (μ := fun _ : Fin n => P.dataMeasure) (i := j)).eventually hsP).mono
      fun s hs j => hs j (Set.mem_univ j)
  have hsPiQ : ∀ᵐ s ∂Measure.pi (fun _ : Fin n => Q.dataMeasure),
      ∀ j, s j ∈ sampleSpace d :=
    ((Filter.eventually_all_finite
      (Set.finite_univ : (Set.univ : Set (Fin n)).Finite)).2 fun j _ =>
        (Measure.tendsto_eval_ae_ae
          (μ := fun _ : Fin n => Q.dataMeasure) (i := j)).eventually hsQ).mono
      fun s hs j => hs j (Set.mem_univ j)
  have hintP : (∫ s, g s ∂Measure.pi fun _ : Fin n => P.dataMeasure) =
      ∫ s, f s ∂Measure.pi fun _ : Fin n => P.dataMeasure := by
    apply integral_congr_ae
    filter_upwards [hsPiP] with s hs
    apply congrArg f
    funext j
    simp [clip, hs j]
  have hintQ : (∫ s, g s ∂Measure.pi fun _ : Fin n => Q.dataMeasure) =
      ∫ s, f s ∂Measure.pi fun _ : Fin n => Q.dataMeasure := by
    apply integral_congr_ae
    filter_upwards [hsPiQ] with s hs
    apply congrArg f
    funext j
    simp [clip, hs j]
  rw [measureReal_bind_eq_integral (Measure.pi fun _ : Fin n => P.dataMeasure)
      M hM hdp.1 B hB,
    measureReal_bind_eq_integral (Measure.pi fun _ : Fin n => Q.dataMeasure)
      M hM hdp.1 B hB, ← hintP, ← hintQ]
  exact hhybrid

end CausalSmith.Stat.DpCateMinimax
