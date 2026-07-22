/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# K-fold cross-fitted Chernozhukov DML

K-fold version of `dml_chernozhukov_asymptoticLinear` from
`Estimation/OrthogonalMoments/DMLChernozhukov.lean`.  Each evaluation fold k uses a
nuisance estimator `η̂^{(-k)}` trained on the complement; the K fold scores
are averaged to form the final estimator.

Reference: Chernozhukov et al. (2018), §3.2 (DML2).
-/

import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
import Causalean.Stat.SampleSplit.KFold
import Causalean.Mathlib.IIDCenteredSum
import Causalean.Stat.EmpiricalProcess.CrossFitRate

/-! # Cross-Fitted Double Machine Learning

This file proves the K-fold analogue of the Chernozhukov-form DML theorem.
The estimator `dmlCrossFitEstimator` evaluates each fold with a nuisance
learner trained on the complementary data and averages the fold scores. The
main theorem `dml_crossFit_asymptoticLinear` shows asymptotic linearity with
influence function `-J₀⁻¹ · m(η₀, ·, θ₀)` under the same mean-zero,
finite-variance, score-difference, individual-rate, and product-rate
hypotheses as the one-shot theorem, but imposed fold by fold. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- **Helper.**  For an i.i.d. sample with mean-zero, square-integrable
transform `ψ`, the fold-normalized partial sum
`(1/√|fold n k|) Σ_{i ∈ fold n k} ψ(Z_i)` is `O_p(1)` under `μ`.

Proof: Markov + the iid second-moment bound
`Causalean.Mathlib.iid_centered_sum_sq_lintegral_le`, instantiated with the
trivial σ-algebra `m_A = ⊥` (independent of any other σ-algebra by
`ProbabilityTheory.indep_bot_left`).  The mean-zero hypothesis turns the
centered sum into the un-centered sum. -/
private lemma foldNormalizedSum_isBigOp
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (sample : IIDSample Ω Z μ P_Z) (ψ : Z → ℝ)
    (hψ_meas : Measurable ψ)
    (hψ_mean : ∫ z, ψ z ∂P_Z = 0)
    (hψ_sq : Integrable (fun z => ψ z ^ 2) P_Z)
    {K : ℕ} (split : KFoldSplit sample K) (k : Fin K) :
    IsBigOp
      (fun n ω => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => (1 : ℝ)) μ := by
  have hψ_memLp : MemLp ψ 2 P_Z :=
    (memLp_two_iff_integrable_sq hψ_meas.aestronglyMeasurable).2 hψ_sq
  -- `N²` is the square of the L² norm of ψ.
  let N : ℝ := (eLpNorm ψ 2 P_Z).toReal
  have hN_nonneg : 0 ≤ N := ENNReal.toReal_nonneg
  -- iid product law for fold n k.
  have hiid : ∀ n,
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω) =
        Measure.pi (fun _ : split.fold n k => P_Z) := by
    intro n
    have hindep_s : iIndepFun (fun i : split.fold n k => sample.Z i) μ := by
      exact sample.indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : split.fold n k => (sample.meas i).aemeasurable)).mp hindep_s
    calc
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω)
          = Measure.pi (fun i : split.fold n k => μ.map (sample.Z i)) := hmap
      _ = Measure.pi (fun _ : split.fold n k => P_Z) := by
          congr with i
          rw [← (sample.identDist i).map_eq, sample.law]
  -- Independence with the trivial σ-algebra ⊥.
  have hindep : ∀ n,
      Indep (⊥ : MeasurableSpace Ω)
        (MeasurableSpace.comap
          (fun ω (i : split.fold n k) => sample.Z i ω) inferInstance) μ := by
    intro n
    exact ProbabilityTheory.indep_bot_left _
  -- Apply the iid centered sum bound with g(ω, x) := ψ(x) (constant in ω).
  have hbound : ∀ n, 0 < (split.fold n k).card →
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2) := by
    intro n hn
    have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
      (s := split.fold n k) hn (W := sample.Z)
      (fun i _ => sample.meas i)
      (⊥ : MeasurableSpace Ω) bot_le (hindep n) (hiid n)
      (fun _ z => ψ z)
      (by
        change Measurable[(⊥ : MeasurableSpace Ω).prod (inferInstance : MeasurableSpace Z)]
          (fun p : Ω × Z => ψ p.2)
        exact hψ_meas.comp measurable_snd)
      (fun _ => hψ_memLp)
    -- Simplify the lambda `fun _ z => ψ z` to ψ in hraw.
    simp only [hψ_mean, sub_zero] at hraw
    -- RHS: ∫ N² ∂μ = N² (μ is probability).
    refine hraw.trans ?_
    simp [N]
  have hbound_all : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos ((split.fold n k).card) with hzero | hpos
    · have hfold_empty : split.fold n k = ∅ := Finset.card_eq_zero.mp hzero
      simp [hfold_empty]
    · exact hbound n hpos
  have hY_aemeas : ∀ n : ℕ, AEMeasurable
      (fun ω => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) μ := by
    intro n
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun i _ => hψ_meas.comp (sample.meas i)))).aemeasurable
  have hbig : IsBigOp
      (fun n ω => (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => Real.sqrt (N ^ 2)) μ :=
    IsBigOp.of_sq_lintegral_le hY_aemeas (fun _ => sq_nonneg N) hbound_all
  have hrate : (fun _ : ℕ => Real.sqrt (N ^ 2)) = (fun _ : ℕ => N) := by
    funext _
    exact Real.sqrt_sq hN_nonneg
  rw [hrate] at hbig
  exact hbig.const_rate_collapse hN_nonneg

/-- **Helper.**  Variant of `foldNormalizedSum_isBigOp` with the full-sample
normalization `(1/√n)` instead of `(1/√|fold n k|)`.  Since
`(split.fold n k).card ≤ n` (from `cover` + `partition`), the second moment
is still bounded by `∫ ψ² dP_Z`, and the same Markov argument applies. -/
private lemma foldNormalizedSumOverN_isBigOp
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (sample : IIDSample Ω Z μ P_Z) (ψ : Z → ℝ)
    (hψ_meas : Measurable ψ)
    (hψ_mean : ∫ z, ψ z ∂P_Z = 0)
    (hψ_sq : Integrable (fun z => ψ z ^ 2) P_Z)
    {K : ℕ} (split : KFoldSplit sample K) (k : Fin K) :
    IsBigOp
      (fun n ω => (Real.sqrt (n : ℝ))⁻¹ *
          ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => (1 : ℝ)) μ := by
  have hψ_memLp : MemLp ψ 2 P_Z :=
    (memLp_two_iff_integrable_sq hψ_meas.aestronglyMeasurable).2 hψ_sq
  let N : ℝ := (eLpNorm ψ 2 P_Z).toReal
  have hN_nonneg : 0 ≤ N := ENNReal.toReal_nonneg
  -- iid product law for fold n k.
  have hiid : ∀ n,
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω) =
        Measure.pi (fun _ : split.fold n k => P_Z) := by
    intro n
    have hindep_s : iIndepFun (fun i : split.fold n k => sample.Z i) μ := by
      exact sample.indep.precomp Subtype.val_injective
    have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : split.fold n k => (sample.meas i).aemeasurable)).mp hindep_s
    calc
      μ.map (fun ω (i : split.fold n k) => sample.Z i ω)
          = Measure.pi (fun i : split.fold n k => μ.map (sample.Z i)) := hmap
      _ = Measure.pi (fun _ : split.fold n k => P_Z) := by
          congr with i
          rw [← (sample.identDist i).map_eq, sample.law]
  have hindep : ∀ n,
      Indep (⊥ : MeasurableSpace Ω)
        (MeasurableSpace.comap
          (fun ω (i : split.fold n k) => sample.Z i ω) inferInstance) μ := by
    intro n
    exact ProbabilityTheory.indep_bot_left _
  -- |fold n k| ≤ n via cover.
  have hfold_le_n : ∀ n, (split.fold n k).card ≤ n := by
    intro n
    have h_cov := split.cover n
    have hsub : split.fold n k ⊆ Finset.range n := by
      have : split.fold n k ⊆
          (Finset.univ : Finset (Fin K)).biUnion (split.fold n) :=
        Finset.subset_biUnion_of_mem _ (Finset.mem_univ k)
      rw [h_cov] at this
      exact this
    calc
      (split.fold n k).card ≤ (Finset.range n).card := Finset.card_le_card hsub
      _ = n := Finset.card_range n
  -- Second-moment bound.
  have hbound : ∀ n, 0 < (split.fold n k).card →
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2) := by
    intro n hn_fold
    have hraw := Causalean.Mathlib.iid_centered_sum_sq_lintegral_le
      (s := split.fold n k) hn_fold (W := sample.Z)
      (fun i _ => sample.meas i)
      (⊥ : MeasurableSpace Ω) bot_le (hindep n) (hiid n)
      (fun _ z => ψ z)
      (by
        change Measurable[(⊥ : MeasurableSpace Ω).prod (inferInstance : MeasurableSpace Z)]
          (fun p : Ω × Z => ψ p.2)
        exact hψ_meas.comp measurable_snd)
      (fun _ => hψ_memLp)
    simp only [hψ_mean, sub_zero] at hraw
    -- The original bound is on (1/√|fold|) Σ. We want (1/√n) Σ. Since |fold|/n ≤ 1,
    -- (1/√n)² Σ² ≤ (1/√|fold|)² Σ² (because (1/n) ≤ (1/|fold|)).
    have hn_pos : 0 < n := lt_of_lt_of_le hn_fold (hfold_le_n n)
    have hn_R : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hfold_R : 0 < ((split.fold n k).card : ℝ) := by exact_mod_cast hn_fold
    have hfold_le_n_R : ((split.fold n k).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hfold_le_n n
    have hinv_le : (n : ℝ)⁻¹ ≤ ((split.fold n k).card : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hn_R hfold_R]
      exact hfold_le_n_R
    -- Pointwise: (1/√n)² ≤ (1/√|fold|)².
    have hpoint : ∀ ω,
        ENNReal.ofReal
            (((Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ≤
          ENNReal.ofReal
            (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
              ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) := by
      intro ω
      apply ENNReal.ofReal_le_ofReal
      set S := ∑ i ∈ split.fold n k, ψ (sample.Z i ω)
      have h_sqr_n : (Real.sqrt (n : ℝ))⁻¹ ^ 2 = (n : ℝ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hn_R.le]
      have h_sqr_fold : (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ ^ 2 =
          ((split.fold n k).card : ℝ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hfold_R.le]
      have hL : ((Real.sqrt (n : ℝ))⁻¹ * S) ^ 2 = (n : ℝ)⁻¹ * S ^ 2 := by
        rw [mul_pow, h_sqr_n]
      have hR : ((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ * S) ^ 2 =
          ((split.fold n k).card : ℝ)⁻¹ * S ^ 2 := by
        rw [mul_pow, h_sqr_fold]
      rw [hL, hR]
      exact mul_le_mul_of_nonneg_right hinv_le (sq_nonneg _)
    have hint_le :
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal
            (((Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
              ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ :=
      lintegral_mono hpoint
    refine hint_le.trans ?_
    refine hraw.trans ?_
    simp [N]
  have hbound_all : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal
          (((Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) ^ 2) ∂μ
        ≤ ENNReal.ofReal (N ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos ((split.fold n k).card) with hzero | hpos
    · have hfold_empty : split.fold n k = ∅ := Finset.card_eq_zero.mp hzero
      simp [hfold_empty]
    · exact hbound n hpos
  have hY_aemeas : ∀ n : ℕ, AEMeasurable
      (fun ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω)) μ := by
    intro n
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun i _ => hψ_meas.comp (sample.meas i)))).aemeasurable
  have hbig : IsBigOp
      (fun n ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k, ψ (sample.Z i ω))
      (fun _ => Real.sqrt (N ^ 2)) μ :=
    IsBigOp.of_sq_lintegral_le hY_aemeas (fun _ => sq_nonneg N) hbound_all
  have hrate : (fun _ : ℕ => Real.sqrt (N ^ 2)) = (fun _ : ℕ => N) := by
    funext _
    exact Real.sqrt_sq hN_nonneg
  rw [hrate] at hbig
  exact hbig.const_rate_collapse hN_nonneg

private lemma IsLittleOp_zero_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} :
    IsLittleOp (fun _ (_ : Ω) => (0 : ℝ)) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hzero :
      (fun n : ℕ => μ {ω : Ω | ε * (fun _ => (1 : ℝ)) n < |(0 : ℝ)|}) =
        fun _ => (0 : ENNReal) := by
    funext n
    simp [hε.not_gt]
  rw [hzero]
  exact tendsto_const_nhds

private lemma IsLittleOp_congr_eventually
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (hX : IsLittleOp X r μ)
    (hXY : ∀ᶠ n in atTop, ∀ ω, Y n ω = X n ω) :
    IsLittleOp Y r μ := by
  intro ε hε
  exact (hX ε hε).congr' (hXY.mono fun n hn => by
    congr 1
    ext ω
    simp [hn ω])

private lemma IsLittleOp_add_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℕ → Ω → ℝ}
    (hX : IsLittleOp X (fun _ => (1 : ℝ)) μ)
    (hY : IsLittleOp Y (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => X n ω + Y n ω) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  by_cases hηtop : η = ⊤
  · filter_upwards with n
    simp [hηtop]
  have hηpos : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) hηtop
  let α : ℝ := η.toReal / 4
  have hαpos : 0 < α := by
    dsimp [α]
    linarith
  let A : ℕ → Set Ω := fun n => {ω | (ε / 2) * 1 < |X n ω|}
  let B : ℕ → Set Ω := fun n => {ω | (ε / 2) * 1 < |Y n ω|}
  let C : ℕ → Set Ω := fun n => {ω | ε * 1 < |X n ω + Y n ω|}
  have hAevent := (ENNReal.tendsto_nhds_zero.mp
    (hX (ε / 2) (by linarith))) (ENNReal.ofReal α)
      (ENNReal.ofReal_pos.mpr hαpos)
  have hBevent := (ENNReal.tendsto_nhds_zero.mp
    (hY (ε / 2) (by linarith))) (ENNReal.ofReal α)
      (ENNReal.ofReal_pos.mpr hαpos)
  have htwo_alpha_lt_eta : ENNReal.ofReal (2 * α) < η := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [α]
      linarith
    · dsimp [α]
      linarith [le_of_lt hηpos]
    · exact hηtop
  filter_upwards [hAevent, hBevent] with n hAn hBn
  have hsubset : C n ⊆ A n ∪ B n := by
    intro ω hω
    by_contra hnot
    have hnotA : ¬ (ε / 2) * 1 < |X n ω| := by
      intro hx
      exact hnot (Or.inl hx)
    have hnotB : ¬ (ε / 2) * 1 < |Y n ω| := by
      intro hy
      exact hnot (Or.inr hy)
    have hXle : |X n ω| ≤ (ε / 2) * 1 := le_of_not_gt hnotA
    have hYle : |Y n ω| ≤ (ε / 2) * 1 := le_of_not_gt hnotB
    have hsum_le : |X n ω + Y n ω| ≤ ε * 1 := by
      calc
        |X n ω + Y n ω| ≤ |X n ω| + |Y n ω| :=
          abs_add_le (X n ω) (Y n ω)
        _ ≤ (ε / 2) * 1 + (ε / 2) * 1 := add_le_add hXle hYle
        _ = ε * 1 := by ring
    exact not_lt_of_ge hsum_le hω
  exact le_of_lt <| calc
    μ {ω | ε * 1 < |X n ω + Y n ω|} = μ (C n) := by
      simp [C]
    _ ≤ μ (A n ∪ B n) := measure_mono hsubset
    _ ≤ μ (A n) + μ (B n) := MeasureTheory.measure_union_le (A n) (B n)
    _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hAn hBn
    _ = ENNReal.ofReal (2 * α) := by
      rw [← ENNReal.ofReal_add]
      · congr 1
        ring
      · linarith
      · linarith
    _ < η := htwo_alpha_lt_eta

private lemma IsLittleOp_const_mul_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (a : ℝ) {X : ℕ → Ω → ℝ}
    (hX : IsLittleOp X (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => a * X n ω) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  by_cases ha : a = 0
  · subst a
    have hzero :
        (fun n => μ {ω | ε * (fun _ => (1 : ℝ)) n < |0 * X n ω|}) =
          fun _ => (0 : ENNReal) := by
      funext n
      simp [hε.not_gt]
    rw [hzero]
    exact tendsto_const_nhds
  · have hscale_pos : 0 < ε / |a| := div_pos hε (abs_pos.mpr ha)
    have hXt := hX (ε / |a|) hscale_pos
    refine hXt.congr' ?_
    filter_upwards with n
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, mul_one, abs_mul]
    rw [div_lt_iff₀ (abs_pos.mpr ha)]
    ring_nf

private lemma IsLittleOp_finset_sum_one
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → ℕ → Ω → ℝ)
    (h : ∀ i ∈ s, IsLittleOp (f i) (fun _ => (1 : ℝ)) μ) :
    IsLittleOp (fun n ω => ∑ i ∈ s, f i n ω) (fun _ => (1 : ℝ)) μ := by
  classical
  revert h
  refine Finset.induction_on s ?base ?step
  · intro h
    simpa using (IsLittleOp_zero_one (Ω := Ω) (μ := μ))
  · intro a s has ih h
    have ha : IsLittleOp (f a) (fun _ => (1 : ℝ)) μ :=
      h a (Finset.mem_insert_self a s)
    have hs :
        IsLittleOp (fun n ω => ∑ i ∈ s, f i n ω) (fun _ => (1 : ℝ)) μ := by
      apply ih
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)
    have hadd := IsLittleOp_add_one ha hs
    simpa [Finset.sum_insert, has, add_comm, add_left_comm, add_assoc] using hadd

private lemma deterministic_tendsto_isBigOp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {a : ℕ → ℝ} {c : ℝ} (ha : Tendsto a atTop (𝓝 c)) :
    IsBigOp (fun n (_ : Ω) => a n) (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  refine ⟨|c| + 1, ?_⟩
  have hbound : ∀ᶠ n in atTop, |a n| ≤ |c| + 1 := by
    have hdist := (Metric.tendsto_nhds.mp ha) (1 : ℝ) zero_lt_one
    filter_upwards [hdist] with n hn
    have habs_sub : |a n - c| < 1 := by
      simpa [Real.dist_eq] using hn
    calc
      |a n| = |(a n - c) + c| := by ring_nf
      _ ≤ |a n - c| + |c| := abs_add_le (a n - c) c
      _ ≤ |c| + 1 := by linarith
  have hzero_event : ∀ᶠ n in atTop,
      μ {ω : Ω | (|c| + 1) * (fun _ => (1 : ℝ)) n < |a n|} ≤ 0 := by
    filter_upwards [hbound] with n hn
    have hempty :
        {ω : Ω | (|c| + 1) * (fun _ => (1 : ℝ)) n < |a n|} = ∅ := by
      ext ω
      simp [hn.not_gt]
    rw [hempty]
    simp
  exact (Filter.limsup_le_of_le ⟨0, by intro _ _; exact bot_le⟩
    hzero_event).trans bot_le

/-- **K-fold cross-fitted Chernozhukov DML estimator.**  At each fold k,
the nuisance estimator `η_hat n k ω : H` is trained on the complement of
fold k.  The fold-k score is the empirical mean of `m(η̂^{(-k)}, ·, θ₀)`
over fold k, rescaled by `−J₀⁻¹` and shifted by `θ₀`.  The final
estimator averages these K fold scores. -/
noncomputable def dmlCrossFitEstimator
    (M : GeneralMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ}
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    (n : ℕ) : Ω → ℝ :=
  fun ω =>
    M.θ₀ - M.J₀_inv *
      ((K : ℝ)⁻¹ *
        ∑ k : Fin K,
          ((split.fold n k).card : ℝ)⁻¹ *
            ∑ i ∈ split.fold n k, M.m (η_hat n k ω) (sample.Z i ω) M.θ₀)

/-- **Asymptotic linearity of the K-fold cross-fitted Chernozhukov DML
estimator.**  Same Chernozhukov form as `dml_chernozhukov_asymptoticLinear`,
but with K folds.  Conclusion: asymptotic linearity at `M.θ₀` with IF
`−J₀⁻¹ · m(η₀, ·, θ₀)`, indexed over the full sample (the fold-k
sub-aggregations sum to a full-sample average asymptotically).

Hypotheses mirror the one-shot version, but with per-fold nuisance rates. -/
theorem dml_crossFit_asymptoticLinear
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z) {K : ℕ} (_hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (η_hat : ℕ → Fin K → Ω → H)
    {Crem : ℝ}
    (_hBR_at :
      ∀ n k ω,
        |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤
          Crem * ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
                 ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
    (_h_m_meas :
      ∀ n k, Measurable (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_train :
      ∀ n k,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
          (fun ω z => M.m (η_hat n k ω) z M.θ₀))
    (_h_m_train_uncurry :
      ∀ n k,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.trainComplement n k) => sample.Z i ω)
            inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun (p : Ω × Z) => M.m (η_hat n k p.1) p.2 M.θ₀))
    (_h_m_int :
      ∀ n k ω, Integrable (fun z => M.m (η_hat n k ω) z M.θ₀) P_Z)
    (_h_m_sq_int :
      ∀ n k ω, Integrable (fun z => (M.m (η_hat n k ω) z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate :
      ∀ k, IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
        (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₁ :
      ∀ k, IsLittleOp
        (fun n ω => ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) μ)
    (_h_indiv_rate_ρ₂ :
      ∀ k, IsLittleOp
        (fun n ω => ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) μ)
    (_h_product_rate :
      ∀ k, IsLittleOp
        (fun n ω =>
          ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
            ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear
      (dmlCrossFitEstimator M sample split η_hat)
      M.θ₀
      (fun z => -M.J₀_inv * M.m M.η₀ z M.θ₀)
      sample
      (fun n => Finset.range n) := by
  let ψ₀ : Z → ℝ := fun z => M.m M.η₀ z M.θ₀
  have hMZ_int : ∫ z, ψ₀ z ∂P_Z = 0 := _hMZ
  refine ⟨?_, ?_, ?_⟩
  · -- Mean zero: multiply `MeanZero M` by the fixed scalar `-J₀⁻¹`.
    show ∫ z, -M.J₀_inv * M.m M.η₀ z M.θ₀ ∂P_Z = 0
    calc
      ∫ z, -M.J₀_inv * M.m M.η₀ z M.θ₀ ∂P_Z
          = -M.J₀_inv * ∫ z, ψ₀ z ∂P_Z := by
            simp only [ψ₀, neg_mul, integral_neg, integral_const_mul]
      _ = 0 := by rw [hMZ_int]; ring
  · -- Finite variance: fixed scalar multiplication preserves square
    -- integrability of the Chernozhukov score.
    show Integrable (fun z => (-M.J₀_inv * M.m M.η₀ z M.θ₀) ^ 2) P_Z
    have h_eq : ∀ z,
        (-M.J₀_inv * M.m M.η₀ z M.θ₀) ^ 2 =
          M.J₀_inv ^ 2 * (M.m M.η₀ z M.θ₀) ^ 2 := by
      intro z; ring
    simp_rw [h_eq]
    exact _hFV.const_mul (M.J₀_inv ^ 2)
  · -- Remainder: separate the K-fold reduction into the
    -- stochastic fold terms, the population bias terms, and the final
    -- full-sample reweighting from fold averages.
    let foldScoreDiff : ℕ → Fin K → Ω → Z → ℝ := fun n k ω z =>
      M.m (η_hat n k ω) z M.θ₀ - ψ₀ z
    let foldCentered : ℕ → Fin K → Ω → ℝ := fun n k ω =>
      (Real.sqrt ((split.fold n k).card : ℝ))⁻¹ *
        ∑ i ∈ split.fold n k,
          (foldScoreDiff n k ω (sample.Z i ω) -
            ∫ z, foldScoreDiff n k ω z ∂P_Z)
    let foldBias : ℕ → Fin K → Ω → ℝ := fun n k ω =>
      Real.sqrt ((split.fold n k).card : ℝ) *
        ∫ z, foldScoreDiff n k ω z ∂P_Z
    haveI : IsProbabilityMeasure P_Z := by
      rw [← sample.law]
      exact Measure.isProbabilityMeasure_map (sample.meas 0).aemeasurable
    have htruth_L2 : MemLp (fun z => M.m M.η₀ z M.θ₀) 2 P_Z :=
      (memLp_two_iff_integrable_sq
        (M.m_meas M.η₀ M.θ₀).aestronglyMeasurable).2 _hFV
    have h_fold_centered :
        ∀ k, IsLittleOp (fun n ω => foldCentered n k ω) (fun _ => (1 : ℝ)) μ := by
      intro k
      let f : ℕ → Ω → Z → ℝ := fun n ω z =>
        M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀
      have hf_meas : ∀ n, Measurable (Function.uncurry (f n)) := by
        intro n
        change Measurable (fun p : Ω × Z =>
          M.m (η_hat n k p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
        exact (_h_m_meas n k).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
      have hf_train :
          ∀ n,
            Measurable[MeasurableSpace.comap
              (fun ω (i : split.trainComplement n k) => sample.Z i ω)
              inferInstance]
              (fun ω => f n ω) := by
        intro n
        change Measurable[MeasurableSpace.comap
            (fun ω (i : split.trainComplement n k) => sample.Z i ω)
            inferInstance]
          (fun ω z => M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
        exact (_h_m_train n k).sub measurable_const
      have hf_uncurry_train :
          ∀ n,
            Measurable[(MeasurableSpace.comap
                (fun ω (i : split.trainComplement n k) => sample.Z i ω)
                inferInstance).prod
              (inferInstance : MeasurableSpace Z)]
              (Function.uncurry (f n)) := by
        intro n
        change Measurable[(MeasurableSpace.comap
            (fun ω (i : split.trainComplement n k) => sample.Z i ω)
            inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun p : Ω × Z =>
            M.m (η_hat n k p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
        exact (_h_m_train_uncurry n k).sub
          ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
      have hf_memLp : ∀ n ω, MemLp (f n ω) 2 P_Z := by
        intro n ω
        have hrand_L2 : MemLp (fun z => M.m (η_hat n k ω) z M.θ₀) 2 P_Z :=
          (memLp_two_iff_integrable_sq
            (M.m_meas (η_hat n k ω) M.θ₀).aestronglyMeasurable).2
              (_h_m_sq_int n k ω)
        simpa [f] using hrand_L2.sub htruth_L2
      have hf_rate_one :
          IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P_Z).toReal)
            (fun _ => (1 : ℝ)) μ := by
        simpa [f] using _h_score_diff_rate k
      simpa [foldCentered, foldScoreDiff, ψ₀, f] using
        KFoldSplit.fold_centered_sum_isLittleOp_one sample split k f
          hf_meas hf_uncurry_train hf_memLp hf_rate_one
    have h_fold_bias :
        ∀ k, IsLittleOp (fun n ω => foldBias n k ω) (fun _ => (1 : ℝ)) μ := by
      intro k
      let f : ℕ → Ω → Z → ℝ := fun n ω z =>
        M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀
      have hf_meas : ∀ n, Measurable (Function.uncurry (f n)) := by
        intro n
        change Measurable (fun p : Ω × Z =>
          M.m (η_hat n k p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
        exact (_h_m_meas n k).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
      have hf_memLp : ∀ n ω, MemLp (f n ω) 2 P_Z := by
        intro n ω
        have hrand_L2 : MemLp (fun z => M.m (η_hat n k ω) z M.θ₀) 2 P_Z :=
          (memLp_two_iff_integrable_sq
            (M.m_meas (η_hat n k ω) M.θ₀).aestronglyMeasurable).2
              (_h_m_sq_int n k ω)
        simpa [f] using hrand_L2.sub htruth_L2
      have h_int_eq : ∀ n ω,
          ∫ z, f n ω z ∂P_Z =
            ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z := by
        intro n ω
        have hf_int : Integrable (f n ω) P_Z :=
          (hf_memLp n ω).integrable (by norm_num : (1 : ENNReal) ≤ 2)
        have htruth_int : Integrable (fun z => M.m M.η₀ z M.θ₀) P_Z :=
          htruth_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
        have hzero : (∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) = 0 := by
          simpa [MeanZero] using _hMZ
        calc
          ∫ z, f n ω z ∂P_Z =
              ∫ z, (M.m (η_hat n k ω) z M.θ₀ - M.m M.η₀ z M.θ₀) ∂P_Z := by rfl
          _ = ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z -
              ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z :=
            integral_sub (_h_m_int n k ω) htruth_int
          _ = ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z := by
            rw [hzero]
            ring
      have h_int_raw_rate :
          IsLittleOp (fun n ω => ∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z)
            (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
        intro ε hε
        rw [ENNReal.tendsto_nhds_zero]
        intro δ hδ
        let Kc : ℝ := |Crem| + 1
        have hKpos : 0 < Kc := by
          dsimp [Kc]
          linarith [abs_nonneg Crem]
        have htarget := (ENNReal.tendsto_nhds_zero.mp
          (_h_product_rate k (ε / Kc) (div_pos hε hKpos))) δ hδ
        exact htarget.mono fun n hn => (measure_mono (by
          intro ω hω
          let prodρ : ℝ :=
            ((M.ρ₁ (η_hat n k ω) M.η₀ : NNReal) : ℝ) *
              ((M.ρ₂ (η_hat n k ω) M.η₀ : NNReal) : ℝ)
          have hprod_nonneg : 0 ≤ prodρ := by
            dsimp [prodρ]
            exact mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
          have hbr := _hBR_at n k ω
          have hbr0 :
              |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤ Crem * prodρ := by
            simpa [prodρ, mul_assoc] using hbr
          have hle_abs :
              |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤ |Crem| * prodρ :=
            hbr0.trans (mul_le_mul_of_nonneg_right (le_abs_self Crem) hprod_nonneg)
          have hKbound :
              |∫ z, M.m (η_hat n k ω) z M.θ₀ ∂P_Z| ≤ Kc * prodρ := by
            refine hle_abs.trans ?_
            exact mul_le_mul_of_nonneg_right (by dsimp [Kc]; linarith) hprod_nonneg
          have hlt_bound :
              ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) < Kc * prodρ :=
            lt_of_lt_of_le hω hKbound
          have hdiv_lt :
              (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / Kc < prodρ := by
            rw [div_lt_iff₀ hKpos]
            simpa [mul_comm, mul_left_comm, mul_assoc] using hlt_bound
          have hsmall :
              (ε / Kc) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) < |prodρ| := by
            have hdiv_eq :
                (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / Kc =
                  (ε / Kc) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
              ring
            rw [← hdiv_eq]
            simpa [abs_of_nonneg hprod_nonneg] using hdiv_lt
          exact hsmall)).trans hn
      have h_int_rate :
          IsLittleOp (fun n ω => ∫ z, f n ω z ∂P_Z)
            (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
        convert h_int_raw_rate using 1
        funext n ω
        exact h_int_eq n ω
      -- Inline bias bound: mirrors OneShot's `hB` (lines 302-367) with
      -- `split.foldB n` replaced by `split.fold n k` and the ratio limit
      -- `c` replaced by `K⁻¹` (from `split.ratio k`).
      have hK_pos_real : 0 < (K : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hK_pos.le)
      have hK_one_lt_real : (1 : ℝ) < (K : ℝ) := by exact_mod_cast _hK_pos
      have hc_pos : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hK_pos_real
      have hc_lt : (K : ℝ)⁻¹ < 1 := by
        rw [inv_lt_one_iff₀]
        exact Or.inr hK_one_lt_real
      have h_split_rate := split.ratio k
      have hbias :
          IsLittleOp (fun n ω => foldBias n k ω) (fun _ => (1 : ℝ)) μ := by
        intro ε' hε'
        rw [ENNReal.tendsto_nhds_zero]
        intro δ hδ
        let C : ℝ := Real.sqrt ((K : ℝ)⁻¹) + 1
        have hCpos : 0 < C := by
          dsimp [C]
          linarith [Real.sqrt_nonneg ((K : ℝ)⁻¹)]
        have hCnonneg : 0 ≤ C := le_of_lt hCpos
        have hC2 : (K : ℝ)⁻¹ < C ^ 2 := by
          dsimp [C]
          nlinarith [Real.sq_sqrt (le_of_lt hc_pos),
            Real.sqrt_nonneg ((K : ℝ)⁻¹)]
        have hratio_event :
            ∀ᶠ n in atTop, ((split.fold n k).card : ℝ) / n < C ^ 2 :=
          h_split_rate.eventually_lt_const hC2
        have hn_event : ∀ᶠ n : ℕ in atTop, n ≠ 0 := eventually_ne_atTop 0
        have hint_event := (ENNReal.tendsto_nhds_zero.mp
          (h_int_rate (ε' / C) (div_pos hε' hCpos))) δ hδ
        filter_upwards [hratio_event, hn_event, hint_event]
          with n hratio hn_ne hn
        refine (measure_mono ?_).trans hn
        intro ω hω
        have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn_ne
        have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
        have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
        have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
        have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrtn_pos
        have hcard_le : ((split.fold n k).card : ℝ) ≤ C ^ 2 * (n : ℝ) := by
          have hlt : ((split.fold n k).card : ℝ) < C ^ 2 * (n : ℝ) := by
            field_simp [hn_pos.ne'] at hratio ⊢
            nlinarith
          exact le_of_lt hlt
        have hsqrt_le :
            Real.sqrt ((split.fold n k).card : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
          calc
            Real.sqrt ((split.fold n k).card : ℝ) ≤ Real.sqrt (C ^ 2 * (n : ℝ)) :=
              Real.sqrt_le_sqrt hcard_le
            _ = Real.sqrt (C ^ 2) * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_mul (sq_nonneg C)]
            _ = C * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_sq hCnonneg]
        have hsqrtcard_nonneg : 0 ≤ Real.sqrt ((split.fold n k).card : ℝ) :=
          Real.sqrt_nonneg _
        have hlt_prod :
            ε' < Real.sqrt ((split.fold n k).card : ℝ) *
              |∫ z, f n ω z ∂P_Z| := by
          simpa [foldBias, foldScoreDiff, ψ₀, f, abs_mul,
            abs_of_nonneg hsqrtcard_nonneg] using hω
        have hle_prod :
            Real.sqrt ((split.fold n k).card : ℝ) * |∫ z, f n ω z ∂P_Z| ≤
              (C * Real.sqrt (n : ℝ)) * |∫ z, f n ω z ∂P_Z| :=
          mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
        have hlt_bound :
            ε' < (C * Real.sqrt (n : ℝ)) * |∫ z, f n ω z ∂P_Z| :=
          lt_of_lt_of_le hlt_prod hle_prod
        have hrn_eq : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
          rw [Real.rpow_neg hn_nonneg]
          rw [← Real.sqrt_eq_rpow]
        have hdiv_lt :
            ε' / (C * Real.sqrt (n : ℝ)) < |∫ z, f n ω z ∂P_Z| := by
          rw [div_lt_iff₀ (mul_pos hCpos hsqrtn_pos)]
          nlinarith [hlt_bound]
        have hsmall :
            (ε' / C) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) <
              |∫ z, f n ω z ∂P_Z| := by
          rw [hrn_eq]
          convert hdiv_lt using 1
          field_simp [hCpos.ne', hsqrtn_pos.ne']
        exact hsmall
      exact hbias
    -- Prerequisites for the K-fold algebra (used by the helpers below).
    have hK_pos_real : 0 < (K : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one _hK_pos.le)
    have hK_one_lt_real : (1 : ℝ) < (K : ℝ) := by exact_mod_cast _hK_pos
    have hK_ne : (K : ℝ) ≠ 0 := ne_of_gt hK_pos_real
    have hK_inv_pos : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hK_pos_real
    have hψ_meas_glob : Measurable ψ₀ := M.m_meas M.η₀ M.θ₀
    -- Reusable O_p(1) helper for `(1/√n) Σ_{fold n k} ψ₀(Z_i)`.
    have _hfoldNormPsi_isBigOp : ∀ k : Fin K,
        IsBigOp
          (fun n ω => (Real.sqrt (n : ℝ))⁻¹ *
              ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω))
          (fun _ => (1 : ℝ)) μ := by
      intro k
      exact foldNormalizedSumOverN_isBigOp sample ψ₀ hψ_meas_glob hMZ_int _hFV
        split k
    -- ## Final algebraic decomposition.
    --
    -- After unfolding `dmlCrossFitEstimator` and using `cover` + `partition` to
    -- rewrite `∑_{i ∈ range n} ψ₀(Z_i) = ∑_k ∑_{i ∈ fold n k} ψ₀(Z_i)`, the
    -- residual factorises as
    --   R_n = -J₀⁻¹ · ∑_{k : Fin K} D_k(n, ω)
    -- where each `D_k(n, ω)` decomposes as a sum of:
    --   ratio_piece_k = (n / (K · |fold n k|) - 1) · (1/√n) · ∑_{fold n k} ψ₀,
    --   score_piece_k = (1/K) · (√n / √|fold n k|) ·
    --                     (foldCentered n k ω + foldBias n k ω).
    -- `ratio_piece_k` is `o_p(1)` via `IsBigOp.const_mul_tendsto_zero`
    --   (deterministic factor → 0, stochastic factor `O_p(1)` from
    --   `_hfoldNormPsi_isBigOp k`).
    -- `score_piece_k` is `o_p(1)` via `IsBigOp.mul_isLittleOp_one_isLittleOp`
    --   (deterministic factor `√n/√|fold n k| → √K` is `O_p(1)`,
    --   `foldCentered + foldBias` is `o_p(1)` from `h_fold_centered`,
    --   `h_fold_bias`).
    -- Summing K copies of `o_p(1)` (and multiplying by the constant `-J₀⁻¹`)
    -- gives the desired `o_p(1)`.
    have h_full_reweighting :
        IsLittleOp
          (fun n ω =>
            Real.sqrt ((Finset.range n).card : ℝ) *
                (dmlCrossFitEstimator M sample split η_hat n ω - M.θ₀) -
              (Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
                ∑ i ∈ Finset.range n,
                  (-M.J₀_inv * M.m M.η₀ (sample.Z i ω) M.θ₀))
          (fun _ => (1 : ℝ)) μ := by
      classical
      let ratioRaw : Fin K → ℕ → Ω → ℝ := fun k n ω =>
        Real.sqrt (n : ℝ) * (K : ℝ)⁻¹ *
            (((split.fold n k).card : ℝ)⁻¹ *
              ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)) -
          (Real.sqrt (n : ℝ))⁻¹ *
            ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)
      let scoreRaw : Fin K → ℕ → Ω → ℝ := fun k n ω =>
        Real.sqrt (n : ℝ) * (K : ℝ)⁻¹ *
          (((split.fold n k).card : ℝ)⁻¹ *
            ∑ i ∈ split.fold n k,
              foldScoreDiff n k ω (sample.Z i ω))
      let ratioLimit : Fin K → ℕ → ℝ := fun k n =>
        (n : ℝ) / ((K : ℝ) * ((split.fold n k).card : ℝ)) - 1
      let scoreScale : Fin K → ℕ → ℝ := fun k n =>
        (K : ℝ)⁻¹ *
          Real.sqrt ((n : ℝ) / ((split.fold n k).card : ℝ))
      have hratio_limit :
          ∀ k : Fin K, Tendsto (ratioLimit k) atTop (𝓝 0) := by
        intro k
        have h_n_over_card :
            Tendsto
              (fun n : ℕ => (n : ℝ) / ((split.fold n k).card : ℝ))
              atTop (𝓝 (K : ℝ)) := by
          have h_inv :
              Tendsto
                (fun n : ℕ =>
                  (((split.fold n k).card : ℝ) / (n : ℝ))⁻¹)
                atTop (𝓝 (K : ℝ)) := by
            have hlim_ne : ((K : ℝ)⁻¹) ≠ 0 := inv_ne_zero hK_ne
            have h := (split.ratio k).inv₀ hlim_ne
            simpa [inv_inv] using h
          refine h_inv.congr' ?_
          filter_upwards [eventually_ne_atTop 0,
            (split.grow k).eventually_gt_atTop 0] with n hn hcard
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          have hcR : ((split.fold n k).card : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hcard)
          field_simp [hnR, hcR]
        have h_scaled :
            Tendsto
              (fun n : ℕ =>
                ((K : ℝ)⁻¹) *
                  ((n : ℝ) / ((split.fold n k).card : ℝ)))
              atTop (𝓝 1) := by
          have := Tendsto.const_mul ((K : ℝ)⁻¹) h_n_over_card
          simpa [hK_ne] using this
        have h_sub :
            Tendsto
              (fun n : ℕ =>
                ((K : ℝ)⁻¹) *
                    ((n : ℝ) / ((split.fold n k).card : ℝ)) - 1)
              atTop (𝓝 (1 - 1)) :=
          h_scaled.sub (tendsto_const_nhds (x := (1 : ℝ)))
        simpa [ratioLimit, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc]
          using h_sub
      have hratio_raw :
          ∀ k : Fin K, IsLittleOp (ratioRaw k) (fun _ => (1 : ℝ)) μ := by
        intro k
        have hcanonical :
            IsLittleOp
              (fun n ω =>
                ratioLimit k n *
                  ((Real.sqrt (n : ℝ))⁻¹ *
                    ∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)))
              (fun _ => (1 : ℝ)) μ :=
          IsBigOp.const_mul_tendsto_zero (_hfoldNormPsi_isBigOp k)
            (hratio_limit k)
        refine IsLittleOp_congr_eventually hcanonical ?_
        filter_upwards [eventually_ne_atTop 0,
          (split.grow k).eventually_gt_atTop 0] with n hn hcard ω
        have hn_pos : 0 < (n : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hn)
        have hcard_pos : 0 < ((split.fold n k).card : ℝ) := by
          exact_mod_cast hcard
        have hsqrtn_sq :
            Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt hn_pos.le
        have hsqrtn_pow : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := by
          rw [sq, hsqrtn_sq]
        unfold ratioRaw ratioLimit
        field_simp [hK_ne, hn_pos.ne', hcard_pos.ne',
          (Real.sqrt_pos.mpr hn_pos).ne', hsqrtn_sq]
        rw [hsqrtn_pow]
      have hscore_scale_limit :
          ∀ k : Fin K, Tendsto (scoreScale k) atTop
            (𝓝 ((K : ℝ)⁻¹ * Real.sqrt (K : ℝ))) := by
        intro k
        have h_n_over_card :
            Tendsto
              (fun n : ℕ => (n : ℝ) / ((split.fold n k).card : ℝ))
              atTop (𝓝 (K : ℝ)) := by
          have h_inv :
              Tendsto
                (fun n : ℕ =>
                  (((split.fold n k).card : ℝ) / (n : ℝ))⁻¹)
                atTop (𝓝 (K : ℝ)) := by
            have hlim_ne : ((K : ℝ)⁻¹) ≠ 0 := inv_ne_zero hK_ne
            have h := (split.ratio k).inv₀ hlim_ne
            simpa [inv_inv] using h
          refine h_inv.congr' ?_
          filter_upwards [eventually_ne_atTop 0,
            (split.grow k).eventually_gt_atTop 0] with n hn hcard
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          have hcR : ((split.fold n k).card : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hcard)
          field_simp [hnR, hcR]
        have hsqrt :
            Tendsto
              (fun n : ℕ =>
                Real.sqrt ((n : ℝ) / ((split.fold n k).card : ℝ)))
              atTop (𝓝 (Real.sqrt (K : ℝ))) :=
          (Real.continuous_sqrt.tendsto (K : ℝ)).comp h_n_over_card
        have hscaled := Tendsto.const_mul ((K : ℝ)⁻¹) hsqrt
        simpa [scoreScale] using hscaled
      have hscore_raw :
          ∀ k : Fin K, IsLittleOp (scoreRaw k) (fun _ => (1 : ℝ)) μ := by
        intro k
        have hdet :
            IsBigOp (fun n (_ : Ω) => scoreScale k n)
              (fun _ => (1 : ℝ)) μ :=
          deterministic_tendsto_isBigOp (μ := μ) (hscore_scale_limit k)
        have hcenter_bias :
            IsLittleOp
              (fun n ω => foldCentered n k ω + foldBias n k ω)
              (fun _ => (1 : ℝ)) μ :=
          IsLittleOp_add_one (h_fold_centered k) (h_fold_bias k)
        have hcanonical :
            IsLittleOp
              (fun n ω =>
                scoreScale k n *
                  (foldCentered n k ω + foldBias n k ω))
              (fun _ => (1 : ℝ)) μ :=
          IsBigOp.mul_isLittleOp_one_isLittleOp hdet hcenter_bias
        refine IsLittleOp_congr_eventually hcanonical ?_
        filter_upwards [eventually_ne_atTop 0,
          (split.grow k).eventually_gt_atTop 0] with n hn hcard ω
        have hn_pos : 0 < (n : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hn)
        have hcard_pos : 0 < ((split.fold n k).card : ℝ) := by
          exact_mod_cast hcard
        have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
        have hsqrtc_pos : 0 < Real.sqrt ((split.fold n k).card : ℝ) :=
          Real.sqrt_pos.mpr hcard_pos
        have hsqrt_div :
            Real.sqrt ((n : ℝ) / ((split.fold n k).card : ℝ)) =
              Real.sqrt (n : ℝ) /
                Real.sqrt ((split.fold n k).card : ℝ) := by
          rw [Real.sqrt_div hn_pos.le]
        have hsqrtc_sq :
            Real.sqrt ((split.fold n k).card : ℝ) *
                Real.sqrt ((split.fold n k).card : ℝ) =
              ((split.fold n k).card : ℝ) :=
          Real.mul_self_sqrt hcard_pos.le
        have hsqrtc_pow :
            Real.sqrt ((split.fold n k).card : ℝ) ^ 2 =
              ((split.fold n k).card : ℝ) := by
          rw [sq, hsqrtc_sq]
        have hsum_center :
            ∑ i ∈ split.fold n k,
                (foldScoreDiff n k ω (sample.Z i ω) -
                  ∫ z, foldScoreDiff n k ω z ∂P_Z) =
              ∑ i ∈ split.fold n k,
                  foldScoreDiff n k ω (sample.Z i ω) -
                ((split.fold n k).card : ℝ) *
                  ∫ z, foldScoreDiff n k ω z ∂P_Z := by
          simp [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        unfold scoreRaw scoreScale foldCentered foldBias
        rw [hsum_center, hsqrt_div]
        field_simp [hK_ne, hcard_pos.ne', hsqrtn_pos.ne', hsqrtc_pos.ne',
          hsqrtc_sq]
        rw [hsqrtc_pow]
        ring
      have hfold_piece :
          ∀ k : Fin K,
            IsLittleOp
              (fun n ω => ratioRaw k n ω + scoreRaw k n ω)
              (fun _ => (1 : ℝ)) μ := by
        intro k
        exact IsLittleOp_add_one (hratio_raw k) (hscore_raw k)
      have hsum_pieces :
          IsLittleOp
            (fun n ω =>
              ∑ k : Fin K, (ratioRaw k n ω + scoreRaw k n ω))
            (fun _ => (1 : ℝ)) μ := by
        simpa using
          IsLittleOp_finset_sum_one (Finset.univ : Finset (Fin K))
            (fun k n ω => ratioRaw k n ω + scoreRaw k n ω)
            (by intro k hk; exact hfold_piece k)
      have hdecomp :
          (fun n ω =>
            Real.sqrt ((Finset.range n).card : ℝ) *
                (dmlCrossFitEstimator M sample split η_hat n ω - M.θ₀) -
              (Real.sqrt ((Finset.range n).card : ℝ))⁻¹ *
                ∑ i ∈ Finset.range n,
                  (-M.J₀_inv * M.m M.η₀ (sample.Z i ω) M.θ₀))
          =
          (fun n ω =>
            -M.J₀_inv *
              ∑ k : Fin K, (ratioRaw k n ω + scoreRaw k n ω)) := by
        funext n ω
        have hif_sum :
            (∑ i ∈ Finset.range n,
                -M.J₀_inv * M.m M.η₀ (sample.Z i ω) M.θ₀) =
              ∑ k : Fin K,
                -M.J₀_inv *
                  ∑ i ∈ split.fold n k,
                    M.m M.η₀ (sample.Z i ω) M.θ₀ := by
          calc
            (∑ i ∈ Finset.range n,
                -M.J₀_inv * M.m M.η₀ (sample.Z i ω) M.θ₀)
                =
              ∑ k : Fin K, ∑ i ∈ split.fold n k,
                -M.J₀_inv * M.m M.η₀ (sample.Z i ω) M.θ₀ := by
                rw [← split.cover n]
                rw [Finset.sum_biUnion]
                intro k hk l hl hkl
                exact split.partition n k l hkl
            _ =
              ∑ k : Fin K,
                -M.J₀_inv *
                  ∑ i ∈ split.fold n k,
                    M.m M.η₀ (sample.Z i ω) M.θ₀ := by
                simp_rw [← Finset.mul_sum]
        have hscore_decomp : ∀ k : Fin K,
            (∑ i ∈ split.fold n k,
              M.m (η_hat n k ω) (sample.Z i ω) M.θ₀) =
              (∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)) +
                ∑ i ∈ split.fold n k,
                  foldScoreDiff n k ω (sample.Z i ω) := by
          intro k
          unfold foldScoreDiff
          simp [Finset.sum_sub_distrib, ψ₀]
        have hweighted_decomp :
            (∑ k : Fin K,
              ((split.fold n k).card : ℝ)⁻¹ *
                ∑ i ∈ split.fold n k,
                  M.m (η_hat n k ω) (sample.Z i ω) M.θ₀) =
              ∑ k : Fin K,
                ((split.fold n k).card : ℝ)⁻¹ *
                  ((∑ i ∈ split.fold n k, ψ₀ (sample.Z i ω)) +
                    ∑ i ∈ split.fold n k,
                      foldScoreDiff n k ω (sample.Z i ω)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hscore_decomp k]
        unfold dmlCrossFitEstimator ratioRaw scoreRaw
        rw [Finset.card_range, hif_sum]
        rw [hweighted_decomp]
        simp only [ψ₀, Finset.mul_sum, Finset.sum_neg_distrib,
          Finset.sum_add_distrib, mul_add,
          neg_mul, mul_neg, sub_eq_add_neg]
        ring_nf
      rw [hdecomp]
      exact IsLittleOp_const_mul_one (-M.J₀_inv) hsum_pieces
    simpa using h_full_reweighting

end OrthogonalMoments
end Estimation
end Causalean
