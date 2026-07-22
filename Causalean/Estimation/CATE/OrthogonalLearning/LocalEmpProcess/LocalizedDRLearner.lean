/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized empirical-process modulus for the DR-Learner

Apply the generic localized critical-radius bridge
`OrthogonalLearning/LocalEmpProcess/Localized.lean` to the DR-Learner `LearningSystem`
from `OrthogonalLearning/DRLearner.lean`. Chained with
`OrthogonalLearning/OracleInequality.lean`, it yields:

    ‖τ̂_n − τ₀‖² = O_p(δ_n² + nuisance_remainder²)

where `δ_n := criticalRadius ψ` is the population critical radius of the
centred DR-loss class and the nuisance remainder is the cross-fitting
remainder controlled by the upstream identification proof.

Sibling: `Estimation/CATE/OrthogonalLearning/LocalEmpProcess/DRLearner.lean`
realises the non-localized Rademacher rate on nonempty
estimation folds, with an empty-fold `√(2b)` boundary branch. The two files
share the boundedness predicates (`DREvalBounded`, `DROutcomeBounded`,
`DRNuisanceOverlap`) and the `dr_loss_uniformly_bounded` bridge.
-/

import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Localized
import Causalean.Estimation.CATE.OrthogonalLearning.LocalEmpProcess.DRLearner
import Causalean.Estimation.CATE.OrthogonalLearning.DRLearner

/-! # Localized Modulus for the DR-Learner

This file applies the localized empirical-process modulus theorem to the
DR-Learner for conditional average treatment effects. It formulates the
critical-radius hypothesis for the centered quadratic DR-loss class and derives
both the sharp localized modulus and a bounded-loss fallback modulus. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.CATE
  Causalean.Stat Causalean.Stat.Concentration

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]

/-- **Critical-radius hypothesis for the DR-Learner.**

Packages "the centred DR-loss class has population Rademacher complexity
bounded by a sub-root function `ψ`" as a deterministic hypothesis.

The critical radius is treated as a deterministic, population-level object:
callers supply `ψ` together with the sub-root proof, and the bridge consumes
`criticalRadius ψ` as the
localized rate.

The complexity bound is stated via `RademacherUpperBound` against the
centred quadratic DR-loss class indexed by an `ℕ`-dense sequence
`idx : ℕ → Θ_set`:

    f_k(z) := (φ_η(z) − eval (idx k) z.1)² − (φ_η(z) − S.τ_val z.1)²,

evaluated under the data law `S.P_Z` (with `id` for the sample map). -/
def DRCriticalRadius
    {Θ : Type*}
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ_set : Set Θ) (eval : Θ → γ → ℝ)
    (idx : ℕ → Θ_set)
    (h : NuisanceVec γ)
    (norm : ((γ × Bool × ℝ) → ℝ) → ℝ)
    (ψ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, SubRoot (ψ n)) ∧
    ∀ n : ℕ,
      RademacherUpperBound
        (fun (k : ℕ) (z : γ × Bool × ℝ) =>
          (phi_eta z h - eval (idx k).val z.1) ^ 2
            - (phi_eta z h - S.τ_val z.1) ^ 2)
        norm S.toBackdoorEstimationSystem.P_Z (id : (γ × Bool × ℝ) → γ × Bool × ℝ)
        n (ψ n)

/-- **DR-Learner localized modulus, sharp Foster–Syrgkanis form.**

The DR-Learner orthogonal-learning system, under bounded eval / outcomes / overlap and a
sub-root critical-radius hypothesis on the centred loss class, satisfies
the `LocalEmpProcessModulus` predicate with the FS Lemma 29 rate

    ρ n = (8 · L + 3) · criticalRadius (ψ |B(n)|)

(falling back to `√(2 · b)` on empty fold-B). The conclusion's existential
`b` is the centred DR-loss envelope `2 * b_loss`, where `b_loss` is the
explicit `(M_Θ + Mφ)²` value extracted by `dr_loss_uniformly_bounded`,
with `Mφ := 2·M_μ + 2·(M_Y + M_μ)/ε`.

Chained with the orthogonal-learning oracle inequality, this delivers the
localized critical-radius rate
`‖τ̂_n − τ₀‖² = O_p(δ_n² + nuisance²)`.

The sharp hypotheses are explicit inputs: the caller supplies the
Lipschitz constant `L` (and proof) for the centred DR-loss class, the
diameter control, the critical-radius facts for `ψ`, the local Rademacher
bridge, and the FS critical-radius lower-bound `hδ_dom` consumed by
`localEmpProcessModulus_of_localized_sharp`. -/
theorem localEmpProcessModulus_localized_drLearner
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [IsProbabilityMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    [Nonempty Θ_set] [Countable Θ_set]
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (S_iid : IIDSample P.Ω (γ × Bool × ℝ) P.μ
      S.toBackdoorEstimationSystem.P_Z)
    (split : OneShotSplit S_iid)
    {M_Θ M_Y M_μ ε : ℝ}
    (hM_Θ : DREvalBounded Θ_set eval M_Θ)
    (hM_Y : DROutcomeBounded S M_Y)
    (h : NuisanceVec γ)
    (hM_μ : DRNuisanceMuBounded h M_μ)
    (hOverlap : DRNuisanceOverlap S Θ_set h ε)
    (_hLoss_cont : ∀ z,
      Continuous fun (θ :
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set) =>
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h)
    (idx : ℕ →
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
    (_idx_dense : DenseRange idx)
    {norm : ((γ × Bool × ℝ) → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ}
    (hψ : DRCriticalRadius S Θ_set eval
      (fun k => ⟨((idx k).val), (idx k).property⟩)
      h norm ψ)
    (hnorm_ae : ∀ F F' : (γ × Bool × ℝ) → ℝ,
      F =ᵐ[S.toBackdoorEstimationSystem.P_Z] F' → norm F = norm F')
    {Rmax L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hF_lip : ∀ θ ∈
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set,
      norm (fun z =>
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ h
          - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
        ≤ L * ‖θ -
            (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀‖)
    (hF_diam : ∀ θ ∈
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set,
      norm (fun z =>
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ h
          - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
        ≤ Rmax)
    (hRmax_lb : ∀ m : ℕ, criticalRadius (ψ m) ≤ Rmax)
    (hcrit_pos : ∀ m : ℕ, 0 < criticalRadius (ψ m))
    (hcrit_fp : ∀ m : ℕ, ψ m (criticalRadius (ψ m)) ≤ (criticalRadius (ψ m)) ^ 2)
    (hψ_ub : ∀ m : ℕ,
      RademacherUpperBound
        (fun (θ :
            (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
          (z : γ × Bool × ℝ) =>
          (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h
            - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
                (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
        norm S.toBackdoorEstimationSystem.P_Z
        (id : (γ × Bool × ℝ) → γ × Bool × ℝ) m (ψ m))
    -- BddAbove hypothesis needed by the bridge lemma inside `localized_uniform_deviation`.
    (hrad_bdd : ∀ m r, ∀ S_fin : Fin m → γ × Bool × ℝ, ∀ σ : Signs m,
      BddAbove (Set.range fun p : starHullParam
            (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
          starHullZeroOut
            (fun (θ :
                (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
              (z : γ × Bool × ℝ) =>
              (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h
                - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
                    (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
            norm r p (S_fin k)|))
    -- Integrability of the upper empirical Rademacher process (bridge prerequisite).
    (hrad_int : ∀ m r,
      Integrable
        (fun ω : Fin m → γ × Bool × ℝ =>
          empiricalRademacherComplexity m
            (starHullZeroOut
              (fun (θ :
                  (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
                (z : γ × Bool × ℝ) =>
                (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h
                  - (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z
                      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).θ₀ h)
              norm r) ((id : (γ × Bool × ℝ) → (γ × Bool × ℝ)) ∘ ω))
        (Measure.pi (fun _ => S.toBackdoorEstimationSystem.P_Z)))
    (hclamp_minimizes : CenteredClampedThetaMinimizes
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
      (2 * (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2))
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    -- Foster–Syrgkanis Lemma 29 critical-radius lower bound (peeling-aware):
    -- for any dyadic shell count `K` covering `Rmax`, the McDiarmid slack at
    -- the union-bound-adjusted confidence `δ / (2 (K + 1))` (against the
    -- centred-loss bound `2 * (M_Θ + 2*M_μ + 2*(M_Y + M_μ)/ε)^2`) is
    -- dominated by the squared critical radius. Forwarded directly to
    -- `localEmpProcessModulus_of_localized_sharp`.
    (hδ_dom : ∀ n K : ℕ, 0 < (split.foldB n).card →
      Rmax ≤ (criticalRadius (ψ (split.foldB n).card)) * (2 : ℝ) ^ K →
      2 * (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2 *
          Real.sqrt
            (2 * Real.log (2 * ((K : ℝ) + 1) / δ) / (split.foldB n).card)
        ≤ (criticalRadius (ψ (split.foldB n).card)) ^ 2) :
    ∃ b : ℝ, 0 ≤ b ∧
      LocalEmpProcessModulus
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
        S_iid split
        (fun n =>
          if (split.foldB n).card = 0 then Real.sqrt (2 * b)
          else (8 * L + 3) * criticalRadius (ψ (split.foldB n).card)) δ h := by
  classical
  let Ssys := drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes
  haveI : Nonempty Ssys.Θ_set := inferInstanceAs (Nonempty Θ_set)
  haveI : Countable Ssys.Θ_set := inferInstanceAs (Countable Θ_set)
  haveI hPZ : IsProbabilityMeasure S.toBackdoorEstimationSystem.P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  set b_loss : ℝ := (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2 with hb_loss_def
  have hb_loss_nonneg : 0 ≤ b_loss := sq_nonneg _
  have hb_loss : UniformlyBoundedLossAE Ssys h b_loss :=
    dr_loss_uniformly_bounded S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀
      θ₀_minimizes hM_Θ hM_Y h hM_μ hOverlap
  refine ⟨2 * b_loss, by linarith, ?_⟩
  have h_centred_ae :
      ∀ᵐ z ∂S.toBackdoorEstimationSystem.P_Z, ∀ θ ∈ Ssys.Θ_set,
        |Ssys.ℓ z θ h - Ssys.ℓ z Ssys.θ₀ h| ≤ 2 * b_loss := by
    filter_upwards [hb_loss] with z hz
    intro θ hθ
    have h1 : |Ssys.ℓ z θ h| ≤ b_loss := hz θ hθ
    have h2 : |Ssys.ℓ z Ssys.θ₀ h| ≤ b_loss := hz Ssys.θ₀ Ssys.θ₀_mem
    have htri := abs_sub (Ssys.ℓ z θ h) (Ssys.ℓ z Ssys.θ₀ h)
    linarith
  have hℓ_meas_sys :
      ∀ θ ∈ Ssys.Θ_set, Measurable (fun z => Ssys.ℓ z θ h) := by
    intro θ _hθ
    exact Ssys.ℓ_meas θ h
  have hℓ_int_sys :
      ∀ θ ∈ Ssys.Θ_set,
        Integrable (fun z => Ssys.ℓ z θ h) S.toBackdoorEstimationSystem.P_Z := by
    intro θ hθ
    exact Integrable.of_bound (Ssys.ℓ_meas θ h).aestronglyMeasurable b_loss
      (by
        filter_upwards [hb_loss] with z hz
        simpa [Real.norm_eq_abs] using hz θ hθ)
  have hloss_eq :
      (fun (k : ℕ) (z : γ × Bool × ℝ) =>
          Ssys.ℓ z (idx k).val h - Ssys.ℓ z Ssys.θ₀ h)
        = fun (k : ℕ) (z : γ × Bool × ℝ) =>
          (phi_eta z h - eval (idx k).val z.1) ^ 2
            - (phi_eta z h - S.τ_val z.1) ^ 2 := by
    funext k z
    change (phi_eta z h - eval (idx k).val z.1) ^ 2
          - (phi_eta z h - eval θ₀ z.1) ^ 2
        = (phi_eta z h - eval (idx k).val z.1) ^ 2
          - (phi_eta z h - S.τ_val z.1) ^ 2
    rw [eval_θ₀ z.1]
  have hreg :
      LocalizedRademacherRegimeAE Ssys S_iid split h idx norm ψ (2 * b_loss) := by
    refine ⟨by linarith, h_centred_ae, hψ.1, ?_⟩
    intro n
    have hub := hψ.2 (split.foldB n).card
    rw [hloss_eq]
    exact hub
  -- The caller's `hδ_dom` is stated against `2 * (M_Θ + Mφ)^2 = 2 * b_loss` (by `hb_loss_def`).
  exact localEmpProcessModulus_of_localized_sharp_ae
    (S := Ssys) (S_iid := S_iid) (split := split)
    (g := h) (_hg_cont := _hLoss_cont) (idx := idx) (_idx_dense := _idx_dense)
    (norm := norm) (hnorm_ae := hnorm_ae) (ψ := ψ) (L := L)
    (b := 2 * b_loss) (Rmax := Rmax)
    (hreg := hreg) (hL_nonneg := hL_nonneg) (hF_lip := hF_lip)
    (hℓ_meas := hℓ_meas_sys) (hℓ_int := hℓ_int_sys)
    (hF_diam := hF_diam) (hRmax_lb := hRmax_lb)
    (hcrit_pos := hcrit_pos) (hcrit_fp := hcrit_fp)
    (hψ_ub := hψ_ub) (hrad_bdd := fun m r S_fin σ => hrad_bdd m r S_fin σ)
    (hrad_int := fun m r => hrad_int m r)
    (hclamp_minimizes := by
      simpa [Ssys, hb_loss_def] using hclamp_minimizes)
    (hδ := hδ) (hδ' := hδ') (hδ_dom := hδ_dom)

/-- **DR-Learner bounded-loss localized modulus.**

Bounded-loss fallback chain: applies `dr_loss_uniformly_bounded` to
extract a uniform DR-loss bound `b`, then chains
`localEmpProcessModulus_of_localized_bounded` to discharge
`LocalEmpProcessModulus` with the conservative rate `ρ n := √(2 · 2b)`.

This rate does not use the sub-root envelope `ψ` — it is a deterministic
bound that holds regardless of the critical radius. Use the sharp version
(`localEmpProcessModulus_localized_drLearner` above) when critical-radius
control is available. -/
theorem localEmpProcessModulus_localized_drLearner_bounded
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [IsProbabilityMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    [Nonempty Θ_set]
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (S_iid : IIDSample P.Ω (γ × Bool × ℝ) P.μ
      S.toBackdoorEstimationSystem.P_Z)
    (split : OneShotSplit S_iid)
    {M_Θ M_Y M_μ ε : ℝ}
    (hM_Θ : DREvalBounded Θ_set eval M_Θ)
    (hM_Y : DROutcomeBounded S M_Y)
    (h : NuisanceVec γ)
    (hM_μ : DRNuisanceMuBounded h M_μ)
    (hOverlap : DRNuisanceOverlap S Θ_set h ε)
    (_hLoss_cont : ∀ z,
      Continuous fun (θ :
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set) =>
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).ℓ z θ.val h)
    (idx : ℕ →
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes).Θ_set)
    (_idx_dense : DenseRange idx)
    {norm : ((γ × Bool × ℝ) → ℝ) → ℝ}
    {ψ : ℕ → ℝ → ℝ}
    (hψ : DRCriticalRadius S Θ_set eval
      (fun k => ⟨((idx k).val), (idx k).property⟩)
      h norm ψ)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∃ b : ℝ, 0 ≤ b ∧
      LocalEmpProcessModulus
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes)
        S_iid split
        (fun _n => Real.sqrt (2 * (2 * b))) δ h := by
  classical
  let Ssys := drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes
  -- Nonempty instance for the system's parameter set.
  haveI : Nonempty Ssys.Θ_set := inferInstanceAs (Nonempty Θ_set)
  -- Probability-measure instance for P_Z (used by populationRisk integrability).
  haveI hPZ : IsProbabilityMeasure S.toBackdoorEstimationSystem.P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  -- Step 1: extract uniform loss bound `b`.
  set b : ℝ := (M_Θ + 2 * M_μ + 2 * (M_Y + M_μ) / ε) ^ 2 with hb_def
  have hb_nonneg : 0 ≤ b := sq_nonneg _
  have hb_loss : UniformlyBoundedLossAE Ssys h b :=
    dr_loss_uniformly_bounded S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀
      θ₀_minimizes hM_Θ hM_Y h hM_μ hOverlap
  refine ⟨b, hb_nonneg, ?_⟩
  -- Step 2: derive the centred a.e. bound (factor 2).
  have h_centred_ae :
      ∀ᵐ z ∂S.toBackdoorEstimationSystem.P_Z, ∀ θ ∈ Ssys.Θ_set,
        |Ssys.ℓ z θ h - Ssys.ℓ z Ssys.θ₀ h| ≤ 2 * b := by
    filter_upwards [hb_loss] with z hz
    intro θ hθ
    have h1 : |Ssys.ℓ z θ h| ≤ b := hz θ hθ
    have h2 : |Ssys.ℓ z Ssys.θ₀ h| ≤ b := hz Ssys.θ₀ Ssys.θ₀_mem
    have htri := abs_sub (Ssys.ℓ z θ h) (Ssys.ℓ z Ssys.θ₀ h)
    linarith
  -- Step 3: derive the centred population bound via integration.
  have h_centred_pop :
      ∀ θ ∈ Ssys.Θ_set, |Ssys.L θ h - Ssys.L Ssys.θ₀ h| ≤ 2 * b := by
    intro θ hθ
    have hint_θ : Integrable (fun z => Ssys.ℓ z θ h)
        S.toBackdoorEstimationSystem.P_Z :=
      Integrable.of_bound (Ssys.ℓ_meas θ h).aestronglyMeasurable b
        (by
          filter_upwards [hb_loss] with z hz
          simpa [Real.norm_eq_abs] using hz θ hθ)
    have hint_0 : Integrable (fun z => Ssys.ℓ z Ssys.θ₀ h)
        S.toBackdoorEstimationSystem.P_Z :=
      Integrable.of_bound (Ssys.ℓ_meas Ssys.θ₀ h).aestronglyMeasurable b
        (by
          filter_upwards [hb_loss] with z hz
          simpa [Real.norm_eq_abs] using hz Ssys.θ₀ Ssys.θ₀_mem)
    have hL_eq :
        Ssys.L θ h - Ssys.L Ssys.θ₀ h
          = ∫ z, Ssys.ℓ z θ h - Ssys.ℓ z Ssys.θ₀ h
              ∂S.toBackdoorEstimationSystem.P_Z := by
      change (∫ z, Ssys.ℓ z θ h ∂S.toBackdoorEstimationSystem.P_Z)
            - (∫ z, Ssys.ℓ z Ssys.θ₀ h ∂S.toBackdoorEstimationSystem.P_Z)
          = _
      rw [← integral_sub hint_θ hint_0]
    rw [hL_eq]
    calc
      |∫ z, Ssys.ℓ z θ h - Ssys.ℓ z Ssys.θ₀ h
          ∂S.toBackdoorEstimationSystem.P_Z|
          ≤ ∫ z, |Ssys.ℓ z θ h - Ssys.ℓ z Ssys.θ₀ h|
              ∂S.toBackdoorEstimationSystem.P_Z := abs_integral_le_integral_abs
      _ ≤ ∫ _z, 2 * b ∂S.toBackdoorEstimationSystem.P_Z := by
          apply integral_mono_ae
          · exact (hint_θ.sub hint_0).abs
          · exact integrable_const _
          · filter_upwards [h_centred_ae] with z hz
            exact hz θ hθ
      _ = 2 * b := by simp
  -- Step 4: package the LocalizedRademacherRegime for Ssys.
  have hloss_eq :
      (fun (k : ℕ) (z : γ × Bool × ℝ) =>
          Ssys.ℓ z (idx k).val h - Ssys.ℓ z Ssys.θ₀ h)
        = fun (k : ℕ) (z : γ × Bool × ℝ) =>
          (phi_eta z h - eval (idx k).val z.1) ^ 2
            - (phi_eta z h - S.τ_val z.1) ^ 2 := by
    funext k z
    change (phi_eta z h - eval (idx k).val z.1) ^ 2
          - (phi_eta z h - eval θ₀ z.1) ^ 2
        = (phi_eta z h - eval (idx k).val z.1) ^ 2
          - (phi_eta z h - S.τ_val z.1) ^ 2
    rw [eval_θ₀ z.1]
  have hreg :
      LocalizedRademacherRegimeAE Ssys S_iid split h idx norm ψ (2 * b) := by
    refine ⟨by linarith, h_centred_ae, hψ.1, ?_⟩
    intro n
    have hub := hψ.2 (split.foldB n).card
    rw [hloss_eq]
    exact hub
  -- Step 5: apply the bounded fallback bridge.
  exact localEmpProcessModulus_of_localized_bounded_ae
    (S := Ssys) (S_iid := S_iid) (split := split)
    (g := h) (idx := idx)
    (norm := norm) (ψ := ψ) (b := 2 * b)
    (hreg := hreg) (hpop_center := h_centred_pop)
    (_hδ := hδ) (_hδ' := hδ')

end OrthogonalLearning
end Estimation
end Causalean
