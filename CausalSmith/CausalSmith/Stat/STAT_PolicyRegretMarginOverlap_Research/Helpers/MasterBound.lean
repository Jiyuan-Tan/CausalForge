/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.SelfBound
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.BochnerIntegrability

/-! Provides feasible ERM bridge and master-bound algebra helpers. -/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: lem:feasible-erm-welfare-bridge
/-- `lem:feasible-erm-welfare-bridge`. Sample-wise welfare-identity selection
inequality for the feasible clipped-AIPW `1/n`-ERM. Writing `π̂ = feasibleERM …`,
`g = clippedPolicyIncrement P q η̂` (the contrast increment `(π−π_⋆)·Γ_q`), and
`w_k = |I_k|/n`, the population welfare identity
`Ŝ_n(π) − Ŝ_n(π_⋆) = G_cf(π) − R_P(π) + Σ_k w_k drift_k(π)` — obtained foldwise from
`clip_bias`'s conditional-mean drift decomposition applied to the bounded measurable
test `φ(x) = 1{π(x)} − 1{π_⋆(x)}` — together with the `1/n` empirical near-max
inequality of `feasible_erm_basic_inequality` (applied at `π_⋆ ∈ Π` via
`OptimalInClass`) yields the COEFFICIENT-ONE selection bound
`R_P(π̂) ≤ |G_cf(π̂)| + |Σ_k w_k drift_k(π̂)| + 1/n`.

The coefficient ONE (not two) on `|G_cf|` is load-bearing: the master-bound assembly
spends the slack to `2|G_cf|` (the form `localized_vc_self_bound` consumes) on the
Young absorption of the regret-dependent drift term `r_μ (R_P(π̂)/u)^{1/2}`. -/
lemma feasible_erm_welfare_bridge {n K : ℕ} (P : ObservedLaw 𝒳) (q : ℝ)
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ)
    (assign : Fin n → Fin K) (policySet : Set (Policy 𝒳)) (dPi : ℕ)
    (hvc : PolicyClassVC policySet dPi) (hopt : OptimalInClass P policySet)
    (hskel : DenseSkeleton enum policySet)
    (hwf : WellFormedLaw P) (hbdd : BoundedOutcome P) (hpos : Positivity P)
    (hμ0meas : ∀ k : Fin K, Measurable (muHat0 k))
    (hμ1meas : ∀ k : Fin K, Measurable (muHat1 k))
    (hemeas : ∀ k : Fin K, Measurable (eHat k))
    (hμ0bdd : ∀ k : Fin K, ∃ M : ℝ, ∀ x, |muHat0 k x| ≤ M)
    (hμ1bdd : ∀ k : Fin K, ∃ M : ℝ, ∀ x, |muHat1 k x| ≤ M)
    (hq : 0 < q) (hq1 : q < 1) (hn : 0 < n)
    (sample : Fin n → Observation 𝒳) :
    lawRegret P (feasibleERM q enum muHat0 muHat1 eHat assign sample)
      ≤ |pooledCrossfitProcess P (clippedPolicyIncrement P q muHat0 muHat1 eHat)
            assign sample (feasibleERM q enum muHat0 muHat1 eHat assign sample)|
        + |∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
              driftIntegral P q (muHat0 k) (muHat1 k) (eHat k)
                (feasibleERM q enum muHat0 muHat1 eHat assign sample)|
        + (n : ℝ)⁻¹ := by
  classical
  let πhat : Policy 𝒳 := feasibleERM q enum muHat0 muHat1 eHat assign sample
  let πstar : Policy 𝒳 := lawOptimalPolicy P
  let g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrement P q muHat0 muHat1 eHat
  let S : Policy 𝒳 → ℝ :=
    empiricalWelfareScore q muHat0 muHat1 eHat assign sample
  let G : Policy 𝒳 → ℝ :=
    pooledCrossfitProcess P g assign sample
  let D : Policy 𝒳 → ℝ := fun π =>
    ∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
      driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π
  have hbridge_identity :
      ∀ π ∈ policySet, lawRegret P π = G π + D π - (S π - S πstar) := by
    intro π hπmem
    have hπmeas : Measurable π := hvc.1 π hπmem
    have hstar_mem : πstar ∈ policySet := by simpa [πstar] using hopt
    have hstarmeas : Measurable πstar := hvc.1 πstar hstar_mem
    have hπind_meas : Measurable (fun x : 𝒳 => boolIndicator (π x)) :=
      (measurable_of_finite (fun b : Bool => boolIndicator b)).comp hπmeas
    have hstarind_meas : Measurable (fun x : 𝒳 => boolIndicator (πstar x)) :=
      (measurable_of_finite (fun b : Bool => boolIndicator b)).comp hstarmeas
    let φ : 𝒳 → ℝ := fun x => boolIndicator (π x) - boolIndicator (πstar x)
    have hφmeas : Measurable φ := hπind_meas.sub hstarind_meas
    have hφbdd : ∃ M : ℝ, ∀ x, |φ x| ≤ M := by
      refine ⟨2, ?_⟩
      intro x
      dsimp [φ]
      cases π x <;> cases πstar x <;> norm_num [boolIndicator]
    have hτmeas : Measurable P.contrast := by
      rcases hwf with ⟨_, _, _, hτmeas, _⟩
      exact hτmeas
    letI : IsProbabilityMeasure P.PX := by
      rcases hwf with ⟨_, hPXprob, _⟩
      exact hPXprob
    have hπind_bdd : ∃ M : ℝ, ∀ x, |boolIndicator (π x)| ≤ M := by
      refine ⟨1, ?_⟩
      intro x
      cases π x <;> simp [boolIndicator]
    have hstarind_bdd : ∃ M : ℝ, ∀ x, |boolIndicator (πstar x)| ≤ M := by
      refine ⟨1, ?_⟩
      intro x
      cases πstar x <;> simp [boolIndicator]
    have hπterm_int :
        Integrable (fun x : 𝒳 => boolIndicator (π x) * P.contrast x) P.PX :=
      integrable_of_measurable_bounded (hπind_meas.mul hτmeas)
        (bounded_mul hπind_bdd (bounded_law_contrast P hwf hbdd))
    have hstarterm_int :
        Integrable (fun x : 𝒳 => boolIndicator (πstar x) * P.contrast x) P.PX :=
      integrable_of_measurable_bounded (hstarind_meas.mul hτmeas)
        (bounded_mul hstarind_bdd (bounded_law_contrast P hwf hbdd))
    have hcontrast :
        ∫ x, φ x * P.contrast x ∂P.PX = -lawRegret P π := by
      have hpoint :
          (fun x : 𝒳 => φ x * P.contrast x) =
            fun x => boolIndicator (π x) * P.contrast x -
              boolIndicator (πstar x) * P.contrast x := by
        funext x
        dsimp [φ]
        ring
      calc
        ∫ x, φ x * P.contrast x ∂P.PX
            = ∫ x, (boolIndicator (π x) * P.contrast x -
                boolIndicator (πstar x) * P.contrast x) ∂P.PX := by
              rw [hpoint]
        _ = ∫ x, boolIndicator (π x) * P.contrast x ∂P.PX -
              ∫ x, boolIndicator (πstar x) * P.contrast x ∂P.PX := by
              rw [integral_sub hπterm_int hstarterm_int]
        _ = -lawRegret P π := by
              dsimp [πstar]
              unfold lawRegret regret welfare lawOptimalPolicy
              norm_num
    have hscore_split :
        S π - S πstar =
          (n : ℝ)⁻¹ * ∑ i : Fin n, g (assign i) π (sample i) := by
      dsimp [S, g, πstar, empiricalWelfareScore, clippedPolicyIncrement]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    have hdecomp :
        (n : ℝ)⁻¹ * ∑ i : Fin n, g (assign i) π (sample i) =
          G π + (n : ℝ)⁻¹ *
            ∑ i : Fin n, ∫ O, g (assign i) π O ∂P.dataMeasure := by
      dsimp [G, pooledCrossfitProcess]
      have hsum :
          (∑ i : Fin n, g (assign i) π (sample i)) =
            ∑ i : Fin n,
              ((g (assign i) π (sample i) -
                  ∫ O, g (assign i) π O ∂P.dataMeasure) +
                ∫ O, g (assign i) π O ∂P.dataMeasure) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      rw [hsum, Finset.sum_add_distrib]
      ring
    have hmean_k :
        ∀ k : Fin K, ∫ O, g k π O ∂P.dataMeasure =
          -lawRegret P π + driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π := by
      intro k
      have hclip :=
        (clip_bias P q (muHat0 k) (muHat1 k) (eHat k) hwf hbdd hpos
          (hμ0meas k) (hμ1meas k) (hemeas k) (hμ0bdd k) (hμ1bdd k)
          hq hq1 φ hφmeas hφbdd).1
      calc
        ∫ O, g k π O ∂P.dataMeasure
            = ∫ O,
                φ O.X * clippedAIPWScore q (muHat0 k) (muHat1 k) (eHat k) O
                ∂P.dataMeasure := by
              simp [g, φ, clippedPolicyIncrement, πstar]
        _ = ∫ x, φ x * P.contrast x ∂P.PX +
              ∫ x, φ x * clipBias P q (muHat0 k) (muHat1 k) (eHat k) x ∂P.PX := by
              linarith [hclip]
        _ = -lawRegret P π +
              driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π := by
              simp [hcontrast, driftIntegral, φ, πstar]
    let H : Fin K → ℝ :=
      fun k => driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π
    have hmean_sum :
        (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ O, g (assign i) π O ∂P.dataMeasure =
          -lawRegret P π + D π := by
      have hreplace :
          (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ O, g (assign i) π O ∂P.dataMeasure =
            (n : ℝ)⁻¹ * ∑ i : Fin n, (-lawRegret P π + H (assign i)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _hi
        simpa [H] using hmean_k (assign i)
      calc
        (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ O, g (assign i) π O ∂P.dataMeasure
            = (n : ℝ)⁻¹ * ∑ i : Fin n, (-lawRegret P π + H (assign i)) := hreplace
        _ = -lawRegret P π + (n : ℝ)⁻¹ * ∑ i : Fin n, H (assign i) := by
              have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
              rw [Finset.sum_add_distrib]
              have hconst :
                  (∑ _i : Fin n, -lawRegret P π) =
                    (n : ℝ) * (-lawRegret P π) := by
                simp
              rw [hconst]
              field_simp [hnR]
        _ = -lawRegret P π + D π := by
              rw [inv_card_sum_assign_eq_sum_foldWeights assign H hn]
    have hscore_bridge : S π - S πstar = G π - lawRegret P π + D π := by
      calc
        S π - S πstar
            = (n : ℝ)⁻¹ * ∑ i : Fin n, g (assign i) π (sample i) := hscore_split
        _ = G π + (n : ℝ)⁻¹ *
              ∑ i : Fin n, ∫ O, g (assign i) π O ∂P.dataMeasure := hdecomp
        _ = G π + (-lawRegret P π + D π) := by rw [hmean_sum]
        _ = G π - lawRegret P π + D π := by ring
    linarith [hscore_bridge]
  have hbasic :=
    (feasible_erm_basic_inequality P q enum muHat0 muHat1 eHat assign policySet dPi
      hvc hopt hskel.1 hskel.2 hμ0meas hμ1meas hemeas hn).2 sample
  have hπhat_mem : πhat ∈ policySet := hbasic.1
  have hstar_near : S πstar ≤ S πhat + (n : ℝ)⁻¹ := by
    exact hbasic.2 πstar (by simpa [πstar] using hopt)
  have hslack : -(S πhat - S πstar) ≤ (n : ℝ)⁻¹ := by
    linarith
  have hfinal :
      lawRegret P πhat ≤ |G πhat| + |D πhat| + (n : ℝ)⁻¹ := by
    calc
      lawRegret P πhat
          = G πhat + D πhat - (S πhat - S πstar) :=
            hbridge_identity πhat hπhat_mem
      _ ≤ G πhat + D πhat + (n : ℝ)⁻¹ := by
            linarith
      _ ≤ |G πhat| + |D πhat| + (n : ℝ)⁻¹ := by
            have hGabs : G πhat ≤ |G πhat| := le_abs_self (G πhat)
            have hDabs : D πhat ≤ |D πhat| := le_abs_self (D πhat)
            linarith
  simpa [πhat, g, G, D] using hfinal

private lemma Aalpha_nonneg_le_one {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ Aalpha α ∧ Aalpha α ≤ 1 := by
  have hden : 0 < 2 + α := by linarith
  constructor
  · dsimp [Aalpha]
    exact div_nonneg (by linarith) hden.le
  · dsimp [Aalpha]
    exact div_le_one_of_le₀ (by linarith) hden.le

private lemma crude_trunc_offset_rpow_eq {n : ℕ} {q A : ℝ}
    (hn : 0 < n) (hq : 0 < q) :
    (((36 : ℝ) / q) ^ 2 / (n : ℝ)) ^ A =
      ((36 : ℝ) ^ 2) ^ A * (((n : ℝ) * q ^ 2) ^ (-A)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq2pos : 0 < q ^ 2 := sq_pos_of_pos hq
  have hrightbase : 0 < (n : ℝ) * q ^ 2 := mul_pos hnR hq2pos
  calc
    (((36 : ℝ) / q) ^ 2 / (n : ℝ)) ^ A
        = (((36 : ℝ) ^ 2) / ((n : ℝ) * q ^ 2)) ^ A := by
          congr 1
          field_simp [hq.ne', hnR.ne']
    _ = (((36 : ℝ) ^ 2) * (((n : ℝ) * q ^ 2)⁻¹)) ^ A := by
          rw [div_eq_mul_inv]
    _ = ((36 : ℝ) ^ 2) ^ A * (((n : ℝ) * q ^ 2)⁻¹) ^ A := by
          rw [Real.mul_rpow (sq_nonneg (36 : ℝ)) (inv_nonneg.mpr hrightbase.le)]
    _ = ((36 : ℝ) ^ 2) ^ A * (((n : ℝ) * q ^ 2) ^ (-A)) := by
          rw [Real.rpow_neg_eq_inv_rpow]

private lemma crude_trunc_offset_fixed_rpow_eq {n : ℕ} {q A : ℝ}
    (hn : 0 < n) (hq : 0 < q) :
    (((36 : ℝ) / q) ^ 2 / (n : ℝ)) ^ A =
      (((36 : ℝ) / q) ^ 2) ^ A * ((n : ℝ) ^ (-A)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hBnonneg : 0 ≤ ((36 : ℝ) / q) ^ 2 := sq_nonneg _
  calc
    (((36 : ℝ) / q) ^ 2 / (n : ℝ)) ^ A
        = ((((36 : ℝ) / q) ^ 2) * (n : ℝ)⁻¹) ^ A := by
          rw [div_eq_mul_inv]
    _ = (((36 : ℝ) / q) ^ 2) ^ A * ((n : ℝ)⁻¹) ^ A := by
          rw [Real.mul_rpow hBnonneg (inv_nonneg.mpr hnR.le)]
    _ = (((36 : ℝ) / q) ^ 2) ^ A * ((n : ℝ) ^ (-A)) := by
          rw [Real.rpow_neg_eq_inv_rpow]

private lemma crude_self_large {n : ℕ} {α B C p : ℝ}
    (hn : 1 ≤ n) (hα : 0 ≤ α) (hB : 1 ≤ B) (hC : 1 ≤ C) (hp : 0 ≤ p)
    (hlog : 1 ≤ Real.log (n : ℝ)) :
    (n : ℝ)⁻¹ ≤ C * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p) := by
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR1
  have hA := Aalpha_nonneg_le_one hα
  have hA0 : 0 ≤ Aalpha α := hA.1
  have hA1 : Aalpha α ≤ 1 := hA.2
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnRpos.le
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnR1
  have hBsq_ge : 1 ≤ B ^ 2 := by
    nlinarith [sq_nonneg (B - 1)]
  have hbase_ge_inv : (n : ℝ)⁻¹ ≤ B ^ 2 / (n : ℝ) := by
    rw [div_eq_mul_inv]
    simpa [one_mul] using mul_le_mul_of_nonneg_right hBsq_ge hinv_nonneg
  have hinv_le_invA : (n : ℝ)⁻¹ ≤ ((n : ℝ)⁻¹) ^ (Aalpha α) :=
    Real.self_le_rpow_of_le_one hinv_nonneg hinv_le_one hA1
  have hbaseA_ge :
      ((n : ℝ)⁻¹) ^ (Aalpha α) ≤ (B ^ 2 / (n : ℝ)) ^ (Aalpha α) :=
    Real.rpow_le_rpow hinv_nonneg hbase_ge_inv hA0
  have hterm_ge_inv : (n : ℝ)⁻¹ ≤ (B ^ 2 / (n : ℝ)) ^ (Aalpha α) :=
    le_trans hinv_le_invA hbaseA_ge
  have hlogpow : 1 ≤ (Real.log (n : ℝ)) ^ p := Real.one_le_rpow hlog hp
  have hbase_nonneg : 0 ≤ (B ^ 2 / (n : ℝ)) ^ (Aalpha α) := by positivity
  have hmul_log :
      (B ^ 2 / (n : ℝ)) ^ (Aalpha α) ≤
        (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p := by
    calc
      (B ^ 2 / (n : ℝ)) ^ (Aalpha α)
          = (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * 1 := by ring
      _ ≤ (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p :=
            mul_le_mul_of_nonneg_left hlogpow hbase_nonneg
  have hCmul :
      (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p ≤
        C * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p) := by
    have hprod_nonneg :
        0 ≤ (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p := by
      positivity
    calc
      (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p
          = 1 * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p) := by
            ring
      _ ≤ C * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log (n : ℝ)) ^ p) :=
            mul_le_mul_of_nonneg_right hC hprod_nonneg
  exact le_trans hterm_ge_inv (le_trans hmul_log hCmul)

-- @node: young_sqrt_absorb
private lemma young_sqrt_absorb {D m R u : ℝ}
    (hD : 0 ≤ D) (hm : 0 ≤ m) (hR : 0 ≤ R) (hu : 0 < u) :
    D * m * (R / u) ^ (1 / 2 : ℝ) ≤ R / 2 + D ^ 2 * m ^ 2 / (2 * u) := by
  have hsqrt_u_pos : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsqrt_u_ne : Real.sqrt u ≠ 0 := hsqrt_u_pos.ne'
  have hsqrt_div : (R / u) ^ (1 / 2 : ℝ) = Real.sqrt R / Real.sqrt u := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [Real.div_rpow hR hu.le]
  have hsq : 0 ≤ (Real.sqrt R - D * m / Real.sqrt u) ^ 2 := sq_nonneg _
  have hu_sqrt_sq : Real.sqrt u ^ 2 = u := by rw [Real.sq_sqrt hu.le]
  have hR_sqrt_sq : Real.sqrt R ^ 2 = R := by rw [Real.sq_sqrt hR]
  have hsq_core : 2 * Real.sqrt R * Real.sqrt u * (D * m) ≤ R * u + D ^ 2 * m ^ 2 := by
    field_simp [hsqrt_u_ne] at hsq
    nlinarith [hsq, hR_sqrt_sq, hu_sqrt_sq]
  have htarget :
      2 * Real.sqrt R * D * m * u ≤ Real.sqrt u * (R * u + D ^ 2 * m ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hsq_core hsqrt_u_pos.le
    calc
      2 * Real.sqrt R * D * m * u
          = 2 * Real.sqrt R * D * m * (Real.sqrt u) ^ 2 := by
            rw [hu_sqrt_sq]
      _ = Real.sqrt u * (2 * Real.sqrt R * Real.sqrt u * (D * m)) := by
            ring
      _ ≤ Real.sqrt u * (R * u + D ^ 2 * m ^ 2) := hmul
  rw [hsqrt_div]
  field_simp [hsqrt_u_ne, (by norm_num : (2 : ℝ) ≠ 0), hu.ne']
  nlinarith [htarget]

-- @node: weighted_drift_sum_bound_pos
private lemma weighted_drift_sum_bound_pos {n K : ℕ} (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (q rMu rE α γ Co co u0 underlineP : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (hsq0 : ∀ k : Fin K, ∫ x, (muHat0 k x - P.mu0 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hsq1 : ∀ k : Fin K, ∫ x, (muHat1 k x - P.mu1 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hse : ∀ k : Fin K, ∫ x, (eHat k x - P.propensity x) ^ 2 ∂P.PX ≤ rE ^ 2)
    (hμ0L2 : ∀ k : Fin K, MemLp (fun x => muHat0 k x - P.mu0 x) 2 P.PX)
    (hμ1L2 : ∀ k : Fin K, MemLp (fun x => muHat1 k x - P.mu1 x) 2 P.PX)
    (heL2 : ∀ k : Fin K, MemLp (fun x => eHat k x - P.propensity x) 2 P.PX)
    (hrMu_nonneg : 0 ≤ rMu) (hrE_nonneg : 0 ≤ rE)
    (hwf : WellFormedLaw P) (hπmeas : ∀ π ∈ policySet, Measurable π)
    (hq_half : q ≤ 1 / 2) (hod : OverlapDecay P u0 Co co α γ)
    (hze : ZeroEffectRegular P policySet) (hbdd : BoundedOutcome P)
    (hstrict : StrictOverlapEndpoint P γ underlineP) (hq : 0 < q)
    (hn : 0 < n) (hγpos : 0 < γ) (π : Policy 𝒳) (hπmem : π ∈ policySet)
    (u : ℝ) (hu : 0 < u) (hu_le : u ≤ u0) (hq_le : q ≤ co * u ^ γ) :
    |∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
        driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π|
      ≤ 4 * (1 + (max Co 1) ^ (1 / 2 : ℝ)) *
          (rMu * rE / q + rMu * u ^ (α / 2) * q ^ (1 / (2 * γ))
            + rMu * (lawRegret P π / u) ^ (1 / 2 : ℝ)) := by
  classical
  let Cd : ℝ := 4 * (1 + (max Co 1) ^ (1 / 2 : ℝ))
  let X : ℝ := rMu * rE / q + rMu * u ^ (α / 2) * q ^ (1 / (2 * γ))
            + rMu * (lawRegret P π / u) ^ (1 / 2 : ℝ)
  let w : Fin K → ℝ := fun k => (Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact div_nonneg (by positivity) (by exact_mod_cast hn.le)
  have hw_sum : (∑ k : Fin K, w k) = 1 := sum_foldWeights_eq_one assign hn
  have hCd_nonneg : 0 ≤ Cd := by
    dsimp [Cd]
    positivity
  have hX_nonneg : 0 ≤ X := by
    have hπ : Measurable π := hπmeas π hπmem
    have hR_nonneg : 0 ≤ lawRegret P π := lawRegret_nonneg P π hwf hbdd hπ
    dsimp [X]
    positivity
  have hterm : ∀ k : Fin K,
      |driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π| ≤ Cd * X := by
    intro k
    rcases localized_clipped_drift_bound P policySet q rMu rE α γ Co co u0 underlineP
        (muHat0 k) (muHat1 k) (eHat k) (hsq0 k) (hsq1 k) (hse k)
        (hμ0L2 k) (hμ1L2 k) (heL2 k) hrMu_nonneg hrE_nonneg hwf hπmeas
        hq_half hod hze hbdd hstrict hq with
      ⟨⟨C0, _hC0pos, hC0eq, hpos⟩, _⟩
    have hk := hpos hγpos π hπmem u hu hu_le hq_le
    simpa [Cd, X, hC0eq] using hk
  calc
    |∑ k : Fin K, w k * driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π|
        ≤ ∑ k : Fin K, |w k * driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin K, w k * |driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul, abs_of_nonneg (hw_nonneg k)]
    _ ≤ ∑ k : Fin K, w k * (Cd * X) := by
          exact Finset.sum_le_sum (fun k _ =>
            mul_le_mul_of_nonneg_left (hterm k) (hw_nonneg k))
    _ = Cd * X := by
          rw [← Finset.sum_mul]
          rw [hw_sum]
          ring

-- @node: weighted_drift_sum_bound_zero
private lemma weighted_drift_sum_bound_zero {n K : ℕ} (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (q rMu rE α γ Co co u0 underlineP : ℝ)
    (muHat0 muHat1 eHat : Fin K → 𝒳 → ℝ) (assign : Fin n → Fin K)
    (hsq0 : ∀ k : Fin K, ∫ x, (muHat0 k x - P.mu0 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hsq1 : ∀ k : Fin K, ∫ x, (muHat1 k x - P.mu1 x) ^ 2 ∂P.PX ≤ rMu ^ 2)
    (hse : ∀ k : Fin K, ∫ x, (eHat k x - P.propensity x) ^ 2 ∂P.PX ≤ rE ^ 2)
    (hμ0L2 : ∀ k : Fin K, MemLp (fun x => muHat0 k x - P.mu0 x) 2 P.PX)
    (hμ1L2 : ∀ k : Fin K, MemLp (fun x => muHat1 k x - P.mu1 x) 2 P.PX)
    (heL2 : ∀ k : Fin K, MemLp (fun x => eHat k x - P.propensity x) 2 P.PX)
    (hrMu_nonneg : 0 ≤ rMu) (hrE_nonneg : 0 ≤ rE)
    (hwf : WellFormedLaw P) (hπmeas : ∀ π ∈ policySet, Measurable π)
    (hq_half : q ≤ 1 / 2) (hod : OverlapDecay P u0 Co co α γ)
    (hze : ZeroEffectRegular P policySet) (hbdd : BoundedOutcome P)
    (hstrict : StrictOverlapEndpoint P γ underlineP) (hq : 0 < q)
    (hn : 0 < n) (hγ0 : γ = 0) (hq_under : q ≤ underlineP / 2)
    (π : Policy 𝒳) (hπmem : π ∈ policySet) :
    |∑ k : Fin K, ((Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)) *
        driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π|
      ≤ max 1 (2 / q) * (rMu * rE) := by
  classical
  let Cq : ℝ := max 1 (2 / q)
  let w : Fin K → ℝ := fun k => (Fintype.card (foldIndex assign k) : ℝ) / (n : ℝ)
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    exact div_nonneg (by positivity) (by exact_mod_cast hn.le)
  have hw_sum : (∑ k : Fin K, w k) = 1 := sum_foldWeights_eq_one assign hn
  have hprod_nonneg : 0 ≤ rMu * rE := mul_nonneg hrMu_nonneg hrE_nonneg
  have hterm : ∀ k : Fin K,
      |driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π| ≤ Cq * (rMu * rE) := by
    intro k
    rcases localized_clipped_drift_bound P policySet q rMu rE α γ Co co u0 underlineP
        (muHat0 k) (muHat1 k) (eHat k) (hsq0 k) (hsq1 k) (hse k)
        (hμ0L2 k) (hμ1L2 k) (heL2 k) hrMu_nonneg hrE_nonneg hwf hπmeas
        hq_half hod hze hbdd hstrict hq with
      ⟨_, ⟨C1, _hC1pos, hC1eq, hzero⟩⟩
    have hk := hzero hγ0 hq_under π hπmem
    simpa [Cq, hC1eq] using hk
  calc
    |∑ k : Fin K, w k * driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π|
        ≤ ∑ k : Fin K, |w k * driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin K, w k * |driftIntegral P q (muHat0 k) (muHat1 k) (eHat k) π| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul, abs_of_nonneg (hw_nonneg k)]
    _ ≤ ∑ k : Fin K, w k * (Cq * (rMu * rE)) := by
          exact Finset.sum_le_sum (fun k _ =>
            mul_le_mul_of_nonneg_left (hterm k) (hw_nonneg k))
    _ = Cq * (rMu * rE) := by
          rw [← Finset.sum_mul]
          rw [hw_sum]
          ring

private lemma crude_master_pos_algebra
    {C A E D Q L T1 T2 T3 T4 T5 S5 inv : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hL1 : 1 ≤ L)
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3)
    (hT4 : 0 ≤ T4) (hT5 : 0 ≤ T5)
    (hS5 : S5 ≤ T5 / 2)
    (hinv : inv ≤ A * T2 * L)
    (hC : C = 100 + 20 * (A + E + D + D ^ 2 + Q)) :
    (8 / 3 : ℝ) * (A * T2 * L + 2 * (D * (T3 + T4) + D ^ 2 * S5 + inv))
      ≤ C * (T1 + T2 + T3 + T4 + T5) * L := by
  subst C
  let C' : ℝ := 100 + 20 * (A + E + D + D ^ 2 + Q)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hCnonneg : 0 ≤ C' := by
    dsimp [C']
    nlinarith [hA, hE, hD, sq_nonneg D, hQ]
  have hCA : (8 : ℝ) * A ≤ C' := by
    dsimp [C']
    nlinarith [hA, hE, hD, sq_nonneg D, hQ]
  have hCD : (16 / 3 : ℝ) * D ≤ C' := by
    dsimp [C']
    nlinarith [hA, hE, hD, sq_nonneg D, hQ]
  have hCD2 : (8 / 3 : ℝ) * D ^ 2 ≤ C' := by
    dsimp [C']
    nlinarith [hA, hE, hD, sq_nonneg D, hQ]
  have hupper :
      (8 / 3 : ℝ) * (A * T2 * L + 2 * (D * (T3 + T4) + D ^ 2 * S5 + inv))
        ≤ 8 * A * T2 * L + (16 / 3) * D * T3 + (16 / 3) * D * T4 +
          (8 / 3) * D ^ 2 * T5 := by
    nlinarith [hinv, hS5, sq_nonneg D]
  have h2 : 8 * A * T2 * L ≤ C' * T2 * L := by
    have hT2L : 0 ≤ T2 * L := mul_nonneg hT2 hL0
    nlinarith [mul_le_mul_of_nonneg_right hCA hT2L]
  have h3 : (16 / 3 : ℝ) * D * T3 ≤ C' * T3 * L := by
    have hleft : (16 / 3 : ℝ) * D * T3 ≤ C' * T3 :=
      mul_le_mul_of_nonneg_right hCD hT3
    have hright : C' * T3 ≤ C' * T3 * L := by
      calc
        C' * T3 = C' * T3 * 1 := by ring
        _ ≤ C' * T3 * L := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hCnonneg hT3)
    exact le_trans hleft hright
  have h4 : (16 / 3 : ℝ) * D * T4 ≤ C' * T4 * L := by
    have hleft : (16 / 3 : ℝ) * D * T4 ≤ C' * T4 :=
      mul_le_mul_of_nonneg_right hCD hT4
    have hright : C' * T4 ≤ C' * T4 * L := by
      calc
        C' * T4 = C' * T4 * 1 := by ring
        _ ≤ C' * T4 * L := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hCnonneg hT4)
    exact le_trans hleft hright
  have h5 : (8 / 3 : ℝ) * D ^ 2 * T5 ≤ C' * T5 * L := by
    have hleft : (8 / 3 : ℝ) * D ^ 2 * T5 ≤ C' * T5 :=
      mul_le_mul_of_nonneg_right hCD2 hT5
    have hright : C' * T5 ≤ C' * T5 * L := by
      calc
        C' * T5 = C' * T5 * 1 := by ring
        _ ≤ C' * T5 * L := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hCnonneg hT5)
    exact le_trans hleft hright
  have hsum :
      C' * T2 * L + C' * T3 * L + C' * T4 * L + C' * T5 * L
        ≤ C' * (T1 + T2 + T3 + T4 + T5) * L := by
    have hT1term : 0 ≤ C' * T1 * L := mul_nonneg (mul_nonneg hCnonneg hT1) hL0
    nlinarith
  calc
    (8 / 3 : ℝ) * (A * T2 * L + 2 * (D * (T3 + T4) + D ^ 2 * S5 + inv))
        ≤ 8 * A * T2 * L + (16 / 3) * D * T3 + (16 / 3) * D * T4 +
            (8 / 3) * D ^ 2 * T5 := hupper
    _ ≤ C' * T2 * L + C' * T3 * L + C' * T4 * L + C' * T5 * L := by
          nlinarith [h2, h3, h4, h5]
    _ ≤ C' * (T1 + T2 + T3 + T4 + T5) * L := hsum

private lemma crude_master_zero_algebra
    {C A E D Q L Z1 Z2 inv : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hL1 : 1 ≤ L)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2)
    (hinv : inv ≤ E * Z1 * L)
    (hC : C = 100 + 20 * (A + E + D + D ^ 2 + Q)) :
    (8 / 3 : ℝ) * (E * Z1 * L + 2 * (Q * Z2 + inv))
      ≤ C * (Z1 + Z2) * L := by
  subst C
  let C' : ℝ := 100 + 20 * (A + E + D + D ^ 2 + Q)
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hCnonneg : 0 ≤ C' := by
    dsimp [C']
    nlinarith [hA, hE, hD, sq_nonneg D, hQ]
  have hCE : (8 : ℝ) * E ≤ C' := by
    dsimp [C']
    nlinarith [hA, hE, hD, sq_nonneg D, hQ]
  have hCQ : (16 / 3 : ℝ) * Q ≤ C' := by
    dsimp [C']
    nlinarith [hA, hE, hD, sq_nonneg D, hQ]
  have hupper :
      (8 / 3 : ℝ) * (E * Z1 * L + 2 * (Q * Z2 + inv))
        ≤ 8 * E * Z1 * L + (16 / 3) * Q * Z2 := by
    nlinarith [hinv]
  have h1 : 8 * E * Z1 * L ≤ C' * Z1 * L := by
    have hZ1L : 0 ≤ Z1 * L := mul_nonneg hZ1 hL0
    nlinarith [mul_le_mul_of_nonneg_right hCE hZ1L]
  have h2 : (16 / 3 : ℝ) * Q * Z2 ≤ C' * Z2 * L := by
    have hleft : (16 / 3 : ℝ) * Q * Z2 ≤ C' * Z2 :=
      mul_le_mul_of_nonneg_right hCQ hZ2
    have hright : C' * Z2 ≤ C' * Z2 * L := by
      calc
        C' * Z2 = C' * Z2 * 1 := by ring
        _ ≤ C' * Z2 * L := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hCnonneg hZ2)
    exact le_trans hleft hright
  calc
    (8 / 3 : ℝ) * (E * Z1 * L + 2 * (Q * Z2 + inv))
        ≤ 8 * E * Z1 * L + (16 / 3) * Q * Z2 := hupper
    _ ≤ C' * Z1 * L + C' * Z2 * L := by nlinarith [h1, h2]
    _ = C' * (Z1 + Z2) * L := by ring

set_option maxHeartbeats 800000 in
-- @node: lem:crude-localized-master-bound
/-- `lem:crude-localized-master-bound`. Pooled crude `q^{-2}`-envelope master
bound for the cross-fit clipped-AIPW `1/n`-ERM (ARBITRARY `enum`, foldwise
nuisances, `assign` partition). BOTH overlap regimes: for `γ>0` with `q ≤ c_o u^γ`
it is the five-term bound; for `γ=0` with fixed `q ≤ underline_p/2` it collapses
to `C{n^{-A_α}+r_μ r_e}(log n)^p`.

SCOPE (Lean encoding fidelity): the enumeration `enum : ℕ → Policy 𝒳` carries the
note's dense-`Π₀` enumeration condition as `hskel : DenseSkeleton enum policySet`
(every `enum j ∈ Π`, and every `π ∈ Π` is a pointwise limit of an `enum`-indexed
subsequence). So this master bound is the upper-bound backbone specifically for the
pointwise-dense-skeleton `1/n`-ERM of `def:feasible-erm`, not an ARBITRARY
enumeration-based ERM. -/
lemma crude_localized_master_bound {K : ℕ} (policySet : Set (Policy 𝒳))
    (α γ Cm u0 Co co underlineP a c CMu CProd : ℝ) (dPi : ℕ)
    (assign : (m : ℕ) → Fin m → Fin K) (qSeq uSeq rMu rE : ℕ → ℝ)
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ)
    (hvc : PolicyClassVC policySet dPi)
    (henvU : VCLocalizedEnvelopeUnif policySet α)
    (hoffU : VCLocalizedOffsetEnvelopeUnif policySet α)
    (hskel : DenseSkeleton enum policySet)
    (hK : FixedFoldCount K assign)
    (hpoly : PolynomialNuisanceExponents rMu rE a c CMu CProd)
    (hq_pos : ∀ᶠ n : ℕ in Filter.atTop, 0 < qSeq n)
    -- regularity: the note's clips are in the genuine clipping interval, giving
    -- `q ≤ ē_q ≤ 1-q` for score envelopes and drift denominators.
    (hq_half : ∀ᶠ n : ℕ in Filter.atTop, qSeq n ≤ 1 / 2)
    -- schedule regularity: in the strict-overlap endpoint (`γ=0`) the feasible
    -- construction uses a fixed clip, so q-dependent constants are still
    -- hoistable above `∀ n`.
    (hq_zero_fixed : γ = 0 → ∃ q0fix : ℝ, 0 < q0fix ∧
      ∀ᶠ n : ℕ in Filter.atTop, qSeq n = q0fix)
    -- regularity: nuisance rates are nonnegative radii, intrinsic to
    -- `NuisanceRate` / `PolynomialNuisanceExponents` bookkeeping.
    (hrMu_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ rMu n)
    (hrE_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ rE n)
    -- regularity: foldwise plug-in nuisances are measurable so
    -- `feasible_erm_basic_inequality`, `clip_bias`, and centered processes are
    -- genuine Bochner objects.
    (hμ0meas : ∀ n k, Measurable (muHat0 n k))
    (hμ1meas : ∀ n k, Measurable (muHat1 n k))
    (hemeas : ∀ n k, Measurable (eHat n k))
    -- regularity: L² nuisance-error fields are MemLp inputs for
    -- Cauchy-Schwarz in the deterministic drift bound.
    (hμ0L2 : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P →
          ∀ k : Fin K, MemLp (fun x => muHat0 n k x - P.mu0 x) 2 P.PX)
    (hμ1L2 : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P →
          ∀ k : Fin K, MemLp (fun x => muHat1 n k x - P.mu1 x) 2 P.PX)
    (heL2 : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P →
          ∀ k : Fin K, MemLp (fun x => eHat n k x - P.propensity x) 2 P.PX)
    -- bounded cross-fit outcome regressions (A12): needed — together with the
    -- finite-VC dense skeleton (`hvc`) and the positive clip schedule — to DISCHARGE
    -- the Bochner side conditions internally via `bochner_discharge`, so they are no
    -- longer an assumed input.
    (hbn : ∀ k : Fin K,
      BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k)) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (P : ObservedLaw 𝒳),
          LawClass α γ Cm u0 Co co underlineP policySet P →
          OptimalInClass P policySet →
          IsIIDSample P →
          (∀ k : Fin K,
            NuisanceRate P (fun m => muHat0 m k) (fun m => muHat1 m k)
              (fun m => eHat m k) rMu rE) →
          (∀ k : Fin K,
            BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k)) →
          (0 < γ → 0 < uSeq n → uSeq n ≤ u0 → qSeq n ≤ co * (uSeq n) ^ γ →
            ∫ sample,
                lawRegret P
                  (feasibleERM (qSeq n) enum (muHat0 n) (muHat1 n) (eHat n)
                    (assign n) sample)
              ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
              ≤ C * ((n : ℝ) ^ (-(rStar α γ))
                  + ((n : ℝ) * (qSeq n) ^ 2) ^ (-(Aalpha α))
                  + rMu n * rE n / qSeq n
                  + rMu n * (uSeq n) ^ (α / 2) * (qSeq n) ^ (1 / (2 * γ))
                  + (rMu n) ^ 2 / uSeq n) * (Real.log n) ^ p) ∧
          (γ = 0 → qSeq n ≤ underlineP / 2 →
            ∫ sample,
                lawRegret P
                  (feasibleERM (qSeq n) enum (muHat0 n) (muHat1 n) (eHat n)
                    (assign n) sample)
          ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
            ≤ C * ((n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n) * (Real.log n) ^ p)
    := by
  classical
  rcases crossfit_localized_offset_control
      policySet Cm α u0 dPi K assign hvc hK hoffU with
    ⟨Coff0, poff, hCoff0, hpoff, Hoff⟩
  let Coff : ℝ := max Coff0 1
  let Cd : ℝ := 4 * (1 + (max Co 1) ^ (1 / 2 : ℝ))
  let q0fix : ℝ := if hγ0 : γ = 0 then Classical.choose (hq_zero_fixed hγ0) else 1
  let Kpos : ℝ := ((36 : ℝ) ^ 2) ^ (Aalpha α)
  let Kzero : ℝ := (((36 : ℝ) / q0fix) ^ 2) ^ (Aalpha α)
  let Cq0 : ℝ := max 1 (2 / q0fix)
  let C : ℝ :=
    100 + 20 * (Coff * Kpos + Coff * Kzero + Cd + Cd ^ 2 + Cq0)
  have hCoff_pos : 0 < Coff := lt_of_lt_of_le zero_lt_one (le_max_right Coff0 1)
  have hCoff_ge0 : 0 ≤ Coff := hCoff_pos.le
  have hCoff_ge1 : 1 ≤ Coff := le_max_right Coff0 1
  have hCd_nonneg : 0 ≤ Cd := by
    dsimp [Cd]
    positivity
  have hq0fix_pos : 0 < q0fix := by
    by_cases hγ0 : γ = 0
    · have hspec := Classical.choose_spec (hq_zero_fixed hγ0)
      simpa [q0fix, hγ0] using hspec.1
    · simp [q0fix, hγ0]
  have hKpos_nonneg : 0 ≤ Kpos := by
    dsimp [Kpos]
    exact Real.rpow_nonneg (sq_nonneg (36 : ℝ)) _
  have hKzero_nonneg : 0 ≤ Kzero := by
    dsimp [Kzero]
    exact Real.rpow_nonneg (sq_nonneg ((36 : ℝ) / q0fix)) _
  have hCq0_nonneg : 0 ≤ Cq0 := by
    dsimp [Cq0]
    exact le_trans zero_le_one (le_max_left _ _)
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith [hCoff_ge0, hKpos_nonneg, hKzero_nonneg, hCd_nonneg,
      sq_nonneg Cd, hCq0_nonneg]
  have hq_zero_event : ∀ᶠ n : ℕ in Filter.atTop, γ = 0 → qSeq n = q0fix := by
    by_cases hγ0 : γ = 0
    · have hspec := Classical.choose_spec (hq_zero_fixed hγ0)
      filter_upwards [hspec.2] with n hn
      intro _h
      simpa [q0fix, hγ0] using hn
    · exact Filter.Eventually.of_forall (fun n h => False.elim (hγ0 h))
  refine ⟨C, poff, hCpos, hpoff, ?_⟩
  -- The Bochner integrability/BddAbove side conditions are now DISCHARGED internally
  -- from the primitive regularity data, rather than assumed (`bochner_integrability_gate`).
  have hBochner := bochner_discharge α γ Cm u0 Co co underlineP policySet dPi enum
    muHat0 muHat1 eHat assign qSeq hvc hskel hbn hμ0meas hμ1meas hemeas hq_pos hq_half
  filter_upwards
    [hq_pos, hq_half, hrMu_nonneg, hrE_nonneg, hμ0L2, hμ1L2, heL2,
      hBochner, hq_zero_event,
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩,
      Filter.eventually_atTop.mpr ⟨Nat.ceil (Real.exp 1), fun n hn => hn⟩]
    with n hqpos hqhalf hrMuN hrEN hμ0L2n hμ1L2n heL2n hBoN hqZeroN hn1 hnceil
  intro P hLaw hopt hiid hnuis hbnuis
  let q : ℝ := qSeq n
  let B : ℝ := (36 : ℝ) / q
  let g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrement P q (muHat0 n) (muHat1 n) (eHat n)
  let gT : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ :=
    clippedPolicyIncrementTrunc P q B (muHat0 n) (muHat1 n) (eHat n)
  let πhat : (Fin n → Observation 𝒳) → Policy 𝒳 := fun sample =>
    feasibleERM q enum (muHat0 n) (muHat1 n) (eHat n) (assign n) sample
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn1
  have hq : 0 < q := by simpa [q] using hqpos
  have hq_half_n : q ≤ 1 / 2 := by simpa [q] using hqhalf
  have hq_lt_one : q < 1 := by linarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (by norm_num) hq.le
  have hB_one : 1 ≤ B := by
    dsimp [B]
    rw [le_div_iff₀ hq]
    nlinarith [hq_half_n]
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hlog_one : 1 ≤ Real.log (n : ℝ) := by
    have hexp_le_ceil : Real.exp 1 ≤ (Nat.ceil (Real.exp 1) : ℝ) := Nat.le_ceil _
    have hceil_le_n : (Nat.ceil (Real.exp 1) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnceil
    have hexp_le_n : Real.exp 1 ≤ (n : ℝ) := le_trans hexp_le_ceil hceil_le_n
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hexp_le_n)).2 hexp_le_n
  have hα_nonneg : 0 ≤ α := hLaw.margin.1
  have hπmeas : ∀ π ∈ policySet, Measurable π := hvc.1
  have hπhat_mem : ∀ sample, πhat sample ∈ policySet := by
    intro sample
    exact hskel.1 _
  have hμ0bdd : ∀ k : Fin K, ∃ M : ℝ, ∀ x, |muHat0 n k x| ≤ M := by
    intro k
    refine ⟨1, ?_⟩
    intro x
    exact abs_le.mpr ⟨(hbnuis k n x).1.1, (hbnuis k n x).1.2⟩
  have hμ1bdd : ∀ k : Fin K, ∃ M : ℝ, ∀ x, |muHat1 n k x| ≤ M := by
    intro k
    refine ⟨1, ?_⟩
    intro x
    exact abs_le.mpr ⟨(hbnuis k n x).2.1, (hbnuis k n x).2.2⟩
  have hBo := hBoN P hLaw
  dsimp only at hBo
  rcases hBo with ⟨hInt_regret, hInt_offset, hbdd_offset, hInt_fold⟩
  have hInt_pooledT : Integrable (fun sample : Fin n → Observation 𝒳 =>
        sSup ((fun π =>
          max 0 (2 * |pooledCrossfitProcess P gT (assign n) sample π| -
            lawRegret P π / 4)) '' policySet))
      (Measure.pi (fun _ : Fin n => P.dataMeasure)) := by
    have hae := pooledOffsetSup_trunc_eq_original_ae_36 P q (muHat0 n) (muHat1 n)
      (eHat n) (assign n) policySet hLaw.wf hLaw.bdd
      (fun k x => hbnuis k n x) hq hq_half_n
    exact hInt_offset.congr hae.symm
  have hInt_foldT : ∀ k : Fin K,
      Integrable (fun sample : foldIndex (assign n) k → Observation 𝒳 =>
        foldOffsetSubSup P gT (assign n) policySet k sample)
        (Measure.pi (fun _ : foldIndex (assign n) k => P.dataMeasure)) := by
    intro k
    have hae := foldOffsetSubSup_trunc_eq_original_ae_36 P q (muHat0 n) (muHat1 n)
      (eHat n) (assign n) policySet k hLaw.wf hLaw.bdd
      (fun k x => hbnuis k n x) hq hq_half_n
    exact (hInt_fold k).congr hae.symm
  have hoffT := Hoff P hLaw.margin hLaw.zero hiid hLaw.wf hLaw.bdd n B gT hnpos
    hB_nonneg
    (fun k => clippedPolicyIncrementTrunc_compatible P q B (muHat0 n) (muHat1 n) (eHat n) k)
    (fun k π hπmem => clippedPolicyIncrementTrunc_measurable P q B (muHat0 n)
      (muHat1 n) (eHat n) k π hLaw.wf (hπmeas π hπmem)
      (hμ0meas n k) (hμ1meas n k) (hemeas n k))
    hInt_pooledT hInt_foldT
    (fun k π hπmem O => clippedPolicyIncrementTrunc_bound P q B (muHat0 n)
      (muHat1 n) (eHat n) k π O hB_nonneg)
    (fun k π hπmem => clippedPolicyIncrementTrunc_second_moment P q B
      (muHat0 n) (muHat1 n) (eHat n) k π hLaw.wf (hπmeas π hπmem) hB_nonneg)
  have hoffOrig :
      expectedPooledOffsetSup P g (assign n) policySet
        ≤ Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ poff) := by
    have heq := expectedPooledOffsetSup_trunc_eq_original_ae_36 P q (muHat0 n)
      (muHat1 n) (eHat n) (assign n) policySet hLaw.wf hLaw.bdd
      (fun k x => hbnuis k n x) hq hq_half_n
    have hbase_nonneg :
        0 ≤ (B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ poff := by
      positivity
    calc
      expectedPooledOffsetSup P g (assign n) policySet
          = expectedPooledOffsetSup P gT (assign n) policySet := by
            exact heq.symm
      _ ≤ Coff0 * (B ^ 2 / (n : ℝ)) ^ ((1 + α) / (2 + α)) *
            (Real.log n) ^ poff := hoffT
      _ = Coff0 * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ poff) := by
            simp [Aalpha]
            ring
      _ ≤ Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ poff) :=
            mul_le_mul_of_nonneg_right (le_max_left Coff0 1) hbase_nonneg
  have hlarge :
      (n : ℝ)⁻¹ ≤ Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ poff) :=
    crude_self_large hn1 hα_nonneg hB_one hCoff_ge1 hpoff hlog_one
  constructor
  · intro hγpos hu_pos hu_le hq_adm
    let δ : ℝ :=
      2 * (Cd * (rMu n * rE n / q
          + rMu n * (uSeq n) ^ (α / 2) * q ^ (1 / (2 * γ)))
        + Cd ^ 2 * (rMu n) ^ 2 / (2 * uSeq n) + (n : ℝ)⁻¹)
    have hδ_nonneg : 0 ≤ δ := by
      dsimp [δ, Cd]
      positivity
    have hsel : ∀ sample,
        lawRegret P (πhat sample)
          ≤ 2 * |pooledCrossfitProcess P g (assign n) sample (πhat sample)| + δ := by
      intro sample
      have hbridge := feasible_erm_welfare_bridge P q enum (muHat0 n) (muHat1 n)
        (eHat n) (assign n) policySet dPi hvc hopt hskel hLaw.wf hLaw.bdd hLaw.pos
        (hμ0meas n) (hμ1meas n) (hemeas n) hμ0bdd hμ1bdd hq hq_lt_one hnpos sample
      have hdrift := weighted_drift_sum_bound_pos P policySet q (rMu n) (rE n) α γ
        Co co u0 underlineP (muHat0 n) (muHat1 n) (eHat n) (assign n)
        (fun k => (hnuis k).1 n) (fun k => (hnuis k).2.1 n)
        (fun k => (hnuis k).2.2.1 n) (hμ0L2n P hLaw) (hμ1L2n P hLaw)
        (heL2n P hLaw) hrMuN hrEN hLaw.wf hπmeas hq_half_n hLaw.overlapDecay
        hLaw.zero hLaw.bdd hLaw.strict hq hnpos hγpos (πhat sample)
        (hπhat_mem sample) (uSeq n) hu_pos hu_le hq_adm
      have hR_nonneg : 0 ≤ lawRegret P (πhat sample) :=
        lawRegret_nonneg P (πhat sample) hLaw.wf hLaw.bdd
          (hπmeas (πhat sample) (hπhat_mem sample))
      have hyoung := young_sqrt_absorb hCd_nonneg hrMuN hR_nonneg hu_pos
      have hcore :
          Cd * (rMu n) * (lawRegret P (πhat sample) / uSeq n) ^ (1 / 2 : ℝ)
            ≤ lawRegret P (πhat sample) / 2 + Cd ^ 2 * (rMu n) ^ 2 / (2 * uSeq n) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hyoung
      have hbridge' :
          lawRegret P (πhat sample)
            ≤ |pooledCrossfitProcess P g (assign n) sample (πhat sample)|
              + |∑ k : Fin K, ((Fintype.card (foldIndex (assign n) k) : ℝ) / (n : ℝ)) *
                  driftIntegral P q (muHat0 n k) (muHat1 n k) (eHat n k) (πhat sample)|
              + (n : ℝ)⁻¹ := by
        simpa [πhat, g, q] using hbridge
      dsimp [δ, Cd] at hdrift hcore ⊢
      nlinarith [hbridge', hdrift, hcore]
    have hself := localized_vc_self_bound P policySet α B δ Coff poff g (assign n) πhat
      hiid.1 hB_one hnpos hpoff hδ_nonneg hπhat_mem hoffOrig hlarge
      hInt_regret hInt_offset hbdd_offset hsel
    have hmain := hself.2.1
    -- Expand the self-bound into the stated five-term master RHS.
    have hlogpow_ge_one : 1 ≤ (Real.log (n : ℝ)) ^ poff := Real.one_le_rpow hlog_one hpoff
    have hbase_eq :
        (B ^ 2 / (n : ℝ)) ^ (Aalpha α) =
          Kpos * (((n : ℝ) * q ^ 2) ^ (-(Aalpha α))) := by
      simpa [B, Kpos] using
        crude_trunc_offset_rpow_eq (n := n) (q := q) (A := Aalpha α) hnpos hq
    have hinv_le_offset :
        (n : ℝ)⁻¹ ≤ Coff * (Kpos * (((n : ℝ) * q ^ 2) ^ (-(Aalpha α))) *
            (Real.log n) ^ poff) := by
      simpa [hbase_eq, mul_assoc] using hlarge
    have htarget_nonneg :
        0 ≤ (n : ℝ) ^ (-(rStar α γ))
          + ((n : ℝ) * q ^ 2) ^ (-(Aalpha α))
          + rMu n * rE n / q
          + rMu n * (uSeq n) ^ (α / 2) * q ^ (1 / (2 * γ))
          + (rMu n) ^ 2 / uSeq n := by
      positivity
    calc
      ∫ sample, lawRegret P
          (feasibleERM q enum (muHat0 n) (muHat1 n) (eHat n) (assign n) sample)
          ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          = ∫ sample, lawRegret P (πhat sample)
              ∂(Measure.pi (fun _ : Fin n => P.dataMeasure)) := rfl
      _ ≤ (8 / 3 : ℝ) *
            (Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ poff) + δ) := hmain
      _ ≤ C * ((n : ℝ) ^ (-(rStar α γ))
          + ((n : ℝ) * q ^ 2) ^ (-(Aalpha α))
          + rMu n * rE n / q
          + rMu n * (uSeq n) ^ (α / 2) * q ^ (1 / (2 * γ))
          + (rMu n) ^ 2 / uSeq n) * (Real.log n) ^ poff := by
        have hT1 : 0 ≤ (n : ℝ) ^ (-(rStar α γ)) := by positivity
        have hT2 : 0 ≤ ((n : ℝ) * q ^ 2) ^ (-(Aalpha α)) := by positivity
        have hT3 : 0 ≤ rMu n * rE n / q := by positivity
        have hT4 : 0 ≤ rMu n * (uSeq n) ^ (α / 2) * q ^ (1 / (2 * γ)) := by positivity
        have hT5 : 0 ≤ (rMu n) ^ 2 / uSeq n := by positivity
        have hS5 :
            (rMu n) ^ 2 / (2 * uSeq n) ≤ ((rMu n) ^ 2 / uSeq n) / 2 := by
          field_simp [hu_pos.ne']
          exact le_rfl
        have hinv_alg :
            (n : ℝ)⁻¹ ≤ (Coff * Kpos) *
              (((n : ℝ) * q ^ 2) ^ (-(Aalpha α))) * (Real.log n) ^ poff := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hinv_le_offset
        have hC_def :
            C = 100 + 20 * (Coff * Kpos + Coff * Kzero + Cd + Cd ^ 2 + Cq0) := rfl
        have halg := crude_master_pos_algebra
          (C := C) (A := Coff * Kpos) (E := Coff * Kzero) (D := Cd) (Q := Cq0)
          (L := (Real.log n) ^ poff)
          (T1 := (n : ℝ) ^ (-(rStar α γ)))
          (T2 := ((n : ℝ) * q ^ 2) ^ (-(Aalpha α)))
          (T3 := rMu n * rE n / q)
          (T4 := rMu n * (uSeq n) ^ (α / 2) * q ^ (1 / (2 * γ)))
          (T5 := (rMu n) ^ 2 / uSeq n)
          (S5 := (rMu n) ^ 2 / (2 * uSeq n))
          (inv := (n : ℝ)⁻¹)
          (mul_nonneg hCoff_ge0 hKpos_nonneg) (mul_nonneg hCoff_ge0 hKzero_nonneg)
          hCd_nonneg hCq0_nonneg hlogpow_ge_one hT1 hT2 hT3 hT4 hT5 hS5
          hinv_alg hC_def
        rw [hbase_eq]
        simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using halg
  · intro hγ0 hq_under
    have hq_eq_fix : q = q0fix := hqZeroN hγ0
    let δ : ℝ := 2 * (Cq0 * (rMu n * rE n) + (n : ℝ)⁻¹)
    have hδ_nonneg : 0 ≤ δ := by
      dsimp [δ, Cq0]
      positivity
    have hsel : ∀ sample,
        lawRegret P (πhat sample)
          ≤ 2 * |pooledCrossfitProcess P g (assign n) sample (πhat sample)| + δ := by
      intro sample
      have hbridge := feasible_erm_welfare_bridge P q enum (muHat0 n) (muHat1 n)
        (eHat n) (assign n) policySet dPi hvc hopt hskel hLaw.wf hLaw.bdd hLaw.pos
        (hμ0meas n) (hμ1meas n) (hemeas n) hμ0bdd hμ1bdd hq hq_lt_one hnpos sample
      have hdrift := weighted_drift_sum_bound_zero P policySet q (rMu n) (rE n) α γ
        Co co u0 underlineP (muHat0 n) (muHat1 n) (eHat n) (assign n)
        (fun k => (hnuis k).1 n) (fun k => (hnuis k).2.1 n)
        (fun k => (hnuis k).2.2.1 n) (hμ0L2n P hLaw) (hμ1L2n P hLaw)
        (heL2n P hLaw) hrMuN hrEN hLaw.wf hπmeas hq_half_n hLaw.overlapDecay
        hLaw.zero hLaw.bdd hLaw.strict hq hnpos hγ0 hq_under (πhat sample)
        (hπhat_mem sample)
      have hbridge' :
          lawRegret P (πhat sample)
            ≤ |pooledCrossfitProcess P g (assign n) sample (πhat sample)|
              + |∑ k : Fin K, ((Fintype.card (foldIndex (assign n) k) : ℝ) / (n : ℝ)) *
                  driftIntegral P q (muHat0 n k) (muHat1 n k) (eHat n k) (πhat sample)|
              + (n : ℝ)⁻¹ := by
        simpa [πhat, g, q] using hbridge
      dsimp [δ, Cq0] at hdrift ⊢
      rw [hq_eq_fix] at hbridge'
      rw [hq_eq_fix] at hdrift
      have hG_nonneg :
          0 ≤ |pooledCrossfitProcess P g (assign n) sample (πhat sample)| := abs_nonneg _
      have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnRpos.le
      have hprod_nonneg : 0 ≤ rMu n * rE n := mul_nonneg hrMuN hrEN
      have hCq_nonneg' : 0 ≤ max 1 (2 / q0fix) :=
        le_trans zero_le_one (le_max_left _ _)
      nlinarith [hbridge', hdrift, hG_nonneg, hinv_nonneg, hprod_nonneg, hCq_nonneg']
    have hself := localized_vc_self_bound P policySet α B δ Coff poff g (assign n) πhat
      hiid.1 hB_one hnpos hpoff hδ_nonneg hπhat_mem hoffOrig hlarge
      hInt_regret hInt_offset hbdd_offset hsel
    have hmain := hself.2.1
    have hlogpow_ge_one : 1 ≤ (Real.log (n : ℝ)) ^ poff := Real.one_le_rpow hlog_one hpoff
    have hbase_eq_zero :
        (B ^ 2 / (n : ℝ)) ^ (Aalpha α) =
          Kzero * ((n : ℝ) ^ (-(Aalpha α))) := by
      have hfixed :=
        crude_trunc_offset_fixed_rpow_eq (n := n) (q := q0fix) (A := Aalpha α)
          hnpos (by simpa [q0fix] using hq0fix_pos)
      calc
        (B ^ 2 / (n : ℝ)) ^ (Aalpha α)
            = (((36 : ℝ) / q0fix) ^ 2 / (n : ℝ)) ^ (Aalpha α) := by
              simp [B, hq_eq_fix]
        _ = (((36 : ℝ) / q0fix) ^ 2) ^ (Aalpha α) *
              ((n : ℝ) ^ (-(Aalpha α))) := hfixed
        _ = Kzero * ((n : ℝ) ^ (-(Aalpha α))) := by
              simp [Kzero]
    have hinv_le_zero :
        (n : ℝ)⁻¹ ≤ Coff * (Kzero * ((n : ℝ) ^ (-(Aalpha α))) *
            (Real.log n) ^ poff) := by
      simpa [hbase_eq_zero, mul_assoc] using hlarge
    have htarget_nonneg :
        0 ≤ (n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n := by
      positivity
    calc
      ∫ sample, lawRegret P
          (feasibleERM q enum (muHat0 n) (muHat1 n) (eHat n) (assign n) sample)
          ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          = ∫ sample, lawRegret P (πhat sample)
              ∂(Measure.pi (fun _ : Fin n => P.dataMeasure)) := rfl
      _ ≤ (8 / 3 : ℝ) *
            (Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ poff) + δ) := hmain
      _ ≤ C * ((n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n) * (Real.log n) ^ poff := by
        have hZ1 : 0 ≤ (n : ℝ) ^ (-(Aalpha α)) := by positivity
        have hZ2 : 0 ≤ rMu n * rE n := mul_nonneg hrMuN hrEN
        have hinv_alg :
            (n : ℝ)⁻¹ ≤ (Coff * Kzero) *
              ((n : ℝ) ^ (-(Aalpha α))) * (Real.log n) ^ poff := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hinv_le_zero
        have hC_def :
            C = 100 + 20 * (Coff * Kpos + Coff * Kzero + Cd + Cd ^ 2 + Cq0) := rfl
        have halg := crude_master_zero_algebra
          (C := C) (A := Coff * Kpos) (E := Coff * Kzero) (D := Cd) (Q := Cq0)
          (L := (Real.log n) ^ poff)
          (Z1 := (n : ℝ) ^ (-(Aalpha α))) (Z2 := rMu n * rE n)
          (inv := (n : ℝ)⁻¹)
          (mul_nonneg hCoff_ge0 hKpos_nonneg) (mul_nonneg hCoff_ge0 hKzero_nonneg)
          hCd_nonneg hCq0_nonneg hlogpow_ge_one hZ1 hZ2 hinv_alg hC_def
        rw [hbase_eq_zero]
        simpa [δ, mul_assoc, mul_left_comm, mul_comm] using halg

private lemma nat_rpow_neg_le_of_le {n : ℕ} {r e : ℝ}
    (hn : 1 ≤ n) (hre : r ≤ e) :
    (n : ℝ) ^ (-e) ≤ (n : ℝ) ^ (-r) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)

-- @node: lem:clip-balance-exponent
/-- `lem:clip-balance-exponent`. Optimization of the master-bound terms over the
DETERMINISTIC `def:feasible-rate` schedule `q_n = qSched`, `u_n = uSched` (tied to
`s_feas`, `t_feas`, not arbitrary) under the admissibility `q_n ≤ c_o u_n^γ`, to
the solved exponent `r_feas = rFeas α γ a c` (the `FeasibleRate.r` accessor). BOTH
regimes: for `γ>0` the
five master-bound terms; for `γ=0` the fixed-clip `n^{-A_α}+r_μ r_e` terms. -/
lemma clip_balance_exponent (α γ a c CMu CProd q0 uBar co : ℝ) (rMu rE : ℕ → ℝ)
    (hpoly : PolynomialNuisanceExponents rMu rE a c CMu CProd)
    (hCMu : 0 ≤ CMu) (hCProd : 0 ≤ CProd)
    (hrMu_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ rMu n)
    (hq0 : 0 < q0) (huBar : 0 < γ → 0 < uBar)
    (hadm : 0 < γ → feasibleAdmissible α γ a c co q0 uBar) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      (0 < γ → ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) ^ (-(rStar α γ))
          + ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α))
          + rMu n * rE n / qSched α γ a c q0 n
          + rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
          + (rMu n) ^ 2 / uSched α γ a c uBar n
        ≤ C * (n : ℝ) ^ (-(rFeas α γ a c)) * (Real.log n) ^ p) ∧
      (γ = 0 → ∀ᶠ n : ℕ in Filter.atTop,
        (n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n
        ≤ C * (n : ℝ) ^ (-(rFeas α γ a c)) * (Real.log n) ^ p)
    := by
  rcases hpoly with ⟨_ha, _hc, hpoly_eventual⟩
  let Koff : ℝ := (q0 ^ 2) ^ (-(Aalpha α))
  let Kprod : ℝ := CProd / q0
  let Kmu : ℝ := CMu * |uBar| ^ (α / 2) * q0 ^ (1 / (2 * γ))
  let Ksq : ℝ := CMu ^ 2 / |uBar|
  let C : ℝ := 2 + Koff + Kprod + Kmu + Ksq + CProd
  have hKoff_nonneg : 0 ≤ Koff := by
    dsimp [Koff]
    exact Real.rpow_nonneg (sq_nonneg q0) _
  have hKprod_nonneg : 0 ≤ Kprod := by
    dsimp [Kprod]
    exact div_nonneg hCProd (le_of_lt hq0)
  have hKmu_nonneg : 0 ≤ Kmu := by
    dsimp [Kmu]
    exact mul_nonneg
      (mul_nonneg hCMu (Real.rpow_nonneg (abs_nonneg uBar) _))
      (Real.rpow_nonneg (le_of_lt hq0) _)
  have hKsq_nonneg : 0 ≤ Ksq := by
    dsimp [Ksq]
    exact div_nonneg (sq_nonneg CMu) (abs_nonneg uBar)
  have hCpos : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, 0, hCpos, by norm_num, ?_, ?_⟩
  · intro hγ
    have hγne : γ ≠ 0 := ne_of_gt hγ
    have hr_def : rFeas α γ a c = min (rStar α γ) (gJoint α γ a c) := by
      simp [rFeas, hγne]
    have hr_le_star : rFeas α γ a c ≤ rStar α γ := by
      rw [hr_def]
      exact min_le_left _ _
    have hr_le_gJoint : rFeas α γ a c ≤ gJoint α γ a c := by
      rw [hr_def]
      exact min_le_right _ _
    have hvalue := feasibleMaximizer_value α γ a c hγ
    have hg_le_off :
        gJoint α γ a c ≤
          Aalpha α * (1 - 2 * sFeas α γ a c) := by
      rw [← hvalue]
      calc
        feasiblePhi α γ a c (sFeas α γ a c) (tFeas α γ a c)
            ≤ min (Aalpha α * (1 - 2 * sFeas α γ a c))
                (c - sFeas α γ a c) := min_le_left _ _
        _ ≤ Aalpha α * (1 - 2 * sFeas α γ a c) := min_le_left _ _
    have hg_le_prod :
        gJoint α γ a c ≤ c - sFeas α γ a c := by
      rw [← hvalue]
      calc
        feasiblePhi α γ a c (sFeas α γ a c) (tFeas α γ a c)
            ≤ min (Aalpha α * (1 - 2 * sFeas α γ a c))
                (c - sFeas α γ a c) := min_le_left _ _
        _ ≤ c - sFeas α γ a c := min_le_right _ _
    have hg_le_mu :
        gJoint α γ a c ≤
          a + sFeas α γ a c / (2 * γ) + α * tFeas α γ a c / 2 := by
      rw [← hvalue]
      calc
        feasiblePhi α γ a c (sFeas α γ a c) (tFeas α γ a c)
            ≤ min (a + sFeas α γ a c / (2 * γ) + α * tFeas α γ a c / 2)
                (2 * a - tFeas α γ a c) := min_le_right _ _
        _ ≤ a + sFeas α γ a c / (2 * γ) + α * tFeas α γ a c / 2 :=
          min_le_left _ _
    have hg_le_sq :
        gJoint α γ a c ≤ 2 * a - tFeas α γ a c := by
      rw [← hvalue]
      calc
        feasiblePhi α γ a c (sFeas α γ a c) (tFeas α γ a c)
            ≤ min (a + sFeas α γ a c / (2 * γ) + α * tFeas α γ a c / 2)
                (2 * a - tFeas α γ a c) := min_le_right _ _
        _ ≤ 2 * a - tFeas α γ a c := min_le_right _ _
    filter_upwards
      [hpoly_eventual, hrMu_nonneg,
        Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hpoly_n hrMu0 hn1
    have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hnnonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
    let base : ℝ := (n : ℝ) ^ (-(rFeas α γ a c))
    have hbase_nonneg : 0 ≤ base := by
      dsimp [base]
      exact Real.rpow_nonneg hnnonneg _
    have hterm_star :
        (n : ℝ) ^ (-(rStar α γ)) ≤ 1 * base := by
      dsimp [base]
      simpa using nat_rpow_neg_le_of_le hn1 hr_le_star
    have hterm_off_eq :
        ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α)) =
          Koff * (n : ℝ) ^
            (-(Aalpha α * (1 - 2 * sFeas α γ a c))) := by
      dsimp [Koff]
      rw [qSched, if_neg hγne]
      have hqpow_nonneg :
          0 ≤ q0 * (n : ℝ) ^ (-(sFeas α γ a c)) := by positivity
      have hqpow_sq_nonneg :
          0 ≤ (q0 * (n : ℝ) ^ (-(sFeas α γ a c))) ^ (2 : ℕ) := sq_nonneg _
      rw [Real.mul_rpow hnnonneg hqpow_sq_nonneg]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hqpow_nonneg]
      rw [Real.mul_rpow (le_of_lt hq0) (Real.rpow_nonneg hnnonneg _)]
      rw [Real.rpow_mul (le_of_lt hq0)]
      rw [← Real.rpow_mul hnnonneg]
      ring_nf
      conv_lhs =>
        rw [mul_comm ((n : ℝ) ^ (-(Aalpha α))) ((q0 ^ 2) ^ (-(Aalpha α)))]
        rw [mul_assoc]
        rw [← Real.rpow_add hnpos]
      ring_nf
      rw [mul_comm]
      simp
    have hterm_off :
        ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α))
          ≤ Koff * base := by
      rw [hterm_off_eq]
      dsimp [base]
      exact mul_le_mul_of_nonneg_left
        (nat_rpow_neg_le_of_le hn1 (le_trans hr_le_gJoint hg_le_off))
        hKoff_nonneg
    have hterm_prod_step :
        rMu n * rE n / qSched α γ a c q0 n
          ≤ Kprod * (n : ℝ) ^ (-(c - sFeas α γ a c)) := by
      have hq_pos : 0 < qSched α γ a c q0 n := by
        simp [qSched, hγne, hq0, Real.rpow_pos_of_pos hnpos]
      have hinv_nonneg : 0 ≤ (qSched α γ a c q0 n)⁻¹ :=
        inv_nonneg.mpr (le_of_lt hq_pos)
      calc
        rMu n * rE n / qSched α γ a c q0 n
            = (rMu n * rE n) * (qSched α γ a c q0 n)⁻¹ := by
              rw [div_eq_mul_inv]
        _ ≤ (CProd * (n : ℝ) ^ (-c)) * (qSched α γ a c q0 n)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hpoly_n.2 hinv_nonneg
        _ = Kprod * (n : ℝ) ^ (-(c - sFeas α γ a c)) := by
          dsimp [Kprod]
          rw [qSched, if_neg hγne, div_eq_mul_inv]
          rw [mul_inv]
          rw [Real.rpow_neg hnnonneg (sFeas α γ a c)]
          simp only [inv_inv]
          calc
            _ = CProd * q0⁻¹ *
                ((n : ℝ) ^ (-c) * (n : ℝ) ^ (sFeas α γ a c)) := by ring
            _ = CProd * q0⁻¹ * (n : ℝ) ^ (-c + sFeas α γ a c) := by
              rw [Real.rpow_add hnpos]
            _ = CProd * q0⁻¹ * (n : ℝ) ^ (-(c - sFeas α γ a c)) := by
              congr 2
              ring
    have hterm_prod :
        rMu n * rE n / qSched α γ a c q0 n ≤ Kprod * base := by
      exact le_trans hterm_prod_step
        (mul_le_mul_of_nonneg_left
          (nat_rpow_neg_le_of_le hn1 (le_trans hr_le_gJoint hg_le_prod))
          hKprod_nonneg)
    have hterm_mu_step :
        rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
          ≤ Kmu * (n : ℝ) ^
              (-(a + sFeas α γ a c / (2 * γ)
                  + α * tFeas α γ a c / 2)) := by
      have hfactor_nonneg :
          0 ≤ (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ)) := by
        have hu_sched_pos : 0 < uSched α γ a c uBar n := by
          simp [uSched, huBar hγ, Real.rpow_pos_of_pos hnpos]
        have hq_sched_pos : 0 < qSched α γ a c q0 n := by
          simp [qSched, hγne, hq0, Real.rpow_pos_of_pos hnpos]
        exact mul_nonneg
          (Real.rpow_nonneg (le_of_lt hu_sched_pos) _)
          (Real.rpow_nonneg (le_of_lt hq_sched_pos) _)
      calc
        rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
            = rMu n * ((uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))) := by ring
        _ ≤ (CMu * (n : ℝ) ^ (-a)) *
              ((uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))) := by
          exact mul_le_mul_of_nonneg_right hpoly_n.1 hfactor_nonneg
        _ = Kmu * (n : ℝ) ^
              (-(a + sFeas α γ a c / (2 * γ)
                  + α * tFeas α γ a c / 2)) := by
          dsimp [Kmu]
          rw [abs_of_pos (huBar hγ)]
          rw [uSched, qSched, if_neg hγne]
          rw [Real.mul_rpow (le_of_lt (huBar hγ)) (Real.rpow_nonneg hnnonneg _)]
          rw [Real.mul_rpow (le_of_lt hq0) (Real.rpow_nonneg hnnonneg _)]
          rw [← Real.rpow_mul hnnonneg]
          rw [← Real.rpow_mul hnnonneg]
          calc
            _ = (CMu * uBar ^ (α / 2) * q0 ^ (1 / (2 * γ))) *
                ((n : ℝ) ^ (-a) *
                  ((n : ℝ) ^ (-(tFeas α γ a c) * (α / 2)) *
                    (n : ℝ) ^ (-(sFeas α γ a c) * (1 / (2 * γ))))) := by ring
            _ = (CMu * uBar ^ (α / 2) * q0 ^ (1 / (2 * γ))) *
                (n : ℝ) ^
                  (-(a + sFeas α γ a c / (2 * γ) + α * tFeas α γ a c / 2)) := by
              conv_lhs =>
                rw [← Real.rpow_add hnpos]
                rw [← Real.rpow_add hnpos]
              congr 2
              field_simp [hγne]
              ring
    have hterm_mu :
        rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
          ≤ Kmu * base := by
      exact le_trans hterm_mu_step
        (mul_le_mul_of_nonneg_left
          (nat_rpow_neg_le_of_le hn1 (le_trans hr_le_gJoint hg_le_mu))
          hKmu_nonneg)
    have hterm_sq_step :
        (rMu n) ^ 2 / uSched α γ a c uBar n
          ≤ Ksq * (n : ℝ) ^ (-(2 * a - tFeas α γ a c)) := by
      have hsq : (rMu n) ^ 2 ≤ (CMu * (n : ℝ) ^ (-a)) ^ 2 := by
        have hrhs_nonneg : 0 ≤ CMu * (n : ℝ) ^ (-a) :=
          mul_nonneg hCMu (Real.rpow_nonneg hnnonneg _)
        exact sq_le_sq' (by linarith) hpoly_n.1
      have hu_pos : 0 < uSched α γ a c uBar n := by
        simp [uSched, huBar hγ, Real.rpow_pos_of_pos hnpos]
      have hinv_nonneg : 0 ≤ (uSched α γ a c uBar n)⁻¹ :=
        inv_nonneg.mpr (le_of_lt hu_pos)
      calc
        (rMu n) ^ 2 / uSched α γ a c uBar n
            = (rMu n) ^ 2 * (uSched α γ a c uBar n)⁻¹ := by
              rw [div_eq_mul_inv]
        _ ≤ (CMu * (n : ℝ) ^ (-a)) ^ 2 *
              (uSched α γ a c uBar n)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hsq hinv_nonneg
        _ = Ksq * (n : ℝ) ^ (-(2 * a - tFeas α γ a c)) := by
          dsimp [Ksq]
          rw [abs_of_pos (huBar hγ)]
          rw [uSched, div_eq_mul_inv]
          rw [mul_inv]
          rw [← Real.rpow_natCast]
          rw [Real.mul_rpow hCMu (Real.rpow_nonneg hnnonneg _)]
          rw [← Real.rpow_mul hnnonneg]
          rw [Real.rpow_neg hnnonneg (tFeas α γ a c)]
          simp only [inv_inv]
          calc
            _ = (CMu ^ 2 / uBar) *
                ((n : ℝ) ^ (-a * (2 : ℝ)) * (n : ℝ) ^ (tFeas α γ a c)) := by
              rw [Real.rpow_natCast]
              ring
            _ = (CMu ^ 2 / uBar) *
                (n : ℝ) ^ (-a * (2 : ℝ) + tFeas α γ a c) := by
              rw [Real.rpow_add hnpos]
            _ = (CMu ^ 2 / uBar) *
                (n : ℝ) ^ (-(2 * a - tFeas α γ a c)) := by
              congr 2
              ring
    have hterm_sq :
        (rMu n) ^ 2 / uSched α γ a c uBar n ≤ Ksq * base := by
      exact le_trans hterm_sq_step
        (mul_le_mul_of_nonneg_left
          (nat_rpow_neg_le_of_le hn1 (le_trans hr_le_gJoint hg_le_sq))
          hKsq_nonneg)
    have hsum :
        (n : ℝ) ^ (-(rStar α γ))
          + ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α))
          + rMu n * rE n / qSched α γ a c q0 n
          + rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
          + (rMu n) ^ 2 / uSched α γ a c uBar n
        ≤ (1 + Koff + Kprod + Kmu + Ksq) * base := by
      calc
        (n : ℝ) ^ (-(rStar α γ))
          + ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α))
          + rMu n * rE n / qSched α γ a c q0 n
          + rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
          + (rMu n) ^ 2 / uSched α γ a c uBar n
            ≤ 1 * base + Koff * base + Kprod * base + Kmu * base + Ksq * base := by
              linarith
        _ = (1 + Koff + Kprod + Kmu + Ksq) * base := by ring
    have hcoef_le_C : 1 + Koff + Kprod + Kmu + Ksq ≤ C := by
      dsimp [C]
      linarith
    have hmain :
        (n : ℝ) ^ (-(rStar α γ))
          + ((n : ℝ) * (qSched α γ a c q0 n) ^ 2) ^ (-(Aalpha α))
          + rMu n * rE n / qSched α γ a c q0 n
          + rMu n * (uSched α γ a c uBar n) ^ (α / 2)
              * (qSched α γ a c q0 n) ^ (1 / (2 * γ))
          + (rMu n) ^ 2 / uSched α γ a c uBar n
        ≤ C * base :=
      le_trans hsum (mul_le_mul_of_nonneg_right hcoef_le_C hbase_nonneg)
    simpa [base] using hmain
  · intro hγ0
    have hr_def : rFeas α γ a c = min (Aalpha α) c := by
      simp [rFeas, hγ0]
    have hr_le_A : rFeas α γ a c ≤ Aalpha α := by
      rw [hr_def]
      exact min_le_left _ _
    have hr_le_c : rFeas α γ a c ≤ c := by
      rw [hr_def]
      exact min_le_right _ _
    filter_upwards
      [hpoly_eventual, Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n
        hpoly_n hn1
    have hnpos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hnnonneg : 0 ≤ (n : ℝ) := le_of_lt hnpos
    let base : ℝ := (n : ℝ) ^ (-(rFeas α γ a c))
    have hbase_nonneg : 0 ≤ base := by
      dsimp [base]
      exact Real.rpow_nonneg hnnonneg _
    have hterm_A :
        (n : ℝ) ^ (-(Aalpha α)) ≤ 1 * base := by
      dsimp [base]
      simpa using nat_rpow_neg_le_of_le hn1 hr_le_A
    have hterm_prod :
        rMu n * rE n ≤ CProd * base := by
      exact le_trans hpoly_n.2
        (mul_le_mul_of_nonneg_left
          (by
            dsimp [base]
            exact nat_rpow_neg_le_of_le hn1 hr_le_c)
          hCProd)
    have hsum :
        (n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n ≤
          (1 + CProd) * base := by
      calc
        (n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n
            ≤ 1 * base + CProd * base := by linarith
        _ = (1 + CProd) * base := by ring
    have hcoef_le_C : 1 + CProd ≤ C := by
      dsimp [C]
      linarith
    have hmain :
        (n : ℝ) ^ (-(Aalpha α)) + rMu n * rE n ≤ C * base :=
      le_trans hsum (mul_le_mul_of_nonneg_right hcoef_le_C hbase_nonneg)
    simpa [base] using hmain


end CausalSmith.Stat.PolicyRegretMarginOverlap
