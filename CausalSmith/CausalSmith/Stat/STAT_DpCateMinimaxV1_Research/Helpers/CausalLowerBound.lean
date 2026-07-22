/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP CATE minimax: the causal two-point private lower endpoint

Stage-2 scaffold. The heavy crux `lem:causal_oracle_private_lower_bound`: explicit
localized CAUSAL two-point potential-outcome families (C^∞ bump `b_h`, constant
propensity `e₀`, `μ₀ = 0` vs `μ₁ = b_h`) inside the frozen Hölder class, with
membership verification, TV/Hellinger bounds, Hellinger tensorization
`H²(P^n) ≤ n H²(P)`, `TV ≤ H`, and the testing inequality. Non-private branch
`h ≍ n^{-1/(2γ+d)}`; private branch via `dp_output_tv_contraction` with
`h ≍ (n ε_n)^{-1/(γ+d)}`.

RANDOMIZED-ESTIMATOR FIX: the deterministic-estimator
`MinimaxRisk.iid_two_point_lower_bound` is NOT reused (it does not fit the
randomized kernel `M_n`). The two-point risk lower bound is built DIRECTLY on the
release output laws via `Causalean.Stat.Minimax.TotalVariation.one_sub_tvDist_le_test`
(after a local data-processing reduction), reusing only `tvDist`,
`one_sub_tvDist_le_test`, and `chiSqDiv`/`tvDist_le_half_sqrt_chiSqDiv`.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContraction
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CausalNullLaw
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.BumpHolder
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DivergenceLocalized
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DivergenceProduct
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TVSharp
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.MinimaxReduction
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.Bandwidth

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat
open scoped Topology

@[simp] lemma cateWitnessLaw_mu0_apply {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : (cateWitnessLaw Q e0 b).mu0 x = 0 := rfl

@[simp] lemma cateWitnessLaw_mu1_apply {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : (cateWitnessLaw Q e0 b).mu1 x = b x := rfl

@[simp] lemma cateWitnessLaw_mu1_eq {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) : (cateWitnessLaw Q e0 b).mu1 = b := rfl

@[simp] lemma cateWitnessLaw_pi_apply {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : (cateWitnessLaw Q e0 b).pi x = e0 := rfl

@[simp] lemma cateWitnessLaw_PX_eq {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) : (cateWitnessLaw Q e0 b).PX = Q.PX := rfl

@[simp] lemma cateWitnessLaw_px_apply {d : ℕ} (Q : CateLaw d) (e0 : ℝ)
    (b : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : (cateWitnessLaw Q e0 b).px x = Q.px x := rfl

set_option maxHeartbeats 800000 in
/-- **Witness-exposing form of the causal two-point private lower endpoint.** Identical content to
`causal_oracle_private_lower_bound`, but the shared model member `Q`, the two localized bump
regression functions, and the fact that all three laws are `cateWitnessLaw Q e0 ·` applications are
EXPOSED rather than existentially hidden — so a consumer can reason about the laws' construction
(e.g. their mixture decomposition into a treated regression component and a shared control law). -/
lemma causal_oracle_private_lower_bound_witness {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hne : ModelNonempty d alpha beta gamma L e0 f0 f1 r0 x0) :
    ∃ (c cB : ℝ) (B : (Fin d → ℝ) → ℝ) (Q : CateLaw d),
      0 < c ∧ 0 < cB ∧
      IsProbabilityMeasure Q.PX ∧
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 (cateWitnessLaw Q e0 (fun _ => 0)) ∧
      IidSampling (cateWitnessLaw Q e0 (fun _ => 0)) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B ∧ B 0 = 1 ∧
      (∀ u : Fin d → ℝ, 0 ≤ B u ∧ B u ≤ 1) ∧
      (∀ u : Fin d → ℝ, (∃ j, 1 < |u j|) → B u = 0) ∧
      ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
        ∀ᶠ n : ℕ in Filter.atTop,
      (∃ (hnp hpriv : ℝ) (bnp bp : (Fin d → ℝ) → ℝ),
          0 < hnp ∧ hnp ≤ r0 ∧ 0 < hpriv ∧ hpriv ≤ r0 ∧
          Measurable bnp ∧ Measurable bp ∧
          (∀ x, |bnp x| ≤ 1) ∧ (∀ x, |bp x| ≤ 1) ∧
          (∀ x, bnp x = cB * hnp ^ gamma * B (fun j => (x j - x0 j) / hnp)) ∧
          (∀ x, bp x = cB * hpriv ^ gamma * B (fun j => (x j - x0 j) / hpriv)) ∧
          HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 (cateWitnessLaw Q e0 bnp) ∧
          HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 (cateWitnessLaw Q e0 bp) ∧
          IidSampling (cateWitnessLaw Q e0 bnp) ∧ IidSampling (cateWitnessLaw Q e0 bp) ∧
          c * (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
              ≤ |bnp x0| ∧
          tvDist (Measure.pi fun _ : Fin n => (cateWitnessLaw Q e0 (fun _ => 0)).dataMeasure)
              (Measure.pi fun _ : Fin n => (cateWitnessLaw Q e0 bnp).dataMeasure) ≤ 1 / 2 ∧
          c * ((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ))))
              ≤ |bp x0| ∧
          (n : ℝ) * (Real.exp (eps n) - 1 + del n)
              * tvDist (cateWitnessLaw Q e0 (fun _ => 0)).dataMeasure
                  (cateWitnessLaw Q e0 bp).dataMeasure ≤ 1 / 2) ∧
      c * max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
            (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ)))))
        ≤ dpMinimaxRisk n (eps n) (del n)
            (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0 := by
  classical
  let B : (Fin d → ℝ) → ℝ := causalCubeBump
  obtain ⟨Q, hQ, hiidQ⟩ := hne
  have hbeta : 0 < beta := hreg.2.1
  have hgamma : 0 < gamma := hreg.2.2.1
  have hL : 0 < L := hreg.2.2.2.1
  have he0 : 0 < e0 := hreg.2.2.2.2.1.1
  have hehalf : e0 < 1 / 2 := hreg.2.2.2.2.1.2
  have hf1 : 0 < f1 := lt_of_lt_of_le hreg.2.2.2.2.2.1 hreg.2.2.2.2.2.2.1
  have hr0 : 0 < r0 := hreg.2.2.2.2.2.2.2.1.1
  have hx0cube : x0 ∈ cube d := fun i =>
    ⟨(hreg.2.2.2.2.2.2.2.2 i).1.le, (hreg.2.2.2.2.2.2.2.2 i).2.le⟩
  have he0L : |e0| ≤ L := by
    rw [abs_of_pos he0]
    have hb := hQ.piH.2.1 0 (Nat.zero_le _) x0 hx0cube
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
    exact (hQ.overlap x0 hx0cube).1.trans ((le_abs_self _).trans hb)
  let P0 := cateWitnessLaw Q e0 (0 : (Fin d → ℝ) → ℝ)
  have hzeroBeta : HolderBallStd (fun _ : Fin d → ℝ => (0 : ℝ)) beta L (cube d) :=
    holderBallStd_const 0 beta L (cube d) (by simpa using hL.le)
  have hzeroGamma : HolderBallStd (fun _ : Fin d → ℝ => (0 : ℝ)) gamma L (cube d) :=
    holderBallStd_const 0 gamma L (cube d) (by simpa using hL.le)
  have hP0 : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P0 := by
    apply cateWitnessLaw_mem_class alpha beta gamma L e0 f0 f1 r0 x0 Q 0 hQ hiidQ
      measurable_const (by simp) he0.le hehalf.le he0L
    · simpa using hzeroBeta
    · simpa using hzeroGamma
  have hiid0 : IidSampling P0 := cateWitnessLaw_iidSampling Q e0 hiidQ hQ.pxMarginal
    measurable_const (by simp) he0.le (by linarith)
  have hmu00 : ∀ x, P0.mu0 x = 0 := by intro x; simp [P0]
  have hmu10 : ∀ x, P0.mu1 x = 0 := by intro x; simp [P0]
  have hpi0 : ∀ x, P0.pi x = e0 := by intro x; rfl
  obtain ⟨cB, hcB, hprofiles⟩ := causalCubeBump_holder_profiles beta gamma L
    hbeta hgamma hP0.order.2 hL
  have hcB1 : cB ≤ 1 / 2 := by
    have hp := (hprofiles 1 x0 (by norm_num) (by norm_num)).1 x0
    rw [show (fun i => (x0 i - x0 i) / (1 : ℝ)) = (0 : Fin d → ℝ) by
      funext i; simp, causalCubeBump_zero] at hp
    simpa [abs_of_pos hcB] using hp
  let pnp := 2 * gamma + (d : ℝ)
  let pp := gamma + (d : ℝ)
  let Anp := 2 * cB ^ 2 * f1 * (2 : ℝ) ^ d
  let Apriv := (3 * cB * f1 * (2 : ℝ) ^ d) / 2
  have hpnp : 0 < pnp := by dsimp [pnp]; positivity
  have hpp : 0 < pp := by dsimp [pp]; positivity
  have hAnp : 0 ≤ Anp := by dsimp [Anp]; positivity
  have hApriv : 0 ≤ Apriv := by dsimp [Apriv]; positivity
  obtain ⟨anp, cnp, hanp, hcnp, hanpr, hanp1, hnpfacts⟩ :=
    exists_power_bandwidth pnp gamma Anp r0 hpnp hgamma hAnp hr0
  obtain ⟨ap, cp, hap, hcp, hapr, hap1, hpfacts⟩ :=
    exists_power_bandwidth pp gamma Apriv r0 hpp hgamma hApriv hr0
  let c := min (cB * cnp / 8) (cB * cp / 8)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hB0 : B 0 = 1 := by
    simpa [B] using causalCubeBump_zero (d := d)
  have hBbounds : ∀ u : Fin d → ℝ, 0 ≤ B u ∧ B u ≤ 1 := by
    intro u
    simpa [B] using causalCubeBump_bounds u
  have hBsupp : ∀ u : Fin d → ℝ, (∃ j, 1 < |u j|) → B u = 0 := by
    intro u hu
    simpa [B] using causalCubeBump_support u hu
  have hBsmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B := by
    simpa [B] using causalCubeBump_contDiff (d := d)
  letI : IsProbabilityMeasure Q.dataMeasure := hiidQ.1
  haveI : IsProbabilityMeasure Q.PX := by
    rw [hQ.pxMarginal]
    exact Measure.isProbabilityMeasure_map measurable_CateObs_X.aemeasurable
  refine ⟨c, cB, B, Q, hc, hcB, inferInstance, ?_, ?_, hBsmooth, hB0,
    hBbounds, hBsupp, ?_⟩
  · simpa [P0] using hP0
  · simpa [P0] using hiid0
  intro eps del hbudget
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hbudgetn := hbudget n hn
  have heps0 : 0 ≤ eps n := le_trans (by positivity : 0 ≤ (n : ℝ)⁻¹) hbudgetn.1
  have hdel0 : 0 ≤ del n := hbudgetn.2.2.1.le
  have hy : 1 ≤ (n : ℝ) * eps n := by
    calc
      1 = (n : ℝ) * (n : ℝ)⁻¹ := (mul_inv_cancel₀ (by positivity : (n : ℝ) ≠ 0)).symm
      _ ≤ (n : ℝ) * eps n := mul_le_mul_of_nonneg_left hbudgetn.1 (by positivity)
  let hnp := anp * (n : ℝ) ^ (-(1 / pnp))
  let hpriv := ap * ((n : ℝ) * eps n) ^ (-(1 / pp))
  obtain ⟨hhnp, hhnpr, hhnp1, hsepn, hbudn⟩ := hnpfacts (n : ℝ) hnr
  obtain ⟨hhp, hhpr, hhp1, hsepp, hbudp⟩ := hpfacts ((n : ℝ) * eps n) hy
  have hhnp' : hnp = anp * (n : ℝ) ^ (-(1 / pnp)) := rfl
  have hhp' : hpriv = ap * ((n : ℝ) * eps n) ^ (-(1 / pp)) := rfl
  rw [← hhnp'] at hhnp hhnpr hhnp1 hsepn hbudn
  rw [← hhp'] at hhp hhpr hhp1 hsepp hbudp
  let bnp : (Fin d → ℝ) → ℝ := fun x => cB * hnp ^ gamma *
    B (fun j => (x j - x0 j) / hnp)
  let bp : (Fin d → ℝ) → ℝ := fun x => cB * hpriv ^ gamma *
    B (fun j => (x j - x0 j) / hpriv)
  let P1np := cateWitnessLaw Q e0 bnp
  let P1priv := cateWitnessLaw Q e0 bp
  have hprofnp := hprofiles hnp x0 hhnp hhnp1
  have hprofp := hprofiles hpriv x0 hhp hhp1
  have hbnpM : Measurable bnp := by
    exact (((causalCubeBump_contDiff (d := d)).continuous.measurable.comp
      (by fun_prop)).const_mul (cB * hnp ^ gamma))
  have hbpM : Measurable bp := by
    exact (((causalCubeBump_contDiff (d := d)).continuous.measurable.comp
      (by fun_prop)).const_mul (cB * hpriv ^ gamma))
  have hbnpHalf : ∀ x, |bnp x| ≤ 1 / 2 := by
    intro x
    simpa [bnp, B] using hprofnp.1 x
  have hbpHalf : ∀ x, |bp x| ≤ 1 / 2 := by
    intro x
    simpa [bp, B] using hprofp.1 x
  have hbnpOne : ∀ x, |bnp x| ≤ 1 := fun x => (hbnpHalf x).trans (by norm_num)
  have hbpOne : ∀ x, |bp x| ≤ 1 := fun x => (hbpHalf x).trans (by norm_num)
  have hP1np : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P1np := by
    apply cateWitnessLaw_mem_class alpha beta gamma L e0 f0 f1 r0 x0 Q bnp
      hQ hiidQ hbnpM hbnpOne he0.le hehalf.le he0L
    · simpa [bnp, B] using hprofnp.2.1
    · simpa [bnp, B] using hprofnp.2.2
  have hP1p : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P1priv := by
    apply cateWitnessLaw_mem_class alpha beta gamma L e0 f0 f1 r0 x0 Q bp
      hQ hiidQ hbpM hbpOne he0.le hehalf.le he0L
    · simpa [bp, B] using hprofp.2.1
    · simpa [bp, B] using hprofp.2.2
  have hiidnp : IidSampling P1np := cateWitnessLaw_iidSampling Q e0 hiidQ
    hQ.pxMarginal hbnpM hbnpOne he0.le (by linarith)
  have hiidp : IidSampling P1priv := cateWitnessLaw_iidSampling Q e0 hiidQ
    hQ.pxMarginal hbpM hbpOne he0.le (by linarith)
  letI : IsProbabilityMeasure P0.dataMeasure := hiid0.1
  letI : IsProbabilityMeasure P1np.dataMeasure := hiidnp.1
  letI : IsProbabilityMeasure P1priv.dataMeasure := hiidp.1
  have htau0 : P0.mu1 x0 - P0.mu0 x0 = 0 := by rw [hmu10 x0, hmu00 x0]; ring
  have hbnp0 : bnp x0 = cB * hnp ^ gamma := by
    dsimp [bnp, B]
    rw [show (fun j => (x0 j - x0 j) / hnp) = (0 : Fin d → ℝ) by
      funext j; simp, causalCubeBump_zero, mul_one]
  have hbp0 : bp x0 = cB * hpriv ^ gamma := by
    dsimp [bp, B]
    rw [show (fun j => (x0 j - x0 j) / hpriv) = (0 : Fin d → ℝ) by
      funext j; simp, causalCubeBump_zero, mul_one]
  have hrangenp : |P1np.mu1 x0 - P1np.mu0 x0| ≤ 2 := by
    rw [show P1np.mu1 x0 - P1np.mu0 x0 = bnp x0 by
      simpa [P1np, CateLaw.tau] using cateWitnessLaw_tau Q e0 bnp x0]
    exact (hprofnp.1 x0).trans (by norm_num)
  have hrangep : |P1priv.mu1 x0 - P1priv.mu0 x0| ≤ 2 := by
    rw [show P1priv.mu1 x0 - P1priv.mu0 x0 = bp x0 by
      simpa [P1priv, CateLaw.tau] using cateWitnessLaw_tau Q e0 bp x0]
    exact (hprofp.1 x0).trans (by norm_num)
  let Knp := 2 * cB ^ 2 * hnp ^ (2 * gamma) * f1 * (2 * hnp) ^ d
  have hkl : InformationTheory.klDiv P1np.dataMeasure P0.dataMeasure ≤ ENNReal.ofReal Knp := by
    have hk := localized_bump_kl_single_le Q e0 f0 f1 r0 gamma cB hnp x0
      hQ.localDensity hQ.pxDens hQ.pxMarginal hiidQ he0.le (by linarith)
      hf1.le hcB.le hcB1 hgamma hhnp hhnpr hhnp1
    convert hk using 1 <;>
      simp [P1np, P0, bnp, B, Knp, ENNReal.ofReal_mul]
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hpow : ∀ m : ℕ, ENNReal.ofReal ((2 * hnp) ^ m) =
        ENNReal.ofReal (2 * hnp) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg (by positivity) m), ih, pow_succ]
    simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using hpow d
  have hKnp0 : 0 ≤ Knp := by dsimp [Knp]; positivity
  have htvnp0 := cateWitness_tv_product_le (n := n) Q e0 Knp bnp hbnpM
    hbnpHalf he0.le (by linarith) hKnp0 (by simpa [P1np] using hkl)
  have hKidentity : (n : ℝ) * Knp = Anp * (n : ℝ) * hnp ^ pnp := by
    dsimp [Knp, Anp, pnp]
    rw [show (2 * hnp) ^ d = (2 : ℝ) ^ d * hnp ^ d by rw [mul_pow]]
    rw [← Real.rpow_natCast hnp d]
    calc
      (n : ℝ) * (2 * cB ^ 2 * hnp ^ (2 * gamma) * f1 *
          ((2 : ℝ) ^ d * hnp ^ (d : ℝ))) =
          (2 * cB ^ 2 * f1 * (2 : ℝ) ^ d * (n : ℝ)) *
            (hnp ^ (2 * gamma) * hnp ^ (d : ℝ)) := by ring
      _ = _ := by rw [Real.rpow_add hhnp]
  have htvnp : tvDist (Measure.pi fun _ : Fin n => P0.dataMeasure)
      (Measure.pi fun _ : Fin n => P1np.dataMeasure) ≤ 1 / 2 := by
    calc
      _ ≤ Real.sqrt ((n : ℝ) * Knp / 2) := by
        simpa [P1np] using htvnp0
      _ ≤ 1 / 2 := by
        apply (Real.sqrt_le_iff).2
        constructor
        · norm_num
        · rw [hKidentity]
          nlinarith
  have htvsingle0 := localized_bump_tv_single_le Q e0 f0 f1 r0 gamma cB hpriv x0
    hQ.localDensity hQ.pxDens hQ.pxMarginal hiidQ he0.le (by linarith)
    hf1.le hcB.le hcB1 hgamma hhp hhpr hhp1
  have hdel_eps : del n ≤ eps n := by
    calc
      del n ≤ (n : ℝ) ^ (-(2 : ℝ)) := hbudgetn.2.2.2
      _ ≤ (n : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hnr (by norm_num)
      _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ eps n := hbudgetn.1
  have hexp : Real.exp (eps n) - 1 ≤ 2 * eps n := by
    have ha := Real.abs_exp_sub_one_le (show |eps n| ≤ 1 by
      rw [abs_of_nonneg heps0]; exact hbudgetn.2.1)
    exact (le_abs_self _).trans (by simpa [abs_of_nonneg heps0] using ha)
  have hfactor : Real.exp (eps n) - 1 + del n ≤ 3 * eps n := by linarith
  have hfactor0 : 0 ≤ Real.exp (eps n) - 1 + del n :=
    add_nonneg (sub_nonneg.mpr (Real.one_le_exp heps0)) hdel0
  have htvpriv : (n : ℝ) * (Real.exp (eps n) - 1 + del n) *
      tvDist P0.dataMeasure P1priv.dataMeasure ≤ 1 / 2 := by
    rw [tvDist_symm]
    calc
      (n : ℝ) * (Real.exp (eps n) - 1 + del n) *
          tvDist P1priv.dataMeasure P0.dataMeasure
        ≤ (n : ℝ) * (3 * eps n) *
          ((cB * hpriv ^ gamma / 2) * f1 * (2 * hpriv) ^ d) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hfactor (by positivity)
            · simpa [P1priv, P0, bp, B] using htvsingle0
            · exact tvDist_nonneg
            · positivity
      _ = Apriv * ((n : ℝ) * eps n) * hpriv ^ pp := by
        dsimp [Apriv, pp]
        rw [show (2 * hpriv) ^ d = (2 : ℝ) ^ d * hpriv ^ d by rw [mul_pow]]
        rw [← Real.rpow_natCast hpriv d]
        calc
          (n : ℝ) * (3 * eps n) *
              ((cB * hpriv ^ gamma / 2) * f1 * ((2 : ℝ) ^ d * hpriv ^ (d : ℝ))) =
              ((3 * cB * f1 * (2 : ℝ) ^ d) / 2 * ((n : ℝ) * eps n)) *
                (hpriv ^ gamma * hpriv ^ (d : ℝ)) := by ring
          _ = _ := by rw [Real.rpow_add hhp]
      _ ≤ 1 / 2 := hbudp.trans (by norm_num)
  have hsepnp : c * (n : ℝ) ^ (-(gamma / pnp)) ≤
      |(P1np.mu1 x0 - P1np.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| := by
    rw [htau0, sub_zero, show P1np.mu1 x0 - P1np.mu0 x0 = bnp x0 by
      simpa [P1np, CateLaw.tau] using cateWitnessLaw_tau Q e0 bnp x0, hbnp0,
      abs_of_pos (mul_pos hcB (Real.rpow_pos_of_pos hhnp _))]
    calc
      c * (n : ℝ) ^ (-(gamma / pnp))
          ≤ (cB * cnp / 8) * (n : ℝ) ^ (-(gamma / pnp)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ cB * (cnp * (n : ℝ) ^ (-(gamma / pnp))) := by
        have : cB * cnp / 8 ≤ cB * cnp := by nlinarith [mul_pos hcB hcnp]
        calc _ ≤ (cB * cnp) * (n : ℝ) ^ (-(gamma / pnp)) :=
              mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = _ := by ring
      _ ≤ cB * hnp ^ gamma := mul_le_mul_of_nonneg_left hsepn hcB.le
  have hseppv : c * ((n : ℝ) * eps n) ^ (-(gamma / pp)) ≤
      |(P1priv.mu1 x0 - P1priv.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| := by
    rw [htau0, sub_zero, show P1priv.mu1 x0 - P1priv.mu0 x0 = bp x0 by
      simpa [P1priv, CateLaw.tau] using cateWitnessLaw_tau Q e0 bp x0, hbp0,
      abs_of_pos (mul_pos hcB (Real.rpow_pos_of_pos hhp _))]
    calc
      c * ((n : ℝ) * eps n) ^ (-(gamma / pp))
          ≤ (cB * cp / 8) * ((n : ℝ) * eps n) ^ (-(gamma / pp)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _)
          (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) heps0) _)
      _ ≤ cB * (cp * ((n : ℝ) * eps n) ^ (-(gamma / pp))) := by
        have : cB * cp / 8 ≤ cB * cp := by nlinarith [mul_pos hcB hcp]
        calc _ ≤ (cB * cp) * ((n : ℝ) * eps n) ^ (-(gamma / pp)) :=
              mul_le_mul_of_nonneg_right this
                (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) heps0) _)
          _ = _ := by ring
      _ ≤ cB * hpriv ^ gamma := mul_le_mul_of_nonneg_left hsepp hcB.le
  have hrisknp : c * (n : ℝ) ^ (-(gamma / pnp)) ≤
      dpMinimaxRisk n (eps n) (del n)
        (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0 := by
    have hsep8 : 8 * (c * (n : ℝ) ^ (-(gamma / pnp))) ≤
        |(P1np.mu1 x0 - P1np.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| := by
      have hc8 : 8 * c ≤ cB * cnp := by
        calc
          8 * c ≤ 8 * (cB * cnp / 8) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
          _ = cB * cnp := by ring
      calc
        8 * (c * (n : ℝ) ^ (-(gamma / pnp)))
            = (8 * c) * (n : ℝ) ^ (-(gamma / pnp)) := by ring
        _ ≤ (cB * cnp) * (n : ℝ) ^ (-(gamma / pnp)) :=
          mul_le_mul_of_nonneg_right hc8 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = cB * (cnp * (n : ℝ) ^ (-(gamma / pnp))) := by ring
        _ ≤ cB * hnp ^ gamma := mul_le_mul_of_nonneg_left hsepn hcB.le
        _ = _ := by
          rw [htau0, sub_zero, show P1np.mu1 x0 - P1np.mu0 x0 = bnp x0 by
            simpa [P1np, CateLaw.tau] using cateWitnessLaw_tau Q e0 bnp x0,
            hbnp0, abs_of_pos (mul_pos hcB (Real.rpow_pos_of_pos hhnp _))]
    have hl := dpMinimaxRisk_two_point (eps n) (del n) _ x0 P0 P1np hP0 hP1np
      hiid0 hiidnp (by simp [htau0]) hrangenp heps0 hdel0 (fun M =>
        (tvDist_bind_kernel_le _ _ M.1 M.2.1.2.1 M.2.1.1).trans htvnp)
    calc
      c * (n : ℝ) ^ (-(gamma / pnp)) =
          (8 * (c * (n : ℝ) ^ (-(gamma / pnp)))) / 8 := by ring
      _ ≤ |(P1np.mu1 x0 - P1np.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| / 8 :=
        div_le_div_of_nonneg_right hsep8 (by norm_num)
      _ ≤ _ := hl
  have hriskp : c * ((n : ℝ) * eps n) ^ (-(gamma / pp)) ≤
      dpMinimaxRisk n (eps n) (del n)
        (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0 := by
    have hsep8 : 8 * (c * ((n : ℝ) * eps n) ^ (-(gamma / pp))) ≤
        |(P1priv.mu1 x0 - P1priv.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| := by
      have hc8 : 8 * c ≤ cB * cp := by
        calc
          8 * c ≤ 8 * (cB * cp / 8) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
          _ = cB * cp := by ring
      calc
        8 * (c * ((n : ℝ) * eps n) ^ (-(gamma / pp)))
            = (8 * c) * ((n : ℝ) * eps n) ^ (-(gamma / pp)) := by ring
        _ ≤ (cB * cp) * ((n : ℝ) * eps n) ^ (-(gamma / pp)) :=
          mul_le_mul_of_nonneg_right hc8
            (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) heps0) _)
        _ = cB * (cp * ((n : ℝ) * eps n) ^ (-(gamma / pp))) := by ring
        _ ≤ cB * hpriv ^ gamma := mul_le_mul_of_nonneg_left hsepp hcB.le
        _ = _ := by
          rw [htau0, sub_zero, show P1priv.mu1 x0 - P1priv.mu0 x0 = bp x0 by
            simpa [P1priv, CateLaw.tau] using cateWitnessLaw_tau Q e0 bp x0,
            hbp0, abs_of_pos (mul_pos hcB (Real.rpow_pos_of_pos hhp _))]
    have hl := dpMinimaxRisk_two_point (eps n) (del n) _ x0 P0 P1priv hP0 hP1p
      hiid0 hiidp (by simp [htau0]) hrangep heps0 hdel0 (fun M =>
        (dp_output_tv_contraction n (eps n) (del n) P0 P1priv M.1 hiid0 hiidp
          M.2.1 heps0).trans (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using htvpriv))
    calc
      c * ((n : ℝ) * eps n) ^ (-(gamma / pp)) =
          (8 * (c * ((n : ℝ) * eps n) ^ (-(gamma / pp)))) / 8 := by ring
      _ ≤ |(P1priv.mu1 x0 - P1priv.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| / 8 :=
        div_le_div_of_nonneg_right hsep8 (by norm_num)
      _ ≤ _ := hl
  refine ⟨⟨hnp, hpriv, bnp, bp, hhnp, hhnpr, hhp, hhpr, hbnpM, hbpM,
    hbnpOne, hbpOne, (fun _ => rfl), (fun _ => rfl), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa [P1np] using hP1np
  · simpa [P1priv] using hP1p
  · simpa [P1np] using hiidnp
  · simpa [P1priv] using hiidp
  · have hsepnp' := hsepnp
    have htvnp' := htvnp
    have hseppv' := hseppv
    have htvpriv' := htvpriv
    simp only [P1np, P0, pnp, cateWitnessLaw_mu1_apply,
      cateWitnessLaw_mu0_apply, Pi.zero_apply, sub_zero] at hsepnp'
    change tvDist
        (Measure.pi fun _ : Fin n => (cateWitnessLaw Q e0 (fun _ => 0)).dataMeasure)
        (Measure.pi fun _ : Fin n => (cateWitnessLaw Q e0 bnp).dataMeasure) ≤ 1 / 2 at htvnp'
    simp only [P1priv, P0, pp, cateWitnessLaw_mu1_apply,
      cateWitnessLaw_mu0_apply, Pi.zero_apply, sub_zero] at hseppv'
    change (n : ℝ) * (Real.exp (eps n) - 1 + del n)
        * tvDist (cateWitnessLaw Q e0 (fun _ => 0)).dataMeasure
            (cateWitnessLaw Q e0 bp).dataMeasure ≤ 1 / 2 at htvpriv'
    exact ⟨hsepnp', htvnp', hseppv', htvpriv'⟩
  · simpa [pnp, pp, mul_max_of_nonneg _ _ hc.le] using max_le hrisknp hriskp

-- @node: lem:causal-oracle-private-lower-bound
set_option maxHeartbeats 800000 in
/-- **Causal two-point private lower endpoint (crux).** There is `c > 0` such that
for all sufficiently large `n`, `R_n^{DP} ≥ c{n^{-γ/(2γ+d)} ∨ (n ε_n)^{-γ/(γ+d)}}`,
AND both branches are witnessed by EXPLICIT localized causal two-point
potential-outcome families in the frozen Hölder class: a shared null law `P0`
(`μ₀ = μ₁ = 0`, constant propensity `e₀`) and, for each branch, an alternative
(`μ₀ = 0`, constant propensity `e₀`, only `μ₁` locally perturbed) with target
separation of the branch's order — `n^{-γ/(2γ+d)}` (non-private branch `P1np`) and
`(n ε_n)^{-γ/(γ+d)}` (private branch `P1priv`). -/
lemma causal_oracle_private_lower_bound {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hne : ModelNonempty d alpha beta gamma L e0 f0 f1 r0 x0) :
    -- FIXED construction data (c, cB, B, P0) chosen UNIFORMLY over the admissible privacy
    -- regime — quantified OUTSIDE the budget sequences `eps, del` and the sample size `n`,
    -- so the constant `c`, the bump SCALE `cB` / SHAPE `B`, and the null law `P0` cannot
    -- depend on the budget sequence or on `n` (only the bandwidths `hnp, hpriv` and the
    -- alternatives `P1np, P1priv` remain n-dependent witnesses)
    ∃ (c cB : ℝ) (B : (Fin d → ℝ) → ℝ) (P0 : CateLaw d),
      0 < c ∧ 0 < cB ∧
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P0 ∧
      IidSampling P0 ∧ |P0.mu1 x0 - P0.mu0 x0| ≤ 2 ∧
      -- shared C^∞ bump B: supported on the unit ∞-norm cube, peak B 0 = 1, values in
      -- [0,1] (the localized bump SHAPE, fixed across the whole regime and both branches)
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B ∧ B 0 = 1 ∧
      (∀ u : Fin d → ℝ, 0 ≤ B u ∧ B u ≤ 1) ∧
      (∀ u : Fin d → ℝ, (∃ j, 1 < |u j|) → B u = 0) ∧
      -- shared causal null: μ₀ = μ₁ = 0, constant overlapping propensity e₀ (FIXED)
      (∀ x, P0.mu0 x = 0) ∧ (∀ x, P0.mu1 x = 0) ∧ (∀ x, P0.pi x = e0) ∧
      ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
        ∀ᶠ n : ℕ in Filter.atTop,
      (∃ (hnp hpriv : ℝ) (P1np P1priv : CateLaw d),
          HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P1np ∧
          HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P1priv ∧
          -- the alternatives are GENUINE i.i.d. probability laws with in-range estimand, so
          -- they sit in `dpMinimaxRisk`'s sup domain (connecting them to the risk)
          IidSampling P1np ∧ IidSampling P1priv ∧
          |P1np.mu1 x0 - P1np.mu0 x0| ≤ 2 ∧ |P1priv.mu1 x0 - P1priv.mu0 x0| ≤ 2 ∧
          -- n-dependent bandwidths (only these and the alternatives vary with the budget/n)
          0 < hnp ∧ hnp ≤ r0 ∧ 0 < hpriv ∧ hpriv ≤ r0 ∧
          -- alternatives keep ALL non-μ₁ components UNCHANGED from the FIXED null: μ₀ = 0,
          -- constant propensity e₀, and the SAME covariate design law / density
          (∀ x, P1np.mu0 x = 0) ∧
          (∀ x, P1np.pi x = e0) ∧
          P1np.PX = P0.PX ∧ (∀ x, P1np.px x = P0.px x) ∧
          (∀ x, P1priv.mu0 x = 0) ∧
          (∀ x, P1priv.pi x = e0) ∧
          P1priv.PX = P0.PX ∧ (∀ x, P1priv.px x = P0.px x) ∧
          -- EXPLICIT localized γ-Hölder μ₁ bump built from the FIXED scale `cB` and shape
          -- `B`: μ₁(x) = c_B · h^γ · B((x - x₀)/h), supported in supBall x₀ h, peak at x₀.
          -- ONLY μ₁ is perturbed (writeup.tex: "only mu_1 is locally perturbed").
          (∀ x, P1np.mu1 x = cB * hnp ^ gamma * B (fun j => (x j - x0 j) / hnp)) ∧
          (∀ x, P1priv.mu1 x = cB * hpriv ^ gamma * B (fun j => (x j - x0 j) / hpriv)) ∧
          -- non-private branch: target separation ≍ n^{-γ/(2γ+d)}
          c * (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
              ≤ |(P1np.mu1 x0 - P1np.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| ∧
          -- non-private OUTPUT-INDISTINGUISHABILITY: the n-fold product laws are
          -- statistically close (TV ≤ 1/2), so no release can separate the pair — this
          -- (with the testing inequality) is what certifies the non-private branch
          tvDist (Measure.pi fun _ : Fin n => P0.dataMeasure)
              (Measure.pi fun _ : Fin n => P1np.dataMeasure) ≤ 1 / 2 ∧
          -- private branch: target separation ≍ (n ε_n)^{-γ/(γ+d)}
          c * ((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ))))
              ≤ |(P1priv.mu1 x0 - P1priv.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| ∧
          -- private OUTPUT-INDISTINGUISHABILITY (DP TV-contraction budget): the
          -- per-observation TV, amplified by n{exp ε_n − 1 + δ_n}, stays ≤ 1/2, so any
          -- central-DP release of the pair has output TV ≤ 1/2 (via
          -- `dp_output_tv_contraction`) — certifying the private branch
          (n : ℝ) * (Real.exp (eps n) - 1 + del n)
              * tvDist P0.dataMeasure P1priv.dataMeasure ≤ 1 / 2) ∧
      c * max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
            (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ)))))
        ≤ dpMinimaxRisk n (eps n) (del n)
            (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0 := by
  classical
  obtain ⟨c, cB, B, Q, hc, hcB, _hQPX, hP0, hiid0, hBsmooth, hB0,
      hBbounds, hBsupp, htail⟩ :=
    causal_oracle_private_lower_bound_witness alpha beta gamma L e0 f0 f1 r0 x0 hreg hne
  refine ⟨c, cB, B, cateWitnessLaw Q e0 (fun _ => 0), hc, hcB, ?_, ?_, ?_,
    hBsmooth, hB0, hBbounds, hBsupp,
    ?_, ?_, ?_, ?_⟩
  · exact hP0
  · exact hiid0
  · norm_num [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply]
  · intro x; rfl
  · intro x; rfl
  · intro x; rfl
  · intro eps del hbudget
    filter_upwards [htail eps del hbudget] with n hn
    rcases hn with ⟨hw, hrisk⟩
    rcases hw with ⟨hnp, hpriv, bnp, bp, hhnp, hhnpr, hhp, hhpr, _hbnpM, _hbpM,
      hbnpOne, hbpOne, hbnpDef, hbpDef, hP1np, hP1priv, hiidnp, hiidpriv,
      hsepnp, htvnp, hseppriv, htvpriv⟩
    refine ⟨⟨hnp, hpriv, cateWitnessLaw Q e0 bnp, cateWitnessLaw Q e0 bp,
      hP1np, hP1priv, hiidnp, hiidpriv, ?_, ?_, hhnp, hhnpr, hhp, hhpr,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hrisk⟩
    · rw [show (cateWitnessLaw Q e0 bnp).mu1 x0 -
          (cateWitnessLaw Q e0 bnp).mu0 x0 = bnp x0 by
        simp only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply,
          Pi.zero_apply, sub_zero]]
      exact (hbnpOne x0).trans (by norm_num)
    · rw [show (cateWitnessLaw Q e0 bp).mu1 x0 -
          (cateWitnessLaw Q e0 bp).mu0 x0 = bp x0 by
        simp only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply,
          Pi.zero_apply, sub_zero]]
      exact (hbpOne x0).trans (by norm_num)
    · intro x; rfl
    · intro x; rfl
    · rfl
    · intro x; rfl
    · intro x; rfl
    · intro x; rfl
    · rfl
    · intro x; rfl
    · intro x; exact hbnpDef x
    · intro x; exact hbpDef x
    · simpa only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply,
        Pi.zero_apply, sub_zero] using hsepnp
    · exact htvnp
    · simpa only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply,
        Pi.zero_apply, sub_zero] using hseppriv
    · exact htvpriv

end CausalSmith.Stat.DpCateMinimax
