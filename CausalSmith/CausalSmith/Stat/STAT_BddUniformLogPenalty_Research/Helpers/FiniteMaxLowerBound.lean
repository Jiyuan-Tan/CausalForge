import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxDepoisson

/-!
# Shared finite-packing maximum lower bound

This module assembles the angular packing, marked Poisson direct-product
experiment, midpoint loss conversion, and de-Poissonization.
-/

open MeasureTheory Set Filter Asymptotics
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Uniformly over point-indexed rules and all sufficiently large `n`, one law
from the angular hard family makes the measurable finite packing maximum at
least a positive constant times the frontier rate. -/
lemma packing_finite_max_lower_bound :
    ∀ q : ℕ, ∀ L : ℝ, 1 ≤ q → 4 ≤ L →
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ rho : RuleFun n, rho ∈ PointIndexedDecisionClass n q L →
      ∃ P : CtyLaw, ∃ M : ℕ, ∃ centers : Fin M → Score,
        CtyNonparametricClass q L P ∧
        (∀ j, centers j ∈ frontier P.support) ∧
        Measurable (finitePackingLoss rho P centers) ∧
        ENNReal.ofReal (c * frontierRate n) ≤
          ∫⁻ w, finitePackingLoss rho P centers w ∂sampleLaw P n := by
  intro q L hq hL
  obtain ⟨c0, c1, cwLow, cwHigh, cRadial, alpha,
    hc0, hc1, hcwLow, hcwHigh, hcRadial, halpha, halpha8, Npack, hpack⟩ :=
    cty_support_boundary_angular_packing q L hq hL
  let d : ℝ := (1 / 2 : ℝ) * (1 - Real.exp (-(1 : ℝ) / 2))
  have hd : 0 < d := by
    dsimp [d]
    have : Real.exp (-(1 : ℝ) / 2) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    exact mul_pos (by norm_num) (sub_pos.mpr this)
  let c : ℝ := c1 * d / 4
  have hc : 0 < c := div_pos (mul_pos hc1 hd) (by norm_num)
  have htailEvent : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
        (c1 * d / (4 * L)) * frontierRate n := by
    have hcoef : 0 < c1 * d / (4 * L) := by
      have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
      positivity
    have h := poisson_remainder_isLittleO_frontier.def hcoef
    filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with n hnrm hn
    have he0 : 0 ≤ Real.exp (-(n : ℝ) * (1 - Real.log 2)) := Real.exp_pos _ |>.le
    have hr0 : 0 ≤ frontierRate n := (frontierRate_pos hn).le
    simpa [abs_of_nonneg he0, abs_of_nonneg hr0] using hnrm
  obtain ⟨Ntail, hNtail⟩ := (eventually_atTop.1 htailEvent)
  refine ⟨c, hc, max Npack (max Ntail 2), ?_⟩
  intro n hn rho hrho
  have hnpack : Npack ≤ n := le_trans (le_max_left _ _) hn
  have hntail : Ntail ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn2 : 2 ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  obtain ⟨M, w, m, centers, laws, values, hMsize, hw, hcenters,
    hsepCenters, hdis, hclass, hsupport, hmass, hlocal, hoff, hvalues,
    hseparation, hdistflip, hradial, hkl⟩ := hpack n hnpack
  have hM : 1 ≤ M := by
    have hleft : 0 < c0 * Real.rpow (frontierRate n) (-(1 : ℝ) / q) :=
      mul_pos hc0 (Real.rpow_pos_of_pos (frontierRate_pos hn2) _)
    have hMr : (0 : ℝ) < M := lt_of_lt_of_le hleft hMsize
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro hzero
      subst M
      norm_num at hMr))
  have hm : 0 < m := by
    let j0 : Fin M := ⟨0, Nat.zero_lt_of_lt hM⟩
    have hmass0 := hmass (fun _ => false) j0
    have hcenterSupport : centers j0 ∈ (laws (fun _ => false)).support := by
      rw [hsupport]
      have hj := frontier_subset_closure (hcenters j0)
      rw [packingSquare_isCompact.isClosed.closure_eq] at hj
      exact hj
    have hpos := class_pos_on_relopen (laws (fun _ => false))
      (hclass (fun _ => false)) (Metric.ball (centers j0) w) Metric.isOpen_ball
      (centers j0) ⟨Metric.mem_ball_self (by
        have hw0 := hw.1
        exact lt_of_lt_of_le
          (mul_pos hcwLow (Real.rpow_pos_of_pos (frontierRate_pos hn2) _)) hw0),
        hcenterSupport⟩
    have hsubset : Metric.ball (centers j0) w ∩
        (laws (fun _ => false)).support ⊆ packingCell centers w j0 := by
      intro x hx
      rw [hsupport] at hx
      exact ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx.1).le, hx.2⟩
    have hcellpos : 0 < Measure.map Prod.snd (laws (fun _ => false)).law
        (packingCell centers w j0) := hpos.trans_le (measure_mono hsubset)
    rw [hmass0] at hcellpos
    exact ENNReal.ofReal_pos.mp hcellpos
  obtain ⟨T, hT⟩ := hrho
  have herror := packingCoordinatewiseError_lower_bound (n := n)
    (Nat.one_le_of_lt hn2) hM T centers values w m alpha hdis laws
    hsupport hm hmass halpha.le (by linarith) hkl
  have hfiniteCoeff : ENNReal.ofReal d ≤
      ENNReal.ofReal ((1 / 2 : ℝ) *
        (1 - Real.exp (-((M : ℝ) ^ (1 - 2 * alpha)) / 2))) := by
    apply ENNReal.ofReal_le_ofReal
    have hexp0 : 0 ≤ 1 - 2 * alpha := by linarith
    have hpow : 1 ≤ (M : ℝ) ^ (1 - 2 * alpha) :=
      Real.one_le_rpow (by exact_mod_cast hM) hexp0
    have hexp : Real.exp (-((M : ℝ) ^ (1 - 2 * alpha)) / 2) ≤
        Real.exp (-(1 : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
    dsimp [d]
    linarith
  have hcoord : ENNReal.ofReal d ≤ coordinatewiseErrorProbability
      (fun j b => packingCellExperiment
        (packingFinitePartition centers w hdis) laws (2 * n) j b)
      (packingCommonExperiment
        (packingFinitePartition centers w hdis) laws (2 * n))
      (compressPackingCell centers)
      (packingPoissonDecoder T centers values) := hfiniteCoeff.trans herror
  obtain ⟨omega, hpoisson⟩ := exists_vertex_poissonLoss_ge_coordinatewiseError
    T centers values w m (c1 * frontierRate n) hdis laws hsupport hm hmass
    hlocal hoff hvalues hseparation
  let P := laws omega
  have hP : CtyNonparametricClass q L P := hclass omega
  have hcentersP : ∀ j, centers j ∈ frontier P.support := by
    intro j
    simpa [P, hsupport omega] using hcenters j
  have hmeas : Measurable (finitePackingLoss rho P centers) :=
    finitePackingLoss_measurable_of_pointIndexed rho ⟨T, hT⟩ P hP centers hcentersP
  have hsection : ∀ sample j, rho sample (centers j) =
      T.map (centers j) (distanceData n sample (centers j)) := by
    intro sample j
    exact hT P hP sample (centers j) (hcentersP j)
  have hbound : ∀ j, |values j (omega j)| ≤ L := by
    intro j
    rw [← hvalues omega j]
    have hsupportCenter : centers j ∈ P.support := by
      have hj := frontier_subset_closure (hcentersP j)
      rw [hP.2.2.2.1.isClosed.closure_eq] at hj
      exact hj
    have hderiv := hP.2.2.2.2.2.2.2.1.2.1 0 (by omega)
      (centers j) hsupportCenter
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hderiv
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hdepois := globalPackingPoissonRisk_le_fixedRisk_add_tail
    T rho P centers values omega hsection (hvalues omega) hmeas L hbound
  have hmain : ENNReal.ofReal ((c1 * frontierRate n) / 2) *
      ENNReal.ofReal d ≤
      ∫⁻ s, globalPackingPoissonLoss T centers values omega s
        ∂canonicalMarkedPoissonSampleLaw P.law packingMarkLaw (2 * n) :=
    (mul_le_mul_right hcoord _).trans hpoisson
  have htailReal : L * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
      (c1 * d / 4) * frontierRate n := by
    have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
    have := mul_le_mul_of_nonneg_left (hNtail n hntail) hL0.le
    calc
      L * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
          L * ((c1 * d / (4 * L)) * frontierRate n) := this
      _ = (c1 * d / 4) * frontierRate n := by field_simp
  have htailENN : ENNReal.ofReal L *
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) ≤
      ENNReal.ofReal (c * frontierRate n) := by
    rw [← ENNReal.ofReal_mul (le_trans (by norm_num) hL)]
    exact ENNReal.ofReal_le_ofReal (by simpa [c] using htailReal)
  have hmainEq : ENNReal.ofReal ((c1 * frontierRate n) / 2) *
      ENNReal.ofReal d = ENNReal.ofReal (2 * (c * frontierRate n)) := by
    have hdelta0 : 0 ≤ (c1 * frontierRate n) / 2 :=
      div_nonneg (mul_nonneg hc1.le (frontierRate_pos hn2).le) (by norm_num)
    rw [← ENNReal.ofReal_mul hdelta0]
    congr 1
    dsimp [c]
    ring
  refine ⟨P, M, centers, hP, hcentersP, hmeas, ?_⟩
  have hsum : ENNReal.ofReal (c * frontierRate n) +
      ENNReal.ofReal (c * frontierRate n) ≤
      (∫⁻ sample, finitePackingLoss rho P centers sample ∂sampleLaw P n) +
        ENNReal.ofReal (c * frontierRate n) := by
    calc
      ENNReal.ofReal (c * frontierRate n) +
          ENNReal.ofReal (c * frontierRate n) =
          ENNReal.ofReal (2 * (c * frontierRate n)) := by
            have hcr0 : 0 ≤ c * frontierRate n :=
              mul_nonneg hc.le (frontierRate_pos hn2).le
            rw [← ENNReal.ofReal_add hcr0 hcr0]
            congr 1
            ring
      _ = _ := hmainEq.symm
      _ ≤ _ := hmain
      _ ≤ (∫⁻ sample, finitePackingLoss rho P centers sample ∂sampleLaw P n) +
          (ENNReal.ofReal L * ENNReal.ofReal
            (Real.exp (-(n : ℝ) * (1 - Real.log 2)))) := hdepois
      _ ≤ _ := by
        simpa [add_comm] using add_le_add_left htailENN
          (∫⁻ sample, finitePackingLoss rho P centers sample ∂sampleLaw P n)
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hsum

end CausalSmith.Stat.BddUniformLogPenalty
