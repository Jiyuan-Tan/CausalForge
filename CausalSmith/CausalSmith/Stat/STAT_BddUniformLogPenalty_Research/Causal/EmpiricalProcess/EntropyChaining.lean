import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.Separability
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.RadialCover
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.SeparableCover
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.ScoreL2
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EuclideanBallsVC
import Causalean.Stat.Concentration.Covering.DudleyEntropy
import Causalean.Stat.Concentration.Covering.VCCovering
import Causalean.Stat.Concentration.Covering.HausslerPacking
import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal
import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.EntropyChaining

/-!
# VC entropy and chaining for the bounded score class

The hypotheses below expose exactly the envelope, variance, and polynomial
covering information used by the variance-adaptive maximal inequality.
-/

open MeasureTheory Set
open scoped ENNReal
open Causalean.Stat.Concentration

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma winsorizedScore_hasVCUniformEntropy_at
    (p : ℕ) (ν L R : ℝ) (hR : 0 < R) :
    ∃ A v C : ℝ, 0 < C ∧
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
        HasVCUniformEntropy P.law (separableWinsorizedScoreFunction P p h B R)
          (C * B) (C * h) A v := by
  obtain ⟨A₀, v, hA₀, hv, hcover⟩ :=
    separableWinsorizedScore_hasUniformPolynomialL2Cover p hR
  obtain ⟨C₀, hC₀, hL2⟩ :=
    separableWinsorizedScore_hasUniformL2Radius_at p ν L R hR
  let c : ℝ := 2 * ((2 : ℝ) ^ p) ^ 2 + 2
  let Cenv : ℝ := c * (1 + (p + 1 : ℝ) * R)
  let C : ℝ := 1 + max C₀ Cenv
  refine ⟨2 * A₀, v, C, ?_, ?_⟩
  · have hCenv : 0 ≤ Cenv := by dsimp [Cenv, c]; positivity
    have : 0 ≤ max C₀ Cenv := hCenv.trans (le_max_right _ _)
    dsimp [C]
    linarith
  · intro P hP h B hh hhB hB
    letI : IsProbabilityMeasure P.law := P.law_isProbability
    have hbdy := winsorizedScore_boundary_nonempty p ν L P hP
    letI : Nonempty {x : Score // x ∈ P.boundary} := hbdy.to_subtype
    letI : Nonempty (SeparableWinsorizedScoreIndex P p h) := ⟨
      ⟨⟨h, ⟨le_rfl, by linarith⟩⟩,
        ⟨false, ⟨Classical.arbitrary _, ⟨0, Classical.arbitrary _⟩⟩⟩⟩⟩
    obtain ⟨hpoly, hemp⟩ := hcover P hbdy hh (hh.trans hhB)
    have hmeas : ∀ i : SeparableWinsorizedScoreIndex P p h,
        Measurable (separableWinsorizedScoreFunction P p h B R i) :=
      fun i => separableWinsorizedScoreFunction_measurable P p h B R i
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hCenv : 0 ≤ Cenv := by dsimp [Cenv]; positivity
    have hCB : c * (B + (p + 1 : ℝ) * R) ≤ Cenv * B := by
      have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
      have hB0 : 0 ≤ B := le_trans (by norm_num) hB
      dsimp [Cenv]
      have hpr : 0 ≤ (p + 1 : ℝ) * R := by positivity
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hB),
        mul_nonneg hB0 (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hpr)]
    have henvC : Cenv ≤ C := by
      dsimp [C]
      exact (le_max_right C₀ Cenv).trans (by linarith)
    have hU : c * (B + (p + 1 : ℝ) * R) ≤ C * B :=
      hCB.trans (mul_le_mul_of_nonneg_right henvC (le_trans (by norm_num) hB))
    have hU' : (2 * ((2 : ℝ) ^ p) ^ 2 + 2) *
        (B + ((p + 1 : ℕ) : ℝ) * R) ≤ C * B := by
      simpa [c, Nat.cast_add, Nat.cast_one] using hU
    have hC₀C : C₀ ≤ C := by
      dsimp [C]
      exact (le_max_left C₀ Cenv).trans (by linarith)
    have hCpos : 0 < C := by
      have : 0 ≤ max C₀ Cenv := hC₀.le.trans (le_max_left _ _)
      dsimp [C]
      linarith
    refine ⟨mul_pos hCpos hh, mul_lt_mul_of_pos_left hhB hCpos,
      hA₀.trans (by nlinarith [Real.exp_pos 1, hA₀]), hv, hmeas, ?_, ?_, ?_⟩
    · intro i z
      exact (hpoly.envelope i z).trans hU'
    · intro i
      exact (hL2 P hP h B hh hhB hB i).trans
        (mul_le_mul_of_nonneg_right hC₀C hh.le)
    · intro g₀
      exact Causalean.Stat.Concentration.HasPolynomialEmpiricalL2Cover.pullback
        (hemp.enlargeEnvelope hU') hmeas g₀

/-- The same entropy certificate with all witnesses chosen uniformly before
the moment exponent.  The L² proof's displayed constant does not depend on
that exponent. -/
-- @node: winsorizedScore_hasVCUniformEntropy_all_nu
lemma winsorizedScore_hasVCUniformEntropy_all_nu
    (p : ℕ) (L R : ℝ) (hR : 0 < R) :
    ∃ A v C : ℝ, 0 < C ∧ ∀ ν : ℝ,
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
        HasVCUniformEntropy P.law (separableWinsorizedScoreFunction P p h B R)
          (C * B) (C * h) A v := by
  obtain ⟨A₀, v, hA₀, hv, hcover⟩ :=
    separableWinsorizedScore_hasUniformPolynomialL2Cover p hR
  let C₀ : ℝ := 1 + |3 * ((2 : ℝ) ^ p) ^ 2 *
    (2 * (1 + L) + ((p + 1 : ℝ) * (2 : ℝ) ^ p * R) ^ 2) * (16 * L)|
  let c : ℝ := 2 * ((2 : ℝ) ^ p) ^ 2 + 2
  let Cenv : ℝ := c * (1 + (p + 1 : ℝ) * R)
  let C : ℝ := 1 + max C₀ Cenv
  refine ⟨2 * A₀, v, C, ?_, ?_⟩
  · have hCenv : 0 ≤ Cenv := by dsimp [Cenv, c]; positivity
    have : 0 ≤ max C₀ Cenv := hCenv.trans (le_max_right _ _)
    dsimp [C]
    linarith
  · intro ν P hP h B hh hhB hB
    letI : IsProbabilityMeasure P.law := P.law_isProbability
    have hbdy := winsorizedScore_boundary_nonempty p ν L P hP
    letI : Nonempty {x : Score // x ∈ P.boundary} := hbdy.to_subtype
    letI : Nonempty (SeparableWinsorizedScoreIndex P p h) := ⟨
      ⟨⟨h, ⟨le_rfl, by linarith⟩⟩,
        ⟨false, ⟨Classical.arbitrary _, ⟨0, Classical.arbitrary _⟩⟩⟩⟩⟩
    obtain ⟨hpoly, hemp⟩ := hcover P hbdy hh (hh.trans hhB)
    have hmeas : ∀ i : SeparableWinsorizedScoreIndex P p h,
        Measurable (separableWinsorizedScoreFunction P p h B R i) :=
      fun i => separableWinsorizedScoreFunction_measurable P p h B R i
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hCenv : 0 ≤ Cenv := by dsimp [Cenv]; positivity
    have hCB : c * (B + (p + 1 : ℝ) * R) ≤ Cenv * B := by
      have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
      have hB0 : 0 ≤ B := le_trans (by norm_num) hB
      dsimp [Cenv]
      have hpr : 0 ≤ (p + 1 : ℝ) * R := by positivity
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hB),
        mul_nonneg hB0 (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hpr)]
    have henvC : Cenv ≤ C := by
      dsimp [C]
      exact (le_max_right C₀ Cenv).trans (by linarith)
    have hU : c * (B + (p + 1 : ℝ) * R) ≤ C * B :=
      hCB.trans (mul_le_mul_of_nonneg_right henvC (le_trans (by norm_num) hB))
    have hU' : (2 * ((2 : ℝ) ^ p) ^ 2 + 2) *
        (B + ((p + 1 : ℕ) : ℝ) * R) ≤ C * B := by
      simpa [c, Nat.cast_add, Nat.cast_one] using hU
    have hC₀C : C₀ ≤ C := by
      dsimp [C]
      exact (le_max_left C₀ Cenv).trans (by linarith)
    have hCpos : 0 < C := by
      have : 0 ≤ max C₀ Cenv := (by positivity : 0 ≤ C₀).trans (le_max_left _ _)
      dsimp [C]
      linarith
    refine ⟨mul_pos hCpos hh, mul_lt_mul_of_pos_left hhB hCpos,
      hA₀.trans (by nlinarith [Real.exp_pos 1, hA₀]), hv, hmeas, ?_, ?_, ?_⟩
    · intro i z
      exact (hpoly.envelope i z).trans hU'
    · intro i
      exact (separableWinsorizedScore_hasUniformL2Radius_explicit p ν L R hR
        P hP h B hh hhB hB i).trans
          (mul_le_mul_of_nonneg_right hC₀C hh.le)
    · intro g₀
      exact Causalean.Stat.Concentration.HasPolynomialEmpiricalL2Cover.pullback
        (hemp.enlargeEnvelope hU') hmeas g₀

/-- A positive coefficient clipping radius can be chosen together with the
uniform entropy witnesses. -/
-- @node: winsorizedScore_hasVCUniformEntropy
lemma winsorizedScore_hasVCUniformEntropy
    (p : ℕ) (ν L : ℝ) :
    ∃ A v R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ h B : ℝ, 0 < h → h < B → 1 ≤ B →
        HasVCUniformEntropy P.law (separableWinsorizedScoreFunction P p h B R)
          (C * B) (C * h) A v := by
  obtain ⟨A, v, C, hC, h⟩ :=
    winsorizedScore_hasVCUniformEntropy_at p ν L 1 (by norm_num)
  exact ⟨A, v, 1, C, by norm_num, hC, h⟩

end CausalSmith.Stat.BddUniformLogPenalty
