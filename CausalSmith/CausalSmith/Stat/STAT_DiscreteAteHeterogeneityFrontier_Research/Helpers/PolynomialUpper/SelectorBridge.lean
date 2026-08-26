/- Exact transport of fixed heavy/light branches to the independent fold law. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.AggregateBridge

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Causalean.Stat
open Causalean.Stat.FiniteStratumMarkedRatioMse

/-- If [the selected heavy set is fixed](hyp:hH), [the selector's fixed heavy error equals the
  heavy component of the corresponding fixed branch](goal). -/
lemma polynomialFixedHeavyError_eq_fixedBranchHeavy {n d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (base : Obs d) (H : Finset (Fin d))
    (x : (polynomialBalancedSplit P.law).foldB n → Obs d)
    (hH : ∀ k ∈ H, 0 < P.law.cellMass k) :
    polynomialFixedHeavyError P.law base M H x =
      (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
          (fun o => o.y) H (polynomialFoldBReindex P.law x) -
        fixedStratumMarkedTarget P.law.observedLaw (fun o : Obs d => o.x)
          (fun o => o.a) (fun o => o.y) H) / M := by
  classical
  rw [polynomialFixedStratumMarkedTarget_eq_cellEffectSum P H hH]
  unfold polynomialFixedHeavyError fixedStratumMarkedRatio fixedStratumArmScore
  simp_rw [heavyEmpiricalTerm_rebuild_eq_reindex P.law base x]
  simp only [sub_div, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  simp_rw [Finset.sum_div]

/-- [the selector's fixed light error equals the light component of the corresponding fixed
  branch](goal). -/
lemma polynomialFixedLightError_eq_fixedBranchLight {n d : ℕ}
    (P : RealLaw d) (base : Obs d) (M : ℝ) (H : Finset (Fin d))
    (x : (polynomialBalancedSplit P).foldB n → Obs d) :
    polynomialFixedLightError P base M H x =
      allBlockMarkedPolynomialSum M
          (4096 * logEN n / (n - n / 2 : ℕ)) (polynomialDegree n)
          (Finset.univ \ H) (polynomialFoldBReindex P x) -
        ∑ k ∈ Finset.univ \ H, P.cellMass k * cellEffect P k / M := by
  classical
  unfold polynomialFixedLightError
  dsimp only
  calc
    (∑ k : Fin d, if k ∈ H then 0 else
        lightPolynomialTerm M (4096 * logEN n / (n - n / 2 : ℕ))
            (polynomialDegree n) (rebuildPolynomialEstimationSample P base x) k -
          P.cellMass k * cellEffect P k / M) =
        ∑ k ∈ Finset.univ \ H,
          (lightPolynomialTerm M (4096 * logEN n / (n - n / 2 : ℕ))
              (polynomialDegree n) (rebuildPolynomialEstimationSample P base x) k -
            P.cellMass k * cellEffect P k / M) := by
      rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ H <;> simp [hk]
    _ = (∑ k ∈ Finset.univ \ H,
          lightPolynomialTerm M (4096 * logEN n / (n - n / 2 : ℕ))
            (polynomialDegree n) (rebuildPolynomialEstimationSample P base x) k) -
        ∑ k ∈ Finset.univ \ H, P.cellMass k * cellEffect P k / M := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [lightPolynomialSum_rebuild_eq_allBlock]

/-- If [the selected heavy set is fixed](hyp:hH), [the selector's fixed total error equals the
  error of the corresponding fixed branch](goal). -/
lemma polynomialFixedTotalError_eq_fixedBranch {n d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (base : Obs d) (H : Finset (Fin d))
    (x : (polynomialBalancedSplit P.law).foldB n → Obs d)
    (hH : ∀ k ∈ H, 0 < P.law.cellMass k) :
    polynomialFixedTotalError P.law base M H x =
      polynomialFixedBranchNormalizedError P.law M
        (K := polynomialDegree n)
        (4096 * logEN n / (n - n / 2 : ℕ)) H
        (polynomialFoldBReindex P.law x) := by
  rw [polynomialFixedTotalError,
    polynomialFixedHeavyError_eq_fixedBranchHeavy P base H x hH,
    polynomialFixedLightError_eq_fixedBranchLight]
  rfl

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
