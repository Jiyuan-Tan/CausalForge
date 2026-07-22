/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The fixed null law for the private CATE lower bound
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CateWitness

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat
open ProbabilityTheory

-- @node: causalNullLaw
/-- Construct the common null law used by the two localized alternatives.  It keeps
the covariate marginal and density of a genuine member of the model, independently
draws treatment from `Bernoulli(e₀)`, and uses the fair signed two-point outcome
channel whose two arm regressions are both zero. -/
lemma causalNullLaw {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hne : ModelNonempty d alpha beta gamma L e0 f0 f1 r0 x0) :
    ∃ P0 : CateLaw d,
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P0 ∧
      IidSampling P0 ∧
      (∀ x, P0.mu0 x = 0) ∧ (∀ x, P0.mu1 x = 0) ∧ (∀ x, P0.pi x = e0) := by
  classical
  rcases hreg with ⟨halpha, hbeta, hgamma, hL, he0, hf0, hf01, hr0, hx0⟩
  rcases hne with ⟨Q, hQ, hiidQ⟩
  have hx0cube : x0 ∈ cube d := by
    intro i
    exact Set.mem_Icc.mpr ⟨(hx0 i).1.le, (hx0 i).2.le⟩
  have hLe0 : e0 ≤ L := by
    have hb := hQ.piH.2.1 0 (Nat.zero_le _) x0 hx0cube
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
    exact (hQ.overlap x0 hx0cube).1.trans ((le_abs_self _).trans hb)
  have he0L : |e0| ≤ L := by
    rw [abs_of_pos he0.1]
    exact hLe0
  have hzeroBeta : HolderBallStd (fun _ : Fin d → ℝ => (0 : ℝ)) beta L (cube d) :=
    holderBallStd_const 0 beta L (cube d) (by simpa using hL.le)
  have hzeroGamma : HolderBallStd (fun _ : Fin d → ℝ => (0 : ℝ)) gamma L (cube d) :=
    holderBallStd_const 0 gamma L (cube d) (by simpa using hL.le)
  let P0 : CateLaw d := cateWitnessLaw Q e0 0
  have hclass : HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P0 := by
    dsimp [P0]
    apply cateWitnessLaw_mem_class alpha beta gamma L e0 f0 f1 r0 x0 Q 0 hQ hiidQ
    · exact measurable_const
    · intro x
      simp
    · exact he0.1.le
    · exact he0.2.le
    · exact he0L
    · simpa using hzeroBeta
    · simpa using hzeroGamma
  have hiid : IidSampling P0 := by
    dsimp [P0]
    exact cateWitnessLaw_iidSampling Q e0 hiidQ hQ.pxMarginal measurable_const
      (by intro x; simp) he0.1.le (by linarith [he0.2])
  exact ⟨P0, hclass, hiid, by intro x; simp [P0, cateWitnessLaw],
    by intro x; simp [P0, cateWitnessLaw], by intro x; simp [P0, cateWitnessLaw]⟩

end CausalSmith.Stat.DpCateMinimax
