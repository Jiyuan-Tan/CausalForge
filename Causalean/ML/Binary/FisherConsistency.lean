/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Fisher consistency of the logistic cross-entropy loss

The Bernoulli cross-entropy `bernoulliCE η q = −η log q − (1−η) log(1−q)` is
minimized over `q ∈ [0,1]` exactly at `q = η`.  This is the pointwise heart of
Fisher consistency: the population log-loss minimizer recovers the true
conditional probability `η(x) = P(Y = 1 ∣ X = x)`.
-/

namespace Causalean.ML

/-- The Bernoulli cross-entropy of predicting probability `q` when the true
probability is `η`. -/
noncomputable def bernoulliCE (η q : ℝ) : ℝ :=
  -η * Real.log q - (1 - η) * Real.log (1 - q)

/-- For a true probability `η ∈ (0,1)`, the Bernoulli cross-entropy
`q ↦ bernoulliCE η q` is minimized over the interior
`(0,1)` at the truth `q = η`.  (The interior is essential: Mathlib's junk
convention `Real.log 0 = 0` makes the closed-interval version false at the
boundary, where the genuine cross-entropy is `+∞`.) -/
theorem bernoulliCE_isMinOn {η : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    IsMinOn (fun q : ℝ => bernoulliCE η q) (Set.Ioo (0 : ℝ) 1) η := by
  rw [isMinOn_iff]
  intro q hq
  rcases hη with ⟨hη0, hη1⟩
  rcases hq with ⟨hq0, hq1⟩
  have hη1pos : 0 < 1 - η := sub_pos.mpr hη1
  have hq1pos : 0 < 1 - q := sub_pos.mpr hq1
  have hlog1 : Real.log q - Real.log η ≤ q / η - 1 := by
    simpa [Real.log_div hq0.ne' hη0.ne'] using
      (Real.log_le_sub_one_of_pos (div_pos hq0 hη0))
  have hineq1 : η * (Real.log q - Real.log η) ≤ q - η := by
    have hmul := mul_le_mul_of_nonneg_left hlog1 hη0.le
    have hrhs : η * (q / η - 1) = q - η := by
      field_simp [hη0.ne']
    simpa [hrhs] using hmul
  have hlog2 :
      Real.log (1 - q) - Real.log (1 - η) ≤ (1 - q) / (1 - η) - 1 := by
    simpa [Real.log_div hq1pos.ne' hη1pos.ne'] using
      (Real.log_le_sub_one_of_pos (div_pos hq1pos hη1pos))
  have hineq2 :
      (1 - η) * (Real.log (1 - q) - Real.log (1 - η)) ≤ η - q := by
    have hmul := mul_le_mul_of_nonneg_left hlog2 hη1pos.le
    have hrhs : (1 - η) * ((1 - q) / (1 - η) - 1) = η - q := by
      field_simp [hη1pos.ne']
      ring
    simpa [hrhs] using hmul
  have hsum :
      η * Real.log q + (1 - η) * Real.log (1 - q) ≤
        η * Real.log η + (1 - η) * Real.log (1 - η) := by
    nlinarith [hineq1, hineq2]
  unfold bernoulliCE
  nlinarith

end Causalean.ML
