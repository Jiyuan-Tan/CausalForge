import Causalean.Stat.Concentration.Covering.EmpiricalPseudoMetric
import Causalean.Stat.Concentration.Covering.HausslerPacking

/-!
Metric bridge between empirical L² distance and weighted Boolean Hamming distance.

This file records the samplewise algebra used by localized finite-VC covering
arguments: for binary-factored real classes, empirical L² distance is exactly
the weighted Hamming distance of the induced Boolean traces.
-/

namespace Causalean.Stat.Concentration

open scoped BigOperators

/-- **Empirical L² distance as weighted Hamming distance.** For [a real-valued class that factors
through a Boolean classifier at each sample coordinate, `F i (S j) = φ j (π i (S j))`](hyp:hfactor),
[the squared empirical L²(Pₙ) distance between two members F i and F i' equals the weighted Hamming
distance² of their induced Boolean sample-patterns, with per-coordinate weight `(φ j true − φ j
false)² / n`](goal). -/
theorem empiricalDist_sq_eq_weightedHammingSq
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳)
    (π : ι → 𝒳 → Bool) (φ : Fin n → Bool → ℝ)
    (hfactor : ∀ i j, F i (S j) = φ j (π i (S j))) (i i' : ι) :
    (empiricalDist S (F i) (F i')) ^ 2
      = weightedHammingSq (fun j => (φ j true - φ j false) ^ 2 / (n : ℝ))
          (fun j => π i (S j)) (fun j => π i' (S j)) := by
  classical
  unfold empiricalDist empiricalNorm weightedHammingSq
  rw [Real.sq_sqrt]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    simp only [Pi.sub_apply]
    rw [hfactor i j, hfactor i' j]
    cases π i (S j) <;> cases π i' (S j)
    all_goals
      simp only [reduceCtorEq, if_true, if_false]
      ring
  · positivity

end Causalean.Stat.Concentration
