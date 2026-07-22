/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Auxiliary apolar-kernel facts for arrow recovery
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernelIdentity
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarQD

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-- The support annihilator is a binary form of degree `m + 2`. -/
lemma supportAnnihilator_isHomogeneous {m : ℕ} (dirs : Fin (m + 2) → ℂ × ℂ) :
    (supportAnnihilator dirs).IsHomogeneous (m + 2) := by
  rw [supportAnnihilator]
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun j => MvPolynomial.C (dirs j).2 * MvPolynomial.X (0 : Fin 2) -
      MvPolynomial.C (dirs j).1 * MvPolynomial.X (1 : Fin 2)) (fun _ => 1) ?_
  · simpa using h
  · intro i hi
    exact (MvPolynomial.isHomogeneous_C_mul_X (dirs i).2 (0 : Fin 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X (dirs i).1 (1 : Fin 2))

-- `diffApply_sum` / `diffApply_C_mul` (and their `pderiv_iterate_*` helpers) are
-- the public versions in `ApolarKernelIdentity`; used directly below to avoid a
-- duplicate `_aux` copy.
private lemma reverse_contractions_vanish_of_evalAtDir_zero (m : ℕ)
    (η : ParamSpace ℂ m) (q : MvPolynomial (Fin 2) ℂ)
    (hq : q.IsHomogeneous (m + 2))
    (hzero : ∀ j, evalAtDir q (reverseLoading m η.1 η.2.1 j) = 0)
    (k : ℕ) (hk : k ≤ m) :
    diffApply q
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0 := by
  rw [dividedPowerBlock_reverse_eq_sum_linForm_pow m (2 * m + 2) (m + 2 + k) η]
  · rw [diffApply_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [diffApply_C_mul, diffApply_linForm_pow q hq]
    rw [hzero j]
    simp
  · omega
  · omega

/-- The reverse support-annihilator line lies in the common contraction kernel. -/
lemma reverse_supportAnnihilator_in_contraction_kernel (m : ℕ) (η : ParamSpace ℂ m)
    (q : MvPolynomial (Fin 2) ℂ) (hq : q.IsHomogeneous (m + 2))
    (hqD : ∃ c : ℂ, q = c • supportAnnihilator (reverseLoading m η.1 η.2.1)) :
    ∀ k, k ≤ m → diffApply q
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0 := by
  rintro k hk
  apply reverse_contractions_vanish_of_evalAtDir_zero m η q hq _ k hk
  intro j
  rcases hqD with ⟨c, rfl⟩
  simp only [MvPolynomial.smul_eq_C_mul]
  have hQ : evalAtDir (supportAnnihilator (reverseLoading m η.1 η.2.1))
      (reverseLoading m η.1 η.2.1 j) = 0 :=
    evalAtDir_supportAnnihilator_eq_zero _ j
  simp only [evalAtDir] at hQ ⊢
  rw [MvPolynomial.eval_mul, hQ, mul_zero]

/-- The roots of the default forward finite-slope polynomial are its slopes. -/
lemma qDefault_rtsF_roots {m : ℕ} (θ : ParamSpace ℂ m) :
    (qDefault (rtsF θ)).roots = θ.1 ::ₘ (Finset.univ.val.map (fun i => θ.2.1 i)) := by
  rw [qDefault_roots, rtsF]

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
