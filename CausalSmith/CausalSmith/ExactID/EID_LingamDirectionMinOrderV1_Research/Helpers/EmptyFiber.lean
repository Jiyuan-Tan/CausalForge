/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Empty opposite-arrow fibers
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ReverseApolarKernel
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernelAux

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- A point satisfying the forward apolar rank conditions has no reverse-arrow
parameterization with the same truncated cumulants. -/
theorem forward_reverse_fiber_empty (m : ℕ) (θ : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2))
    (hγ : θ.1 ≠ 0) (hρ : ∀ i, θ.2.1 i ≠ 0)
    (hnonzero : ∀ j : Fin (m + 1),
      (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2 ≠ 0)
    (hrank : Function.Injective (forwardWeightedContraction m θ)) :
    fiberCorrespondence (2 * m + 2) (reverseCumulantMap m (2 * m + 2))
      (forwardCumulantMap m (2 * m + 2) θ) = (∅ : Set (ParamSpace ℂ m)) := by
  ext η
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hη
  rcases hη with ⟨_hband, hηband⟩
  -- `fiberCorrespondence` compares the two cumulant vectors on the retained band only;
  -- both maps vanish off the band by construction, so band-equality gives full equality.
  have hη : reverseCumulantMap m (2 * m + 2) η =
      forwardCumulantMap m (2 * m + 2) θ := by
    funext r a
    by_cases hb : 2 ≤ r ∧ r ≤ 2 * m + 2 ∧ a ≤ r
    · exact hηband r a hb.1 hb.2.1 hb.2.2
    · simp [reverseCumulantMap, forwardCumulantMap, hb]
  let Qr := supportAnnihilator (reverseLoading m η.1 η.2.1)
  let Qf := supportAnnihilator (forwardLoading m θ.1 θ.2.1)
  have hQrHom : Qr.IsHomogeneous (m + 2) :=
    supportAnnihilator_isHomogeneous _
  have hQrRev : ∀ k, k ≤ m → diffApply Qr
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0 :=
    reverse_supportAnnihilator_in_contraction_kernel m η Qr hQrHom ⟨1, by simp [Qr]⟩
  have hQrFwd : ∀ k, k ≤ m → diffApply Qr
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0 := by
    simpa [hη] using hQrRev
  obtain ⟨c, hc⟩ :=
    (forward_apolar_kernel_identity m θ hslopes hnonzero hrank Qr hQrHom).mp hQrFwd
  have hdivQr : MvPolynomial.X (1 : Fin 2) ∣ Qr := by
    simpa [Qr] using X1_dvd_supportAnnihilator_reverse η.1 η.2.1
  have hnDivQf : ¬ MvPolynomial.X (1 : Fin 2) ∣ Qf := by
    simpa [Qf] using
      not_X1_dvd_supportAnnihilator_forward θ.1 θ.2.1 hγ hρ
  have hQrNe : Qr ≠ 0 := by
    apply supportAnnihilator_ne_zero (reverseLoading m η.1 η.2.1)
    intro j
    by_cases hj0 : j.val = 0
    · left
      simp [reverseLoading, hj0]
    · right
      simp only [reverseLoading, hj0, ↓reduceDIte]
      split <;> simp
  by_cases hc0 : c = 0
  · apply hQrNe
    rw [hc, hc0]
    simp
  · apply hnDivQf
    obtain ⟨p, hp⟩ := hdivQr
    refine ⟨MvPolynomial.C c⁻¹ * p, ?_⟩
    rw [hc] at hp
    simp only [MvPolynomial.smul_eq_C_mul] at hp
    calc
      Qf = MvPolynomial.C c⁻¹ * (MvPolynomial.C c * Qf) := by
        rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      _ = MvPolynomial.C c⁻¹ * (MvPolynomial.X (1 : Fin 2) * p) := by rw [← hp]
      _ = MvPolynomial.X (1 : Fin 2) * (MvPolynomial.C c⁻¹ * p) := by ring

/-- A point satisfying the reverse apolar rank conditions has no forward-arrow
parameterization with the same truncated cumulants. -/
theorem reverse_forward_fiber_empty (m : ℕ) (η : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (reverseLoading m η.1 η.2.1 j.succ).1))
    (hδ : η.1 ≠ 0) (hσ : ∀ i, η.2.1 i ≠ 0)
    (hnonzero : ∀ j : Fin (m + 1), (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0)
    (hrank : Function.Injective (reverseWeightedContraction m η)) :
    fiberCorrespondence (2 * m + 2) (forwardCumulantMap m (2 * m + 2))
      (reverseCumulantMap m (2 * m + 2) η) = (∅ : Set (ParamSpace ℂ m)) := by
  ext θ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hθ
  rcases hθ with ⟨_hband, hθband⟩
  -- band-equality gives full equality: both cumulant maps vanish off the retained band.
  have hθ : forwardCumulantMap m (2 * m + 2) θ =
      reverseCumulantMap m (2 * m + 2) η := by
    funext r a
    by_cases hb : 2 ≤ r ∧ r ≤ 2 * m + 2 ∧ a ≤ r
    · exact hθband r a hb.1 hb.2.1 hb.2.2
    · simp [forwardCumulantMap, reverseCumulantMap, hb]
  let Qf := supportAnnihilator (forwardLoading m θ.1 θ.2.1)
  let Qr := supportAnnihilator (reverseLoading m η.1 η.2.1)
  have hQfHom : Qf.IsHomogeneous (m + 2) :=
    supportAnnihilator_isHomogeneous _
  have hQfFwd : ∀ k, k ≤ m → diffApply Qf
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0 :=
    forward_supportAnnihilator_in_contraction_kernel m θ Qf hQfHom ⟨1, by simp [Qf]⟩
  have hQfRev : ∀ k, k ≤ m → diffApply Qf
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0 := by
    simpa [hθ] using hQfFwd
  obtain ⟨c, hc⟩ :=
    (reverse_apolar_kernel_identity m η hslopes hnonzero hrank Qf hQfHom).mp hQfRev
  have hdivQf : MvPolynomial.X (0 : Fin 2) ∣ Qf := by
    simpa [Qf] using X0_dvd_supportAnnihilator_forward θ.1 θ.2.1
  have hnDivQr : ¬ MvPolynomial.X (0 : Fin 2) ∣ Qr := by
    simpa [Qr] using
      not_X0_dvd_supportAnnihilator_reverse η.1 η.2.1 hδ hσ
  have hQfNe : Qf ≠ 0 := by
    apply supportAnnihilator_ne_zero (forwardLoading m θ.1 θ.2.1)
    intro j
    by_cases hjlast : j.val = m + 1
    · right
      simp [forwardLoading, hjlast]
    · left
      simp only [forwardLoading]
      split <;> simp_all
  by_cases hc0 : c = 0
  · apply hQfNe
    rw [hc, hc0]
    simp
  · apply hnDivQr
    obtain ⟨p, hp⟩ := hdivQf
    refine ⟨MvPolynomial.C c⁻¹ * p, ?_⟩
    rw [hc] at hp
    simp only [MvPolynomial.smul_eq_C_mul] at hp
    calc
      Qr = MvPolynomial.C c⁻¹ * (MvPolynomial.C c * Qr) := by
        rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      _ = MvPolynomial.C c⁻¹ * (MvPolynomial.X (0 : Fin 2) * p) := by rw [← hp]
      _ = MvPolynomial.X (0 : Fin 2) * (MvPolynomial.C c⁻¹ * p) := by ring

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
