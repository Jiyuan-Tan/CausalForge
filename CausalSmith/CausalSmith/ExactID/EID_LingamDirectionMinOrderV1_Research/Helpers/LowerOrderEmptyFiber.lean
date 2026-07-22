/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Empty opposite fibers at order `2m+1`
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.LowerOrderApolarKernel

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

noncomputable section

-- @node: lowerForwardReverseImpossible
/-- Proves the stated mathematical property of lower Forward Reverse Impossible. -/
theorem lowerForwardReverseImpossible (m : ℕ) (hm : 3 ≤ m) (θ : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (forwardLoading m θ.1 θ.2.1 j.castSucc).2))
    (hγ : θ.1 ≠ 0) (hρ : ∀ i, θ.2.1 i ≠ 0)
    (hnonzero : ∀ j : Fin (m + 1),
      (forwardLoading m θ.1 θ.2.1 j.castSucc).2 ≠ 0)
    (hrank : Function.Injective (lowerForwardWeightedContraction m θ)) :
    ∀ η : ParamSpace ℂ m,
      forwardCumulantMap m (2 * m + 1) θ ≠ reverseCumulantMap m (2 * m + 1) η := by
  intro η heq
  let Qr := supportAnnihilator (reverseLoading m η.1 η.2.1)
  let Qf := supportAnnihilator (forwardLoading m θ.1 θ.2.1)
  have hQrHom : Qr.IsHomogeneous (m + 2) := supportAnnihilator_isHomogeneous _
  have hQrRev : ∀ k, k ≤ m - 1 → diffApply Qr
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 1) η) (m + 2 + k)) = 0 :=
    lowerReverseSupportAnnihilatorInKernel m hm η Qr hQrHom ⟨1, by simp [Qr]⟩
  have hQrFwd : ∀ k, k ≤ m - 1 → diffApply Qr
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 1) θ) (m + 2 + k)) = 0 := by
    simpa [heq] using hQrRev
  obtain ⟨c, hc⟩ :=
    (lowerForwardApolarKernelIdentity m hm θ hslopes hnonzero hrank Qr hQrHom).mp hQrFwd
  have hdivQr : MvPolynomial.X (1 : Fin 2) ∣ Qr := by
    simpa [Qr] using X1_dvd_supportAnnihilator_reverse η.1 η.2.1
  have hnDivQf : ¬ MvPolynomial.X (1 : Fin 2) ∣ Qf := by
    simpa [Qf] using not_X1_dvd_supportAnnihilator_forward θ.1 θ.2.1 hγ hρ
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

-- @node: lowerReverseForwardImpossible
/-- Proves the stated mathematical property of lower Reverse Forward Impossible. -/
theorem lowerReverseForwardImpossible (m : ℕ) (hm : 3 ≤ m) (η : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) => (reverseLoading m η.1 η.2.1 j.succ).1))
    (hδ : η.1 ≠ 0) (hσ : ∀ i, η.2.1 i ≠ 0)
    (hnonzero : ∀ j : Fin (m + 1), (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0)
    (hrank : Function.Injective (lowerReverseWeightedContraction m η)) :
    ∀ θ : ParamSpace ℂ m,
      reverseCumulantMap m (2 * m + 1) η ≠ forwardCumulantMap m (2 * m + 1) θ := by
  intro θ heq
  let Qf := supportAnnihilator (forwardLoading m θ.1 θ.2.1)
  let Qr := supportAnnihilator (reverseLoading m η.1 η.2.1)
  have hQfHom : Qf.IsHomogeneous (m + 2) := supportAnnihilator_isHomogeneous _
  have hQfFwd : ∀ k, k ≤ m - 1 → diffApply Qf
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 1) θ) (m + 2 + k)) = 0 :=
    lowerForwardSupportAnnihilatorInKernel m hm θ Qf hQfHom ⟨1, by simp [Qf]⟩
  have hQfRev : ∀ k, k ≤ m - 1 → diffApply Qf
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 1) η) (m + 2 + k)) = 0 := by
    simpa [heq] using hQfFwd
  obtain ⟨c, hc⟩ :=
    (lowerReverseApolarKernelIdentity m hm η hslopes hnonzero hrank Qf hQfHom).mp hQfRev
  have hdivQf : MvPolynomial.X (0 : Fin 2) ∣ Qf := by
    simpa [Qf] using X0_dvd_supportAnnihilator_forward θ.1 θ.2.1
  have hnDivQr : ¬ MvPolynomial.X (0 : Fin 2) ∣ Qr := by
    simpa [Qr] using not_X0_dvd_supportAnnihilator_reverse η.1 η.2.1 hδ hσ
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
