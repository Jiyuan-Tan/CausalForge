import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.ZeroRisk.ConstructionAnchor

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def zeroRiskDaggerPotential {𝒳 : Type*} [DecidableEq 𝒳]
    (xC : 𝒳) (x : 𝒳) (a : Fin 2) : ℝ :=
  if x = xC ∧ a = 1 then 1 else 0

noncomputable def zeroRiskDaggerPolicy
    {d : ℕ} {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳]
    [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    (E : CommonExperiment d 𝒳 (Fin 2)) (xC : 𝒳) :
    Policy 𝒳 (Fin 2) :=
  gibbsFromPotential E (zeroRiskDaggerPotential xC)

lemma indexQ_lt_one {eta C : ℝ} (heta : 0 < eta)
    (hC1 : 1 < C) :
    indexQ eta C < 1 := by
  have hden : 0 < Real.exp eta - 1 :=
    sub_pos.2 ((Real.one_lt_exp_iff).2 heta)
  rw [indexQ, div_lt_one hden]
  have hdiv : Real.exp eta / C < Real.exp eta :=
    div_lt_self (Real.exp_pos eta) hC1
  linarith

def zeroRiskTiltRatio (eta C t : ℝ) : ℝ :=
  Real.exp (eta * t) /
    (indexQ eta C * Real.exp (eta * t) + (1 - indexQ eta C))

lemma zeroRiskTiltNormalizer_pos {eta C t : ℝ}
    (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    0 < indexQ eta C * Real.exp (eta * t) +
      (1 - indexQ eta C) := by
  have hq : 0 < indexQ eta C :=
    indexQ_pos heta (by linarith) hCexp
  have hq1 : indexQ eta C < 1 := indexQ_lt_one heta hC1
  exact add_pos (mul_pos hq (Real.exp_pos _)) (sub_pos.2 hq1)

lemma zeroRiskTiltRatio_one {eta C : ℝ}
    (heta : 0 < eta) (hC1 : 1 < C) :
    zeroRiskTiltRatio eta C 1 = C := by
  have hCpos : 0 < C := by linarith
  rw [zeroRiskTiltRatio, mul_one,
    indexQ_normalizer (K := C) heta hCpos]
  field_simp [ne_of_gt hCpos]

lemma zeroRiskTiltRatio_lt_one_endpoint {eta C t : ℝ}
    (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) (ht : t < 1) :
    zeroRiskTiltRatio eta C t < C := by
  have hq1 : indexQ eta C < 1 := indexQ_lt_one heta hC1
  have hut : Real.exp (eta * t) < Real.exp eta := by
    rw [Real.exp_lt_exp]
    nlinarith
  have hden_t := zeroRiskTiltNormalizer_pos
    (t := t) heta hC1 hCexp
  have hden_one := zeroRiskTiltNormalizer_pos
    (t := (1 : ℝ)) heta hC1 hCexp
  calc
    zeroRiskTiltRatio eta C t < zeroRiskTiltRatio eta C 1 := by
      unfold zeroRiskTiltRatio
      norm_num at hden_one ⊢
      rw [div_lt_div_iff₀ hden_t hden_one]
      have hpos :
          0 < (1 - indexQ eta C) *
            (Real.exp eta - Real.exp (eta * t)) :=
        mul_pos (sub_pos.2 hq1) (sub_pos.2 hut)
      have hid :
          Real.exp eta *
              (indexQ eta C * Real.exp (eta * t) +
                (1 - indexQ eta C)) -
            Real.exp (eta * t) *
              (indexQ eta C * Real.exp eta +
                (1 - indexQ eta C)) =
            (1 - indexQ eta C) *
              (Real.exp eta - Real.exp (eta * t)) := by ring
      nlinarith
    _ = C := zeroRiskTiltRatio_one heta hC1

lemma zeroRisk_common_gibbs
    {d : ℕ} {𝒳 : Type*}
    [Fintype 𝒳] [DecidableEq 𝒳]
    [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    (E : CommonExperiment d 𝒳 (Fin 2)) (xC : 𝒳)
    (C D : ℝ) (hC1 : 1 < C) (hCexp : C < Real.exp E.eta)
    (href0 : E.reference xC 0 = 1 - indexQ E.eta C)
    (href1 : E.reference xC 1 = indexQ E.eta C)
    (hzero : ∀ P ∈ exactShellSet E C D,
      linearReward P xC 0 = 0)
    (hinvariant : ∀ P ∈ exactShellSet E C D,
      ∀ x, x ≠ xC → ∀ a,
        linearReward P x a = linearReward P x 0) :
    ∀ P ∈ exactShellSet E C D,
      gibbsPolicy E P = zeroRiskDaggerPolicy E xC := by
  intro P hP
  have hshell : ExactShell E P C D := hP
  let t := linearReward P xC 1
  have htmem : t ∈ Set.Icc (0 : ℝ) 1 :=
    hshell.linearRealizability.1 xC 1
  have hu : 1 ≤ Real.exp (E.eta * t) :=
    Real.one_le_exp (mul_nonneg E.eta_pos.le htmem.1)
  have hqpos : 0 < indexQ E.eta C :=
    indexQ_pos E.eta_pos (by linarith) hCexp
  have hqle : indexQ E.eta C ≤ 1 :=
    (indexQ_lt_one E.eta_pos hC1).le
  have hZpos := zeroRiskTiltNormalizer_pos
    (t := t) E.eta_pos hC1 hCexp
  have hratio_one : 1 ≤ zeroRiskTiltRatio E.eta C t := by
    unfold zeroRiskTiltRatio
    rw [le_div_iff₀ hZpos]
    nlinarith [mul_nonneg (sub_nonneg.2 hqle) (sub_nonneg.2 hu)]
  have hnormalizer :
      gibbsNormalizer E P xC =
        indexQ E.eta C * Real.exp (E.eta * t) +
          (1 - indexQ E.eta C) := by
    simp [gibbsNormalizer, Fin.sum_univ_two, href0, href1,
      hzero P hP, t]
    ring
  let R : Set ℝ :=
    {c | ∃ x a, 0 < contextMass P x ∧ 0 < E.reference x a ∧
      c = gibbsPolicy E P x a / E.reference x a}
  have hRfinite : R.Finite := by
    apply Set.Finite.subset (Set.finite_range
      (fun p : 𝒳 × Fin 2 =>
        gibbsPolicy E P p.1 p.2 / E.reference p.1 p.2))
    rintro c ⟨x, a, _, _, rfl⟩
    exact Set.mem_range_self (x, a)
  have hRnonempty : R.Nonempty := by
    by_contra hn
    have hcov0 : pointwiseCoverage E P = 0 := by
      unfold pointwiseCoverage
      change sSup R = 0
      rw [Set.not_nonempty_iff_eq_empty.mp hn]
      simp
    have : C = 0 := hshell.pointwiseExactShell.2.symm.trans hcov0
    linarith
  have hupper : ∀ c ∈ R, c ≤ zeroRiskTiltRatio E.eta C t := by
    rintro c ⟨x, a, hx, ha, rfl⟩
    by_cases hxc : x = xC
    · subst x
      fin_cases a
      · norm_num at ha ⊢
        rw [gibbsPolicy, hnormalizer, hzero P hP, href0]
        change ((1 - indexQ E.eta C) * Real.exp (E.eta * 0) /
            (indexQ E.eta C * Real.exp (E.eta * t) +
              (1 - indexQ E.eta C))) /
            (1 - indexQ E.eta C) ≤ zeroRiskTiltRatio E.eta C t
        norm_num
        have hq1 : 0 < 1 - indexQ E.eta C :=
          sub_pos.2 (indexQ_lt_one E.eta_pos hC1)
        unfold zeroRiskTiltRatio
        field_simp [ne_of_gt hq1, ne_of_gt hZpos]
        exact hu
      · norm_num at ha ⊢
        rw [gibbsPolicy, hnormalizer, href1]
        change (indexQ E.eta C * Real.exp (E.eta * t) /
            (indexQ E.eta C * Real.exp (E.eta * t) +
              (1 - indexQ E.eta C))) /
            indexQ E.eta C ≤ zeroRiskTiltRatio E.eta C t
        unfold zeroRiskTiltRatio
        field_simp [ne_of_gt hqpos, ne_of_gt hZpos]
        norm_num
    · have hconst := hinvariant P hP x hxc
      have hnorm :
          gibbsNormalizer E P x =
            Real.exp (E.eta * linearReward P x 0) := by
        simp only [gibbsNormalizer]
        simp_rw [hconst]
        rw [← Finset.sum_mul, E.reference_isPolicy.2 x, one_mul]
      rw [gibbsPolicy, hnorm]
      rw [hconst a]
      field_simp [ne_of_gt ha, ne_of_gt (Real.exp_pos _)]
      simpa using hratio_one
  have hC_le : C ≤ zeroRiskTiltRatio E.eta C t := by
    calc
      C = pointwiseCoverage E P := hshell.pointwiseExactShell.2.symm
      _ = sSup R := rfl
      _ ≤ zeroRiskTiltRatio E.eta C t := csSup_le hRnonempty hupper
  have ht : t = 1 := by
    apply le_antisymm htmem.2
    by_contra hnot
    have hlt : t < 1 := lt_of_not_ge hnot
    exact (not_lt_of_ge hC_le)
      (zeroRiskTiltRatio_lt_one_endpoint E.eta_pos hC1 hCexp hlt)
  funext x a
  by_cases hxc : x = xC
  · subst x
    have ht' : linearReward P xC 1 = 1 := ht
    fin_cases a
    · norm_num at ⊢
      simp only [zeroRiskDaggerPolicy, gibbsFromPotential]
      rw [gibbsPolicy, hnormalizer, hzero P hP, href0, ht]
      simp [zeroRiskDaggerPotential, Fin.sum_univ_two, href0, href1]
      ring
    · norm_num at ⊢
      simp only [zeroRiskDaggerPolicy, gibbsFromPotential]
      rw [gibbsPolicy, hnormalizer, href1, ht, ht']
      simp [zeroRiskDaggerPotential, Fin.sum_univ_two, href0, href1]
      ring
  · have hconst := hinvariant P hP x hxc
    have hnorm :
        gibbsNormalizer E P x =
          Real.exp (E.eta * linearReward P x 0) := by
      simp only [gibbsNormalizer]
      simp_rw [hconst]
      rw [← Finset.sum_mul, E.reference_isPolicy.2 x, one_mul]
    rw [gibbsPolicy, hnorm]
    simp only [zeroRiskDaggerPolicy, gibbsFromPotential,
      zeroRiskDaggerPotential, hxc, false_and, if_false]
    rw [show ∑ b : Fin 2, E.reference x b * Real.exp (E.eta * 0) = 1 by
      simp [E.reference_isPolicy.2 x]]
    rw [hconst a]
    simp

lemma zeroRiskCore_common_gibbs (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    ∀ P ∈ exactShellSet
        (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) C D,
      gibbsPolicy
          (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp) P =
        zeroRiskDaggerPolicy
          (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
          (⟨0, by omega⟩ : Fin d) := by
  refine zeroRisk_common_gibbs
    (zeroRiskCoreExperiment d hd eta C heta hC1 hCexp)
    (⟨0, by omega⟩ : Fin d) C D hC1 ?_ ?_ ?_ ?_ ?_
  · exact hCexp
  · simp [zeroRiskCoreExperiment, zeroRiskCoreReference,
      diagonalIndexReference]
  · simp [zeroRiskCoreExperiment, zeroRiskCoreReference,
      diagonalIndexReference]
  · intro P hP
    simp [linearReward, zeroRiskCoreExperiment, zeroRiskCoreFeature,
      diagonalIndexFeature]
  · intro P hP x hx a
    simp [linearReward, zeroRiskCoreExperiment, zeroRiskCoreFeature, hx]

lemma zeroRiskAnchor_common_gibbs (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    ∀ P ∈ exactShellSet
        (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) C D,
      gibbsPolicy
          (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp) P =
        zeroRiskDaggerPolicy
          (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
          (⟨0, by omega⟩ : Fin d).succ := by
  refine zeroRisk_common_gibbs
    (zeroRiskAnchorExperiment d hd eta C heta hC1 hCexp)
    (⟨0, by omega⟩ : Fin d).succ C D hC1 ?_ ?_ ?_ ?_ ?_
  · exact hCexp
  · simp [zeroRiskAnchorExperiment, zeroRiskAnchorReference,
      zeroRiskCoreReference, diagonalIndexReference]
  · simp [zeroRiskAnchorExperiment, zeroRiskAnchorReference,
      zeroRiskCoreReference, diagonalIndexReference]
  · intro P hP
    simp [linearReward, zeroRiskAnchorExperiment, zeroRiskAnchorFeature,
      zeroRiskCoreFeature, diagonalIndexFeature]
  · intro P hP x hx a
    revert hx
    refine Fin.cases ?_ (fun j => ?_) x
    · intro hx
      simp [linearReward, zeroRiskAnchorExperiment, zeroRiskAnchorFeature]
    · intro hx
      have hj : j ≠ (⟨0, by omega⟩ : Fin d) := by
        intro hj
        subst j
        exact hx rfl
      simp [linearReward, zeroRiskAnchorExperiment, zeroRiskAnchorFeature,
        zeroRiskCoreFeature, hj]

end

end CausalSmith.Stat.ReverseKLTwoCoverage

