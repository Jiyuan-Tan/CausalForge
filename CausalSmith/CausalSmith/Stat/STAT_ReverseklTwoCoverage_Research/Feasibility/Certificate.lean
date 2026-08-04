import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.CertificateAlgebra

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

-- @node: fixedExperimentBranchCount_le
lemma fixedExperimentBranchCount_le :
    fixedExperimentBranchCount E ≤
      (2 ^ Fintype.card 𝒳 - 1) * Fintype.card (𝒳 × 𝒜) := by
  let supports : Finset (Finset 𝒳) :=
    Finset.univ.filter Finset.Nonempty
  let cells : Finset (𝒳 × 𝒜) := Finset.univ
  have hsub :
      (Finset.univ.filter fun b : Finset 𝒳 × (𝒳 × 𝒜) =>
        b.1.Nonempty ∧ b.2.1 ∈ b.1 ∧
          0 < E.reference b.2.1 b.2.2) ⊆
        supports.product cells := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Finset.mem_product.mpr
      ⟨by simpa [supports] using hb.1, by simp [cells]⟩
  calc
    fixedExperimentBranchCount E ≤ (supports.product cells).card :=
      Finset.card_le_card hsub
    _ = supports.card * cells.card := Finset.card_product _ _
    _ = (2 ^ Fintype.card 𝒳 - 1) * Fintype.card (𝒳 × 𝒜) := by
      congr 1
      · rw [show supports =
            (Finset.univ : Finset (Finset 𝒳)).erase ∅ by
          ext s
          simp [supports, Finset.nonempty_iff_ne_empty]]
        rw [Finset.card_erase_of_mem (Finset.mem_univ ∅)]
        simp

-- @node: fixedExperimentVariableEquiv
lemma fixedExperimentVariableEquiv (I : Finset 𝒳) :
    Nonempty
      (((Fin d → ℝ) × (I → ℝ) × (Fin d → ℝ)) ≃
        (Fin (2 * d + I.card) → ℝ)) := by
  let eprod : (((Fin d → ℝ) × (I → ℝ)) × (Fin d → ℝ)) ≃
      (((Fin d ⊕ I) ⊕ Fin d) → ℝ) :=
    (Equiv.prodCongr
      (Equiv.sumPiEquivProdPi (fun _ : Fin d ⊕ I => ℝ)).symm
      (Equiv.refl (Fin d → ℝ))).trans
      (Equiv.sumPiEquivProdPi
        (fun _ : (Fin d ⊕ I) ⊕ Fin d => ℝ)).symm
  let eassoc : ((Fin d → ℝ) × (I → ℝ) × (Fin d → ℝ)) ≃
      (((Fin d → ℝ) × (I → ℝ)) × (Fin d → ℝ)) :=
    (Equiv.prodAssoc _ _ _).symm
  have hcard : Fintype.card ((Fin d ⊕ I) ⊕ Fin d) =
      2 * d + I.card := by
    simp
    omega
  let eind := (Fintype.equivFin ((Fin d ⊕ I) ⊕ Fin d)).trans
    (finCongr hcard)
  exact
    ⟨eassoc.trans
      (eprod.trans (Equiv.arrowCongr eind (Equiv.refl ℝ)))⟩

-- @node: lem:fixed-experiment-shell-certificate
lemma fixed_experiment_shell_certificate (C D : ℝ) :
    ((∃ P : BanditLaw E, ExactShell E P C D) ↔
      BoundedFeatures E ∧ FixedExperimentFeasibilitySystem E C D) ∧
    fixedExperimentBranchCount E ≤
      (2 ^ Fintype.card 𝒳 - 1) * Fintype.card (𝒳 × 𝒜) ∧
    ∀ I : Finset 𝒳, I.Nonempty →
      Nonempty
        (((Fin d → ℝ) × (I → ℝ) × (Fin d → ℝ)) ≃
          (Fin (2 * d + I.card) → ℝ)) := by
  refine ⟨?_, fixedExperimentBranchCount_le E, ?_⟩
  · exact fixed_experiment_shell_certificate_equiv E C D
  · intro I _hI
    exact fixedExperimentVariableEquiv I

end CausalSmith.Stat.ReverseKLTwoCoverage
