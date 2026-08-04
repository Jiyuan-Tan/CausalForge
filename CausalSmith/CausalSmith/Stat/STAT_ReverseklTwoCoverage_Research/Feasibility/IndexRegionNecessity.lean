import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionNecessityAlgebra

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

theorem exactShell_index_constraints
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hP : ExactShell E P C D) :
    1 ≤ D ∧ D ≤ C ∧ C < Real.exp E.eta ∧
      ((C = 1 ∧ D = 1) ∨ (1 < D ∧ D ≤ C)) := by
  rcases (fixed_experiment_shell_certificate E C D).1.mp ⟨P, hP⟩ with
    ⟨_hbounded, I, hI, x0, a0, theta, rho, u, href0, hscore,
      hrho, hsum, hBpos, hcovle, hcoveq, hPSD, hker, hunorm⟩
  let B := ∑ x : I, rho x • loggingBlock E x.1
  let G := ∑ x : I, rho x • targetBlock E theta x.1
  have hune : u ≠ 0 := by
    intro hu
    simp [hu] at hunorm
  have hBupos : 0 < quadraticForm B u := by
    rw [quadraticForm_eq_toQuadraticMap]
    exact hBpos.toQuadraticForm' u hune
  have hGu_eq : quadraticForm G u = D * quadraticForm B u := by
    have hz : quadraticForm (D • B - G) u = 0 := by
      rw [quadraticForm_eq_dotProduct_mulVec, hker]
      simp
    rw [quadraticForm_smul_sub] at hz
    linarith
  have hGu_le : quadraticForm G u ≤ C * quadraticForm B u := by
    rw [quadraticForm_sum_blocks rho
      (fun x : I => targetBlock E theta x.1) u,
      quadraticForm_sum_blocks rho
        (fun x : I => loggingBlock E x.1) u]
    calc
      (∑ x : I, rho x * quadraticForm (targetBlock E theta x.1) u) ≤
          ∑ x : I, rho x *
            (C * quadraticForm (loggingBlock E x.1) u) := by
              apply Finset.sum_le_sum
              intro x _
              exact mul_le_mul_of_nonneg_left
                (targetBlock_le_pointwise E theta u x.1 C (hcovle x))
                (hrho x).le
      _ = C * ∑ x : I, rho x *
          quadraticForm (loggingBlock E x.1) u := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
  have hDC : D ≤ C := by nlinarith
  have hlocal_tilt :
      ∀ x : I, quadraticForm (loggingBlock E x.1) theta ≤
        quadraticForm (targetBlock E theta x.1) theta :=
    fun x => loggingBlock_le_targetBlock_at_theta E theta x.1 (hscore x.1)
  have hglobal_tilt : quadraticForm B theta ≤ quadraticForm G theta := by
    rw [quadraticForm_sum_blocks rho
      (fun x : I => loggingBlock E x.1) theta,
      quadraticForm_sum_blocks rho
        (fun x : I => targetBlock E theta x.1) theta]
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hlocal_tilt x) (hrho x).le
  have hDone : 1 ≤ D := by
    by_cases htheta : theta = 0
    · have hblock :
          ∀ x : I, targetBlock E theta x.1 = loggingBlock E x.1 := by
        intro x
        ext i j
        simp [targetBlock, loggingBlock, candidateWeight,
          candidateNormalizer, htheta, E.reference_isPolicy.2]
      have hGB : G = B := by
        simp only [G, B]
        apply Finset.sum_congr rfl
        intro x _
        rw [hblock x]
      rw [hGB] at hGu_eq
      nlinarith
    · have hBtpos : 0 < quadraticForm B theta := by
        rw [quadraticForm_eq_toQuadraticMap]
        exact hBpos.toQuadraticForm' theta htheta
      have hpsd := hPSD.dotProduct_mulVec_nonneg theta
      rw [← quadraticForm_eq_dotProduct_mulVec,
        quadraticForm_smul_sub] at hpsd
      nlinarith
  have hpoint :=
    certificate_pointwise_lower_and_strict_upper E theta x0.1 a0 C
      href0 (hscore x0.1) (hcovle x0) hcoveq
  rcases hpoint with ⟨hCone, hCexp⟩
  have hstrict : C ≠ 1 → 1 < D := by
    intro hCne
    have hvar : ∃ a b, 0 < E.reference x0.1 a ∧
        0 < E.reference x0.1 b ∧
        (∑ i, E.feature x0.1 a i * theta i) ≠
          ∑ i, E.feature x0.1 b i * theta i := by
      by_contra hn
      have hall : ∀ b, 0 < E.reference x0.1 b →
          (∑ i, E.feature x0.1 b i * theta i) =
            ∑ i, E.feature x0.1 a0 i * theta i := by
        intro b hb
        by_contra hne
        apply hn
        exact ⟨a0, b, href0, hb, Ne.symm hne⟩
      have hZeq :
          candidateNormalizer E theta x0.1 =
            Real.exp (E.eta *
              ∑ i, E.feature x0.1 a0 i * theta i) := by
        simp only [candidateNormalizer]
        calc
          (∑ b, E.reference x0.1 b *
              Real.exp (E.eta * ∑ i, E.feature x0.1 b i * theta i)) =
              ∑ b, E.reference x0.1 b *
                Real.exp (E.eta *
                  ∑ i, E.feature x0.1 a0 i * theta i) := by
                    apply Finset.sum_congr rfl
                    intro b _
                    by_cases hb : E.reference x0.1 b = 0
                    · simp [hb]
                    · rw [hall b (lt_of_le_of_ne
                        (E.reference_isPolicy.1 x0.1 b) (Ne.symm hb))]
          _ = _ := by
            rw [← Finset.sum_mul, E.reference_isPolicy.2]
            simp
      rw [hZeq] at hcoveq
      have hCgt : 1 < C := lt_of_le_of_ne hCone (Ne.symm hCne)
      nlinarith [Real.exp_pos
        (E.eta * ∑ i, E.feature x0.1 a0 i * theta i)]
    have htheta : theta ≠ 0 := by
      rintro rfl
      rcases hvar with ⟨a, b, _, _, hab⟩
      simp at hab
    have hstrict_local :
        quadraticForm (loggingBlock E x0.1) theta <
          quadraticForm (targetBlock E theta x0.1) theta :=
      loggingBlock_lt_targetBlock_at_theta E theta x0.1
        (hscore x0.1) hvar
    have hstrict_global : quadraticForm B theta <
        quadraticForm G theta := by
      rw [quadraticForm_sum_blocks rho
        (fun x : I => loggingBlock E x.1) theta,
        quadraticForm_sum_blocks rho
          (fun x : I => targetBlock E theta x.1) theta]
      apply Finset.sum_lt_sum
      · intro x _
        exact mul_le_mul_of_nonneg_left (hlocal_tilt x) (hrho x).le
      · refine ⟨x0, Finset.mem_univ x0, ?_⟩
        exact mul_lt_mul_of_pos_left hstrict_local (hrho x0)
    have hBtpos : 0 < quadraticForm B theta := by
      rw [quadraticForm_eq_toQuadraticMap]
      exact hBpos.toQuadraticForm' theta htheta
    have hpsd := hPSD.dotProduct_mulVec_nonneg theta
    rw [← quadraticForm_eq_dotProduct_mulVec,
      quadraticForm_smul_sub] at hpsd
    nlinarith
  refine ⟨hDone, hDC, hCexp, ?_⟩
  by_cases hCeq : C = 1
  · left
    exact ⟨hCeq, le_antisymm (hCeq ▸ hDC) hDone⟩
  · right
    exact ⟨hstrict hCeq, hDC⟩

end CausalSmith.Stat.ReverseKLTwoCoverage
