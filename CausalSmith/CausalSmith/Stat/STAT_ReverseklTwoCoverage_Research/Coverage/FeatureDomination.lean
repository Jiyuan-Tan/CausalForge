import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.MetricSpace.ProperSpace

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators
open Set

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

def InFeatureSpan (h : 𝒳 → 𝒜 → ℝ) : Prop :=
  ∃ b : Fin d → ℝ, ∀ x a, h x a = ∑ i, E.feature x a i * b i
  -- @realizes h(linear prediction contrast in span(φ))

noncomputable def policySecondMoment (P : BanditLaw E)
    (π : Policy 𝒳 𝒜) (h : 𝒳 → 𝒜 → ℝ) : ℝ :=
  ∑ x, contextMass P x * ∑ a, π x a * (h x a) ^ 2

-- @node: quadraticForm_eq_toQuadraticMap
lemma quadraticForm_eq_toQuadraticMap
    (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadraticForm M v = M.toQuadraticMap' v := by
  simp only [quadraticForm, Matrix.toQuadraticMap',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  congr 1 with i
  congr 1 with j
  ring

-- @node: quadraticForm_smul
lemma quadraticForm_smul
    (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (v : Fin d → ℝ) :
    quadraticForm M (c • v) = c ^ 2 * quadraticForm M v := by
  rw [quadraticForm_eq_toQuadraticMap, quadraticForm_eq_toQuadraticMap]
  simpa [pow_two] using (M.toQuadraticMap').map_smul c v

-- @node: generalizedRayleigh_bddAbove
lemma generalizedRayleigh_bddAbove
    {L T : Matrix (Fin d) (Fin d) ℝ} (hL : Matrix.PosDef L) :
    BddAbove {q : ℝ | ∃ v : Fin d → ℝ, v ≠ 0 ∧
      q = quadraticForm T v / quadraticForm L v} := by
  let K : Set (Fin d → ℝ) := Metric.sphere 0 1
  let f : (Fin d → ℝ) → ℝ :=
    fun v => quadraticForm T v / quadraticForm L v
  have hcontT : Continuous (fun v : Fin d → ℝ => quadraticForm T v) := by
    unfold quadraticForm
    fun_prop
  have hcontL : Continuous (fun v : Fin d → ℝ => quadraticForm L v) := by
    unfold quadraticForm
    fun_prop
  have hden : ∀ v ∈ K, quadraticForm L v ≠ 0 := by
    intro v hv
    have hvnorm : ‖v‖ = 1 := by simpa [K] using hv
    have hvne : v ≠ 0 := by
      intro hv0
      simp [hv0] at hvnorm
    have hp := hL.toQuadraticForm' v hvne
    rw [← quadraticForm_eq_toQuadraticMap] at hp
    exact ne_of_gt hp
  have hfcont : ContinuousOn f K :=
    hcontT.continuousOn.div hcontL.continuousOn hden
  have hKcompact : IsCompact K := by
    simpa [K] using (isCompact_sphere (0 : Fin d → ℝ) 1)
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hfcont
  refine ⟨B, ?_⟩
  intro q hq
  rcases hq with ⟨v, hvne, rfl⟩
  let w : Fin d → ℝ := ‖v‖⁻¹ • v
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hvne
  have hwK : w ∈ K := by
    simp [w, K, norm_smul, hvnorm]
  have hfw : f w ≤ B := hB (mem_image_of_mem f hwK)
  dsimp [f, w] at hfw
  rw [quadraticForm_smul, quadraticForm_smul] at hfw
  have hscale : ‖v‖⁻¹ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (inv_ne_zero hvnorm)
  have heq :
      (‖v‖⁻¹ ^ 2 * quadraticForm T v) /
          (‖v‖⁻¹ ^ 2 * quadraticForm L v) =
        quadraticForm T v / quadraticForm L v := by
    field_simp [hscale]
  rw [heq] at hfw
  exact hfw

-- @node: policySecondMoment_eq_quadraticForm
lemma policySecondMoment_eq_quadraticForm
    (P : BanditLaw E) (π : Policy 𝒳 𝒜) (b : Fin d → ℝ) :
    policySecondMoment E P π
        (fun x a => ∑ i, E.feature x a i * b i) =
      quadraticForm
        (fun i j => ∑ x, contextMass P x * ∑ a,
          π x a * (E.feature x a i * E.feature x a j)) b := by
  simp only [policySecondMoment, quadraticForm, pow_two]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  ring_nf
  calc
    _ = ∑ x, ∑ i, ∑ a, ∑ j, contextMass P x * π x a *
        E.feature x a i * b i * E.feature x a j * b j := by
      congr 1 with x
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ x, ∑ a, ∑ j, contextMass P x * π x a *
        E.feature x a i * b i * E.feature x a j * b j := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ x, ∑ j, ∑ a, contextMass P x * π x a *
        E.feature x a i * b i * E.feature x a j * b j := by
      congr 1 with i
      congr 1 with x
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ x, ∑ a, contextMass P x * π x a *
        E.feature x a i * b i * E.feature x a j * b j := by
      congr 1 with i
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1 with i
      congr 1 with j
      rw [Finset.sum_mul]
      congr 1 with x
      rw [Finset.sum_mul]
      congr 1 with a
      ring

-- @node: lem:feature-coverage-domination
lemma feature_coverage_domination
    (P : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P C D)
    (h : 𝒳 → 𝒜 → ℝ) (hspan : InFeatureSpan E h) :
    policySecondMoment E P (gibbsPolicy E P) h ≤
      featureCoverage E P * policySecondMoment E P E.reference h := by
  rcases hspan with ⟨b, hb⟩
  have heq : h = fun x a => ∑ i, E.feature x a i * b i := by
    funext x a
    exact hb x a
  subst h
  by_cases hbzero : b = 0
  · subst b
    simp [policySecondMoment]
  · have hLpos :
        0 < quadraticForm (loggingCovariance E P) b := by
      rw [quadraticForm_eq_toQuadraticMap]
      exact hshell.nonsingularLoggingGeometry.toQuadraticForm' b hbzero
    have hratio :
        quadraticForm (targetCovariance E P) b /
            quadraticForm (loggingCovariance E P) b ≤
          featureCoverage E P := by
      unfold featureCoverage maxGeneralizedEigenvalue
      apply le_csSup
      · exact generalizedRayleigh_bddAbove
          hshell.nonsingularLoggingGeometry
      · exact ⟨b, hbzero, rfl⟩
    have hquad :
        quadraticForm (targetCovariance E P) b ≤
          featureCoverage E P *
            quadraticForm (loggingCovariance E P) b :=
      (div_le_iff₀ hLpos).mp hratio
    simpa [targetCovariance, loggingCovariance,
      policySecondMoment_eq_quadraticForm] using hquad

noncomputable def matrixFeatureMoment (P : BanditLaw E) (π : Policy 𝒳 𝒜)
    (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ x, contextMass P x * ∑ a, π x a *
    quadraticForm M (E.feature x a)

-- @node: contextMass_nonneg
lemma contextMass_nonneg (P : BanditLaw E) (x : 𝒳) :
    0 ≤ contextMass P x :=
  ENNReal.toReal_nonneg

-- @node: gibbsNormalizer_pos_feature
lemma gibbsNormalizer_pos_feature (P : BanditLaw E) (x : 𝒳) :
    0 < gibbsNormalizer E P x := by
  unfold gibbsNormalizer
  apply Finset.sum_pos'
  · intro a _
    exact mul_nonneg (E.reference_isPolicy.1 x a) (Real.exp_pos _).le
  · by_contra h
    push_neg at h
    have hz : ∀ a, E.reference x a = 0 := by
      intro a
      have hn := h a (Finset.mem_univ a)
      have hp :
          0 ≤ E.reference x a *
            Real.exp (E.eta * linearReward P x a) :=
        mul_nonneg (E.reference_isPolicy.1 x a) (Real.exp_pos _).le
      have heq := le_antisymm hn hp
      exact (mul_eq_zero.mp heq).resolve_right (ne_of_gt (Real.exp_pos _))
    have hm := E.reference_isPolicy.2 x
    simp_rw [hz] at hm
    norm_num at hm

-- @node: gibbsPolicy_nonneg
lemma gibbsPolicy_nonneg (P : BanditLaw E) (x : 𝒳) (a : 𝒜) :
    0 ≤ gibbsPolicy E P x a := by
  unfold gibbsPolicy
  exact div_nonneg
    (mul_nonneg (E.reference_isPolicy.1 x a) (Real.exp_pos _).le)
    (gibbsNormalizer_pos_feature E P x).le

-- @node: quadraticForm_conjTranspose_mul_self
lemma quadraticForm_conjTranspose_mul_self
    (B : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadraticForm (B.conjTranspose * B) v =
      ∑ k, (∑ i, B k i * v i) ^ 2 := by
  simp only [quadraticForm, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_id_of_comm, pow_two]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ x, ∑ y, ∑ k, v x * (B k x * B k y) * v y) =
        ∑ x, ∑ k, ∑ y, v x * (B k x * B k y) * v y := by
      congr 1 with x
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ x, ∑ y, v x * (B k x * B k y) * v y := by
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ x, ∑ y, B k x * v x * (B k y * v y) := by
      congr 1 with k
      congr 1 with x
      congr 1 with y
      ring
    _ = _ := by
      congr 1 with k
      rw [Finset.sum_comm]

-- @node: matrixFeatureMoment_conjTranspose_mul_self
lemma matrixFeatureMoment_conjTranspose_mul_self
    (P : BanditLaw E) (π : Policy 𝒳 𝒜)
    (B : Matrix (Fin d) (Fin d) ℝ) :
    matrixFeatureMoment E P π (B.conjTranspose * B) =
      ∑ k, policySecondMoment E P π
        (fun x a => ∑ i, B k i * E.feature x a i) := by
  unfold matrixFeatureMoment policySecondMoment
  simp_rw [quadraticForm_conjTranspose_mul_self]
  simp_rw [Finset.mul_sum]
  calc
    (∑ x, ∑ a, ∑ k,
        contextMass P x *
          (π x a * (∑ i, B k i * E.feature x a i) ^ 2)) =
      ∑ x, ∑ k, ∑ a,
        contextMass P x *
          (π x a * (∑ i, B k i * E.feature x a i) ^ 2) := by
      congr 1 with x
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ x, ∑ a,
        contextMass P x *
          (π x a * (∑ i, B k i * E.feature x a i) ^ 2) := by
      rw [Finset.sum_comm]
    _ = _ := by rfl

-- @node: lem:quadratic-majorant-transfer
lemma quadratic_majorant_transfer
    (P : BanditLaw E) (C D : ℝ) (hshell : ExactShell E P C D)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : Matrix.PosSemidef M)
    (q : 𝒳 → 𝒜 → ℝ)
    (hq : ∀ x a, (q x a) ^ 2 ≤ quadraticForm M (E.feature x a)) :
    policySecondMoment E P (gibbsPolicy E P) q ≤
        matrixFeatureMoment E P (gibbsPolicy E P) M ∧
      matrixFeatureMoment E P (gibbsPolicy E P) M ≤
        featureCoverage E P * matrixFeatureMoment E P E.reference M := by
  constructor
  · unfold policySecondMoment matrixFeatureMoment
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hq x a)
        (gibbsPolicy_nonneg E P x a)
    · exact contextMass_nonneg E P x
  · obtain ⟨B, rfl⟩ :=
      Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hM
    rw [matrixFeatureMoment_conjTranspose_mul_self,
      matrixFeatureMoment_conjTranspose_mul_self]
    calc
      (∑ k, policySecondMoment E P (gibbsPolicy E P)
          (fun x a => ∑ i, B k i * E.feature x a i)) ≤
        ∑ k, featureCoverage E P *
          policySecondMoment E P E.reference
            (fun x a => ∑ i, B k i * E.feature x a i) := by
        apply Finset.sum_le_sum
        intro k _
        apply feature_coverage_domination E P C D hshell
        refine ⟨fun i => B k i, ?_⟩
        intro x a
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = featureCoverage E P *
          ∑ k, policySecondMoment E P E.reference
            (fun x a => ∑ i, B k i * E.feature x a i) := by
        rw [Finset.mul_sum]

end CausalSmith.Stat.ReverseKLTwoCoverage
