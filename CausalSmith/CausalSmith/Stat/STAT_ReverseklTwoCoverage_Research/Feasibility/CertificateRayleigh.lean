import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Coverage.FeatureDomination
import Mathlib.Analysis.Matrix.Order

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

variable {d : ℕ}

lemma quadraticForm_eq_dotProduct_mulVec
    (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadraticForm M v = star v ⬝ᵥ M.mulVec v := by
  simp only [quadraticForm, dotProduct, Matrix.mulVec, star_trivial]
  simp_rw [Finset.mul_sum]
  congr 1 with i
  congr 1 with j
  ring_nf

lemma quadraticForm_smul_sub
    (B G : Matrix (Fin d) (Fin d) ℝ) (D : ℝ) (v : Fin d → ℝ) :
    quadraticForm (D • B - G) v =
      D * quadraticForm B v - quadraticForm G v := by
  simp only [quadraticForm, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf
  have hreorder :
      (∑ i, ∑ j, v i * D * B i j * v j) =
        ∑ i, ∑ j, D * v i * B i j * v j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hreorder]
  abel

lemma sum_sq_pos_of_ne_zero (v : Fin d → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, (v i) ^ 2 := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos'
    (fun j _ => sq_nonneg (v j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

lemma generalizedRayleigh_attains
    {B G : Matrix (Fin d) (Fin d) ℝ}
    (hd : 0 < d) (hB : Matrix.PosDef B) :
    ∃ w : Fin d → ℝ, w ≠ 0 ∧
      maxGeneralizedEigenvalue B G =
        quadraticForm G w / quadraticForm B w := by
  let K : Set (Fin d → ℝ) := Metric.sphere 0 1
  let f : (Fin d → ℝ) → ℝ :=
    fun v => quadraticForm G v / quadraticForm B v
  have hcontG : Continuous (fun v : Fin d → ℝ => quadraticForm G v) := by
    unfold quadraticForm
    fun_prop
  have hcontB : Continuous (fun v : Fin d → ℝ => quadraticForm B v) := by
    unfold quadraticForm
    fun_prop
  have hden : ∀ v ∈ K, quadraticForm B v ≠ 0 := by
    intro v hv
    have hvnorm : ‖v‖ = 1 := by simpa [K] using hv
    have hvne : v ≠ 0 := by
      intro hv0
      simp [hv0] at hvnorm
    have hp := hB.toQuadraticForm' v hvne
    rw [← quadraticForm_eq_toQuadraticMap] at hp
    exact ne_of_gt hp
  have hfcont : ContinuousOn f K :=
    hcontG.continuousOn.div hcontB.continuousOn hden
  have hKcompact : IsCompact K := by
    simpa [K] using (isCompact_sphere (0 : Fin d → ℝ) 1)
  let i0 : Fin d := ⟨0, hd⟩
  letI : Nonempty (Fin d) := ⟨i0⟩
  let e : Fin d → ℝ := fun i => if i = i0 then 1 else 0
  have henorm : ‖e‖ = 1 := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonempty e).2 (fun i => by
        simp only [e]
        split_ifs <;> norm_num)
    · simpa [e] using (norm_le_pi_norm e i0)
  have hKnonempty : K.Nonempty := ⟨e, by simpa [K] using henorm⟩
  obtain ⟨w, hwK, hwmax⟩ :=
    hKcompact.exists_isMaxOn hKnonempty hfcont
  have hwne : w ≠ 0 := by
    intro hw0
    have : ‖w‖ = 1 := by simpa [K] using hwK
    simp [hw0] at this
  have hupper :
      ∀ q ∈ {q : ℝ | ∃ v : Fin d → ℝ, v ≠ 0 ∧
        q = quadraticForm G v / quadraticForm B v}, q ≤ f w := by
    rintro q ⟨v, hvne, rfl⟩
    let z : Fin d → ℝ := ‖v‖⁻¹ • v
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hvne
    have hzK : z ∈ K := by
      simp [z, K, norm_smul, hvnorm]
    have hzle := hwmax hzK
    dsimp [f, z] at hzle
    rw [quadraticForm_smul, quadraticForm_smul] at hzle
    have hscale : ‖v‖⁻¹ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (inv_ne_zero hvnorm)
    have heq :
        (‖v‖⁻¹ ^ 2 * quadraticForm G v) /
            (‖v‖⁻¹ ^ 2 * quadraticForm B v) =
          quadraticForm G v / quadraticForm B v := by
      field_simp [hscale]
    rwa [heq] at hzle
  have hset_nonempty :
      {q : ℝ | ∃ v : Fin d → ℝ, v ≠ 0 ∧
        q = quadraticForm G v / quadraticForm B v}.Nonempty :=
    ⟨f w, w, hwne, rfl⟩
  refine ⟨w, hwne, le_antisymm ?_ ?_⟩
  · unfold maxGeneralizedEigenvalue
    exact csSup_le hset_nonempty hupper
  · unfold maxGeneralizedEigenvalue
    exact le_csSup (generalizedRayleigh_bddAbove hB)
      ⟨w, hwne, rfl⟩

lemma generalizedRayleigh_certificate_iff
    {B G : Matrix (Fin d) (Fin d) ℝ} {D : ℝ}
    (hd : 0 < d) (hB : Matrix.PosDef B) (hG : G.IsHermitian) :
    maxGeneralizedEigenvalue B G = D ↔
      Matrix.PosSemidef (D • B - G) ∧
      ∃ u : Fin d → ℝ,
        (D • B - G).mulVec u = 0 ∧ ∑ i, (u i) ^ 2 = 1 := by
  constructor
  · intro hmax
    have hset_bdd :
        BddAbove {q : ℝ | ∃ v : Fin d → ℝ, v ≠ 0 ∧
          q = quadraticForm G v / quadraticForm B v} :=
      generalizedRayleigh_bddAbove hB
    have hratio_le :
        ∀ v : Fin d → ℝ, v ≠ 0 →
          quadraticForm G v / quadraticForm B v ≤ D := by
      intro v hv
      calc
        quadraticForm G v / quadraticForm B v ≤
            maxGeneralizedEigenvalue B G := by
          unfold maxGeneralizedEigenvalue
          exact le_csSup hset_bdd ⟨v, hv, rfl⟩
        _ = D := hmax
    have hPSD : Matrix.PosSemidef (D • B - G) := by
      have hDB : (D • B).IsHermitian := by
        ext i j
        have hsymm : B j i = B i j := by
          simpa using hB.isHermitian.apply i j
        simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial,
          smul_eq_mul]
        rw [hsymm]
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (hDB.sub hG)
      intro v
      rw [← quadraticForm_eq_dotProduct_mulVec,
        quadraticForm_smul_sub]
      by_cases hv : v = 0
      · subst v
        simp [quadraticForm]
      · have hBpos : 0 < quadraticForm B v := by
          rw [quadraticForm_eq_toQuadraticMap]
          exact hB.toQuadraticForm' v hv
        have := hratio_le v hv
        exact sub_nonneg.mpr ((div_le_iff₀ hBpos).mp this)
    obtain ⟨w, hwne, hwmax⟩ :=
      generalizedRayleigh_attains hd hB (G := G)
    have hwratio :
        quadraticForm G w / quadraticForm B w = D := by
      rw [← hwmax, hmax]
    have hsumpos := sum_sq_pos_of_ne_zero w hwne
    let s : ℝ := Real.sqrt (∑ i, (w i) ^ 2)
    have hspos : 0 < s := Real.sqrt_pos.2 hsumpos
    let u : Fin d → ℝ := s⁻¹ • w
    have husum : ∑ i, (u i) ^ 2 = 1 := by
      simp only [u, Pi.smul_apply, smul_eq_mul]
      rw [show (∑ i, (s⁻¹ * w i) ^ 2) =
          s⁻¹ ^ 2 * ∑ i, (w i) ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
      have hs_sq : s ^ 2 = ∑ i, (w i) ^ 2 := by
        exact (Real.sq_sqrt hsumpos.le)
      rw [← hs_sq]
      field_simp [ne_of_gt hspos]
    have huratio :
        quadraticForm G u / quadraticForm B u = D := by
      simp only [u, quadraticForm_smul]
      have hscale : s⁻¹ ^ 2 ≠ 0 :=
        pow_ne_zero 2 (inv_ne_zero (ne_of_gt hspos))
      rw [show
          (s⁻¹ ^ 2 * quadraticForm G w) /
              (s⁻¹ ^ 2 * quadraticForm B w) =
            quadraticForm G w / quadraticForm B w by
        field_simp [hscale]]
      exact hwratio
    have hune : u ≠ 0 := by
      intro hu
      simp [hu] at husum
    have hBupos : 0 < quadraticForm B u := by
      rw [quadraticForm_eq_toQuadraticMap]
      exact hB.toQuadraticForm' u hune
    have hquadzero : quadraticForm (D • B - G) u = 0 := by
      rw [quadraticForm_smul_sub]
      have := (div_eq_iff (ne_of_gt hBupos)).mp huratio
      linarith
    have hudot :
        star u ⬝ᵥ (D • B - G).mulVec u = 0 := by
      rwa [← quadraticForm_eq_dotProduct_mulVec]
    refine ⟨hPSD, u, ?_, husum⟩
    exact (hPSD.dotProduct_mulVec_zero_iff u).mp hudot
  · rintro ⟨hPSD, u, huker, hunorm⟩
    have hune : u ≠ 0 := by
      intro hu
      simp [hu] at hunorm
    have hBpos : 0 < quadraticForm B u := by
      rw [quadraticForm_eq_toQuadraticMap]
      exact hB.toQuadraticForm' u hune
    have huquad : quadraticForm (D • B - G) u = 0 := by
      rw [quadraticForm_eq_dotProduct_mulVec, huker]
      simp
    have huratio : quadraticForm G u / quadraticForm B u = D := by
      rw [quadraticForm_smul_sub] at huquad
      apply (div_eq_iff (ne_of_gt hBpos)).2
      linarith
    apply le_antisymm
    · unfold maxGeneralizedEigenvalue
      apply csSup_le
      · exact ⟨quadraticForm G u / quadraticForm B u, u, hune, rfl⟩
      · rintro q ⟨v, hv, rfl⟩
        have hvBpos : 0 < quadraticForm B v := by
          rw [quadraticForm_eq_toQuadraticMap]
          exact hB.toQuadraticForm' v hv
        have hnonneg := hPSD.dotProduct_mulVec_nonneg v
        rw [← quadraticForm_eq_dotProduct_mulVec,
          quadraticForm_smul_sub] at hnonneg
        exact (div_le_iff₀ hvBpos).2 (sub_nonneg.mp hnonneg)
    · rw [← huratio]
      unfold maxGeneralizedEigenvalue
      exact le_csSup (generalizedRayleigh_bddAbove hB)
        ⟨u, hune, rfl⟩

end CausalSmith.Stat.ReverseKLTwoCoverage
