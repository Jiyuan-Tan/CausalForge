import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.Concentration
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Coverage.FeatureDomination
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory ProbabilityTheory
open CausalSmith.Substrate.FiniteExponentialTiltCalculus
open scoped BigOperators

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

lemma linear_evaluation_sq_le_covariance_mul_inverse
    (L : Matrix (Fin d) (Fin d) ℝ) (hL : Matrix.PosDef L)
    (b v : Fin d → ℝ) :
    (∑ i, v i * b i) ^ 2 ≤
      quadraticForm L b * quadraticForm L⁻¹ v := by
  let B : LinearMap.BilinForm ℝ (Fin d → ℝ) :=
    (Matrix.toLinearMap₂' ℝ) L
  have hBnonneg : ∀ x, 0 ≤ (B x) x := by
    intro x
    simpa [B, Matrix.toLinearMap₂'_apply', dotProduct, quadraticForm,
      mul_comm] using hL.posSemidef.dotProduct_mulVec_nonneg x
  have hsymm : ∀ i j, L i j = L j i := by
    have hHerm := hL.1
    simp only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] at hHerm
    intro i j
    exact congrFun₂ hHerm j i
  have hBsymm : LinearMap.IsSymm B := by
    rw [LinearMap.isSymm_def]
    intro x y
    simp only [RingHom.id_apply, B, Matrix.toLinearMap₂'_apply',
      dotProduct, Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
    ring
  let x := L⁻¹.mulVec v
  have hcs :=
    LinearMap.BilinForm.apply_sq_le_of_symm B hBnonneg hBsymm x b
  have hdet : IsUnit L.det :=
    (Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit
  have hLinv : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hdet
  have hLx : L.mulVec x = v := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, hLinv, Matrix.one_mulVec]
  have hx :
      (B x) b = ∑ i, v i * b i := by
    have hswap := LinearMap.isSymm_def.mp hBsymm x b
    simp only [RingHom.id_apply] at hswap
    rw [hswap]
    simp only [B, Matrix.toLinearMap₂'_apply', dotProduct]
    rw [hLx]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hxx : (B x) x = quadraticForm L⁻¹ v := by
    simp only [B, Matrix.toLinearMap₂'_apply', dotProduct]
    rw [hLx]
    dsimp [x]
    simp only [Matrix.mulVec, dotProduct, quadraticForm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hbb : (B b) b = quadraticForm L b := by
    simp only [B, Matrix.toLinearMap₂'_apply', dotProduct]
    simp only [Matrix.mulVec, dotProduct, quadraticForm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hx, hxx, hbb] at hcs
  nlinarith

lemma quadraticForm_smul_matrix
    (c : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quadraticForm (c • M) v = c * quadraticForm M v := by
  unfold quadraticForm
  change (∑ i, ∑ j, v i * (c * M i j) * v j) =
    c * ∑ i, ∑ j, v i * M i j * v j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma matrixFeatureMoment_smul
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (π : Policy 𝒳 𝒜) (c : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    matrixFeatureMoment E P π (c • M) =
      c * matrixFeatureMoment E P π M := by
  unfold matrixFeatureMoment
  simp_rw [quadraticForm_smul_matrix]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma matrixFeatureMoment_reference_inverse
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (hL : Matrix.PosDef (loggingCovariance E P)) :
    matrixFeatureMoment E P E.reference (loggingCovariance E P)⁻¹ = d := by
  let L := loggingCovariance E P
  have hdet : IsUnit L.det :=
    (Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit
  have hinv : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hdet
  have htrace :
      matrixFeatureMoment E P E.reference L⁻¹ =
        ∑ i, (L⁻¹ * L) i i := by
    unfold matrixFeatureMoment
    simp only [quadraticForm, L, loggingCovariance]
    simp only [Finset.mul_sum, Finset.sum_mul]
    calc
      (∑ x, ∑ a, ∑ i, ∑ j,
          contextMass P x *
            (E.reference x a *
              (E.feature x a i * (loggingCovariance E P)⁻¹ i j *
                E.feature x a j))) =
          ∑ x, ∑ i, ∑ a, ∑ j,
            contextMass P x *
              (E.reference x a *
                (E.feature x a i * (loggingCovariance E P)⁻¹ i j *
                  E.feature x a j)) := by
            congr 1 with x
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ x, ∑ a, ∑ j,
            contextMass P x *
              (E.reference x a *
                (E.feature x a i * (loggingCovariance E P)⁻¹ i j *
                  E.feature x a j)) := by
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ x, ∑ j, ∑ a,
            contextMass P x *
              (E.reference x a *
                (E.feature x a i * (loggingCovariance E P)⁻¹ i j *
                  E.feature x a j)) := by
            congr 1 with i
            congr 1 with x
            rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ∑ x, ∑ a,
            contextMass P x *
              (E.reference x a *
                (E.feature x a i * (loggingCovariance E P)⁻¹ i j *
                  E.feature x a j)) := by
            congr 1 with i
            rw [Finset.sum_comm]
      _ =
          ∑ i, ∑ j, ∑ x, ∑ a,
            (loggingCovariance E P)⁻¹ i j *
              (contextMass P x * E.reference x a *
                (E.feature x a j * E.feature x a i)) := by
            congr 1 with i
            congr 1 with j
            congr 1 with x
            congr 1 with a
            ring
      _ = ∑ i, ∑ j,
          (loggingCovariance E P)⁻¹ i j *
            (∑ x, contextMass P x * ∑ a,
              E.reference x a *
                (E.feature x a j * E.feature x a i)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            symm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = ∑ i, ∑ j,
          (loggingCovariance E P)⁻¹ i j * loggingCovariance E P j i := by
            rfl
      _ = ∑ i, ((loggingCovariance E P)⁻¹ *
          loggingCovariance E P) i i := by rfl
  rw [htrace, hinv]
  simp

lemma lowerEnvelope_mem_Icc_of_confidence_member
    (E : CommonExperiment d 𝒳 𝒜) (c0 : ℝ)
    (sample : LoggedSample n 𝒳 𝒜)
    (f0 : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hf0 : f0 ∈ confidencePolytope E c0 sample) :
    ∀ x a, lowerEnvelope E c0 sample x a ∈ Set.Icc (0 : ℝ) 1 := by
  intro x a
  let S : Set ℝ :=
    {r | ∃ f ∈ confidencePolytope E c0 sample, r = f x a}
  have hSne : S.Nonempty := by
    refine ⟨f0 x a, ?_⟩
    exact ⟨f0, hf0, rfl⟩
  have hzero : ∀ r ∈ S, (0 : ℝ) ≤ r := by
    rintro r ⟨f, hf, rfl⟩
    exact (hf.1.1 x a).1
  have hSbdd : BddBelow S := ⟨0, hzero⟩
  constructor
  · change 0 ≤ sInf S
    exact le_csInf hSne hzero
  · change sInf S ≤ 1
    have hf0S : f0 x a ∈ S := ⟨f0, hf0, rfl⟩
    exact (csInf_le hSbdd hf0S).trans (hf0.1.1 x a).2

lemma lowerEnvelope_sq_le_inverse_majorant
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D c0 R : ℝ)
    (sample : LoggedSample n 𝒳 𝒜)
    (hshell : ExactShell E P C D)
    (hrmem : linearReward P ∈ confidencePolytope E c0 sample)
    (hR : 0 ≤ R)
    (hlocal :
      ∀ f ∈ confidencePolytope E c0 sample,
        policySecondMoment E P E.reference
            (fun x a => f x a - linearReward P x a) ≤ R) :
    ∀ x a,
      (lowerEnvelope E c0 sample x a - linearReward P x a) ^ 2 ≤
        R * quadraticForm (loggingCovariance E P)⁻¹ (E.feature x a) := by
  intro x a
  let r := linearReward P
  let L := loggingCovariance E P
  let S : Set ℝ :=
    {z | ∃ f ∈ confidencePolytope E c0 sample, z = f x a}
  have hSne : S.Nonempty := by
    refine ⟨r x a, ?_⟩
    exact ⟨r, hrmem, rfl⟩
  have hzero : ∀ z ∈ S, (0 : ℝ) ≤ z := by
    rintro z ⟨f, hf, rfl⟩
    exact (hf.1.1 x a).1
  have hSbdd : BddBelow S := ⟨0, hzero⟩
  have hL : Matrix.PosDef L := hshell.nonsingularLoggingGeometry
  have hlev :
      0 ≤ quadraticForm L⁻¹ (E.feature x a) := by
    by_cases hv : E.feature x a = 0
    · simp [hv, quadraticForm]
    · rw [quadraticForm_eq_toQuadraticMap]
      exact (hL.inv.toQuadraticForm' _ hv).le
  have hall :
      ∀ f ∈ confidencePolytope E c0 sample,
        (f x a - r x a) ^ 2 ≤
          R * quadraticForm L⁻¹ (E.feature x a) := by
    intro f hf
    rcases hf.1.2 with ⟨bf, hbf⟩
    let b : Fin d → ℝ := fun i => bf i - P.theta i
    have hrepr : ∀ y c,
        f y c - r y c = ∑ i, E.feature y c i * b i := by
      intro y c
      dsimp [r, b]
      rw [hbf y c]
      change
        (∑ i, E.feature y c i * bf i) -
            (∑ i, E.feature y c i * P.theta i) =
          ∑ i, E.feature y c i * (bf i - P.theta i)
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hquad : quadraticForm L b ≤ R := by
      have hm := hlocal f hf
      rw [show
        (fun y c => f y c - r y c) =
          fun y c => ∑ i, E.feature y c i * b i by
            funext y c
            exact hrepr y c] at hm
      simpa [L, policySecondMoment_eq_quadraticForm] using hm
    have heval :=
      linear_evaluation_sq_le_covariance_mul_inverse L hL b (E.feature x a)
    rw [← hrepr x a] at heval
    exact heval.trans
      (mul_le_mul_of_nonneg_right hquad hlev)
  have hm : 0 ≤ R * quadraticForm L⁻¹ (E.feature x a) :=
    mul_nonneg hR hlev
  have hlower :
      r x a - Real.sqrt (R * quadraticForm L⁻¹ (E.feature x a)) ≤
        sInf S := by
    apply le_csInf hSne
    rintro z ⟨f, hf, rfl⟩
    have hfbound := hall f hf
    nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg
      (R * quadraticForm L⁻¹ (E.feature x a))]
  have hupper : sInf S ≤ r x a :=
    csInf_le hSbdd (show r x a ∈ S from ⟨r, hrmem, rfl⟩)
  change (sInf S - r x a) ^ 2 ≤
    R * quadraticForm L⁻¹ (E.feature x a)
  nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg
    (R * quadraticForm L⁻¹ (E.feature x a))]

lemma bounded_gibbs_welfare_regret_le_two
    (E : CommonExperiment d 𝒳 𝒜)
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1) :
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤ 2 := by
  let A :=
    ∑ x, rho x *
      ∑ a, gibbsFromPotential E r x a * (g x a - r x a) ^ 2
  let B :=
    ∑ x, rho x *
      ∑ a, gibbsFromPotential E g x a * (g x a - r x a) ^ 2
  have hmoment (s : 𝒳 → 𝒜 → ℝ) :
      ∑ x, rho x *
          ∑ a, gibbsFromPotential E s x a * (g x a - r x a) ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ x, rho x * 1 := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hrho_nonneg x)
        calc
          _ ≤ ∑ a, gibbsFromPotential E s x a * 1 := by
            apply Finset.sum_le_sum
            intro a _
            apply mul_le_mul_of_nonneg_left
            · nlinarith [hr x a |>.1, hr x a |>.2,
                hg x a |>.1, hg x a |>.2]
            · exact (gibbsFromPotential_isPolicy E s).1 x a
          _ = 1 := by simp [(gibbsFromPotential_isPolicy E s).2 x]
      _ = 1 := by simp [hrho_mass]
  have hA : 0 ≤ A := by
    dsimp [A]
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (hrho_nonneg x)
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg ((gibbsFromPotential_isPolicy E r).1 x a)
        (sq_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (hrho_nonneg x)
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg ((gibbsFromPotential_isPolicy E g).1 x a)
        (sq_nonneg _)
  have hconv :=
    two_endpoint_gibbs_conversion E rho r g hrho_nonneg hrho_mass hr hg
  calc
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤
        min (E.eta * (A + B)) (Real.sqrt A + Real.sqrt B) := by
          simpa only [A, B] using hconv
    _ ≤ Real.sqrt A + Real.sqrt B := min_le_right _ _
    _ ≤ 1 + 1 := add_le_add
      (Real.sqrt_le_one.mpr (by simpa [A] using hmoment r))
      (Real.sqrt_le_one.mpr (by simpa [B] using hmoment g))
    _ = 2 := by norm_num

lemma weighted_policy_linear_le_sqrt_secondMoment
    (rho : 𝒳 → ℝ) (π : Policy 𝒳 𝒜) (h : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hπ_nonneg : ∀ x a, 0 ≤ π x a) (hπ_mass : ∀ x, ∑ a, π x a = 1) :
    ∑ x, rho x * ∑ a, π x a * (-h x a) ≤
      Real.sqrt (∑ x, rho x * ∑ a, π x a * (h x a) ^ 2) := by
  let q : 𝒳 → ℝ := fun x => ∑ a, π x a * (h x a) ^ 2
  have hq : ∀ x, 0 ≤ q x := by
    intro x
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (hπ_nonneg x a) (sq_nonneg _)
  have hlocal : ∀ x, ∑ a, π x a * (-h x a) ≤ Real.sqrt (q x) := by
    intro x
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun a => Real.sqrt (π x a))
      (fun a => Real.sqrt (π x a) * (-h x a))
    have hsqrt : ∀ a, (Real.sqrt (π x a)) ^ 2 = π x a :=
      fun a => Real.sq_sqrt (hπ_nonneg x a)
    simp_rw [← mul_assoc, ← pow_two, hsqrt, mul_pow, hsqrt] at hcs
    simpa [q, hπ_mass x, Real.sqrt_one, one_mul] using hcs
  calc
    ∑ x, rho x * ∑ a, π x a * (-h x a) ≤
        ∑ x, rho x * Real.sqrt (q x) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hlocal x) (hrho_nonneg x)
    _ ≤ Real.sqrt (∑ x, rho x * q x) :=
      weighted_context_sqrt_le_sqrt rho q hrho_nonneg hrho_mass hq
    _ = _ := by rfl

lemma bounded_gibbs_welfare_regret_le_eta_half
    (E : CommonExperiment d 𝒳 𝒜)
    (rho : 𝒳 → ℝ) (r g : 𝒳 → 𝒜 → ℝ)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1) :
    welfareFromPotential E rho r (gibbsFromPotential E r) -
        welfareFromPotential E rho r (gibbsFromPotential E g) ≤
      E.eta / 2 := by
  rw [gibbs_regret_eq_weighted_endpoint_remainder E]
  have hrem : ∀ x,
      mean (gibbsFromPotential E r x)
            (fun a => E.eta * (g x a - r x a)) 1 -
        (Real.log
            (partition (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 1) -
          Real.log
            (partition (gibbsFromPotential E r x)
              (fun a => E.eta * (g x a - r x a)) 0)) ≤
        E.eta ^ 2 / 2 := by
    intro x
    let w := gibbsFromPotential E r x
    let h : 𝒜 → ℝ := fun a => E.eta * (g x a - r x a)
    have hw : ∀ a, 0 ≤ w a := (gibbsFromPotential_isPolicy E r).1 x
    have hmass : ∑ a, w a = 1 := (gibbsFromPotential_isPolicy E r).2 x
    have hh : ∀ a, |h a| ≤ E.eta := by
      intro a
      dsimp [h]
      rw [abs_mul, abs_of_pos E.eta_pos]
      have : |g x a - r x a| ≤ 1 := by
        rw [abs_le]
        constructor <;>
          nlinarith [hr x a |>.1, hr x a |>.2, hg x a |>.1, hg x a |>.2]
      exact mul_le_of_le_one_right E.eta_pos.le this
    rw [endpointRemainder_eq_intervalIntegral w h hw hmass]
    have hleft : IntervalIntegrable (fun t : ℝ => t * variance w h t)
        volume 0 1 :=
      (continuous_id.mul (continuous_variance w h hw hmass)).intervalIntegrable 0 1
    have hright : IntervalIntegrable (fun t : ℝ => t * E.eta ^ 2)
        volume 0 1 := (continuous_id.mul continuous_const).intervalIntegrable 0 1
    calc
      (∫ t in (0 : ℝ)..1, t * variance w h t) ≤
          ∫ t in (0 : ℝ)..1, t * E.eta ^ 2 := by
        exact intervalIntegral.integral_mono_on zero_le_one hleft hright
          fun t ht => by
            apply mul_le_mul_of_nonneg_left _ ht.1
            calc
              variance w h t ≤ secondMoment w h t := by
                change secondMoment w h t - mean w h t ^ 2 ≤
                  secondMoment w h t
                nlinarith [sq_nonneg (mean w h t)]
              _ = ∑ a, tilt w h t a * h a ^ 2 :=
                secondMoment_eq_sum_tilt w h t
              _ ≤ ∑ a, tilt w h t a * E.eta ^ 2 := by
                apply Finset.sum_le_sum
                intro a _
                have hs : h a ^ 2 ≤ E.eta ^ 2 := by
                  have habs :
                      |h a| ^ 2 ≤ E.eta ^ 2 :=
                    (sq_le_sq₀ (abs_nonneg (h a)) E.eta_pos.le).2 (hh a)
                  simpa [sq_abs] using habs
                exact mul_le_mul_of_nonneg_left hs
                  (tilt_nonneg w h t hw hmass a)
              _ = E.eta ^ 2 := by
                rw [← Finset.sum_mul, sum_tilt w h t hw hmass]
                ring
      _ = E.eta ^ 2 / 2 := by
        rw [intervalIntegral.integral_mul_const, integral_id]
        ring
  have hsum :
      ∑ x, rho x *
          (mean (gibbsFromPotential E r x)
                (fun a => E.eta * (g x a - r x a)) 1 -
            (Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 1) -
              Real.log
                (partition (gibbsFromPotential E r x)
                  (fun a => E.eta * (g x a - r x a)) 0))) ≤
        E.eta ^ 2 / 2 := by
    calc
      _ ≤ ∑ x, rho x * (E.eta ^ 2 / 2) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hrem x) (hrho_nonneg x)
      _ = E.eta ^ 2 / 2 := by rw [← Finset.sum_mul, hrho_mass]; ring
  calc
    E.eta⁻¹ * _ ≤ E.eta⁻¹ * (E.eta ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr E.eta_pos.le)
    _ = E.eta / 2 := by field_simp [ne_of_gt E.eta_pos]

end CausalSmith.Stat.ReverseKLTwoCoverage
