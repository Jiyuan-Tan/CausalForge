import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.CitedInterfaces
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.VCExpectedMaximal
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.EmpiricalProcess.PopulationCoefficient
import Causalean.Stat.Concentration.Matrix.IidSums

/-!
# Expected maximal bound for the bounded winsorized score

The score-specific VC closure, envelope, and variance calculation are local.
The final step calls the in-run `vcExpectedMaximalInequality`; there is no
external empirical-process assumption.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
open Causalean.Stat.Concentration

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Winsorized empirical residual score evaluated at the original population
coefficient. -/
noncomputable def winsorizedCenteredScore (n p : ℕ) (P : A1A2Law)
    (t : Bool) (x : Score) (h B : ℝ) (w : CausalSample n) :
    Fin (p + 1) → ℝ := by
  classical
  let u := signedDistanceData n P w x
  exact fun j => empiricalScore n p t h B u j -
    ∑ k, empiricalGram n p t h u j k * populationCoefficient P p t x h k

/-- Interface supremum of the centered winsorized score process. -/
noncomputable def winsorizedScoreDeviation (n p : ℕ) (P : A1A2Law)
    (h B : ℝ) (w : CausalSample n) : ℝ≥0∞ :=
  ⨆ t : Bool, ⨆ x : Score, ⨆ (_hx : x ∈ P.boundary),
    ENNReal.ofReal ‖winsorizedCenteredScore n p P t x h B w -
      fun j => ∫ w', winsorizedCenteredScore n p P t x h B w' j
        ∂causalSampleLaw P n‖

-- @node: winsorizedCenteredScore_apply_eq_separableAverage
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma winsorizedCenteredScore_apply_eq_separableAverage
    (n p : ℕ) (P : A1A2Law) (t : Bool) (x : Score)
    (hx : x ∈ P.boundary) (h B R : ℝ) (hh : 0 < h)
    (hbeta : ∀ k, |populationCoefficient P p t x h k| ≤ R)
    (w : CausalSample n) (j : Fin (p + 1)) :
    winsorizedCenteredScore n p P t x h B w j =
      h⁻¹ ^ 2 * (n : ℝ)⁻¹ * ∑ a,
        separableWinsorizedScoreFunction P p h B R
          (⟨h, ⟨le_rfl, by linarith⟩⟩, t, ⟨x, hx⟩,
            populationCoefficient P p t x h, j) (w a) := by
  classical
  have hclip (k : Fin (p + 1)) :
      clip R (populationCoefficient P p t x h k) =
        populationCoefficient P p t x h k := by
    have hk := hbeta k
    rw [abs_le] at hk
    simp [clip, min_eq_right hk.2, max_eq_right hk.1]
  simp only [winsorizedCenteredScore, empiricalScore, empiricalGram,
    signedDistanceData, separableWinsorizedScoreFunction]
  simp_rw [hclip]
  simp_rw [mul_sub]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring_nf
  rw [Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hs : signedArm t
      (signedDistance (knownGeometry P) x (causalScore (w i))) <;>
    simp [hs] <;> ring

-- @node: winsorizedCenteredScore_integral_eq
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma winsorizedCenteredScore_integral_eq
    (n p : ℕ) (P : A1A2Law) (t : Bool) (x : Score)
    (hx : x ∈ P.boundary) (h B R : ℝ) (hh : 0 < h) (hn : 1 ≤ n)
    (hbeta : ∀ k, |populationCoefficient P p t x h k| ≤ R)
    (j : Fin (p + 1))
    (hg : Integrable (separableWinsorizedScoreFunction P p h B R
      (⟨h, ⟨le_rfl, by linarith⟩⟩, t, ⟨x, hx⟩,
        populationCoefficient P p t x h, j)) P.law) :
    (∫ w', winsorizedCenteredScore n p P t x h B w' j
        ∂causalSampleLaw P n) =
      h⁻¹ ^ 2 * ∫ z, separableWinsorizedScoreFunction P p h B R
        (⟨h, ⟨le_rfl, by linarith⟩⟩, t, ⟨x, hx⟩,
          populationCoefficient P p t x h, j) z ∂P.law := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let g := separableWinsorizedScoreFunction P p h B R
      (⟨h, ⟨le_rfl, by linarith⟩⟩, t, ⟨x, hx⟩,
        populationCoefficient P p t x h, j)
  have heq (w : CausalSample n) :
      winsorizedCenteredScore n p P t x h B w j =
        h⁻¹ ^ 2 * (n : ℝ)⁻¹ * ∑ a, g (w a) :=
    winsorizedCenteredScore_apply_eq_separableAverage n p P t x hx h B R hh hbeta w j
  rw [integral_congr_ae (ae_of_all _ heq), integral_const_mul]
  simp only [causalSampleLaw]
  rw [Causalean.Stat.Concentration.integral_sum_pi_eq P.law g hg]
  dsimp only [g]
  field_simp

-- @node: winsorizedScoreDeviation_le_empiricalProcessSup
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma winsorizedScoreDeviation_le_empiricalProcessSup
    (n p : ℕ) (P : A1A2Law) (h B R U : ℝ)
    (hh : 0 < h) (hn : 1 ≤ n)
    (hbeta : ∀ t x, x ∈ P.boundary → ∀ k,
      |populationCoefficient P p t x h k| ≤ R)
    (hmeas : ∀ i : SeparableWinsorizedScoreIndex P p h,
      Measurable (separableWinsorizedScoreFunction P p h B R i))
    (henv : ∀ i z, |separableWinsorizedScoreFunction P p h B R i z| ≤ U)
    (w : CausalSample n) :
    winsorizedScoreDeviation n p P h B w ≤ ENNReal.ofReal (h⁻¹ ^ 2) *
      empiricalProcessSup P.law
        (separableWinsorizedScoreFunction P p h B R) w := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  unfold winsorizedScoreDeviation
  apply iSup_le
  intro t
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  let v := winsorizedCenteredScore n p P t x h B w -
      fun j => ∫ w', winsorizedCenteredScore n p P t x h B w' j
        ∂causalSampleLaw P n
  obtain ⟨j0, _hj0, hj0max⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin (p + 1) => |v j|) Finset.univ_nonempty
  have hnorm : ‖v‖ = |v j0| := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg (abs_nonneg (v j0))]
      intro k
      simpa [Real.norm_eq_abs] using hj0max k (Finset.mem_univ k)
    · simpa [Real.norm_eq_abs] using norm_le_pi_norm v j0
  let idx : SeparableWinsorizedScoreIndex P p h :=
    (⟨h, ⟨le_rfl, by linarith⟩⟩, t, ⟨x, hx⟩,
      populationCoefficient P p t x h, j0)
  have hg : Integrable (separableWinsorizedScoreFunction P p h B R idx) P.law :=
    Integrable.of_bound (hmeas idx).aestronglyMeasurable U
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using henv idx z)
  have hsample := winsorizedCenteredScore_apply_eq_separableAverage
    n p P t x hx h B R hh (hbeta t x hx) w j0
  have hmean := winsorizedCenteredScore_integral_eq
    n p P t x hx h B R hh hn (hbeta t x hx) j0 (by simpa only [idx] using hg)
  have hdiff : v j0 = h⁻¹ ^ 2 * centeredEmpiricalAverage P.law w
      (separableWinsorizedScoreFunction P p h B R idx) := by
    simp only [v, Pi.sub_apply]
    rw [hsample, hmean]
    unfold centeredEmpiricalAverage
    dsimp only [idx]
    ring
  rw [show ‖winsorizedCenteredScore n p P t x h B w -
      (fun j => ∫ w', winsorizedCenteredScore n p P t x h B w' j
        ∂causalSampleLaw P n)‖ = ‖v‖ by rfl, hnorm, hdiff, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ h⁻¹ ^ 2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ h⁻¹ ^ 2)]
  exact mul_le_mul_right (le_iSup
    (fun i : SeparableWinsorizedScoreIndex P p h =>
      ENNReal.ofReal |centeredEmpiricalAverage P.law w
        (separableWinsorizedScoreFunction P p h B R i)|) idx) _

-- @node: outerLIntegral_const_mul_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma outerLIntegral_const_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (f : Ω → ℝ≥0∞) :
    MeasureTheory.outerLIntegral μ (fun x => c * f x) ≤
      c * MeasureTheory.outerLIntegral μ f := by
  rw [MeasureTheory.outerLIntegral]
  rw [MeasureTheory.outerLIntegral, ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro g
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro hg
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro hfg
  refine iInf_le_of_le (fun x => c * g x) ?_
  refine iInf_le_of_le (hg.const_mul c) ?_
  refine iInf_le_of_le (fun x => mul_le_mul_right (hfg x) c) ?_
  rw [lintegral_const_mul _ hg]

-- @node: outerLIntegral_mono
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma outerLIntegral_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f g : Ω → ℝ≥0∞} (hfg : f ≤ g) :
    MeasureTheory.outerLIntegral μ f ≤ MeasureTheory.outerLIntegral μ g := by
  rw [MeasureTheory.outerLIntegral, MeasureTheory.outerLIntegral]
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  apply le_iInf
  intro hgG
  exact iInf_le_of_le G (iInf_le_of_le hG
    (iInf_le_of_le (fun x => (hfg x).trans (hgG x)) le_rfl))

-- @node: lem:cty-winsorized-score-maximal-bound
/-- The bounded-envelope adaptation of the CTY expected maximal argument.
The continuum-index empirical-process engine is proved in this repository by
`vcExpectedMaximalInequality`; the constant is uniform in the moment offset
and depends only on `p` and `L`. -/
lemma cty_winsorized_score_maximal_bound (p : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ,
      ∀ P : A1A2Law, A1A2Class p ν L P →
      ∀ (n : ℕ) (h B : ℝ), 1 ≤ n → 0 < h → h ≤ L⁻¹ → 1 ≤ B →
        MeasureTheory.outerLIntegral (causalSampleLaw P n)
            (winsorizedScoreDeviation n p P h B) ≤
          ENNReal.ofReal (C *
            (Real.sqrt (Real.log (B / h) / ((n : ℝ) * h ^ 2)) +
              B * Real.log (B / h) / ((n : ℝ) * h ^ 2))) := by
  let R : ℝ := 1 + |L * (p + 1 : ℝ) * (16 * L * (2 + L))|
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨A, v, C₀, hC₀, hent⟩ :=
    winsorizedScore_hasVCUniformEntropy_all_nu p L R hR
  let k : ℝ := 1 + Real.log A
  let C : ℝ := 1 + |varianceAdaptiveVCConstant * C₀ *
    (Real.sqrt (v * k) + v * k)|
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro ν P hP n h B hn hh hhL hB
    letI : IsProbabilityMeasure P.law := P.law_isProbability
    have hL : 0 < L := lt_of_lt_of_le (by norm_num) hP.2.1
    have hhB : h < B := by
      have hinv : L⁻¹ < 1 := inv_lt_one_of_one_lt₀
        (lt_of_lt_of_le (by norm_num) hP.2.1)
      exact (hhL.trans_lt hinv).trans_le hB
    have hentropy := hent ν P hP h B hh hhB hB
    rcases hentropy with ⟨hσ, hσU, hA, hv, hmeas, henv, hL2, hcover⟩
    have hsep := winsorizedScore_hasCountableEmpiricalSupReduction_at
      p ν L R hR P hP h B hh hB
    have hproc := vcExpectedMaximalInequality_explicit P.law
      (separableWinsorizedScoreFunction P p h B R) (C₀ * B) (C₀ * h) A v
      hsep ⟨hσ, hσU, hA, hv, hmeas, henv, hL2, hcover⟩ n hn
    have hbeta : ∀ t x, x ∈ P.boundary → ∀ j,
        |populationCoefficient P p t x h j| ≤ R := by
      intro t x hx j
      exact populationCoefficient_uniform_bound_explicit p ν L P hP t x h hx hh hhL j
    have hpoint : winsorizedScoreDeviation n p P h B ≤
        fun w => ENNReal.ofReal (h⁻¹ ^ 2) *
          empiricalProcessSup P.law
            (separableWinsorizedScoreFunction P p h B R) w := by
      intro w
      exact winsorizedScoreDeviation_le_empiricalProcessSup n p P h B R
        (C₀ * B) hh hn hbeta hmeas henv w
    have hc0 : ENNReal.ofReal (h⁻¹ ^ 2) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    have hct : ENNReal.ofReal (h⁻¹ ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
    have houter : MeasureTheory.outerLIntegral (causalSampleLaw P n)
          (winsorizedScoreDeviation n p P h B) ≤
        ENNReal.ofReal (h⁻¹ ^ 2) *
          ENNReal.ofReal (varianceAdaptiveVCConstant *
            vcExpectedMaximalRate (C₀ * B) (C₀ * h) A v n) := by
      calc
        _ ≤ MeasureTheory.outerLIntegral (causalSampleLaw P n)
            (fun w => ENNReal.ofReal (h⁻¹ ^ 2) *
              empiricalProcessSup P.law
                (separableWinsorizedScoreFunction P p h B R) w) :=
          outerLIntegral_mono _ hpoint
        _ ≤ ENNReal.ofReal (h⁻¹ ^ 2) *
            MeasureTheory.outerLIntegral (causalSampleLaw P n)
              (empiricalProcessSup P.law
                (separableWinsorizedScoreFunction P p h B R)) :=
          outerLIntegral_const_mul_le _ _ hc0 hct _
        _ ≤ _ := mul_le_mul_right (by simpa [causalSampleLaw] using hproc) _
    apply houter.trans
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ h⁻¹ ^ 2)]
    apply ENNReal.ofReal_le_ofReal
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
    have hratio4 : 4 ≤ B / h := by
      apply (le_div_iff₀ hh).2
      have hLh : L * h ≤ 1 := by
        calc
          L * h ≤ L * L⁻¹ := mul_le_mul_of_nonneg_left hhL hL.le
          _ = 1 := mul_inv_cancel₀ hL.ne'
      calc
        4 * h ≤ L * h := mul_le_mul_of_nonneg_right hP.2.1 hh.le
        _ ≤ 1 := hLh
        _ ≤ B := hB
    have hratio : 0 < B / h := div_pos (lt_of_lt_of_le zero_lt_one hB) hh
    have hlog1 : 1 ≤ Real.log (B / h) := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos 1) hratio
        ((Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4)).trans hratio4)
    have hA1 : 1 ≤ A := (Real.one_le_exp (by norm_num)).trans hA
    have hApos : 0 < A := zero_lt_one.trans_le hA1
    have hbase : max (Real.exp 1) (A * (C₀ * B) / (C₀ * h)) = A * (B / h) := by
      have hcancel : A * (C₀ * B) / (C₀ * h) = A * (B / h) := by
        field_simp [hC₀.ne']
      rw [hcancel, max_eq_right]
      exact hA.trans (le_mul_of_one_le_right hApos.le (le_trans (by norm_num) hratio4))
    have hlogA : 1 ≤ Real.log A := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hApos hA
    have hlogBound : vcMaximalLog A (C₀ * B) (C₀ * h) ≤
        k * Real.log (B / h) := by
      rw [vcMaximalLog, hbase, Real.log_mul hApos.ne' hratio.ne']
      dsimp [k]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlogA) (sub_nonneg.mpr hlog1)]
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hv0 : 0 ≤ v := le_trans (by norm_num) hv
    have hsqrt : Real.sqrt (v * vcMaximalLog A (C₀ * B) (C₀ * h) / n) ≤
        Real.sqrt (v * k) * Real.sqrt (Real.log (B / h) / n) := by
      rw [← Real.sqrt_mul (mul_nonneg hv0 hk)]
      apply Real.sqrt_le_sqrt
      calc
        v * vcMaximalLog A (C₀ * B) (C₀ * h) / (n : ℝ) ≤
            v * (k * Real.log (B / h)) / n := by gcongr
        _ = (v * k) * (Real.log (B / h) / n) := by ring
    have hrate : h⁻¹ ^ 2 * (varianceAdaptiveVCConstant *
          vcExpectedMaximalRate (C₀ * B) (C₀ * h) A v n) ≤
        C * (Real.sqrt (Real.log (B / h) / ((n : ℝ) * h ^ 2)) +
          B * Real.log (B / h) / ((n : ℝ) * h ^ 2)) := by
      unfold vcExpectedMaximalRate
      have hsqrtScale : h⁻¹ ^ 2 * (C₀ * h *
          Real.sqrt (v * vcMaximalLog A (C₀ * B) (C₀ * h) / n)) ≤
          C₀ * Real.sqrt (v * k) *
            Real.sqrt (Real.log (B / h) / ((n : ℝ) * h ^ 2)) := by
        have hsqrtH : Real.sqrt (Real.log (B / h) / ((n : ℝ) * h ^ 2)) =
            h⁻¹ * Real.sqrt (Real.log (B / h) / n) := by
          rw [show Real.log (B / h) / ((n : ℝ) * h ^ 2) =
              h⁻¹ ^ 2 * (Real.log (B / h) / n) by field_simp,
            Real.sqrt_mul (by positivity : 0 ≤ h⁻¹ ^ 2),
            Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hh)]
        calc
          _ = (h⁻¹ ^ 2 * (C₀ * h)) *
              Real.sqrt (v * vcMaximalLog A (C₀ * B) (C₀ * h) / n) := by ring
          _ ≤ (h⁻¹ ^ 2 * (C₀ * h)) *
              (Real.sqrt (v * k) * Real.sqrt (Real.log (B / h) / n)) :=
            mul_le_mul_of_nonneg_left hsqrt
              (mul_nonneg (by positivity) (mul_nonneg hC₀.le hh.le))
          _ = _ := by rw [hsqrtH]; field_simp
      have hsecond : h⁻¹ ^ 2 *
          (v * (C₀ * B) * vcMaximalLog A (C₀ * B) (C₀ * h) / n) ≤
          C₀ * v * k * (B * Real.log (B / h) / ((n : ℝ) * h ^ 2)) := by
        calc
          _ ≤ h⁻¹ ^ 2 * (v * (C₀ * B) * (k * Real.log (B / h)) / n) := by
            gcongr
          _ = _ := by field_simp
      dsimp [C]
      let X := Real.sqrt (Real.log (B / h) / ((n : ℝ) * h ^ 2))
      let Y := B * Real.log (B / h) / ((n : ℝ) * h ^ 2)
      have hX : 0 ≤ X :=
        Real.sqrt_nonneg _
      have hY : 0 ≤ Y := by
        exact div_nonneg (mul_nonneg (le_trans (by norm_num) hB)
          (by linarith : 0 ≤ Real.log (B / h)))
          (mul_nonneg hnR.le (sq_nonneg h))
      have hDnonneg : 0 ≤ varianceAdaptiveVCConstant * C₀ *
          (Real.sqrt (v * k) + v * k) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num [varianceAdaptiveVCConstant]) hC₀.le)
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hv0 hk))
      have hvc : 0 ≤ varianceAdaptiveVCConstant := by
        norm_num [varianceAdaptiveVCConstant]
      have hs1 := mul_le_mul_of_nonneg_left hsqrtScale hvc
      have hs2 := mul_le_mul_of_nonneg_left hsecond hvc
      let D := varianceAdaptiveVCConstant * C₀ *
        (Real.sqrt (v * k) + v * k)
      have hcross1 : 0 ≤ Real.sqrt (v * k) *
          Y := mul_nonneg (Real.sqrt_nonneg _) hY
      have hcross2 : 0 ≤ v * k *
          X := mul_nonneg (mul_nonneg hv0 hk) hX
      calc
        _ = varianceAdaptiveVCConstant *
              (h⁻¹ ^ 2 * (C₀ * h *
                Real.sqrt (v * vcMaximalLog A (C₀ * B) (C₀ * h) / n))) +
            varianceAdaptiveVCConstant *
              (h⁻¹ ^ 2 * (v * (C₀ * B) *
                vcMaximalLog A (C₀ * B) (C₀ * h) / n)) := by ring
        _ ≤ varianceAdaptiveVCConstant *
              (C₀ * Real.sqrt (v * k) * X) +
            varianceAdaptiveVCConstant * (C₀ * v * k * Y) := by
          simpa only [X, Y] using add_le_add hs1 hs2
        _ ≤ D * (X + Y) := by
          dsimp [D]
          nlinarith [mul_nonneg (mul_nonneg hvc hC₀.le) hcross1,
            mul_nonneg (mul_nonneg hvc hC₀.le) hcross2]
        _ ≤ (1 + |D|) * (X + Y) :=
          mul_le_mul_of_nonneg_right ((le_abs_self D).trans (by linarith))
            (add_nonneg hX hY)
        _ = _ := by simp only [D, X, Y]
    exact hrate

end CausalSmith.Stat.BddUniformLogPenalty
