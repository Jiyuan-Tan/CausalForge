import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.Transforms
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.UniformDiskSeries
import Causalean.Mathlib.IIDCenteredSum

/-!
# Uniform L2 control of empirical transforms
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- The uniform error of a random transform against a fixed target on a disk: the supremum,
over all complex points of modulus at most the given radius, of the distance between the value
of the random transform at that point and the value of the target there. -/
def transformSupError (Fhat : Ω → ℂ → ℂ) (F : ℂ → ℂ)
    (R : ℝ) (w : Ω) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ ≤ R ∧ x = ‖Fhat w z - F z‖}

/-- The transform error is exactly the disk supremum of the centered random
analytic function. -/
lemma transformSupError_eq_diskSupNorm
    (Fhat : Ω → ℂ → ℂ) (F : ℂ → ℂ) (R : ℝ) :
    transformSupError Fhat F R =
      diskSupNorm (fun ω z ↦ Fhat ω z - F z) R := by
  rfl

/-- The two deterministic folds, indexed by `Fin 2`. -/
def inferenceFold (n : ℕ) (a : Fin 2) : Finset (Fin n) :=
  if a = 0 then fold0 n else fold1 n

/-- A Luxemburg-square envelope controls every even moment with the
factorial constant used in the empirical-transform coefficient series. -/
lemma luxemburg_even_moment_integral_le
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (W : Ω → ℝ) (hW : Measurable W) {σ : ℝ} (hσ : 0 < σ)
    (hexp : Integrable (fun ω ↦ Real.exp ((W ω) ^ 2 / σ ^ 2)) μ)
    (hexp_le : ∫ ω, Real.exp ((W ω) ^ 2 / σ ^ 2) ∂μ ≤ 2)
    (k : ℕ) :
    ∫ ω, |W ω| ^ (2 * k) ∂μ ≤ 2 * σ ^ (2 * k) * k.factorial := by
  let c : ℝ := σ ^ (2 * k) * k.factorial
  have hc : 0 ≤ c := mul_nonneg (pow_nonneg hσ.le _) (Nat.cast_nonneg _)
  have hpoint : ∀ ω, |W ω| ^ (2 * k) ≤
      c * Real.exp ((W ω) ^ 2 / σ ^ 2) := by
    intro ω
    have hx : 0 ≤ (W ω) ^ 2 / σ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hseries := Real.pow_div_factorial_le_exp ((W ω) ^ 2 / σ ^ 2) hx k
    have hσne : σ ≠ 0 := hσ.ne'
    have hkfac : 0 < (k.factorial : ℝ) := by positivity
    have hseries' : ((W ω) ^ 2 / σ ^ 2) ^ k ≤
        k.factorial * Real.exp ((W ω) ^ 2 / σ ^ 2) :=
      by simpa [mul_comm] using (div_le_iff₀ hkfac).mp hseries
    calc
      |W ω| ^ (2 * k) = σ ^ (2 * k) * ((W ω) ^ 2 / σ ^ 2) ^ k := by
        rw [pow_mul, sq_abs]
        rw [div_pow]
        field_simp [hσne]
        simp [pow_mul]
      _ ≤ σ ^ (2 * k) *
          (k.factorial * Real.exp ((W ω) ^ 2 / σ ^ 2)) :=
        mul_le_mul_of_nonneg_left hseries' (pow_nonneg hσ.le _)
      _ = c * Real.exp ((W ω) ^ 2 / σ ^ 2) := by
        simp [c]
        ring
  have hmoment : Integrable (fun ω ↦ |W ω| ^ (2 * k)) μ := by
    exact (hexp.const_mul c).mono'
      ((hW.abs.pow_const (2 * k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (abs_nonneg (W ω)) (2 * k))]
        exact hpoint ω)
  calc
    ∫ ω, |W ω| ^ (2 * k) ∂μ
        ≤ ∫ ω, c * Real.exp ((W ω) ^ 2 / σ ^ 2) ∂μ :=
      integral_mono_ae hmoment (hexp.const_mul c)
        (Filter.Eventually.of_forall hpoint)
    _ = c * ∫ ω, Real.exp ((W ω) ^ 2 / σ ^ 2) ∂μ := by
      rw [integral_const_mul]
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left hexp_le hc
    _ = 2 * σ ^ (2 * k) * k.factorial := by simp [c]; ring

/-- The treatment-noise Luxemburg assumption gives the factorial even-moment
majorant used for residual-transform coefficients. -/
lemma eta_even_moment_integral_le
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n k : ℕ)
    (hclass : NonGaussianClass p n m) :
    ∫ o, |eta p m o| ^ (2 * k) ∂m.P ≤
      2 * p.psieta ^ (2 * k) * k.factorial := by
  apply luxemburg_even_moment_integral_le
  · unfold eta treatment covariate
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  · exact p.constants_pos.2.2.2.1
  · exact hclass.etaSubGaussian.1
  · exact hclass.etaSubGaussian.2

/-- The conditional Luxemburg bound for the outcome innovation implies its
unconditional square-exponential bound. -/
lemma xi_luxemburg_integral_le
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ)
    (hclass : NonGaussianClass p n m) :
    ∫ o, Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2) ∂m.P ≤ 2 := by
  let f := fun o : Obs Xspace ↦ Real.exp ((xi p m o) ^ 2 / p.psixi ^ 2)
  have hcond : ∀ᵐ o ∂m.P,
      (@condExp (Obs Xspace) ℝ
        (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P f) o ≤ 2 := by
    simpa [f] using hclass.xiSubGaussian.2
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  calc
    ∫ o, f o ∂m.P = ∫ o, (@condExp (Obs Xspace) ℝ
        (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P f) o ∂m.P := by
      symm
      exact integral_condExp (μ := m.P) (f := f) hcov.comap_le
    _ ≤ ∫ _o, (2 : ℝ) ∂m.P := integral_mono_ae
      (integrable_condExp (μ := m.P) (f := f)) (integrable_const 2) hcond
    _ = 2 := by simp

/-- A uniform square-integral envelope for the absolute exponential of the
learned residual. -/
lemma learnedResidual_exp_abs_sq_lintegral_le
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ)
    (hclass : NonGaussianClass p n m) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ o, ENNReal.ofReal ((Real.exp (2 * R * |learnedResidual p m n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal (2 * Real.exp (8 * R * p.Cg + 4 * R ^ 2 * p.psieta ^ 2)) := by
  have hpsi := p.constants_pos.2.2.2.1
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hbar (x : Xspace) : |barG p m n x| ≤ p.Cg := by
    rw [abs_le]
    dsimp [barG]
    constructor <;> simp_all <;> linarith [p.constants_pos.2.1]
  have hD : ∀ᵐ o ∂m.P, |treatmentError p m n o| ≤ 2 * p.Cg := by
    have hg := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.gRange
    filter_upwards [hg] with o ho
    exact (abs_sub _ _).trans (by linarith [hbar (covariate o)])
  have hpoint : ∀ᵐ o ∂m.P,
      (Real.exp (2 * R * |learnedResidual p m n o|)) ^ 2 ≤
        Real.exp (8 * R * p.Cg + 4 * R ^ 2 * p.psieta ^ 2) *
          Real.exp ((eta p m o) ^ 2 / p.psieta ^ 2) := by
    filter_upwards [hD] with o hDo
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hZ : |learnedResidual p m n o| ≤ |eta p m o| + 2 * p.Cg := by
      rw [show learnedResidual p m n o = eta p m o + treatmentError p m n o by
        simp [learnedResidual, eta, treatmentError]]
      exact (abs_add_le _ _).trans (add_le_add_right hDo _)
    have hyoung : 4 * R * |eta p m o| ≤
        (eta p m o) ^ 2 / p.psieta ^ 2 + 4 * R ^ 2 * p.psieta ^ 2 := by
      have hs : 0 ≤ (|eta p m o| / p.psieta - 2 * R * p.psieta) ^ 2 := sq_nonneg _
      field_simp [hpsi.ne'] at hs ⊢
      nlinarith [sq_abs (eta p m o)]
    nlinarith
  calc
    _ ≤ ∫⁻ o, ENNReal.ofReal
        (Real.exp (8 * R * p.Cg + 4 * R ^ 2 * p.psieta ^ 2) *
          Real.exp ((eta p m o) ^ 2 / p.psieta ^ 2)) ∂m.P :=
      lintegral_mono_ae (hpoint.mono fun _ h ↦ ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal (Real.exp (8 * R * p.Cg + 4 * R ^ 2 * p.psieta ^ 2)) *
        ∫⁻ o, ENNReal.ofReal (Real.exp ((eta p m o) ^ 2 / p.psieta ^ 2)) ∂m.P := by
      simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [lintegral_const_mul']
      simp
    _ = ENNReal.ofReal (Real.exp (8 * R * p.Cg + 4 * R ^ 2 * p.psieta ^ 2)) *
        ENNReal.ofReal (∫ o, Real.exp ((eta p m o) ^ 2 / p.psieta ^ 2) ∂m.P) := by
      rw [ofReal_integral_eq_lintegral_ofReal]
      · exact hclass.etaSubGaussian.1
      · exact Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le
    _ ≤ ENNReal.ofReal (Real.exp (8 * R * p.Cg + 4 * R ^ 2 * p.psieta ^ 2)) *
        ENNReal.ofReal 2 := by
      gcongr
      exact hclass.etaSubGaussian.2
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      simp [mul_comm]

/-- The primitive bounds imply a uniform fourth moment for the observed
outcome. -/
lemma outcome_fourth_moment_le
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ)
    (hclass : NonGaussianClass p n m) :
    Integrable (fun o ↦ |outcome o| ^ 4) m.P ∧
    ∫ o, |outcome o| ^ 4 ∂m.P ≤
      64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 + 4 * p.psixi ^ 4) := by
  have hcov : Measurable (covariate (Xspace := Xspace)) := measurable_fst
  have hq := MeasureTheory.ae_of_ae_map hcov.aemeasurable hclass.qRange
  have heta4 := eta_even_moment_integral_le p m n 2 hclass
  have hxiExp := xi_luxemburg_integral_le p m n hclass
  have hxiMeas : Measurable (xi p m) := by
    unfold xi outcome covariate eta treatment
    exact measurable_snd.snd.sub (m.q0_measurable.comp measurable_fst) |>.sub
      (measurable_const.mul
        (measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)))
  have hxi4 := luxemburg_even_moment_integral_le (xi p m) hxiMeas
    p.constants_pos.2.2.2.2.1 hclass.xiSubGaussian.1 hxiExp 2
  have hetaSet : integrableExpSet (eta p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, eta_integrable_exp p m n hclass t]
  have hxiSet : integrableExpSet (xi p m) m.P = Set.univ := by
    ext t
    simp [integrableExpSet, xi_integrable_exp p m n hclass t]
  have heta4int : Integrable (fun o ↦ |eta p m o| ^ 4) m.P :=
    integrable_pow_abs_of_mem_interior_integrableExpSet (by simp [hetaSet]) 4
  have hxi4int : Integrable (fun o ↦ |xi p m o| ^ 4) m.P :=
    integrable_pow_abs_of_mem_interior_integrableExpSet (by simp [hxiSet]) 4
  have hpoint : ∀ᵐ o ∂m.P, |outcome o| ^ 4 ≤
      64 * (p.Cq ^ 4 + p.Ctheta ^ 4 * |eta p m o| ^ 4 + |xi p m o| ^ 4) := by
    filter_upwards [hq] with o hqo
    have hout : outcome o = m.q0 (covariate o) + m.theta0 * eta p m o + xi p m o := by
      simp [xi]
    rw [hout]
    calc
      |m.q0 (covariate o) + m.theta0 * eta p m o + xi p m o| ^ 4 ≤
          (|m.q0 (covariate o)| + |m.theta0| * |eta p m o| + |xi p m o|) ^ 4 := by
        gcongr
        calc
          |m.q0 (covariate o) + m.theta0 * eta p m o + xi p m o| ≤
              |m.q0 (covariate o) + m.theta0 * eta p m o| + |xi p m o| :=
            abs_add_le _ _
          _ ≤ |m.q0 (covariate o)| + |m.theta0 * eta p m o| + |xi p m o| :=
            by nlinarith [abs_add_le (m.q0 (covariate o)) (m.theta0 * eta p m o)]
          _ = _ := by rw [abs_mul]
      _ ≤ 64 * (|m.q0 (covariate o)| ^ 4 +
          (|m.theta0| * |eta p m o|) ^ 4 + |xi p m o| ^ 4) := by
        nlinarith [sq_nonneg (|m.q0 (covariate o)| + |m.theta0| * |eta p m o| -
          |xi p m o|),
          sq_nonneg ((|m.q0 (covariate o)| + |m.theta0| * |eta p m o|) ^ 2 -
            |xi p m o| ^ 2),
          sq_nonneg (|m.q0 (covariate o)| - |m.theta0| * |eta p m o|),
          sq_nonneg (|m.q0 (covariate o)| ^ 2 -
            (|m.theta0| * |eta p m o|) ^ 2)]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · apply add_le_add
          · exact pow_le_pow_left₀ (abs_nonneg _) hqo 4
          · rw [mul_pow]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (abs_nonneg _) hclass.thetaRange 4) (by positivity)
        · exact le_rfl
  have hrhsint : Integrable (fun o ↦
      64 * (p.Cq ^ 4 + p.Ctheta ^ 4 * |eta p m o| ^ 4 + |xi p m o| ^ 4)) m.P :=
    (((integrable_const (p.Cq ^ 4)).add
      (heta4int.const_mul (p.Ctheta ^ 4))).add hxi4int).const_mul 64
  have hlhsint : Integrable (fun o ↦ |outcome o| ^ 4) m.P :=
    hrhsint.mono' ((measurable_snd.snd.abs.pow_const 4).aestronglyMeasurable)
      (hpoint.mono fun _ h ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 4)]
        exact h)
  refine ⟨hlhsint, ?_⟩
  calc
    _ ≤ ∫ o, 64 * (p.Cq ^ 4 + p.Ctheta ^ 4 * |eta p m o| ^ 4 +
        |xi p m o| ^ 4) ∂m.P := integral_mono_ae hlhsint hrhsint hpoint
    _ = 64 * (p.Cq ^ 4 + p.Ctheta ^ 4 * ∫ o, |eta p m o| ^ 4 ∂m.P +
        ∫ o, |xi p m o| ^ 4 ∂m.P) := by
      rw [integral_const_mul]
      congr 1
      change (∫ o, (p.Cq ^ 4 + p.Ctheta ^ 4 * |eta p m o| ^ 4) +
        |xi p m o| ^ 4 ∂m.P) = _
      calc
        _ = (∫ o, p.Cq ^ 4 + p.Ctheta ^ 4 * |eta p m o| ^ 4 ∂m.P) +
            ∫ o, |xi p m o| ^ 4 ∂m.P := integral_add
              ((integrable_const (p.Cq ^ 4)).add
                (heta4int.const_mul (p.Ctheta ^ 4))) hxi4int
        _ = ((∫ _o, p.Cq ^ 4 ∂m.P) +
              ∫ o, p.Ctheta ^ 4 * |eta p m o| ^ 4 ∂m.P) +
            ∫ o, |xi p m o| ^ 4 ∂m.P := by
              rw [integral_add (integrable_const (p.Cq ^ 4))
                (heta4int.const_mul (p.Ctheta ^ 4))]
        _ = _ := by simp [integral_const_mul]
    _ ≤ _ := by
      norm_num at heta4 hxi4
      have heta4' : ∫ o, |eta p m o| ^ 4 ∂m.P ≤ 4 * p.psieta ^ 4 := by linarith
      have hxi4' : ∫ o, |xi p m o| ^ 4 ∂m.P ≤ 4 * p.psixi ^ 4 := by linarith
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ p.Cq ^ 4 + p.Ctheta ^ 4 * (4 * p.psieta ^ 4) +
            4 * p.psixi ^ 4 := by gcongr
        _ = _ := by ring

/-- Multiplying the outcome by an absolute learned-residual exponential still
has a uniform `L²` envelope. -/
lemma outcome_exp_abs_sq_lintegral_le
    (p : Parameters) (m : Model (Xspace := Xspace) p) (n : ℕ)
    (hclass : NonGaussianClass p n m) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ o, ENNReal.ofReal
        ((|outcome o| * Real.exp (2 * R * |learnedResidual p m n o|)) ^ 2) ∂m.P ≤
      ENNReal.ofReal
        (64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 + 4 * p.psixi ^ 4) +
          2 * Real.exp (16 * R * p.Cg + 16 * R ^ 2 * p.psieta ^ 2)) := by
  have hY4 := outcome_fourth_moment_le p m n hclass
  have hZ8 := learnedResidual_exp_abs_sq_lintegral_le p m n hclass (2 * R)
    (mul_nonneg (by norm_num) hR)
  have hpoint (o : Obs Xspace) :
      (|outcome o| * Real.exp (2 * R * |learnedResidual p m n o|)) ^ 2 ≤
        |outcome o| ^ 4 +
          (Real.exp (2 * (2 * R) * |learnedResidual p m n o|)) ^ 2 := by
    let B := Real.exp (4 * R * |learnedResidual p m n o|)
    calc
      (|outcome o| * Real.exp (2 * R * |learnedResidual p m n o|)) ^ 2 =
          |outcome o| ^ 2 * B := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        simp [B]
        ring
      _ ≤ |outcome o| ^ 4 + B ^ 2 := by
        nlinarith [sq_nonneg (|outcome o| ^ 2 - B)]
      _ = _ := by
        congr 1
        apply congrArg (fun x : ℝ ↦ x ^ 2)
        dsimp [B]
        congr 1
        ring
  calc
    _ ≤ ∫⁻ o, ENNReal.ofReal (|outcome o| ^ 4 +
        (Real.exp (2 * (2 * R) * |learnedResidual p m n o|)) ^ 2) ∂m.P :=
      lintegral_mono fun o ↦ ENNReal.ofReal_le_ofReal (hpoint o)
    _ = (∫⁻ o, ENNReal.ofReal (|outcome o| ^ 4) ∂m.P) +
        ∫⁻ o, ENNReal.ofReal
          ((Real.exp (2 * (2 * R) * |learnedResidual p m n o|)) ^ 2) ∂m.P := by
      rw [show (fun o ↦ ENNReal.ofReal (|outcome o| ^ 4 +
          (Real.exp (2 * (2 * R) * |learnedResidual p m n o|)) ^ 2)) =
          fun o ↦ ENNReal.ofReal (|outcome o| ^ 4) + ENNReal.ofReal
            ((Real.exp (2 * (2 * R) * |learnedResidual p m n o|)) ^ 2) by
        funext o
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]]
      exact lintegral_add_left
        (measurable_snd.snd.abs.pow_const 4).ennreal_ofReal _
    _ = ENNReal.ofReal (∫ o, |outcome o| ^ 4 ∂m.P) +
        ∫⁻ o, ENNReal.ofReal
          ((Real.exp (2 * (2 * R) * |learnedResidual p m n o|)) ^ 2) ∂m.P := by
      rw [ofReal_integral_eq_lintegral_ofReal hY4.1
        (Filter.Eventually.of_forall fun _ ↦ by positivity)]
    _ ≤ ENNReal.ofReal
          (64 * (p.Cq ^ 4 + 4 * p.Ctheta ^ 4 * p.psieta ^ 4 + 4 * p.psixi ^ 4)) +
        ENNReal.ofReal
          (2 * Real.exp (8 * (2 * R) * p.Cg + 4 * (2 * R) ^ 2 * p.psieta ^ 2)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hY4.2) hZ8
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity)
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)]
      congr 2
      ring_nf

/-- A real-weighted exponential transform is its factorial-weighted moment
series whenever the doubled absolute exponential is integrable. -/
theorem weighted_exp_integral_eq_moment_tsum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W V : Ω → ℝ) (hW : Measurable W) (hV : Measurable V)
    (z : ℂ)
    (hdom : Integrable (fun o ↦ |W o| * Real.exp (2 * ‖z‖ * |V o|)) μ) :
    ∫ o, (W o : ℂ) * Complex.exp (z * V o) ∂μ =
      ∑' k : ℕ, ((∫ o, W o * V o ^ k ∂μ : ℝ) / k.factorial : ℂ) * z ^ k := by
  let F : ℕ → Ω → ℂ := fun k o ↦
    ((W o * V o ^ k / k.factorial : ℝ) : ℂ) * z ^ k
  let D : Ω → ℝ := fun o ↦ |W o| * Real.exp (2 * ‖z‖ * |V o|)
  have hpoint (k : ℕ) (o : Ω) : ‖F k o‖ ≤ (1 / 2 : ℝ) ^ k * D o := by
    have hp := Real.pow_div_factorial_le_exp (2 * ‖z‖ * |V o|) (by positivity) k
    dsimp [F, D]
    simp only [norm_mul, Complex.norm_real, norm_pow, Real.norm_eq_abs,
      abs_div, abs_mul, abs_pow, Nat.cast_nonneg, abs_of_nonneg]
    have hk : (0 : ℝ) < k.factorial := by positivity
    calc
      |W o| * |V o| ^ k / k.factorial * ‖z‖ ^ k =
          (1 / 2 : ℝ) ^ k * |W o| *
            ((2 * ‖z‖ * |V o|) ^ k / k.factorial) := by
        simp only [mul_pow]
        field_simp
        have ht : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by
          rw [one_div, inv_pow, inv_mul_cancel₀]
          positivity
        let L := |W o| * |V o| ^ k * ‖z‖ ^ k
        change L = L * (1 / 2 : ℝ) ^ k * 2 ^ k
        calc
          L = L * 1 := by ring
          _ = L * ((1 / 2 : ℝ) ^ k * 2 ^ k) := by rw [ht]
          _ = _ := by ring
      _ ≤ (1 / 2 : ℝ) ^ k * |W o| * Real.exp (2 * ‖z‖ * |V o|) := by
        gcongr
      _ = _ := by ring
  have hFint : ∀ k, Integrable (F k) μ := by
    intro k
    exact (hdom.const_mul ((1 / 2 : ℝ) ^ k)).mono'
      (((Complex.measurable_ofReal.comp
        (hW.mul (hV.pow_const k) |>.div_const k.factorial)).mul_const
          (z ^ k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun o ↦ by simpa [D] using hpoint k o)
  have hnormsum : Summable (fun k ↦ ∫ o, ‖F k o‖ ∂μ) := by
    apply Summable.of_nonneg_of_le
      (fun k ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun k ↦ ?_)
      ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
        (∫ o, D o ∂μ))
    calc
      ∫ o, ‖F k o‖ ∂μ ≤ ∫ o, (1 / 2 : ℝ) ^ k * D o ∂μ :=
        integral_mono (hFint k).norm (hdom.const_mul _) (hpoint k)
      _ = (1 / 2 : ℝ) ^ k * ∫ o, D o ∂μ := integral_const_mul _ _
      _ = _ := by ring
  calc
    _ = ∫ o, ∑' k, F k o ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with o
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
      apply tsum_congr
      intro k
      simp [F]
      ring
    _ = ∑' k, ∫ o, F k o ∂μ :=
      (integral_tsum_of_summable_integral_norm hFint hnormsum).symm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [show F k = fun o ↦
          ((W o * V o ^ k / k.factorial : ℝ) : ℂ) * z ^ k by rfl]
      rw [show (fun o ↦ ((W o * V o ^ k / k.factorial : ℝ) : ℂ) * z ^ k) =
          fun o ↦ (((W o * V o ^ k : ℝ) : ℂ) / (k.factorial : ℂ)) * z ^ k by
        funext o
        push_cast
        ring]
      calc
        _ = (∫ o, ((W o * V o ^ k : ℝ) : ℂ) / (k.factorial : ℂ) ∂μ) * z ^ k :=
          integral_mul_const _ _
        _ = ((k.factorial : ℂ)⁻¹ * ∫ o, ((W o * V o ^ k : ℝ) : ℂ) ∂μ) *
            z ^ k := by
          congr 1
          rw [show (fun o ↦ ((W o * V o ^ k : ℝ) : ℂ) / (k.factorial : ℂ)) =
              fun o ↦ (k.factorial : ℂ)⁻¹ * ((W o * V o ^ k : ℝ) : ℂ) by
            funext o
            ring]
          exact integral_const_mul _ _
        _ = _ := by
          have hi : (∫ o, ((W o * V o ^ k : ℝ) : ℂ) ∂μ) =
              ((∫ o, W o * V o ^ k ∂μ : ℝ) : ℂ) := integral_complex_ofReal
          rw [hi]
          ring

/-- A doubled absolute-exponential `L²` envelope gives geometric `L²` bounds
for factorial-weighted moment coefficients. -/
theorem factorial_coefficient_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (W V : Ω → ℝ) (hW : Measurable W) (hV : Measurable V)
    (R : ℝ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C)
    (henv : ∫⁻ o, ENNReal.ofReal
        ((|W o| * Real.exp (2 * R * |V o|)) ^ 2) ∂μ ≤ ENNReal.ofReal (C ^ 2))
    (k : ℕ) :
    MemLp (fun o ↦ W o * V o ^ k / k.factorial) 2 μ ∧
      eLpNorm (fun o ↦ W o * V o ^ k / k.factorial) 2 μ ≤
        ENNReal.ofReal (C / (2 * R) ^ k) := by
  let a : ℝ := ((2 * R) ^ k)⁻¹
  let E : Ω → ℝ := fun o ↦ |W o| * Real.exp (2 * R * |V o|)
  have ha : 0 ≤ a := inv_nonneg.mpr (pow_nonneg (mul_nonneg (by norm_num) hR.le) _)
  have hpoint (o : Ω) : |W o * V o ^ k / k.factorial| ≤ a * E o := by
    have hp := Real.pow_div_factorial_le_exp (2 * R * |V o|) (by positivity) k
    dsimp [a, E]
    rw [abs_div, abs_mul, abs_pow]
    have hfact : |(k.factorial : ℝ)| = (k.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [hfact]
    have hk : (0 : ℝ) < k.factorial := by positivity
    have hbase : 0 < 2 * R := mul_pos (by norm_num) hR
    calc
      |W o| * |V o| ^ k / k.factorial =
          ((2 * R) ^ k)⁻¹ * |W o| * ((2 * R * |V o|) ^ k / k.factorial) := by
        field_simp
        simp only [mul_pow]
        field_simp
      _ ≤ ((2 * R) ^ k)⁻¹ * |W o| * Real.exp (2 * R * |V o|) := by
        gcongr
      _ = _ := by ring
  have hfmeas : Measurable (fun o ↦ W o * V o ^ k / k.factorial) :=
    (hW.mul (hV.pow_const k)).div_const _
  have hsq : ∫⁻ o, ENNReal.ofReal ((W o * V o ^ k / k.factorial) ^ 2) ∂μ ≤
      ENNReal.ofReal ((C / (2 * R) ^ k) ^ 2) := by
    calc
      _ = ∫⁻ o, ENNReal.ofReal (|W o * V o ^ k / k.factorial| ^ 2) ∂μ := by
        apply lintegral_congr
        intro o
        rw [sq_abs]
      _ ≤ ∫⁻ o, ENNReal.ofReal ((a * E o) ^ 2) ∂μ :=
        lintegral_mono fun o ↦ ENNReal.ofReal_le_ofReal
          ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg ha (by positivity))).2 (hpoint o))
      _ = ENNReal.ofReal (a ^ 2) *
          ∫⁻ o, ENNReal.ofReal ((E o) ^ 2) ∂μ := by
        rw [← lintegral_const_mul' _ _ (by simp [a, hR.ne'])]
        apply lintegral_congr
        intro o
        rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg a)]
      _ ≤ ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (C ^ 2) :=
        mul_le_mul_right henv _
      _ = ENNReal.ofReal ((C / (2 * R) ^ k) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg a)]
        congr 1
        dsimp [a]
        rw [div_eq_mul_inv, mul_pow, inv_pow]
        ring
  exact memLp_two_and_eLpNorm_le_of_sq_lintegral_le μ hfmeas
    (div_nonneg hC (pow_nonneg (mul_nonneg (by norm_num) hR.le) _)) hsq

/-- A split-fold residual-transform error is the average of its centered
single-observation transform values. -/
lemma empiricalF_sub_eq_centered
    (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) (data : Fin n → Obs Xspace) (I : Finset (Fin n))
    (hI : I.Nonempty) (z : ℂ) :
    empiricalF p m n data I z - residualMGF p m n z =
      (I.card : ℂ)⁻¹ * ∑ i ∈ I,
        (Complex.exp (z * learnedResidual p m n (data i)) -
          residualMGF p m n z) := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  unfold empiricalF residualMGF ProbabilityTheory.complexMGF
  have hc : (I.card : ℂ) ≠ 0 := by exact_mod_cast hI.card_pos.ne'
  field_simp

/-- A split-fold outcome-transform error is the average of its centered
single-observation weighted transform values. -/
lemma empiricalG_sub_eq_centered
    (p : Parameters) (m : Model (Xspace := Xspace) p)
    (n : ℕ) (data : Fin n → Obs Xspace) (I : Finset (Fin n))
    (hI : I.Nonempty) (z : ℂ) :
    empiricalG p m n data I z - outcomeResidualTransform p m n z =
      (I.card : ℂ)⁻¹ * ∑ i ∈ I,
        ((outcome (data i) : ℂ) *
          Complex.exp (z * learnedResidual p m n (data i)) -
            outcomeResidualTransform p m n z) := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  unfold empiricalG outcomeResidualTransform weightedTransform
  have hc : (I.card : ℂ) ≠ 0 := by exact_mod_cast hI.card_pos.ne'
  field_simp

set_option maxHeartbeats 600000 in
/-- A summable sequence of real centered coefficients with coefficientwise
`L²` bounds controls the uniform squared norm of its analytic series. -/
theorem centered_real_series_diskSupNorm_sq_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c : Ω → ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hcmeas : ∀ k, Measurable (fun ω ↦ c ω k))
    (hcsum : ∀ ω, Summable (fun k ↦ |c ω k| * R ^ k))
    (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k)
    (hbsum : Summable fun k ↦ b k * R ^ k)
    (hcl2 : ∀ k, MemLp (fun ω ↦ c ω k) 2 μ ∧
      eLpNorm (fun ω ↦ c ω k) 2 μ ≤ ENNReal.ofReal (b k)) :
    ∫⁻ ω, ENNReal.ofReal
        ((diskSupNorm (fun ω z ↦ ∑' k, (c ω k : ℂ) * z ^ k) R ω) ^ 2) ∂μ ≤
      ENNReal.ofReal ((∑' k, b k * R ^ k) ^ 2) := by
  let A : ℕ → Ω → ℝ := fun k ω ↦ |c ω k| * R ^ k
  have hAmeas : ∀ k, Measurable (A k) := by
    intro k
    exact (hcmeas k).abs.mul_const _
  have hAbound : ∀ k, eLpNorm (A k) 2 μ ≤ ENNReal.ofReal (b k * R ^ k) := by
    intro k
    rw [show A k = (R ^ k) • (fun ω ↦ |c ω k|) by
      funext ω
      simp [A, mul_comm]]
    rw [eLpNorm_const_smul]
    rw [show eLpNorm (fun ω ↦ |c ω k|) 2 μ =
        eLpNorm (fun ω ↦ c ω k) 2 μ by
      simpa [Real.norm_eq_abs] using
        (eLpNorm_norm (f := fun ω ↦ c ω k) (p := 2) (μ := μ))]
    rw [show ‖R ^ k‖ₑ = ENNReal.ofReal (R ^ k) by
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hR k)]]
    rw [ENNReal.ofReal_mul (hb k)]
    calc
      ENNReal.ofReal (R ^ k) * eLpNorm (fun ω ↦ c ω k) 2 μ ≤
          ENNReal.ofReal (R ^ k) * ENNReal.ofReal (b k) :=
        mul_le_mul_right (hcl2 k).2 _
      _ = _ := by ac_rfl
  apply (lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal ?_).trans
    (tsum_sq_lintegral_le_tsum_lpNorm μ A hAmeas hcsum
      (fun k ↦ b k * R ^ k) (fun k ↦ mul_nonneg (hb k) (pow_nonneg hR k))
      hbsum hAbound)
  have hs := diskSupNorm_tsum_mul_pow_le
    (fun ω k ↦ (c ω k : ℂ)) hR ω (by simpa [A] using hcsum ω)
  have hsup0 : 0 ≤ diskSupNorm
      (fun ω z ↦ ∑' k, (c ω k : ℂ) * z ^ k) R ω := by
    exact (norm_nonneg _).trans (by
      rw [diskSupNorm_eq_sSup_image]
      apply le_csSup
      · exact ⟨∑' k, |c ω k| * R ^ k, by
          rintro x ⟨z, hz, rfl⟩
          convert norm_tsum_mul_pow_le_tsum_norm_mul_pow
            (fun k ↦ (c ω k : ℂ)) (by simpa using hcsum ω) hz using 1 <;>
            first | rfl | simp⟩
      · exact ⟨0, by simpa using hR, rfl⟩)
  exact (sq_le_sq₀ hsup0
    (tsum_nonneg fun k ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hR k))).2
      (by simpa using hs)

end CausalSmith.Stat.SaPlmCumulantConverse
