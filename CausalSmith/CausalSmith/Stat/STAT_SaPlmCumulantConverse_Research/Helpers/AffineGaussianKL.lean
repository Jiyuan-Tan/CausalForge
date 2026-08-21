import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.AffineGaussianOutcomePath
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.EmpiricalTransform
import Causalean.Mathlib.Probability.Kernel.GraphMapProd

/-!
# KL control for affine Gaussian outcome paths

Kernel and bind representations of the affine outcome channel, used to reduce
its KL divergence to the equal-variance Gaussian location formula.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

private abbrev XT' (Xspace : Type*) := Xspace × ℝ

/-- The scalar innovation channel obtained after expressing an affine outcome
law in the coordinates of a fixed reference parameter. -/
-- @node: shiftedInnovationKernel
def shiftedInnovationKernel {p : Parameters} (base : Model (Xspace := Xspace) p)
    (theta thetaRef tau : ℝ) : Kernel (XT' Xspace) ℝ :=
  Causalean.Mathlib.GraphMapProd.mechanismKernel
    (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩)
    (fun w ↦ (theta - thetaRef) * (w.1.2 - base.g0 w.1.1) + w.2)

/-- [The scalar innovation channel — which, given the covariates and the treatment, draws a
normal variable centred at the parameter displacement times the treatment innovation, with
variance the square of the innovation scale — is a probability kernel: every one of its
conditional slices is a probability measure](goal). -/
instance shiftedInnovationKernel_isMarkov {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta thetaRef tau : ℝ) :
    IsMarkovKernel (shiftedInnovationKernel base theta thetaRef tau) := by
  unfold shiftedInnovationKernel
  apply Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel
  exact (measurable_const.mul
    ((measurable_snd.comp measurable_fst).sub
      (base.g0_measurable.comp (measurable_fst.comp measurable_fst)))).add measurable_snd

/-- Each scalar slice is the equal-variance Gaussian whose mean is the
parameter displacement times the retained treatment innovation. -/
-- @node: shiftedInnovationKernel_apply
lemma shiftedInnovationKernel_apply {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta thetaRef tau : ℝ)
    (xt : XT' Xspace) :
    shiftedInnovationKernel base theta thetaRef tau xt =
      gaussianReal ((theta - thetaRef) * (xt.2 - base.g0 xt.1))
        ⟨tau ^ 2, sq_nonneg tau⟩ := by
  rw [shiftedInnovationKernel,
    Causalean.Mathlib.GraphMapProd.mechanismKernel_apply]
  · -- The variance is an anonymous-constructor term, which blocks rewriting
    -- inside the goal; state the shift identity for a general variance instead.
    have hmap : ∀ (v : NNReal) (c : ℝ),
        (gaussianReal 0 v).map (fun l ↦ c + l) = gaussianReal c v := by
      intro v c
      rw [gaussianReal_map_const_add, zero_add]
    change (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩).map
      (fun l ↦ (theta - thetaRef) * (xt.2 - base.g0 xt.1) + l) = _
    exact hmap _ _
  · exact (measurable_const.mul
      ((measurable_snd.comp measurable_fst).sub
        (base.g0_measurable.comp (measurable_fst.comp measurable_fst)))).add measurable_snd

/-- In reference affine coordinates, the observed affine Gaussian law is the
pushforward of the retained `(X,T)` law and the scalar shifted innovation. -/
-- @node: affineGaussianLaw_eq_map_shiftedInnovation
lemma affineGaussianLaw_eq_map_shiftedInnovation {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta thetaRef tau : ℝ) :
    affineGaussianLaw base theta tau =
      ((xtLaw base) ⊗ₘ (shiftedInnovationKernel base theta thetaRef tau)).map
        (affineOutcomeEquiv base.g0 base.q0 thetaRef
          base.g0_measurable base.q0_measurable) := by
  have hmech : Measurable (fun w : XT' Xspace × ℝ ↦
      (theta - thetaRef) * (w.1.2 - base.g0 w.1.1) + w.2) :=
    (measurable_const.mul
      ((measurable_snd.comp measurable_fst).sub
        (base.g0_measurable.comp (measurable_fst.comp measurable_fst)))).add measurable_snd
  have hgraph := Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd
    (xtLaw base) (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩) hmech
  change affineGaussianLaw base theta tau =
    ((xtLaw base) ⊗ₘ
      (Causalean.Mathlib.GraphMapProd.mechanismKernel
        (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩)
        (fun w ↦ (theta - thetaRef) * (w.1.2 - base.g0 w.1.1) + w.2))).map _
  rw [← hgraph, Measure.map_map
    (affineOutcomeEquiv base.g0 base.q0 thetaRef
      base.g0_measurable base.q0_measurable).measurable
    (measurable_fst.prodMk hmech)]
  · unfold affineGaussianLaw
    apply Measure.map_congr
    filter_upwards with w
    ext <;> simp [affineOutcomeEquiv]
    ring

/-- The affine outcome mechanism applied to `(X,T)` and a scalar innovation. -/
def affineOutcomeMechanism {p : Parameters} (base : Model (Xspace := Xspace) p)
    (theta : ℝ) : XT' Xspace × ℝ → Obs Xspace := fun w ↦
  (w.1.1, w.1.2, base.q0 w.1.1 + theta * (w.1.2 - base.g0 w.1.1) + w.2)

/-- [The affine outcome mechanism — which maps covariates, treatment, and a scalar innovation
to the observed triple whose outcome coordinate is the baseline outcome regression plus the
treatment coefficient times the treatment innovation plus that scalar innovation — is jointly
measurable](goal). -/
lemma affineOutcomeMechanism_measurable {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta : ℝ) :
    Measurable (affineOutcomeMechanism base theta) := by
  exact (measurable_fst.comp measurable_fst).prodMk <|
    (measurable_snd.comp measurable_fst).prodMk <|
      ((base.q0_measurable.comp (measurable_fst.comp measurable_fst)).add
        (measurable_const.mul ((measurable_snd.comp measurable_fst).sub
          (base.g0_measurable.comp (measurable_fst.comp measurable_fst))))).add
            measurable_snd

/-- Conditional affine Gaussian outcome channel given `(X,T)`. -/
def affineOutcomeKernel {p : Parameters} (base : Model (Xspace := Xspace) p)
    (theta tau : ℝ) : Kernel (XT' Xspace) (Obs Xspace) :=
  Causalean.Mathlib.GraphMapProd.mechanismKernel
    (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩) (affineOutcomeMechanism base theta)

/-- [The conditional affine Gaussian outcome channel — which, given the covariates and the
treatment, returns the observed triple whose outcome is the baseline outcome regression plus
the treatment coefficient times the treatment innovation plus centred Gaussian noise of the
stated scale — is a probability kernel](goal). -/
instance affineOutcomeKernel_isMarkov {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    IsMarkovKernel (affineOutcomeKernel base theta tau) := by
  unfold affineOutcomeKernel
  exact Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel
    _ (affineOutcomeMechanism_measurable base theta)

/-- The affine Gaussian law is the base `(X,T)` law bound to its affine
Gaussian outcome channel. -/
lemma affineGaussianLaw_eq_bind {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    affineGaussianLaw base theta tau =
      (xtLaw base).bind (affineOutcomeKernel base theta tau) := by
  have hgraph := Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd
    (xtLaw base) (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩)
      (affineOutcomeMechanism_measurable base theta)
  have hsnd := congrArg (Measure.map Prod.snd) hgraph
  rw [Measure.map_map measurable_snd
      ((measurable_fst.prodMk (affineOutcomeMechanism_measurable base theta)))] at hsnd
  change _ = (xtLaw base ⊗ₘ affineOutcomeKernel base theta tau).snd at hsnd
  rw [Measure.snd_compProd] at hsnd
  simpa [affineGaussianLaw, affineOutcomeKernel, affineOutcomeMechanism,
    affineOutcomeEquiv, Function.comp_def] using hsnd

/-- A channel slice is a pushforward of its centered Gaussian innovation. -/
lemma affineOutcomeKernel_apply {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) (xt : XT' Xspace) :
    affineOutcomeKernel base theta tau xt =
      (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩).map
        (fun z ↦ affineOutcomeMechanism base theta (xt, z)) := by
  unfold affineOutcomeKernel
  exact Causalean.Mathlib.GraphMapProd.mechanismKernel_apply _
    (affineOutcomeMechanism_measurable base theta) xt

/-- A second parameter value can be represented through the first affine map
by shifting only the Gaussian innovation mean. -/
lemma affineOutcomeKernel_apply_eq_shifted {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta0 theta1 tau : ℝ)
    (xt : XT' Xspace) :
    affineOutcomeKernel base theta1 tau xt =
      (gaussianReal ((theta1 - theta0) * (xt.2 - base.g0 xt.1))
        ⟨tau ^ 2, sq_nonneg tau⟩).map
          (fun z ↦ affineOutcomeMechanism base theta0 (xt, z)) := by
  rw [affineOutcomeKernel_apply]
  let d := (theta1 - theta0) * (xt.2 - base.g0 xt.1)
  have hshift := gaussianReal_map_add_const
    (μ := 0) (v := ⟨tau ^ 2, sq_nonneg tau⟩) d
  rw [zero_add] at hshift
  have hslice : Measurable (fun z ↦ affineOutcomeMechanism base theta0 (xt, z)) :=
    (affineOutcomeMechanism_measurable base theta0).comp
      (measurable_const.prodMk measurable_id)
  rw [← hshift, Measure.map_map hslice (by fun_prop)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun z ↦ by
    simp [affineOutcomeMechanism, d]
    ring

/-- Pointwise channel KL is bounded by the corresponding Gaussian-location
KL, with shift proportional to the treatment residual. -/
lemma affineOutcomeKernel_kl_le {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta0 theta1 tau : ℝ)
    (htau : 0 < tau) (xt : XT' Xspace) :
    InformationTheory.klDiv (affineOutcomeKernel base theta0 tau xt)
        (affineOutcomeKernel base theta1 tau xt) ≤
      ENNReal.ofReal
        ((((theta1 - theta0) * (xt.2 - base.g0 xt.1)) ^ 2) /
          (2 * tau ^ 2)) := by
  rw [affineOutcomeKernel_apply, affineOutcomeKernel_apply_eq_shifted]
  let d := (theta1 - theta0) * (xt.2 - base.g0 xt.1)
  calc
    InformationTheory.klDiv
        ((gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩).map
          (fun z ↦ affineOutcomeMechanism base theta0 (xt, z)))
        ((gaussianReal d ⟨tau ^ 2, sq_nonneg tau⟩).map
          (fun z ↦ affineOutcomeMechanism base theta0 (xt, z))) ≤
        InformationTheory.klDiv
          (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩)
          (gaussianReal d ⟨tau ^ 2, sq_nonneg tau⟩) :=
      Causalean.Mathlib.InformationTheory.Measure.klDiv_map_le
        ((affineOutcomeMechanism_measurable base theta0).comp
          (measurable_const.prodMk measurable_id))
    _ = ENNReal.ofReal ((0 - d) ^ 2 / (2 * (⟨tau ^ 2, sq_nonneg tau⟩ : NNReal) : ℝ)) := by
      apply Causalean.Mathlib.InformationTheory.gaussianKL_eq
      exact_mod_cast sq_pos_of_pos htau
    _ = ENNReal.ofReal
        ((((theta1 - theta0) * (xt.2 - base.g0 xt.1)) ^ 2) /
          (2 * tau ^ 2)) := by
      congr 1
      simp [d]

/-- The treatment innovation has an integrable square under the exact
Luxemburg assumption. -/
-- @node: eta_sq_integrable
lemma eta_sq_integrable {p : Parameters} (base : Model (Xspace := Xspace) p)
    (heta : EtaSubGaussian p base) :
    Integrable (fun o ↦ (eta p base o) ^ 2) base.P := by
  have hpsi : 0 < p.psieta := p.constants_pos.2.2.2.1
  have hmeas : AEStronglyMeasurable (fun o ↦ (eta p base o) ^ 2) base.P := by
    apply Measurable.aestronglyMeasurable
    unfold eta treatment covariate
    exact (measurable_snd.fst.sub
      (base.g0_measurable.comp measurable_fst)).pow_const 2
  let c := max 1 (p.psieta ^ 2)
  have hg : Integrable
      (fun o ↦ c * Real.exp ((eta p base o) ^ 2 / p.psieta ^ 2)) base.P :=
    heta.1.const_mul c
  refine hg.mono' hmeas ?_
  filter_upwards with o
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hx : 0 ≤ eta p base o ^ 2 / p.psieta ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hseries := Real.add_one_le_exp (eta p base o ^ 2 / p.psieta ^ 2)
  have hpsi2 : 0 < p.psieta ^ 2 := sq_pos_of_pos hpsi
  calc
    eta p base o ^ 2 = p.psieta ^ 2 * (eta p base o ^ 2 / p.psieta ^ 2) := by
      field_simp
    _ ≤ p.psieta ^ 2 * Real.exp (eta p base o ^ 2 / p.psieta ^ 2) := by
      gcongr
      linarith
    _ ≤ c * Real.exp (eta p base o ^ 2 / p.psieta ^ 2) := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- One observation on the affine Gaussian path has KL bounded by the
parameter displacement squared times the treatment-innovation second moment. -/
-- @node: affineGaussianLaw_kl_le
lemma affineGaussianLaw_kl_le {p : Parameters}
    (base : Model (Xspace := Xspace) p) (heta : EtaSubGaussian p base)
    (theta0 theta1 tau : ℝ)
    (htau : 0 < tau) :
    InformationTheory.klDiv (affineGaussianLaw base theta0 tau)
        (affineGaussianLaw base theta1 tau) ≤
      ENNReal.ofReal (((theta1 - theta0) ^ 2 *
        (2 * p.psieta ^ 2)) / (2 * tau ^ 2)) := by
  let v : NNReal := ⟨tau ^ 2, sq_nonneg tau⟩
  let k0 := shiftedInnovationKernel base theta0 theta0 tau
  let k1 := shiftedInnovationKernel base theta1 theta0 tau
  have hv : v ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact (sq_pos_of_pos htau).ne'
  have hac : ∀ᵐ xt ∂xtLaw base, k0 xt ≪ k1 xt := by
    filter_upwards with xt
    rw [show k0 xt = gaussianReal 0 v by
      simp [k0, v, shiftedInnovationKernel_apply],
      show k1 xt = gaussianReal
        ((theta1 - theta0) * (xt.2 - base.g0 xt.1)) v by
          simp [k1, v, shiftedInnovationKernel_apply]]
    exact Causalean.Mathlib.InformationTheory.gaussianReal_ac_gaussianReal _ _ hv hv
  rw [affineGaussianLaw_eq_map_shiftedInnovation base theta0 theta0 tau,
    affineGaussianLaw_eq_map_shiftedInnovation base theta1 theta0 tau,
    Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
      (affineOutcomeEquiv base.g0 base.q0 theta0
        base.g0_measurable base.q0_measurable).measurableEmbedding,
    Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac hac]
  have hsquareXT : Integrable (fun xt : XT' Xspace ↦
      (xt.2 - base.g0 xt.1) ^ 2) (xtLaw base) := by
    have hxt : AEMeasurable (fun o : Obs Xspace ↦
        (covariate o, treatment o)) base.P := by
      unfold covariate treatment
      exact (measurable_fst.prodMk measurable_snd.fst).aemeasurable
    have hsq : AEStronglyMeasurable (fun xt : XT' Xspace ↦
        (xt.2 - base.g0 xt.1) ^ 2) (xtLaw base) :=
      ((measurable_snd.sub (base.g0_measurable.comp measurable_fst)).pow_const 2).aestronglyMeasurable
    rw [xtLaw]
    apply (integrable_map_measure (μ := base.P)
      (g := fun xt : XT' Xspace ↦ (xt.2 - base.g0 xt.1) ^ 2)
      hsq hxt).2
    simpa [Function.comp_def, eta, treatment, covariate] using
      eta_sq_integrable base heta
  have hfint : Integrable (fun xt : XT' Xspace ↦
      (((theta1 - theta0) * (xt.2 - base.g0 xt.1)) ^ 2) /
        (2 * tau ^ 2)) (xtLaw base) := by
    convert (hsquareXT.const_mul ((theta1 - theta0) ^ 2 / (2 * tau ^ 2))) using 1
    funext xt
    ring
  have hfiber : ∀ xt : XT' Xspace,
      InformationTheory.klDiv (k0 xt) (k1 xt) =
        ENNReal.ofReal
          ((((theta1 - theta0) * (xt.2 - base.g0 xt.1)) ^ 2) /
            (2 * tau ^ 2)) := by
    intro xt
    rw [show k0 xt = gaussianReal 0 v by
      simp [k0, v, shiftedInnovationKernel_apply],
      show k1 xt = gaussianReal
        ((theta1 - theta0) * (xt.2 - base.g0 xt.1)) v by
          simp [k1, v, shiftedInnovationKernel_apply],
      Causalean.Mathlib.InformationTheory.gaussianKL_eq]
    · congr 1
      have hv' : ((v : NNReal) : ℝ) = tau ^ 2 := rfl
      rw [hv']
      ring
    · exact_mod_cast sq_pos_of_pos htau
  simp_rw [hfiber]
  rw [← ofReal_integral_eq_lintegral_ofReal hfint
    (Filter.Eventually.of_forall fun _ ↦ by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ xt, (((theta1 - theta0) * (xt.2 - base.g0 xt.1)) ^ 2) /
        (2 * tau ^ 2) ∂xtLaw base) =
        ((theta1 - theta0) ^ 2 / (2 * tau ^ 2)) *
          ∫ xt, (xt.2 - base.g0 xt.1) ^ 2 ∂xtLaw base := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with xt
            ring
    _ = ((theta1 - theta0) ^ 2 / (2 * tau ^ 2)) *
          ∫ o, |eta p base o| ^ (2 * 1) ∂base.P := by
            congr 1
            rw [xtLaw, integral_map
              (show AEMeasurable (fun o : Obs Xspace ↦
                (covariate o, treatment o)) base.P by
                  unfold covariate treatment
                  exact (measurable_fst.prodMk measurable_snd.fst).aemeasurable)
              (show AEStronglyMeasurable (fun xt : XT' Xspace ↦
                (xt.2 - base.g0 xt.1) ^ 2)
                  (base.P.map fun o ↦ (covariate o, treatment o)) by
                    exact ((measurable_snd.sub
                      (base.g0_measurable.comp measurable_fst)).pow_const 2).aestronglyMeasurable)]
            apply integral_congr_ae
            filter_upwards with o
            simp [eta, treatment, covariate, sq_abs]
    _ ≤ ((theta1 - theta0) ^ 2 / (2 * tau ^ 2)) *
          (2 * p.psieta ^ (2 * 1) * (1 : ℕ).factorial) := by
            gcongr
            exact luxemburg_even_moment_integral_le (eta p base)
              (by unfold eta treatment covariate
                  exact measurable_snd.fst.sub (base.g0_measurable.comp measurable_fst))
              p.constants_pos.2.2.2.1 heta.1 heta.2 1
    _ = ((theta1 - theta0) ^ 2 * (2 * p.psieta ^ 2)) /
          (2 * tau ^ 2) := by norm_num; ring

/-- Tensorization turns the one-observation affine-path bound into the
corresponding finite i.i.d. KL budget. -/
-- @node: affineGaussianModel_iid_kl_le
lemma affineGaussianModel_iid_kl_le {p : Parameters}
    (base : Model (Xspace := Xspace) p) (sampleN : ℕ)
    (heta : EtaSubGaussian p base) (theta0 theta1 tau : ℝ)
    (htau : 0 < tau) :
    InformationTheory.klDiv
        (iidLaw (affineGaussianModel base theta0 tau) sampleN)
        (iidLaw (affineGaussianModel base theta1 tau) sampleN) ≤
      ENNReal.ofReal ((sampleN : ℝ) *
        (((theta1 - theta0) ^ 2 * (2 * p.psieta ^ 2)) /
          (2 * tau ^ 2))) := by
  let μ := affineGaussianLaw base theta0 tau
  let ν := affineGaussianLaw base theta1 tau
  let B := ((theta1 - theta0) ^ 2 * (2 * p.psieta ^ 2)) / (2 * tau ^ 2)
  have hsingle : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal B := by
    dsimp [μ, ν, B]
    exact affineGaussianLaw_kl_le base heta theta0 theta1 tau htau
  have hfinite : InformationTheory.klDiv μ ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsingle
  have hac : μ ≪ ν := (InformationTheory.klDiv_ne_top_iff.mp hfinite).1
  have hint : Integrable (llr μ ν) μ :=
    (InformationTheory.klDiv_ne_top_iff.mp hfinite).2
  have htensor := (Causalean.Mathlib.InformationTheory.productKL_tensorization
    sampleN μ ν hac hint).apply
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hsingleReal : (InformationTheory.klDiv μ ν).toReal ≤ B := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsingle
    simpa [ENNReal.toReal_ofReal hB] using h
  have hprodFinite :=
    (Causalean.Mathlib.InformationTheory.productKL_tensorization
      sampleN μ ν hac hint).product_ne_top
  change InformationTheory.klDiv
    (Measure.pi fun _ : Fin sampleN ↦ μ)
    (Measure.pi fun _ : Fin sampleN ↦ ν) ≤ ENNReal.ofReal ((sampleN : ℝ) * B)
  rw [← ENNReal.toReal_le_toReal hprodFinite ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hB)]
  calc
    (InformationTheory.klDiv
      (Measure.pi fun _ : Fin sampleN ↦ μ)
      (Measure.pi fun _ : Fin sampleN ↦ ν)).toReal ≤
        (sampleN : ℝ) * (InformationTheory.klDiv μ ν).toReal := htensor
    _ ≤ (sampleN : ℝ) * B :=
      mul_le_mul_of_nonneg_left hsingleReal (Nat.cast_nonneg _)

end CausalSmith.Stat.SaPlmCumulantConverse
