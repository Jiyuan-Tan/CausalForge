import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import Causalean.Mathlib.InformationTheory.GaussianKL
import Causalean.Mathlib.InformationTheory.KLBind
import Causalean.Mathlib.InformationTheory.ProductKLLeCam
import Causalean.Stat.Minimax.LeCamTwoPoint
import Mathlib.Probability.ConditionalExpectation

/-!
# Affine Gaussian outcome paths

Measure-theoretic infrastructure for replacing the outcome coordinate by an
affine partially-linear signal plus independent Gaussian noise while retaining
the joint covariate-treatment law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- A conditional-mean identity is determined by the joint law of the
conditioning variable and the integrand. -/
lemma condExp_comp_eq_of_map_prod_eq
    {Omega : Type*} [MeasurableSpace Omega]
    {S : Type*} [MeasurableSpace S]
    (mu nu : Measure Omega) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (X : Omega → S) (Y : Omega → ℝ) (g : S → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hg : Measurable g)
    (hYmu : Integrable Y mu) (hYnu : Integrable Y nu)
    (hgnu : Integrable (fun omega ↦ g (X omega)) nu)
    (hlaw : mu.map (fun omega ↦ (X omega, Y omega)) =
      nu.map (fun omega ↦ (X omega, Y omega)))
    (hcond : @MeasureTheory.condExp Omega ℝ
      (MeasurableSpace.comap X inferInstance) inferInstance _ _ mu Y
        =ᵐ[mu] fun omega ↦ g (X omega)) :
    @MeasureTheory.condExp Omega ℝ
      (MeasurableSpace.comap X inferInstance) inferInstance _ _ nu Y
        =ᵐ[nu] fun omega ↦ g (X omega) := by
  have hpair : Measurable (fun omega ↦ (X omega, Y omega)) := hX.prodMk hY
  symm
  apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hYnu
  · intro s _ _
    exact hgnu.integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    have hprod : MeasurableSet (t ×ˢ (Set.univ : Set ℝ)) := ht.prod MeasurableSet.univ
    calc
      ∫ omega in X ⁻¹' t, g (X omega) ∂nu =
          ∫ z in t ×ˢ (Set.univ : Set ℝ), g z.1
            ∂(nu.map fun omega ↦ (X omega, Y omega)) := by
              simpa [Function.comp_def, Set.mk_preimage_prod] using
                (MeasureTheory.setIntegral_map hprod
                  (hg.comp measurable_fst).aestronglyMeasurable
                  hpair.aemeasurable).symm
      _ = ∫ z in t ×ˢ (Set.univ : Set ℝ), g z.1
            ∂(mu.map fun omega ↦ (X omega, Y omega)) := by rw [hlaw]
      _ = ∫ omega in X ⁻¹' t, g (X omega) ∂mu := by
              simpa [Function.comp_def, Set.mk_preimage_prod] using
                MeasureTheory.setIntegral_map hprod
                  (hg.comp measurable_fst).aestronglyMeasurable hpair.aemeasurable
      _ = ∫ omega in X ⁻¹' t,
            (@MeasureTheory.condExp Omega ℝ
              (MeasurableSpace.comap X inferInstance) inferInstance _ _ mu Y) omega ∂mu := by
              exact MeasureTheory.integral_congr_ae
                hcond.symm.restrict
      _ = ∫ omega in X ⁻¹' t, Y omega ∂mu := by
              rw [MeasureTheory.setIntegral_condExp hX.comap_le hYmu
                (show MeasurableSet[MeasurableSpace.comap X inferInstance]
                  (X ⁻¹' t) from ⟨t, ht, rfl⟩)]
      _ = ∫ z in t ×ˢ (Set.univ : Set ℝ), z.2
            ∂(mu.map fun omega ↦ (X omega, Y omega)) := by
              simpa [Function.comp_def, Set.mk_preimage_prod] using
                (MeasureTheory.setIntegral_map hprod
                  measurable_snd.aestronglyMeasurable hpair.aemeasurable).symm
      _ = ∫ z in t ×ˢ (Set.univ : Set ℝ), z.2
            ∂(nu.map fun omega ↦ (X omega, Y omega)) := by rw [← hlaw]
      _ = ∫ omega in X ⁻¹' t, Y omega ∂nu := by
              simpa [Function.comp_def, Set.mk_preimage_prod] using
                MeasureTheory.setIntegral_map hprod
                  measurable_snd.aestronglyMeasurable hpair.aemeasurable
  · have hX' : Measurable[MeasurableSpace.comap X inferInstance] X :=
      measurable_iff_comap_le.mpr le_rfl
    exact (hg.comp hX').aestronglyMeasurable

private abbrev XT (Xspace : Type*) := Xspace × ℝ

private lemma measurable_covariate : Measurable (covariate : Obs Xspace → Xspace) := by
  exact measurable_fst

private lemma measurable_treatment : Measurable (treatment : Obs Xspace → ℝ) := by
  exact measurable_fst.comp measurable_snd

private lemma measurable_outcome : Measurable (outcome : Obs Xspace → ℝ) := by
  exact measurable_snd.comp measurable_snd

private lemma measurable_xt :
    Measurable (fun o : Obs Xspace ↦ (covariate o, treatment o)) :=
  measurable_covariate.prodMk measurable_treatment

/-- The measurable coordinate change from `(X,T,Z)` to `(X,T,Y)` for an
affine Gaussian outcome path. -/
def affineOutcomeEquiv (g q : Xspace → ℝ) (theta : ℝ)
    (hg : Measurable g) (hq : Measurable q) :
    (XT Xspace × ℝ) ≃ᵐ Obs Xspace where
  toEquiv :=
    { toFun := fun w ↦ (w.1.1, w.1.2, q w.1.1 + theta * (w.1.2 - g w.1.1) + w.2)
      invFun := fun o ↦ ((covariate o, treatment o),
        outcome o - q (covariate o) - theta * (treatment o - g (covariate o)))
      left_inv := by
        intro w
        ext <;> simp [covariate, treatment, outcome]
        ring
      right_inv := by
        intro o
        rcases o with ⟨x, t, y⟩
        ext <;> simp [covariate, treatment, outcome] }
  measurable_toFun := by
    have hx : Measurable (fun w : XT Xspace × ℝ ↦ w.1.1) :=
      measurable_fst.comp measurable_fst
    have ht : Measurable (fun w : XT Xspace × ℝ ↦ w.1.2) :=
      measurable_snd.comp measurable_fst
    have hy : Measurable (fun w : XT Xspace × ℝ ↦
        q w.1.1 + theta * (w.1.2 - g w.1.1) + w.2) :=
      ((hq.comp hx).add (measurable_const.mul (ht.sub (hg.comp hx)))).add measurable_snd
    exact hx.prodMk (ht.prodMk hy)
  measurable_invFun := by
    exact measurable_xt.prodMk <|
      (measurable_outcome.sub (hq.comp measurable_covariate)).sub
        (measurable_const.mul (measurable_treatment.sub (hg.comp measurable_covariate)))

/-- The fixed covariate-treatment marginal used by an affine outcome path. -/
def xtLaw {p : Parameters} (base : Model (Xspace := Xspace) p) : Measure (XT Xspace) :=
  base.P.map (fun o ↦ (covariate o, treatment o))

/-- The covariate–treatment marginal of a base model is again a probability
distribution: discarding the outcome coordinate from an observed-data law leaves
a law of total mass one on covariate–treatment pairs. -/
instance xtLaw_isProbabilityMeasure {p : Parameters}
    (base : Model (Xspace := Xspace) p) : IsProbabilityMeasure (xtLaw base) := by
  exact Measure.isProbabilityMeasure_map measurable_xt.aemeasurable

/-- The Gaussian law with mean `mu` and variance `tau ^ 2` is a probability
measure.

This restates the Mathlib instance for the specific variance literal
`⟨tau ^ 2, sq_nonneg tau⟩`.  Instance synthesis runs at instance transparency,
where the anonymous-constructor term is not recognised as an `ℝ≥0`, so the
generic instance is not applicable to it; naming the instance explicitly
elaborates the argument at default transparency and makes the fact available to
downstream synthesis. -/
instance gaussianReal_sq_isProbabilityMeasure (mu tau : ℝ) :
    IsProbabilityMeasure (gaussianReal mu ⟨tau ^ 2, sq_nonneg tau⟩) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _

/-- The observed-data law obtained by adjoining centered Gaussian noise and
applying the affine outcome coordinate change. -/
def affineGaussianLaw {p : Parameters} (base : Model (Xspace := Xspace) p)
    (theta tau : ℝ) : Measure (Obs Xspace) :=
  ((xtLaw base).prod (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩)).map
    (affineOutcomeEquiv base.g0 base.q0 theta base.g0_measurable base.q0_measurable)

/-- The observed-data law of an affine Gaussian outcome path is a probability
distribution: it couples the base covariate–treatment marginal with an
independent centered Gaussian noise draw of standard deviation `tau` and then
relabels coordinates by a measurable bijection, and neither step changes total
mass. -/
instance affineGaussianLaw_isProbabilityMeasure {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    IsProbabilityMeasure (affineGaussianLaw base theta tau) := by
  unfold affineGaussianLaw xtLaw
  haveI : IsProbabilityMeasure
      (base.P.map (fun o ↦ (covariate o, treatment o))) :=
    Measure.isProbabilityMeasure_map measurable_xt.aemeasurable
  exact Measure.isProbabilityMeasure_map
    (affineOutcomeEquiv base.g0 base.q0 theta
      base.g0_measurable base.q0_measurable).measurable.aemeasurable

/-- An affine Gaussian outcome law retains the base joint `(X,T)` marginal. -/
lemma affineGaussianLaw_map_xt {p : Parameters} (base : Model (Xspace := Xspace) p)
    (theta tau : ℝ) :
    (affineGaussianLaw base theta tau).map
        (fun o ↦ (covariate o, treatment o)) = xtLaw base := by
  rw [affineGaussianLaw, Measure.map_map]
  · have hf : (fun o ↦ (covariate o, treatment o)) ∘
        affineOutcomeEquiv base.g0 base.q0 theta
          base.g0_measurable base.q0_measurable = Prod.fst := by
      funext w
      rfl
    rw [hf, Measure.map_fst_prod, measure_univ, one_smul]
  · exact measurable_xt
  · exact (affineOutcomeEquiv base.g0 base.q0 theta
      base.g0_measurable base.q0_measurable).measurable

/-- Treatment remains integrable along the affine Gaussian outcome path. -/
lemma affineGaussianLaw_treatment_integrable {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    Integrable treatment (affineGaussianLaw base theta tau) := by
  have hbase : Integrable (fun z : XT Xspace ↦ z.2) (xtLaw base) := by
    rw [xtLaw]
    exact (integrable_map_measure measurable_snd.aestronglyMeasurable
      measurable_xt.aemeasurable).mpr (by
        simpa [Function.comp_def, treatment] using base.treatment_integrable)
  have hpath : Integrable (fun z : XT Xspace ↦ z.2)
      ((affineGaussianLaw base theta tau).map
        (fun o ↦ (covariate o, treatment o))) := by
    rwa [affineGaussianLaw_map_xt]
  simpa [Function.comp_def] using hpath.comp_aemeasurable measurable_xt.aemeasurable

/-- The supplied treatment regression remains integrable along the affine
Gaussian outcome path. -/
lemma affineGaussianLaw_g0_integrable {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    Integrable (fun o ↦ base.g0 (covariate o))
      (affineGaussianLaw base theta tau) := by
  have hbase : Integrable (fun o ↦ base.g0 (covariate o)) base.P :=
    MeasureTheory.integrable_condExp.congr base.g0_condMean
  have hxt : Integrable (fun z : XT Xspace ↦ base.g0 z.1) (xtLaw base) := by
    rw [xtLaw]
    exact (integrable_map_measure
      (base.g0_measurable.comp measurable_fst).aestronglyMeasurable
      measurable_xt.aemeasurable).mpr (by
        simpa [Function.comp_def] using hbase)
  have hpath : Integrable (fun z : XT Xspace ↦ base.g0 z.1)
      ((affineGaussianLaw base theta tau).map
        (fun o ↦ (covariate o, treatment o))) := by
    rwa [affineGaussianLaw_map_xt]
  simpa [Function.comp_def] using hpath.comp_aemeasurable measurable_xt.aemeasurable

/-- The supplied outcome regression remains integrable along the affine
Gaussian outcome path. -/
lemma affineGaussianLaw_q0_integrable {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    Integrable (fun o ↦ base.q0 (covariate o))
      (affineGaussianLaw base theta tau) := by
  have hbase : Integrable (fun o ↦ base.q0 (covariate o)) base.P :=
    MeasureTheory.integrable_condExp.congr base.q0_condMean
  have hxt : Integrable (fun z : XT Xspace ↦ base.q0 z.1) (xtLaw base) := by
    rw [xtLaw]
    exact (integrable_map_measure
      (base.q0_measurable.comp measurable_fst).aestronglyMeasurable
      measurable_xt.aemeasurable).mpr (by
        simpa [Function.comp_def] using hbase)
  have hpath : Integrable (fun z : XT Xspace ↦ base.q0 z.1)
      ((affineGaussianLaw base theta tau).map
        (fun o ↦ (covariate o, treatment o))) := by
    rwa [affineGaussianLaw_map_xt]
  simpa [Function.comp_def] using hpath.comp_aemeasurable measurable_xt.aemeasurable

/-- The treatment conditional mean is unchanged by replacing only the outcome
channel with the affine Gaussian channel. -/
lemma affineGaussianLaw_g0_condMean {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _
      (affineGaussianLaw base theta tau) treatment
        =ᵐ[affineGaussianLaw base theta tau]
          fun o ↦ base.g0 (covariate o) := by
  apply condExp_comp_eq_of_map_prod_eq base.P (affineGaussianLaw base theta tau)
    covariate treatment base.g0 measurable_covariate measurable_treatment
      base.g0_measurable base.treatment_integrable
      (affineGaussianLaw_treatment_integrable base theta tau)
      (affineGaussianLaw_g0_integrable base theta tau)
  · simpa [xtLaw] using (affineGaussianLaw_map_xt base theta tau).symm
  · exact base.g0_condMean

/-- Under the affine law, algebraically extracting the residual returns the
fresh Gaussian coordinate. -/
lemma affineGaussianLaw_map_residual {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianLaw base theta tau).map
        (fun o ↦ outcome o - base.q0 (covariate o) -
          theta * (treatment o - base.g0 (covariate o))) =
      gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩ := by
  rw [affineGaussianLaw, Measure.map_map]
  · have hf : (fun o ↦ outcome o - base.q0 (covariate o) -
          theta * (treatment o - base.g0 (covariate o))) ∘
        affineOutcomeEquiv base.g0 base.q0 theta
          base.g0_measurable base.q0_measurable = Prod.snd := by
      funext w
      change (base.q0 w.1.1 + theta * (w.1.2 - base.g0 w.1.1) + w.2) -
        base.q0 w.1.1 - theta * (w.1.2 - base.g0 w.1.1) = w.2
      ring
    rw [hf, Measure.map_snd_prod, measure_univ, one_smul]
  · exact (measurable_outcome.sub (base.q0_measurable.comp measurable_covariate)).sub
      (measurable_const.mul
        (measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)))
  · exact (affineOutcomeEquiv base.g0 base.q0 theta
      base.g0_measurable base.q0_measurable).measurable

/-- The extracted Gaussian residual is integrable. -/
lemma affineGaussianLaw_residual_integrable {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    Integrable
      (fun o ↦ outcome o - base.q0 (covariate o) -
        theta * (treatment o - base.g0 (covariate o)))
      (affineGaussianLaw base theta tau) := by
  have hgauss : Integrable (fun z : ℝ ↦ z)
      (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩) := by
    exact (memLp_id_gaussianReal (μ := 0) (v := ⟨tau ^ 2, sq_nonneg tau⟩) 1).integrable
      (by norm_num)
  rw [← affineGaussianLaw_map_residual base theta tau] at hgauss
  simpa [Function.comp_def] using hgauss.comp_aemeasurable
    ((measurable_outcome.sub (base.q0_measurable.comp measurable_covariate)).sub
      (measurable_const.mul
        (measurable_treatment.sub
          (base.g0_measurable.comp measurable_covariate)))).aemeasurable

/-- Outcomes are integrable under the affine Gaussian outcome path. -/
lemma affineGaussianLaw_outcome_integrable {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    Integrable outcome (affineGaussianLaw base theta tau) := by
  have heta : Integrable
      (fun o ↦ treatment o - base.g0 (covariate o))
      (affineGaussianLaw base theta tau) :=
    (affineGaussianLaw_treatment_integrable base theta tau).sub
      (affineGaussianLaw_g0_integrable base theta tau)
  have hsum := ((affineGaussianLaw_q0_integrable base theta tau).add
    (heta.const_mul theta)).add (affineGaussianLaw_residual_integrable base theta tau)
  exact hsum.congr (Filter.Eventually.of_forall fun o ↦ by
    simp only [Pi.add_apply]
    ring)

/-- The extracted Gaussian residual is independent of `(X,T)`. -/
lemma affineGaussianLaw_indep_residual_xt {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    IndepFun
      (fun o ↦ outcome o - base.q0 (covariate o) -
        theta * (treatment o - base.g0 (covariate o)))
      (fun o ↦ (covariate o, treatment o))
      (affineGaussianLaw base theta tau) := by
  have hres : Measurable (fun o : Obs Xspace ↦
      outcome o - base.q0 (covariate o) -
        theta * (treatment o - base.g0 (covariate o))) :=
    (measurable_outcome.sub (base.q0_measurable.comp measurable_covariate)).sub
      (measurable_const.mul
        (measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)))
  rw [indepFun_iff_map_prod_eq_prod_map_map hres.aemeasurable measurable_xt.aemeasurable]
  unfold affineGaussianLaw
  rw [Measure.map_map, Measure.map_map, Measure.map_map]
  · have hprod : IndepFun (Prod.snd : XT Xspace × ℝ → ℝ) Prod.fst
        ((xtLaw base).prod (gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩)) := by
      exact (indepFun_prod measurable_id measurable_id).symm
    have hf : (fun o ↦ outcome o - base.q0 (covariate o) -
          theta * (treatment o - base.g0 (covariate o))) ∘
        affineOutcomeEquiv base.g0 base.q0 theta
          base.g0_measurable base.q0_measurable = Prod.snd := by
      funext w
      change (base.q0 w.1.1 + theta * (w.1.2 - base.g0 w.1.1) + w.2) -
        base.q0 w.1.1 - theta * (w.1.2 - base.g0 w.1.1) = w.2
      ring
    have hg : (fun o ↦ (covariate o, treatment o)) ∘
        affineOutcomeEquiv base.g0 base.q0 theta
          base.g0_measurable base.q0_measurable = Prod.fst := by
      funext w
      rfl
    rw [hf, hg]
    have hpair : (fun ω ↦
        (outcome ω - base.q0 (covariate ω) -
          theta * (treatment ω - base.g0 (covariate ω)),
          covariate ω, treatment ω)) ∘
        affineOutcomeEquiv base.g0 base.q0 theta
          base.g0_measurable base.q0_measurable =
        fun w : XT Xspace × ℝ ↦ (w.2, w.1) := by
      funext w
      apply Prod.ext
      · change (base.q0 w.1.1 + theta * (w.1.2 - base.g0 w.1.1) + w.2) -
          base.q0 w.1.1 - theta * (w.1.2 - base.g0 w.1.1) = w.2
        ring
      · rfl
    rw [hpair]
    exact (indepFun_iff_map_prod_eq_prod_map_map
      measurable_snd.aemeasurable measurable_fst.aemeasurable).mp hprod
  all_goals first
    | exact hres.prodMk measurable_xt
    | exact hres
    | exact measurable_xt
    | exact (affineOutcomeEquiv base.g0 base.q0 theta
        base.g0_measurable base.q0_measurable).measurable

/-- The extracted residual has conditional mean zero given the covariate. -/
lemma affineGaussianLaw_residual_condMean_zero {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _
      (affineGaussianLaw base theta tau)
      (fun o ↦ outcome o - base.q0 (covariate o) -
        theta * (treatment o - base.g0 (covariate o)))
        =ᵐ[affineGaussianLaw base theta tau] 0 := by
  let res : Obs Xspace → ℝ := fun o ↦
    outcome o - base.q0 (covariate o) -
      theta * (treatment o - base.g0 (covariate o))
  have hres : Measurable res :=
    (measurable_outcome.sub (base.q0_measurable.comp measurable_covariate)).sub
      (measurable_const.mul
        (measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)))
  have hind : IndepFun res covariate (affineGaussianLaw base theta tau) := by
    have h := (affineGaussianLaw_indep_residual_xt base theta tau).comp
      measurable_id measurable_fst
    simpa [Function.comp_def, res] using h
  have hmean : ∫ o, res o ∂(affineGaussianLaw base theta tau) = 0 := by
    have hmap := integral_map (μ := affineGaussianLaw base theta tau)
      (φ := res) (f := fun z : ℝ ↦ z)
      hres.aemeasurable stronglyMeasurable_id.aestronglyMeasurable
    rw [affineGaussianLaw_map_residual base theta tau] at hmap
    exact ((integral_id_gaussianReal (μ := 0)
      (v := ⟨tau ^ 2, sq_nonneg tau⟩)).symm.trans hmap).symm
  have hstrong : StronglyMeasurable[MeasurableSpace.comap res inferInstance] res := by
    exact (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  change Indep (MeasurableSpace.comap res inferInstance)
    (MeasurableSpace.comap covariate inferInstance)
    (affineGaussianLaw base theta tau) at hind
  have hce := MeasureTheory.condExp_indep_eq
    (μ := affineGaussianLaw base theta tau)
    (m₁ := MeasurableSpace.comap res inferInstance)
    (m₂ := MeasurableSpace.comap covariate inferInstance)
    (f := res) (by exact hres.comap_le) (by exact measurable_covariate.comap_le)
      hstrong hind
  simpa [res, hmean, Pi.zero_def] using hce

/-- Treatment residuals have conditional mean zero given the covariate along
the affine Gaussian path. -/
lemma affineGaussianLaw_eta_condMean_zero {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _
      (affineGaussianLaw base theta tau)
      (fun o ↦ treatment o - base.g0 (covariate o))
        =ᵐ[affineGaussianLaw base theta tau] 0 := by
  let mu := affineGaussianLaw base theta tau
  have hgint := affineGaussianLaw_g0_integrable base theta tau
  have hgm : StronglyMeasurable[MeasurableSpace.comap covariate inferInstance]
      (fun o ↦ base.g0 (covariate o)) := by
    have hcov : @Measurable (Obs Xspace) Xspace
        (MeasurableSpace.comap covariate inferInstance) inferInstance covariate :=
      measurable_iff_comap_le.mpr le_rfl
    exact (base.g0_measurable.comp hcov).stronglyMeasurable
  have hgce : @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ mu
      (fun o ↦ base.g0 (covariate o)) = fun o ↦ base.g0 (covariate o) :=
    MeasureTheory.condExp_of_stronglyMeasurable measurable_covariate.comap_le hgm hgint
  have hsub := MeasureTheory.condExp_sub
      (μ := affineGaussianLaw base theta tau)
      (f := treatment) (g := fun o ↦ base.g0 (covariate o))
      (affineGaussianLaw_treatment_integrable base theta tau) hgint
      (MeasurableSpace.comap covariate inferInstance)
  exact (by
    filter_upwards [hsub, affineGaussianLaw_g0_condMean base theta tau] with o hs ht
    calc
      (affineGaussianLaw base theta tau)[fun o ↦
          treatment o - base.g0 (covariate o) |
          MeasurableSpace.comap covariate inferInstance] o =
          (affineGaussianLaw base theta tau)[treatment |
              MeasurableSpace.comap covariate inferInstance] o -
            (affineGaussianLaw base theta tau)[fun o ↦ base.g0 (covariate o) |
              MeasurableSpace.comap covariate inferInstance] o := by
                exact hs
      _ = 0 := by rw [ht, hgce]; simp)

/-- The affine Gaussian outcome has conditional mean `q0(X)`. -/
lemma affineGaussianLaw_q0_condMean {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _
      (affineGaussianLaw base theta tau) outcome
        =ᵐ[affineGaussianLaw base theta tau]
          fun o ↦ base.q0 (covariate o) := by
  let mu := affineGaussianLaw base theta tau
  let eta0 : Obs Xspace → ℝ := fun o ↦ treatment o - base.g0 (covariate o)
  let res : Obs Xspace → ℝ := fun o ↦
    outcome o - base.q0 (covariate o) - theta * eta0 o
  have hqint := affineGaussianLaw_q0_integrable base theta tau
  have heta : Integrable eta0 mu :=
    (affineGaussianLaw_treatment_integrable base theta tau).sub
      (affineGaussianLaw_g0_integrable base theta tau)
  have hres : Integrable res mu := affineGaussianLaw_residual_integrable base theta tau
  have hqmeas : StronglyMeasurable[MeasurableSpace.comap covariate inferInstance]
      (fun o ↦ base.q0 (covariate o)) := by
    have hcov : @Measurable (Obs Xspace) Xspace
        (MeasurableSpace.comap covariate inferInstance) inferInstance covariate :=
      measurable_iff_comap_le.mpr le_rfl
    exact (base.q0_measurable.comp hcov).stronglyMeasurable
  have hqce : @MeasureTheory.condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ mu
      (fun o ↦ base.q0 (covariate o)) = fun o ↦ base.q0 (covariate o) :=
    MeasureTheory.condExp_of_stronglyMeasurable measurable_covariate.comap_le hqmeas hqint
  have hdecomp : outcome = fun o ↦ base.q0 (covariate o) + theta * eta0 o + res o := by
    funext o
    simp [res]
  rw [hdecomp]
  have hsmul := MeasureTheory.condExp_smul
    (μ := mu) theta eta0 (MeasurableSpace.comap covariate inferInstance)
  have hmul : mu[fun x ↦ theta * eta0 x |
      MeasurableSpace.comap covariate inferInstance] =ᵐ[mu]
        fun x ↦ theta * mu[eta0 | MeasurableSpace.comap covariate inferInstance] x := by
    exact hsmul
  filter_upwards [MeasureTheory.condExp_add (hqint.add (heta.const_mul theta)) hres
      (MeasurableSpace.comap covariate inferInstance),
    MeasureTheory.condExp_add hqint (heta.const_mul theta)
      (MeasurableSpace.comap covariate inferInstance),
    hmul,
    affineGaussianLaw_eta_condMean_zero base theta tau,
    affineGaussianLaw_residual_condMean_zero base theta tau] with o ha hb hc he hr
  have he' : mu[eta0 | MeasurableSpace.comap covariate inferInstance] o = 0 := by
    simpa [eta0] using he
  have hr' : mu[res | MeasurableSpace.comap covariate inferInstance] o = 0 := by
    simpa [res, eta0] using hr
  calc
      mu[fun o ↦ base.q0 (covariate o) + theta * eta0 o + res o |
          MeasurableSpace.comap covariate inferInstance] o
          = (mu[(fun o ↦ base.q0 (covariate o)) + (fun x ↦ theta * eta0 x) |
              MeasurableSpace.comap covariate inferInstance] +
            mu[res | MeasurableSpace.comap covariate inferInstance]) o := by
              exact ha
      _ = ((mu[fun o ↦ base.q0 (covariate o) |
              MeasurableSpace.comap covariate inferInstance]) +
            mu[fun x ↦ theta * eta0 x | MeasurableSpace.comap covariate inferInstance] +
            mu[res | MeasurableSpace.comap covariate inferInstance]) o := by
              simpa only [Pi.add_apply] using
                congrArg (fun z ↦ z + mu[res |
                  MeasurableSpace.comap covariate inferInstance] o) hb
      _ = base.q0 (covariate o) := by
              simp only [Pi.add_apply]
              rw [hc, hqce, he', hr']
              ring

/-- The model obtained by keeping every supplied nuisance component fixed and
replacing the outcome channel by affine Gaussian noise. -/
def affineGaussianModel {p : Parameters} (base : Model (Xspace := Xspace) p)
    (theta tau : ℝ) : Model (Xspace := Xspace) p where
  P := affineGaussianLaw base theta tau
  probability := affineGaussianLaw_isProbabilityMeasure base theta tau
  theta0 := theta
  g0 := base.g0
  q0 := base.q0
  gcode := base.gcode
  qcode := base.qcode
  g0_measurable := base.g0_measurable
  q0_measurable := base.q0_measurable
  gcode_measurable := base.gcode_measurable
  qcode_measurable := base.qcode_measurable
  treatment_integrable := affineGaussianLaw_treatment_integrable base theta tau
  outcome_integrable := affineGaussianLaw_outcome_integrable base theta tau
  g0_condMean := affineGaussianLaw_g0_condMean base theta tau
  q0_condMean := affineGaussianLaw_q0_condMean base theta tau

/-- Rebuilding a model along the affine Gaussian outcome path at slope `theta`
and noise scale `tau` [makes `theta` the treatment-effect parameter of the new
model](goal). -/
@[simp] lemma affineGaussianModel_theta0 {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).theta0 = theta := rfl

/-- Rebuilding a model along the affine Gaussian outcome path [leaves the
treatment regression — the conditional mean of treatment given the covariate —
exactly the one carried by the base model](goal). -/
@[simp] lemma affineGaussianModel_g0 {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).g0 = base.g0 := rfl

/-- Rebuilding a model along the affine Gaussian outcome path [leaves the
outcome regression — the conditional mean of the outcome given the covariate —
exactly the one carried by the base model](goal). -/
@[simp] lemma affineGaussianModel_q0 {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).q0 = base.q0 := rfl

/-- Rebuilding a model along the affine Gaussian outcome path [carries over the
supplied sequence of treatment-regression estimates unchanged](goal). -/
@[simp] lemma affineGaussianModel_gcode {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).gcode = base.gcode := rfl

/-- Rebuilding a model along the affine Gaussian outcome path [carries over the
supplied sequence of outcome-regression estimates unchanged](goal). -/
@[simp] lemma affineGaussianModel_qcode {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).qcode = base.qcode := rfl

/-- The model-level outcome residual is exactly the extracted fresh Gaussian
coordinate. -/
lemma affineGaussianModel_xi {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    xi p (affineGaussianModel base theta tau) =
      fun o ↦ outcome o - base.q0 (covariate o) -
        theta * (treatment o - base.g0 (covariate o)) := rfl

/-- The model-level treatment residual is unchanged. -/
lemma affineGaussianModel_eta {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    eta p (affineGaussianModel base theta tau) = eta p base := rfl

/-- The affine model residual has the prescribed centered Gaussian law. -/
lemma affineGaussianModel_map_xi {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).P.map
        (xi p (affineGaussianModel base theta tau)) =
      gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩ := by
  exact affineGaussianLaw_map_residual base theta tau

/-- The affine model residual is independent of the retained `(X,T)` pair. -/
lemma affineGaussianModel_indep_xi_xt {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    IndepFun (xi p (affineGaussianModel base theta tau))
      (fun o ↦ (covariate o, treatment o))
      (affineGaussianModel base theta tau).P := by
  exact affineGaussianLaw_indep_residual_xt base theta tau

/-- The affine model satisfies the paper's conditional mean-independence
condition for its outcome residual. -/
lemma affineGaussianModel_outcomeMeanIndependence {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    OutcomeMeanIndependence p (affineGaussianModel base theta tau) := by
  let m := affineGaussianModel base theta tau
  have hxi : Integrable (xi p m) m.P := by
    exact affineGaussianLaw_residual_integrable base theta tau
  refine ⟨hxi, ?_⟩
  have hmeas : Measurable (xi p m) :=
    (measurable_outcome.sub (base.q0_measurable.comp measurable_covariate)).sub
      (measurable_const.mul
        (measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)))
  have hind : IndepFun (xi p m) (fun o ↦ (covariate o, treatment o)) m.P := by
    simpa [m] using affineGaussianModel_indep_xi_xt base theta tau
  change Indep (MeasurableSpace.comap (xi p m) inferInstance)
    (xTSigma (Xspace := Xspace)) m.P at hind
  have hmean : ∫ o, xi p m o ∂m.P = 0 := by
    have hmap := integral_map (μ := m.P) (φ := xi p m) (f := fun z : ℝ ↦ z)
      hmeas.aemeasurable stronglyMeasurable_id.aestronglyMeasurable
    rw [affineGaussianModel_map_xi base theta tau] at hmap
    exact ((integral_id_gaussianReal (μ := 0)
      (v := ⟨tau ^ 2, sq_nonneg tau⟩)).symm.trans hmap).symm
  have hstrong : StronglyMeasurable[MeasurableSpace.comap (xi p m) inferInstance]
      (xi p m) := (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  haveI : SigmaFinite (m.P.trim (measurable_xt (Xspace := Xspace)).comap_le) :=
    inferInstance
  have hce := MeasureTheory.condExp_indep_eq
    (μ := m.P) (m₁ := MeasurableSpace.comap (xi p m) inferInstance)
    (m₂ := xTSigma (Xspace := Xspace)) (f := xi p m)
    (by exact hmeas.comap_le) (by exact measurable_xt.comap_le) hstrong hind
  simpa [hmean, Pi.zero_def] using hce

/-- The covariate-treatment marginal of the packaged affine model is the base
model's covariate-treatment marginal. -/
lemma affineGaussianModel_map_xt {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).P.map
        (fun o ↦ (covariate o, treatment o)) =
      base.P.map (fun o ↦ (covariate o, treatment o)) := by
  exact affineGaussianLaw_map_xt base theta tau

/-- The covariate marginal is retained by the affine Gaussian model. -/
lemma affineGaussianModel_covariateLaw {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    covariateLaw p (affineGaussianModel base theta tau) = covariateLaw p base := by
  unfold covariateLaw
  have hf : covariate = Prod.fst ∘
      (fun o : Obs Xspace ↦ (covariate o, treatment o)) := rfl
  rw [hf, ← Measure.map_map measurable_fst measurable_xt,
    affineGaussianModel_map_xt, Measure.map_map measurable_fst measurable_xt]

/-- Any property depending only on the treatment residual's pushforward law is
unchanged along the affine Gaussian outcome path. -/
lemma affineGaussianModel_map_eta {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    (affineGaussianModel base theta tau).P.map
        (eta p (affineGaussianModel base theta tau)) = base.P.map (eta p base) := by
  have hmeas : Measurable (fun z : Xspace × ℝ ↦ z.2 - base.g0 z.1) :=
    measurable_snd.sub (base.g0_measurable.comp measurable_fst)
  calc
    (affineGaussianModel base theta tau).P.map
        (eta p (affineGaussianModel base theta tau)) =
        ((affineGaussianModel base theta tau).P.map
          (fun o ↦ (covariate o, treatment o))).map
            (fun z ↦ z.2 - base.g0 z.1) := by
              rw [Measure.map_map hmeas measurable_xt]
              rfl
    _ = (base.P.map (fun o ↦ (covariate o, treatment o))).map
          (fun z ↦ z.2 - base.g0 z.1) := by rw [affineGaussianModel_map_xt]
    _ = base.P.map (eta p base) := by
          rw [Measure.map_map hmeas measurable_xt]
          rfl

/-- The treatment-residual complex MGF is retained by the affine model. -/
lemma affineGaussianModel_complexMGF_eta {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    complexMGF (eta p (affineGaussianModel base theta tau))
        (affineGaussianModel base theta tau).P =
      complexMGF (eta p base) base.P := by
  have heta : Measurable (eta p base) :=
    measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)
  have hnew : AEMeasurable (eta p (affineGaussianModel base theta tau))
      (affineGaussianModel base theta tau).P := by
    exact heta.aemeasurable
  rw [← complexMGF_id_map hnew, ← complexMGF_id_map heta.aemeasurable]
  exact congrArg (complexMGF id) (affineGaussianModel_map_eta base theta tau)

/-- The cumulant separation functional is retained by the affine model. -/
lemma affineGaussianModel_kappaEta {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ) :
    kappaEta p (affineGaussianModel base theta tau) = kappaEta p base := by
  unfold kappaEta
  rw [affineGaussianModel_complexMGF_eta]

/-- Integrability of any measurable function of the treatment residual is
retained along the affine path. -/
lemma affineGaussianModel_integrable_comp_eta_iff {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun o ↦ f (eta p (affineGaussianModel base theta tau) o))
        (affineGaussianModel base theta tau).P ↔
      Integrable (fun o ↦ f (eta p base o)) base.P := by
  have heta : Measurable (eta p base) :=
    measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)
  have hnew : AEMeasurable (eta p (affineGaussianModel base theta tau))
      (affineGaussianModel base theta tau).P := heta.aemeasurable
  calc
    Integrable (fun o ↦ f (eta p (affineGaussianModel base theta tau) o))
        (affineGaussianModel base theta tau).P ↔
      Integrable f ((affineGaussianModel base theta tau).P.map
        (eta p (affineGaussianModel base theta tau))) :=
          (integrable_map_measure hf.aestronglyMeasurable hnew).symm
    _ ↔ Integrable f (base.P.map (eta p base)) := by
      rw [affineGaussianModel_map_eta]
    _ ↔ Integrable (fun o ↦ f (eta p base o)) base.P :=
      integrable_map_measure hf.aestronglyMeasurable heta.aemeasurable

/-- Integrals of measurable functions of the treatment residual are retained
along the affine path. -/
lemma affineGaussianModel_integral_comp_eta {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ o, f (eta p (affineGaussianModel base theta tau) o)
        ∂(affineGaussianModel base theta tau).P =
      ∫ o, f (eta p base o) ∂base.P := by
  have heta : Measurable (eta p base) :=
    measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)
  calc
    ∫ o, f (eta p (affineGaussianModel base theta tau) o)
        ∂(affineGaussianModel base theta tau).P =
        ∫ z, f z ∂((affineGaussianModel base theta tau).P.map
          (eta p (affineGaussianModel base theta tau))) := by
            exact (integral_map heta.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(base.P.map (eta p base)) := by
          rw [affineGaussianModel_map_eta]
    _ = ∫ o, f (eta p base o) ∂base.P := by
          exact integral_map heta.aemeasurable hf.aestronglyMeasurable

/-- Independence of the treatment residual and covariate is preserved along
the affine Gaussian outcome path. -/
lemma affineGaussianModel_indep_eta_covariate {p : Parameters}
    (base : Model (Xspace := Xspace) p) (theta tau : ℝ)
    (hbase : IndependentTreatmentNoise p base) :
    IndependentTreatmentNoise p (affineGaussianModel base theta tau) := by
  have heta : Measurable (eta p base) :=
    measurable_treatment.sub (base.g0_measurable.comp measurable_covariate)
  have hjoint : (affineGaussianModel base theta tau).P.map
      (fun o ↦ (eta p (affineGaussianModel base theta tau) o, covariate o)) =
      base.P.map (fun o ↦ (eta p base o, covariate o)) := by
    have hf : Measurable (fun z : Xspace × ℝ ↦ (z.2 - base.g0 z.1, z.1)) :=
      (measurable_snd.sub (base.g0_measurable.comp measurable_fst)).prodMk measurable_fst
    calc
      (affineGaussianModel base theta tau).P.map
          (fun o ↦ (eta p (affineGaussianModel base theta tau) o, covariate o)) =
          ((affineGaussianModel base theta tau).P.map
            (fun o ↦ (covariate o, treatment o))).map
              (fun z ↦ (z.2 - base.g0 z.1, z.1)) := by
                rw [Measure.map_map hf measurable_xt]
                rfl
      _ = (base.P.map (fun o ↦ (covariate o, treatment o))).map
          (fun z ↦ (z.2 - base.g0 z.1, z.1)) := by rw [affineGaussianModel_map_xt]
      _ = base.P.map (fun o ↦ (eta p base o, covariate o)) := by
            rw [Measure.map_map hf measurable_xt]
            rfl
  have hcov : (affineGaussianModel base theta tau).P.map covariate =
      base.P.map covariate := by
    have hf : covariate = Prod.fst ∘
        (fun o : Obs Xspace ↦ (covariate o, treatment o)) := rfl
    rw [hf, ← Measure.map_map measurable_fst measurable_xt,
      affineGaussianModel_map_xt, Measure.map_map measurable_fst measurable_xt]
  have hmapeta : (affineGaussianModel base theta tau).P.map (eta p base) =
      base.P.map (eta p base) := by
    change (affineGaussianModel base theta tau).P.map
      (eta p (affineGaussianModel base theta tau)) = _
    exact affineGaussianModel_map_eta base theta tau
  apply (indepFun_iff_map_prod_eq_prod_map_map
    heta.aemeasurable measurable_covariate.aemeasurable).mpr
  change (affineGaussianModel base theta tau).P.map
      (fun o ↦ (eta p (affineGaussianModel base theta tau) o, covariate o)) = _
  rw [hjoint, hmapeta, hcov]
  exact (indepFun_iff_map_prod_eq_prod_map_map
    heta.aemeasurable measurable_covariate.aemeasurable).mp hbase

/-- All non-Gaussian-class fields except the explicitly supplied Gaussian
residual Luxemburg bound transport automatically along the affine path. -/
lemma affineGaussianModel_nonGaussianClass {p : Parameters}
    (base : Model (Xspace := Xspace) p) (n : ℕ)
    (hbase : NonGaussianClass p n base) (theta tau : ℝ)
    (htheta : |theta| ≤ p.Ctheta)
    (hxi : XiSubGaussian p (affineGaussianModel base theta tau)) :
    NonGaussianClass p n (affineGaussianModel base theta tau) where
  n_pos := hbase.n_pos
  independentTreatmentNoise :=
    affineGaussianModel_indep_eta_covariate base theta tau
      hbase.independentTreatmentNoise
  outcomeMeanIndependence := affineGaussianModel_outcomeMeanIndependence base theta tau
  thetaRange := htheta
  gRange := by
    rw [GRange, affineGaussianModel_covariateLaw]
    exact hbase.gRange
  qRange := by
    rw [QRange, affineGaussianModel_covariateLaw]
    exact hbase.qRange
  etaSubGaussian := by
    refine ⟨?_, ?_⟩
    · exact (affineGaussianModel_integrable_comp_eta_iff base theta tau
        (fun z ↦ Real.exp (z ^ 2 / p.psieta ^ 2)) (by fun_prop)).mpr
          hbase.etaSubGaussian.1
    · rw [affineGaussianModel_integral_comp_eta base theta tau
        (fun z ↦ Real.exp (z ^ 2 / p.psieta ^ 2)) (by fun_prop)]
      exact hbase.etaSubGaussian.2
  xiSubGaussian := hxi
  cumulantSeparation := by
    rw [CumulantSeparation, affineGaussianModel_kappaEta]
    exact hbase.cumulantSeparation
  treatmentCodeRadiusL1 := by
    unfold TreatmentCodeRadiusL1At at ⊢
    rw [affineGaussianModel_covariateLaw]
    exact hbase.treatmentCodeRadiusL1

/-- The published ACE comparator class is likewise retained, apart from the
explicitly supplied Gaussian residual Luxemburg bound. -/
lemma affineGaussianModel_jmsAceClass {p : Parameters}
    (base : Model (Xspace := Xspace) p) (n : ℕ)
    (hbase : JmsAceClass p n base) (theta tau : ℝ)
    (htheta : |theta| ≤ p.Ctheta)
    (hxi : XiSubGaussian p (affineGaussianModel base theta tau)) :
    JmsAceClass p n (affineGaussianModel base theta tau) where
  n_pos := hbase.n_pos
  independentTreatmentNoise :=
    affineGaussianModel_indep_eta_covariate base theta tau
      hbase.independentTreatmentNoise
  outcomeMeanIndependence := affineGaussianModel_outcomeMeanIndependence base theta tau
  thetaRange := htheta
  gRange := by
    rw [GRange, affineGaussianModel_covariateLaw]
    exact hbase.gRange
  qRange := by
    rw [QRange, affineGaussianModel_covariateLaw]
    exact hbase.qRange
  etaSubGaussian := by
    refine ⟨?_, ?_⟩
    · exact (affineGaussianModel_integrable_comp_eta_iff base theta tau
        (fun z ↦ Real.exp (z ^ 2 / p.psieta ^ 2)) (by fun_prop)).mpr
          hbase.etaSubGaussian.1
    · rw [affineGaussianModel_integral_comp_eta base theta tau
        (fun z ↦ Real.exp (z ^ 2 / p.psieta ^ 2)) (by fun_prop)]
      exact hbase.etaSubGaussian.2
  xiSubGaussian := hxi
  cumulantSeparation := by
    rw [CumulantSeparation, affineGaussianModel_kappaEta]
    exact hbase.cumulantSeparation
  treatmentCodeRadiusLr := by
    unfold TreatmentCodeRadiusLrAt at ⊢
    rw [affineGaussianModel_covariateLaw]
    exact hbase.treatmentCodeRadiusLr
  outcomeCodeRadiusLr := by
    unfold OutcomeCodeRadiusLrAt at ⊢
    rw [affineGaussianModel_covariateLaw]
    exact hbase.outcomeCodeRadiusLr

end CausalSmith.Stat.SaPlmCumulantConverse
