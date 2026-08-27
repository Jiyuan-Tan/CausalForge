import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductTV
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Count sufficiency for predictive total variation

This module records the exact common-reconstruction-kernel interface needed
to transport a count-table bound to the full marked-Poisson experiment.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped NNReal

private lemma measureReal_bind_eq_integral'
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (K : X → Measure Y) (hK : Measurable K)
    (hprob : ∀ x, IsProbabilityMeasure (K x))
    (B : Set Y) (hB : MeasurableSet B) :
    (Q.bind K).real B = ∫ x, (K x).real B ∂Q := by
  letI : ∀ x, IsProbabilityMeasure (K x) := hprob
  letI : IsProbabilityMeasure (Q.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hprob)
  let f : Y → ℝ := B.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hB
  have hfint : Integrable f (Q.bind K) :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun z => by
        simp only [f, Set.indicator]
        split <;> simp)
  calc
    (Q.bind K).real B = ∫ z in B, (1 : ℝ) ∂(Q.bind K) := by simp
    _ = ∫ z, f z ∂(Q.bind K) := by rw [integral_indicator hB]
    _ = ∫ x, ∫ z, f z ∂K x ∂Q :=
      Causalean.Mathlib.MeasureTheory.integral_bind hK hfint
    _ = ∫ x, (K x).real B ∂Q := by
      congr 1
      funext x
      rw [show f = B.indicator (fun _ => (1 : ℝ)) from rfl,
        integral_indicator hB]
      simp

/-- Applying the same probability kernel to two input laws cannot increase
their total-variation distance. -/
lemma tvDist_bind_common_kernel_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q₀ Q₁ : Measure X) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (K : X → Measure Y) (hK : Measurable K)
    (hprob : ∀ x, IsProbabilityMeasure (K x)) :
    tvDist (Q₀.bind K) (Q₁.bind K) ≤ tvDist Q₀ Q₁ := by
  letI : ∀ x, IsProbabilityMeasure (K x) := hprob
  letI : IsProbabilityMeasure (Q₀.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hprob)
  letI : IsProbabilityMeasure (Q₁.bind K) :=
    isProbabilityMeasure_bind hK.aemeasurable (ae_of_all _ hprob)
  refine ciSup_le fun B => ?_
  rw [measureReal_bind_eq_integral' Q₀ K hK hprob B.1 B.2,
    measureReal_bind_eq_integral' Q₁ K hK hprob B.1 B.2]
  have h := tvDist_integral_range Q₀ Q₁ (fun x => (K x).real B.1)
    ((Measure.measurable_coe B.2).ennreal_toReal.comp hK) 0 1 (by norm_num)
    (fun x => ⟨measureReal_nonneg,
      by simpa using measureReal_le_one (μ := K x) (s := B.1)⟩)
  simpa using h

/-- If two full experiments are reconstructed from their complete count laws
by one parameter-independent probability kernel, full-data TV is bounded by
count-table TV. -/
lemma tvDist_full_le_count_of_common_reconstruction
    {C Y : Type*} [MeasurableSpace C] [MeasurableSpace Y]
    (Q₀ Q₁ : Measure C) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (P₀ P₁ : Measure Y) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (K : C → Measure Y) (hK : Measurable K)
    (hprob : ∀ c, IsProbabilityMeasure (K c))
    (h₀ : P₀ = Q₀.bind K) (h₁ : P₁ = Q₁.bind K) :
    tvDist P₀ P₁ ≤ tvDist Q₀ Q₁ := by
  rw [h₀, h₁]
  exact tvDist_bind_common_kernel_le Q₀ Q₁ K hK hprob

/-- Given a scalar count, draw an independent iid stream and retain exactly
that prefix.  This kernel is independent of the Poisson intensity. -/
noncomputable def finitePoissonCountReconstruction
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    Measure (FiniteSample X) :=
  Measure.map (fun z : ℕ → X => streamToFiniteSample (n, z)) (iidStreamLaw P)

/-- The prefix reconstruction kernel depends measurably on the count it is given.
This is the measurability side condition required before the kernel can be composed
with the Poisson count law. -/
lemma measurable_finitePoissonCountReconstruction
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] :
    Measurable (finitePoissonCountReconstruction P) := by
  exact measurable_of_countable _

/-- For each count, the prefix reconstruction produces a probability measure on
finite samples, being the pushforward of an iid stream law.  This is the other side
condition needed to treat the reconstruction as a Markov kernel. -/
noncomputable instance finitePoissonCountReconstruction_isProbabilityMeasure
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    IsProbabilityMeasure (finitePoissonCountReconstruction P n) := by
  unfold finitePoissonCountReconstruction
  exact Measure.isProbabilityMeasure_map
    (measurable_streamToFiniteSample.comp
      (measurable_const.prodMk measurable_id)).aemeasurable

/-- A finite Poisson sample is exactly the scalar Poisson count followed by
the intensity-independent prefix reconstruction kernel. -/
lemma finitePoissonSampleLaw_eq_count_bind_reconstruction
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    finitePoissonSampleLaw P lam =
      (poissonMeasure lam).bind (finitePoissonCountReconstruction P) := by
  unfold finitePoissonSampleLaw poissonIIDStreamLaw
  rw [Measure.prod]
  rw [← Measure.bind_dirac_eq_map _ measurable_streamToFiniteSample]
  rw [Measure.bind_bind]
  · congr 1
    funext n
    rw [Measure.bind_dirac_eq_map]
    · unfold finitePoissonCountReconstruction
      rw [Measure.map_map]
      · rfl
      · exact measurable_streamToFiniteSample
      · exact measurable_const.prodMk measurable_id
    · exact measurable_streamToFiniteSample
  · exact (Measurable.map_prodMk_left (ν := iidStreamLaw P)).aemeasurable
  · exact Measure.measurable_dirac.comp_aemeasurable
      measurable_streamToFiniteSample.aemeasurable

/-- The marked version uses the same intensity-independent reconstruction
kernel, now with iid observation-mark pairs. -/
lemma finiteMarkedPoissonSampleLaw_eq_count_bind_reconstruction
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    finiteMarkedPoissonSampleLaw P R lam =
      (poissonMeasure lam).bind
        (finitePoissonCountReconstruction (P.prod R)) := by
  exact finitePoissonSampleLaw_eq_count_bind_reconstruction (P.prod R) lam

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
