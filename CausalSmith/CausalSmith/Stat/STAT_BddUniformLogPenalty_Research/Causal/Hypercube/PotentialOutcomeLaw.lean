import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.BernoulliKernel
import Causalean.Mathlib.Probability.Kernel.ProductCondDistrib

/-!
# Explicit potential-outcome laws for the causal angular family

This module assembles two pointwise Bernoulli selected kernels over a common
score design into the `(Y(0),Y(1),X)` law carried by `A1A2Law`.  In particular,
the selected kernels in the resulting decorated law are the same kernels used
to build its joint measure, so the disintegration field is exact.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The joint potential-outcome measure obtained by drawing the score and then
two conditionally independent Bernoulli potential outcomes. -/
-- @node: causalBernoulliPotentialOutcomeMeasure
noncomputable def causalBernoulliPotentialOutcomeMeasure
    (nu : Measure Score) (p0 p1 : Score → ℝ)
    (hp0 : Measurable p0) (hp1 : Measurable p1) : Measure CausalObservation :=
  Measure.map (fun z : Score × (ℝ × ℝ) => (z.2.1, z.2.2, z.1))
    (Measure.compProd nu
      (Kernel.prod (causalSelectedBernoulliKernel p0 hp0)
        (causalSelectedBernoulliKernel p1 hp1)))

/-- The score marginal of the explicit potential-outcome measure is its input
design measure. -/
-- @node: causalBernoulliPotentialOutcomeMeasure_map_score
lemma causalBernoulliPotentialOutcomeMeasure_map_score
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p0 p1 : Score → ℝ) (hp0 : Measurable p0) (hp1 : Measurable p1)
    (hp0lo : ∀ x, 0 ≤ p0 x) (hp0hi : ∀ x, p0 x ≤ 1)
    (hp1lo : ∀ x, 0 ≤ p1 x) (hp1hi : ∀ x, p1 x ≤ 1) :
    Measure.map causalScore
        (causalBernoulliPotentialOutcomeMeasure nu p0 p1 hp0 hp1) = nu := by
  letI : IsMarkovKernel (causalSelectedBernoulliKernel p0 hp0) :=
    causalSelectedBernoulliKernel_isMarkovKernel p0 hp0 hp0lo hp0hi
  letI : IsMarkovKernel (causalSelectedBernoulliKernel p1 hp1) :=
    causalSelectedBernoulliKernel_isMarkovKernel p1 hp1 hp1lo hp1hi
  unfold causalBernoulliPotentialOutcomeMeasure
  rw [Measure.map_map (by unfold causalScore; fun_prop) (by fun_prop)]
  change Measure.map Prod.fst
    (Measure.compProd nu
      (Kernel.prod (causalSelectedBernoulliKernel p0 hp0)
        (causalSelectedBernoulliKernel p1 hp1))) = nu
  exact Measure.fst_compProd _ _

/-- The explicit potential-outcome measure is a probability law. -/
-- @node: causalBernoulliPotentialOutcomeMeasure_isProbabilityMeasure
lemma causalBernoulliPotentialOutcomeMeasure_isProbabilityMeasure
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p0 p1 : Score → ℝ) (hp0 : Measurable p0) (hp1 : Measurable p1)
    (hp0lo : ∀ x, 0 ≤ p0 x) (hp0hi : ∀ x, p0 x ≤ 1)
    (hp1lo : ∀ x, 0 ≤ p1 x) (hp1hi : ∀ x, p1 x ≤ 1) :
    IsProbabilityMeasure
      (causalBernoulliPotentialOutcomeMeasure nu p0 p1 hp0 hp1) := by
  letI : IsMarkovKernel (causalSelectedBernoulliKernel p0 hp0) :=
    causalSelectedBernoulliKernel_isMarkovKernel p0 hp0 hp0lo hp0hi
  letI : IsMarkovKernel (causalSelectedBernoulliKernel p1 hp1) :=
    causalSelectedBernoulliKernel_isMarkovKernel p1 hp1 hp1lo hp1hi
  unfold causalBernoulliPotentialOutcomeMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Restricting two explicit potential-outcome laws to a measurable score
cell gives the same measure when their restricted score designs agree and
both Bernoulli profiles agree throughout that cell. -/
-- @node: causalBernoulliPotentialOutcomeMeasure_restrict_score_eq
lemma causalBernoulliPotentialOutcomeMeasure_restrict_score_eq
    (nu nu' : Measure Score) [SFinite nu] [SFinite nu']
    (p0 p1 p0' p1' : Score → ℝ)
    (hp0 : Measurable p0) (hp1 : Measurable p1)
    (hp0' : Measurable p0') (hp1' : Measurable p1')
    (hp0lo : ∀ x, 0 ≤ p0 x) (hp0hi : ∀ x, p0 x ≤ 1)
    (hp1lo : ∀ x, 0 ≤ p1 x) (hp1hi : ∀ x, p1 x ≤ 1)
    (hp0lo' : ∀ x, 0 ≤ p0' x) (hp0hi' : ∀ x, p0' x ≤ 1)
    (hp1lo' : ∀ x, 0 ≤ p1' x) (hp1hi' : ∀ x, p1' x ≤ 1)
    {C : Set Score} (hC : MeasurableSet C)
    (hnu : nu.restrict C = nu'.restrict C)
    (hparam0 : ∀ x ∈ C, p0 x = p0' x)
    (hparam1 : ∀ x ∈ C, p1 x = p1' x) :
    (causalBernoulliPotentialOutcomeMeasure nu p0 p1 hp0 hp1).restrict
        {z | causalScore z ∈ C} =
      (causalBernoulliPotentialOutcomeMeasure nu' p0' p1' hp0' hp1').restrict
        {z | causalScore z ∈ C} := by
  let k0 := causalSelectedBernoulliKernel p0 hp0
  let k1 := causalSelectedBernoulliKernel p1 hp1
  let k0' := causalSelectedBernoulliKernel p0' hp0'
  let k1' := causalSelectedBernoulliKernel p1' hp1'
  letI : IsMarkovKernel k0 :=
    causalSelectedBernoulliKernel_isMarkovKernel p0 hp0 hp0lo hp0hi
  letI : IsMarkovKernel k1 :=
    causalSelectedBernoulliKernel_isMarkovKernel p1 hp1 hp1lo hp1hi
  letI : IsMarkovKernel k0' :=
    causalSelectedBernoulliKernel_isMarkovKernel p0' hp0' hp0lo' hp0hi'
  letI : IsMarkovKernel k1' :=
    causalSelectedBernoulliKernel_isMarkovKernel p1' hp1' hp1lo' hp1hi'
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold causalBernoulliPotentialOutcomeMeasure
  have hE : MeasurableSet (s ∩ {z : CausalObservation | causalScore z ∈ C}) :=
    hs.inter (hC.preimage (by unfold causalScore; fun_prop))
  rw [Measure.map_apply (by fun_prop) hE, Measure.map_apply (by fun_prop) hE]
  have hpre : MeasurableSet
      ((fun z : Score × (ℝ × ℝ) => (z.2.1, z.2.2, z.1)) ⁻¹'
        (s ∩ {z : CausalObservation | causalScore z ∈ C})) :=
    hE.preimage (by fun_prop)
  rw [Measure.compProd_apply hpre, Measure.compProd_apply hpre]
  have hsupp : Function.support (fun x ↦
      (Kernel.prod k0 k1 x)
        (Prod.mk x ⁻¹' ((fun z : Score × (ℝ × ℝ) =>
          (z.2.1, z.2.2, z.1)) ⁻¹'
            (s ∩ {z : CausalObservation | causalScore z ∈ C})))) ⊆ C := by
    intro x hx
    by_contra hxC
    apply hx
    simp [causalScore, hxC]
  have hsupp' : Function.support (fun x ↦
      (Kernel.prod k0' k1' x)
        (Prod.mk x ⁻¹' ((fun z : Score × (ℝ × ℝ) =>
          (z.2.1, z.2.2, z.1)) ⁻¹'
            (s ∩ {z : CausalObservation | causalScore z ∈ C})))) ⊆ C := by
    intro x hx
    by_contra hxC
    apply hx
    simp [causalScore, hxC]
  rw [← setLIntegral_eq_of_support_subset hsupp,
    ← setLIntegral_eq_of_support_subset hsupp', hnu]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hC] with x hx
  have hk0 : k0 x = k0' x := by
    ext A hA
    simp [k0, k0', causalSelectedBernoulliKernel, hparam0 x hx]
  have hk1 : k1 x = k1' x := by
    ext A hA
    simp [k1, k1', causalSelectedBernoulliKernel, hparam1 x hx]
  rw [Kernel.prod_apply, Kernel.prod_apply, hk0, hk1]

/-- Mapping the explicit law to `(X,Y(t))` recovers composition with the
selected arm-`t` Bernoulli kernel. -/
-- @node: causalBernoulliPotentialOutcomeMeasure_map_score_arm
lemma causalBernoulliPotentialOutcomeMeasure_map_score_arm
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p0 p1 : Score → ℝ) (hp0 : Measurable p0) (hp1 : Measurable p1)
    (hp0lo : ∀ x, 0 ≤ p0 x) (hp0hi : ∀ x, p0 x ≤ 1)
    (hp1lo : ∀ x, 0 ≤ p1 x) (hp1hi : ∀ x, p1 x ≤ 1) (t : Bool) :
    Measure.map (fun w => (causalScore w, armCoord t w))
        (causalBernoulliPotentialOutcomeMeasure nu p0 p1 hp0 hp1) =
      Measure.compProd nu
        (if t then causalSelectedBernoulliKernel p1 hp1
          else causalSelectedBernoulliKernel p0 hp0) := by
  let k0 := causalSelectedBernoulliKernel p0 hp0
  let k1 := causalSelectedBernoulliKernel p1 hp1
  letI : IsMarkovKernel k0 :=
    causalSelectedBernoulliKernel_isMarkovKernel p0 hp0 hp0lo hp0hi
  letI : IsMarkovKernel k1 :=
    causalSelectedBernoulliKernel_isMarkovKernel p1 hp1 hp1lo hp1hi
  cases t with
  | false =>
      unfold causalBernoulliPotentialOutcomeMeasure
      rw [Measure.map_map
        (by
          simp only [causalScore, armCoord]
          exact (measurable_snd.comp measurable_snd).prodMk measurable_fst)
        (by fun_prop)]
      change Measure.map (Prod.map id Prod.fst)
          (Measure.compProd nu (Kernel.prod k0 k1)) = Measure.compProd nu k0
      rw [← Measure.compProd_map (μ := nu) (κ := Kernel.prod k0 k1)
        measurable_fst]
      rw [show (Kernel.prod k0 k1).map Prod.fst = k0 by
        simpa [Kernel.fst_eq] using Kernel.fst_prod k0 k1]
  | true =>
      unfold causalBernoulliPotentialOutcomeMeasure
      rw [Measure.map_map
        (by
          simp only [causalScore, armCoord]
          exact (measurable_snd.comp measurable_snd).prodMk
            (measurable_fst.comp measurable_snd))
        (by fun_prop)]
      change Measure.map (Prod.map id Prod.snd)
          (Measure.compProd nu (Kernel.prod k0 k1)) = Measure.compProd nu k1
      rw [← Measure.compProd_map (μ := nu) (κ := Kernel.prod k0 k1)
        measurable_snd]
      rw [show (Kernel.prod k0 k1).map Prod.snd = k1 by
        simpa [Kernel.snd_eq] using Kernel.snd_prod k0 k1]

/-- Package the explicit two-kernel construction as a decorated `A1A2Law`.
All pointwise conditional fields are definitionally tied to the same selected
Bernoulli kernels used to assemble the joint potential-outcome measure. -/
-- @node: causalBernoulliA1A2Law
noncomputable def causalBernoulliA1A2Law
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (S A0 A1 B : Set Score) (density p0 p1 : Score → ℝ)
    (hp0 : Measurable p0) (hp1 : Measurable p1)
    (hp0lo : ∀ x, 0 ≤ p0 x) (hp0hi : ∀ x, p0 x ≤ 1)
    (hp1lo : ∀ x, 0 ≤ p1 x) (hp1hi : ∀ x, p1 x ≤ 1)
    (hA0 : MeasurableSet A0) (hA1 : MeasurableSet A1)
    (hpartition : A0 ∪ A1 = S ∧ Disjoint A0 A1)
    (hboundary : B = frontier A0 ∩ frontier A1)
    (hboundaryInterior : B ⊆ interior S)
    (hmarginal : nu = volume.withDensity
      (fun x => ENNReal.ofReal (S.indicator density x)))
    (hsupport : S = nu.support) : A1A2Law where
  law := causalBernoulliPotentialOutcomeMeasure nu p0 p1 hp0 hp1
  support := S
  A0 := A0
  A1 := A1
  boundary := B
  A0_measurable := hA0
  A1_measurable := hA1
  assignment_partition := hpartition
  boundary_eq := hboundary
  boundary_subset_interior := hboundaryInterior
  density := density
  muPO := fun t => if t then p1 else p0
  sigmaSqPO := fun t x =>
    let p := if t then p1 x else p0 x
    p * (1 - p)
  condKer := fun t => if t then causalSelectedBernoulliKernel p1 hp1
    else causalSelectedBernoulliKernel p0 hp0
  law_isProbability :=
    causalBernoulliPotentialOutcomeMeasure_isProbabilityMeasure nu p0 p1 hp0 hp1
      hp0lo hp0hi hp1lo hp1hi
  condKer_markov := by
    intro t
    cases t with
    | false =>
        exact causalSelectedBernoulliKernel_isMarkovKernel p0 hp0 hp0lo hp0hi
    | true =>
        exact causalSelectedBernoulliKernel_isMarkovKernel p1 hp1 hp1lo hp1hi
  marginal_eq := by
    rw [causalBernoulliPotentialOutcomeMeasure_map_score nu p0 p1 hp0 hp1
      hp0lo hp0hi hp1lo hp1hi]
    exact hmarginal
  support_eq_marginal_support := by
    rw [causalBernoulliPotentialOutcomeMeasure_map_score nu p0 p1 hp0 hp1
      hp0lo hp0hi hp1lo hp1hi]
    exact hsupport
  condKer_disint := by
    intro t
    rw [causalBernoulliPotentialOutcomeMeasure_map_score nu p0 p1 hp0 hp1
      hp0lo hp0hi hp1lo hp1hi]
    exact (causalBernoulliPotentialOutcomeMeasure_map_score_arm nu p0 p1 hp0 hp1
      hp0lo hp0hi hp1lo hp1hi t).symm
  mu_condMean := by
    intro t
    filter_upwards [] with x
    cases t with
    | false =>
        exact (causalSelectedBernoulliKernel_integral_id p0 hp0 hp0lo hp0hi x).symm
    | true =>
        exact (causalSelectedBernoulliKernel_integral_id p1 hp1 hp1lo hp1hi x).symm
  sigmaSq_condVar := by
    intro t
    filter_upwards [] with x
    cases t with
    | false =>
        exact (causalSelectedBernoulliKernel_variance_id p0 hp0 hp0lo hp0hi x).symm
    | true =>
        exact (causalSelectedBernoulliKernel_variance_id p1 hp1 hp1lo hp1hi x).symm

end CausalSmith.Stat.BddUniformLogPenalty
