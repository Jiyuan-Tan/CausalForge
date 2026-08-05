/-
# Fixed-geometry continuum witness

The geometry handle fixes the source/target laws, weights, and propensity and
sets the first stage and compliance probability at exact effective strength.
The witness predicate records the continuum law's compliance-type and Bernoulli
moment identities without introducing a new causal typeclass.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Frontier
import Causalean.Estimation.MinimaxATE.Model
import Causalean.Stat.Minimax.ChiSquared
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Causalean.Mathlib.Probability.BernoulliMeasure
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.TwoPointConstruction

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory
open scoped ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ### Measure-theoretic leaves for the witness

The following definitions spell out the three independent coins used by the
paper.  The first chooses compliance, the second chooses the common receipt
type when the unit is not a complier, and the third chooses the binary treated
outcome. -/

private noncomputable abbrev witnessCoin (p : ℝ) : Measure Bool :=
  Causalean.Mathlib.Probability.bernoulliBool p

private lemma measurable_witnessCoin : Measurable witnessCoin := by
  exact Causalean.Mathlib.Probability.measurable_bernoulliBool

private lemma witnessCoin_probability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (witnessCoin p) := by
  exact Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure hp0 hp1

private lemma witnessCoin_integral {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Bool → ℝ) :
    ∫ z, f z ∂witnessCoin p = p * f true + (1 - p) * f false := by
  exact Causalean.Mathlib.Probability.bernoulliBool_integral hp0 hp1 f

private lemma witnessCoin_bind {β : Type*} [MeasurableSpace β] (p : ℝ)
    (K : Bool → Measure β) :
    (witnessCoin p).bind K =
      ENNReal.ofReal p • K true + ENNReal.ofReal (1 - p) • K false := by
  exact Causalean.Mathlib.Probability.bernoulliBool_bind p K

private lemma witnessCoin_map {β : Type*} [MeasurableSpace β] (p : ℝ)
    (f : Bool → β) :
    (witnessCoin p).map f =
      ENNReal.ofReal p • Measure.dirac (f true) +
        ENNReal.ofReal (1 - p) • Measure.dirac (f false) := by
  exact Causalean.Mathlib.Probability.bernoulliBool_map p f

@[fun_prop] private lemma measurable_variable_smul_measure
    {ι β : Type*} [MeasurableSpace ι] [MeasurableSpace β]
    {c : ι → ENNReal} {μ : ι → Measure β}
    (hc : Measurable c) (hμ : Measurable μ) :
    Measurable fun x => c x • μ x := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  exact hc.mul ((Measure.measurable_coe hA).comp hμ)

private def witnessFullPack (s : Bool) (x : 𝒳) (complier common y1 : Bool) :
    FullData 𝒳 :=
  (s, x, if complier then false else common,
    if complier then true else common, 0, boolReal y1)

private lemma measurable_witnessFullPack (s : Bool) :
    Measurable (fun q : (𝒳 × Bool) × (Bool × Bool) =>
      witnessFullPack s q.1.1 q.1.2 q.2.1 q.2.2) := by
  unfold witnessFullPack boolReal
  have hc : Measurable (fun q : (𝒳 × Bool) × (Bool × Bool) => q.1.2) :=
    measurable_snd.comp measurable_fst
  have ha : Measurable (fun q : (𝒳 × Bool) × (Bool × Bool) => q.2.1) :=
    measurable_fst.comp measurable_snd
  have hy : Measurable (fun q : (𝒳 × Bool) × (Bool × Bool) => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hd0 : Measurable (fun q : (𝒳 × Bool) × (Bool × Bool) =>
      if q.1.2 then false else q.2.1) :=
    Measurable.ite (measurableSet_eq_fun hc measurable_const)
      measurable_const ha
  have hd1 : Measurable (fun q : (𝒳 × Bool) × (Bool × Bool) =>
      if q.1.2 then true else q.2.1) :=
    Measurable.ite (measurableSet_eq_fun hc measurable_const)
      measurable_const ha
  have hyr : Measurable (fun q : (𝒳 × Bool) × (Bool × Bool) =>
      if q.2.2 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun hy measurable_const)
      measurable_const measurable_const
  exact measurable_const.prodMk <| (measurable_fst.comp measurable_fst).prodMk <|
    hd0.prodMk <| hd1.prodMk <| measurable_const.prodMk hyr

private noncomputable def witnessPotentialKernel (s : Bool) (p : 𝒳 → ℝ)
    (x : 𝒳) : Measure (FullData 𝒳) :=
  (witnessCoin (p x)).bind fun complier =>
    (witnessCoin (1 / 2)).bind fun common =>
      (witnessCoin (1 / 2)).map (witnessFullPack s x complier common)

private lemma measurable_witnessPotentialKernel (s : Bool) {p : 𝒳 → ℝ}
    (hp : Measurable p) : Measurable (witnessPotentialKernel s p) := by
  unfold witnessPotentialKernel
  simp_rw [witnessCoin_bind]
  simp_rw [witnessCoin_map]
  have hpack (complier common : Bool) :
      Measurable (fun x : 𝒳 => witnessFullPack s x complier common true) ∧
      Measurable (fun x : 𝒳 => witnessFullPack s x complier common false) := by
    constructor <;>
      exact (measurable_witnessFullPack s).comp
        ((measurable_id.prodMk measurable_const).prodMk
          (measurable_const.prodMk measurable_const))
  have hdirac (complier common y : Bool) :
      Measurable (fun x : 𝒳 =>
        Measure.dirac (witnessFullPack s x complier common y)) :=
    Measure.measurable_dirac.comp <| by
      rcases hpack complier common with ⟨htrue, hfalse⟩
      cases y <;> assumption
  exact by fun_prop (disch := aesop)

private lemma witnessPotentialKernel_probability (s : Bool) {p : 𝒳 → ℝ}
    {x : 𝒳} (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    IsProbabilityMeasure (witnessPotentialKernel s p x) := by
  unfold witnessPotentialKernel
  letI : IsProbabilityMeasure (witnessCoin (p x)) :=
    witnessCoin_probability hp0 hp1
  letI : IsProbabilityMeasure (witnessCoin (1 / 2)) :=
    witnessCoin_probability (by norm_num) (by norm_num)
  apply isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
  filter_upwards with complier
  apply isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
  filter_upwards with common
  have hmap : Measurable (fun y : Bool =>
      witnessFullPack s x complier common y) := measurable_of_finite _
  exact Measure.isProbabilityMeasure_map (μ := witnessCoin (1 / 2))
    hmap.aemeasurable

private noncomputable def witnessPopulationMeasure (s : Bool) (μ : Measure 𝒳)
    (p : 𝒳 → ℝ) : Measure (FullData 𝒳) :=
  μ.bind (witnessPotentialKernel s p)

private noncomputable def witnessFullMeasure (μS μT : Measure 𝒳)
    (p : 𝒳 → ℝ) : Measure (FullData 𝒳) :=
  ENNReal.ofReal (1 / 2 : ℝ) • witnessPopulationMeasure true μS p +
    ENNReal.ofReal (1 / 2 : ℝ) • witnessPopulationMeasure false μT p

private noncomputable def witnessAssignedMeasure (μS : Measure 𝒳)
    (p e : 𝒳 → ℝ) : Measure (AssignedFullData 𝒳) :=
  (witnessPopulationMeasure true μS p).bind fun o =>
    (witnessCoin (e (fullX o))).map (fun z => (o, z))

private lemma measurable_fullS : Measurable (fullS : FullData 𝒳 → Bool) :=
  measurable_fst

private lemma measurable_fullX : Measurable (fullX : FullData 𝒳 → 𝒳) :=
  measurable_fst.comp measurable_snd

private lemma measurable_witnessAssignmentKernel {e : 𝒳 → ℝ}
    (he : Measurable e) :
    Measurable (fun o : FullData 𝒳 =>
      (witnessCoin (e (fullX o))).map (fun z => (o, z))) := by
  simp_rw [witnessCoin_map]
  have hoz (z : Bool) :
      Measurable (fun o : FullData 𝒳 =>
        Measure.dirac (o, z)) :=
    Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const)
  have hex : Measurable (fun o : FullData 𝒳 => e (fullX o)) :=
    he.comp measurable_fullX
  exact (measurable_variable_smul_measure
    (ENNReal.measurable_ofReal.comp hex) (hoz true)).add <|
      measurable_variable_smul_measure
        (ENNReal.measurable_ofReal.comp (measurable_const.sub hex)) (hoz false)

private lemma witnessPopulationMeasure_probability
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    IsProbabilityMeasure (witnessPopulationMeasure s μ p) := by
  unfold witnessPopulationMeasure
  apply isProbabilityMeasure_bind
    (measurable_witnessPotentialKernel s hpmeas).aemeasurable
  filter_upwards with x
  exact witnessPotentialKernel_probability s (hp x).1 (hp x).2

private lemma witnessFullMeasure_probability
    {μS μT : Measure 𝒳} [IsProbabilityMeasure μS] [IsProbabilityMeasure μT]
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    IsProbabilityMeasure (witnessFullMeasure μS μT p) := by
  letI : IsProbabilityMeasure (witnessPopulationMeasure true μS p) :=
    witnessPopulationMeasure_probability true hpmeas hp
  letI : IsProbabilityMeasure (witnessPopulationMeasure false μT p) :=
    witnessPopulationMeasure_probability false hpmeas hp
  rw [isProbabilityMeasure_iff]
  unfold witnessFullMeasure
  simp [Measure.add_apply, Measure.smul_apply, measure_univ,
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1 / 2)
      (by positivity : (0 : ℝ) ≤ 1 / 2)]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

private lemma witnessAssignedMeasure_probability
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    IsProbabilityMeasure (witnessAssignedMeasure μS p e) := by
  letI : IsProbabilityMeasure (witnessPopulationMeasure true μS p) :=
    witnessPopulationMeasure_probability true hpmeas hp
  unfold witnessAssignedMeasure
  apply isProbabilityMeasure_bind
    (measurable_witnessAssignmentKernel hemeas).aemeasurable
  filter_upwards with o
  haveI : IsProbabilityMeasure (witnessCoin (e (fullX o))) :=
    witnessCoin_probability (he _).1 (he _).2
  exact Measure.isProbabilityMeasure_map
    (μ := witnessCoin (e (fullX o))) (measurable_of_finite _).aemeasurable

/-! ### The paper's `h`-indexed measure family

This parallel chain leaves the established centre witness unchanged.  Its
treated-outcome coin has success probability `1 / 2 + h` for compliers and
`1 / 2` for both non-complier types.
-/

private noncomputable def witnessPotentialKernelH (h : ℝ) (s : Bool)
    (p : 𝒳 → ℝ) (x : 𝒳) : Measure (FullData 𝒳) :=
  (witnessCoin (p x)).bind fun complier =>
    (witnessCoin (1 / 2)).bind fun common =>
      (witnessCoin (if complier then 1 / 2 + h else 1 / 2)).map
        (witnessFullPack s x complier common)

private lemma measurable_witnessPotentialKernelH (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hp : Measurable p) :
    Measurable (witnessPotentialKernelH h s p) := by
  unfold witnessPotentialKernelH
  simp_rw [witnessCoin_bind]
  simp_rw [witnessCoin_map]
  have hpack (complier common : Bool) :
      Measurable (fun x : 𝒳 => witnessFullPack s x complier common true) ∧
      Measurable (fun x : 𝒳 => witnessFullPack s x complier common false) := by
    constructor <;>
      exact (measurable_witnessFullPack s).comp
        ((measurable_id.prodMk measurable_const).prodMk
          (measurable_const.prodMk measurable_const))
  have hdirac (complier common y : Bool) :
      Measurable (fun x : 𝒳 =>
        Measure.dirac (witnessFullPack s x complier common y)) :=
    Measure.measurable_dirac.comp <| by
      rcases hpack complier common with ⟨htrue, hfalse⟩
      cases y <;> assumption
  exact by fun_prop (disch := aesop)

private lemma witnessPotentialKernelH_probability (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} {x : 𝒳} (hh : |h| ≤ 1 / 4)
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    IsProbabilityMeasure (witnessPotentialKernelH h s p x) := by
  have hh' := abs_le.mp hh
  have hy0 : 0 ≤ 1 / 2 + h := by linarith
  have hy1 : 1 / 2 + h ≤ 1 := by linarith
  unfold witnessPotentialKernelH
  letI : IsProbabilityMeasure (witnessCoin (p x)) :=
    witnessCoin_probability hp0 hp1
  letI : IsProbabilityMeasure (witnessCoin (1 / 2)) :=
    witnessCoin_probability (by norm_num) (by norm_num)
  apply isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
  filter_upwards with complier
  apply isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
  filter_upwards with common
  have hq0 : 0 ≤ if complier then 1 / 2 + h else 1 / 2 := by
    cases complier
    · norm_num
    · simpa using hy0
  have hq1 : (if complier then 1 / 2 + h else 1 / 2) ≤ 1 := by
    cases complier
    · norm_num
    · simpa using hy1
  letI : IsProbabilityMeasure
      (witnessCoin (if complier then 1 / 2 + h else 1 / 2)) :=
    witnessCoin_probability hq0 hq1
  exact Measure.isProbabilityMeasure_map
    (μ := witnessCoin (if complier then 1 / 2 + h else 1 / 2))
    (measurable_of_finite _).aemeasurable

private noncomputable def witnessPopulationMeasureH (h : ℝ) (s : Bool)
    (μ : Measure 𝒳) (p : 𝒳 → ℝ) : Measure (FullData 𝒳) :=
  μ.bind (witnessPotentialKernelH h s p)

private noncomputable def witnessFullMeasureH (h : ℝ)
    (μS μT : Measure 𝒳) (p : 𝒳 → ℝ) : Measure (FullData 𝒳) :=
  ENNReal.ofReal (1 / 2 : ℝ) • witnessPopulationMeasureH h true μS p +
    ENNReal.ofReal (1 / 2 : ℝ) • witnessPopulationMeasureH h false μT p

private noncomputable def witnessAssignedMeasureH (h : ℝ)
    (μS : Measure 𝒳) (p e : 𝒳 → ℝ) : Measure (AssignedFullData 𝒳) :=
  (witnessPopulationMeasureH h true μS p).bind fun o =>
    (witnessCoin (e (fullX o))).map (fun z => (o, z))

private lemma witnessPotentialKernelH_zero
    (s : Bool) (p : 𝒳 → ℝ) :
    witnessPotentialKernelH 0 s p = witnessPotentialKernel s p := by
  funext x
  simp [witnessPotentialKernelH, witnessPotentialKernel]

private lemma witnessPopulationMeasureH_zero
    (s : Bool) (μ : Measure 𝒳) (p : 𝒳 → ℝ) :
    witnessPopulationMeasureH 0 s μ p = witnessPopulationMeasure s μ p := by
  simp [witnessPopulationMeasureH, witnessPopulationMeasure,
    witnessPotentialKernelH_zero]

private lemma witnessFullMeasureH_zero
    (μS μT : Measure 𝒳) (p : 𝒳 → ℝ) :
    witnessFullMeasureH 0 μS μT p = witnessFullMeasure μS μT p := by
  simp [witnessFullMeasureH, witnessFullMeasure,
    witnessPopulationMeasureH_zero]

private lemma witnessAssignedMeasureH_zero
    (μS : Measure 𝒳) (p e : 𝒳 → ℝ) :
    witnessAssignedMeasureH 0 μS p e = witnessAssignedMeasure μS p e := by
  simp [witnessAssignedMeasureH, witnessAssignedMeasure,
    witnessPopulationMeasureH_zero]

private lemma witnessPopulationMeasureH_probability
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    IsProbabilityMeasure (witnessPopulationMeasureH h s μ p) := by
  unfold witnessPopulationMeasureH
  apply isProbabilityMeasure_bind
    (measurable_witnessPotentialKernelH h s hpmeas).aemeasurable
  filter_upwards with x
  exact witnessPotentialKernelH_probability h s hh (hp x).1 (hp x).2

private lemma witnessFullMeasureH_probability
    {μS μT : Measure 𝒳} [IsProbabilityMeasure μS] [IsProbabilityMeasure μT]
    {h : ℝ} {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hpmeas : Measurable p) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    IsProbabilityMeasure (witnessFullMeasureH h μS μT p) := by
  letI : IsProbabilityMeasure (witnessPopulationMeasureH h true μS p) :=
    witnessPopulationMeasureH_probability h true hh hpmeas hp
  letI : IsProbabilityMeasure (witnessPopulationMeasureH h false μT p) :=
    witnessPopulationMeasureH_probability h false hh hpmeas hp
  rw [isProbabilityMeasure_iff]
  unfold witnessFullMeasureH
  simp [Measure.add_apply, Measure.smul_apply, measure_univ,
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1 / 2)
      (by positivity : (0 : ℝ) ≤ 1 / 2)]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

private lemma witnessAssignedMeasureH_probability
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {h : ℝ} {p e : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    IsProbabilityMeasure (witnessAssignedMeasureH h μS p e) := by
  letI : IsProbabilityMeasure (witnessPopulationMeasureH h true μS p) :=
    witnessPopulationMeasureH_probability h true hh hpmeas hp
  unfold witnessAssignedMeasureH
  apply isProbabilityMeasure_bind
    (measurable_witnessAssignmentKernel hemeas).aemeasurable
  filter_upwards with o
  haveI : IsProbabilityMeasure (witnessCoin (e (fullX o))) :=
    witnessCoin_probability (he _).1 (he _).2
  exact Measure.isProbabilityMeasure_map
    (μ := witnessCoin (e (fullX o))) (measurable_of_finite _).aemeasurable

private lemma witnessPotentialKernel_fullX
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    witnessPotentialKernel s p x {o | fullX o ∈ A} =
      A.indicator 1 x := by
  unfold witnessPotentialKernel
  rw [witnessCoin_bind]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hEvent : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  simp_rw [Measure.dirac_apply' _ hEvent]
  simp only [witnessFullPack, fullX, Set.indicator, Pi.one_apply]
  have hhalf : (2 : ENNReal)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hhalfsub : ENNReal.ofReal (1 - (1 / 2 : ℝ)) = (2 : ENNReal)⁻¹ := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by ring,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hpadd : ENNReal.ofReal (p x) + ENNReal.ofReal (1 - p x) = 1 := by
    rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
    convert ENNReal.ofReal_one using 1 <;> ring
  simp_rw [hhalfsub]
  by_cases hx : x ∈ A
  · simp [hx, hhalfsub, hhalf, hpadd]
  · simp [hx]

private lemma witnessPotentialKernel_fullS
    (s t : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    witnessPotentialKernel s p x {o | fullS o = t} =
      if s = t then 1 else 0 := by
  unfold witnessPotentialKernel
  rw [witnessCoin_bind]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  have hset : MeasurableSet {o : FullData 𝒳 | fullS o = t} :=
    measurableSet_eq_fun measurable_fullS measurable_const
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ hset]
  simp only [witnessFullPack, fullS, Set.indicator, Pi.one_apply]
  have hhalf : (2 : ENNReal)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hhalfsub : ENNReal.ofReal (1 - (1 / 2 : ℝ)) = (2 : ENNReal)⁻¹ := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by ring,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hpadd : ENNReal.ofReal (p x) + ENNReal.ofReal (1 - p x) = 1 := by
    rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
    convert ENNReal.ofReal_one using 1 <;> ring
  simp_rw [hhalfsub]
  by_cases hst : s = t
  · simp [hst, hhalfsub, hhalf, hpadd]
  · simp [hst]

private lemma witnessPotentialKernel_event_eq_one
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (B : Set (FullData 𝒳)) (hB : MeasurableSet B)
    (hpack : ∀ complier common y,
      witnessFullPack s x complier common y ∈ B) :
    witnessPotentialKernel s p x B = 1 := by
  unfold witnessPotentialKernel
  rw [witnessCoin_bind]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ hB]
  simp_rw [Set.indicator_of_mem (hpack _ _ _)]
  have hhalf : (2 : ENNReal)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hhalfsub : ENNReal.ofReal (1 - (1 / 2 : ℝ)) = (2 : ENNReal)⁻¹ := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by ring,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hpadd : ENNReal.ofReal (p x) + ENNReal.ofReal (1 - p x) = 1 := by
    rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
    convert ENNReal.ofReal_one using 1 <;> ring
  simp_rw [hhalfsub]
  simp [hhalf, hpadd]

private lemma witnessPotentialKernel_complier
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    witnessPotentialKernel s p x
        {o | fullD1 o = true ∧ fullD0 o = false} =
      ENNReal.ofReal (p x) := by
  unfold witnessPotentialKernel
  rw [witnessCoin_bind]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  have hset : MeasurableSet {o : FullData 𝒳 |
      fullD1 o = true ∧ fullD0 o = false} :=
    (measurableSet_eq_fun
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ hset]
  simp only [witnessFullPack, fullD0, fullD1, Set.indicator]
  have hhalf : (2 : ENNReal)⁻¹ + 2⁻¹ = 1 := by
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hhalfsub : ENNReal.ofReal (1 - (1 / 2 : ℝ)) = (2 : ENNReal)⁻¹ := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by ring,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  simp_rw [hhalfsub]
  simp [hhalf]

private def witnessGood (o : FullData 𝒳) : Prop :=
  fullY0 o = 0 ∧ (fullY1 o = 0 ∨ fullY1 o = 1) ∧
  boolReal (fullD0 o) ≤ boolReal (fullD1 o) ∧
  derivedAssignmentOutcome o true - derivedAssignmentOutcome o false =
    (boolReal (fullD1 o) - boolReal (fullD0 o)) * fullY1 o

private lemma measurableSet_witnessGood :
    MeasurableSet {o : FullData 𝒳 | witnessGood o} := by
  have hy0 : Measurable (fun o : FullData 𝒳 => fullY0 o) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hy1 : Measurable (fun o : FullData 𝒳 => fullY1 o) :=
    measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hd0 : Measurable (fun o : FullData 𝒳 => boolReal (fullD0 o)) := by
    unfold boolReal
    exact Measurable.ite
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const) measurable_const measurable_const
  have hd1 : Measurable (fun o : FullData 𝒳 => boolReal (fullD1 o)) := by
    unfold boolReal
    exact Measurable.ite
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const) measurable_const measurable_const
  have hout (z : Bool) :
      Measurable (fun o : FullData 𝒳 => derivedAssignmentOutcome o z) := by
    unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
    have hd : Measurable (fun o : FullData 𝒳 =>
        if z then fullD1 o else fullD0 o) :=
      Measurable.ite
        (measurableSet_eq_fun measurable_const measurable_const)
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    exact Measurable.ite (measurableSet_eq_fun hd measurable_const) hy1 hy0
  exact (measurableSet_eq_fun hy0 measurable_const).inter <|
    ((measurableSet_eq_fun hy1 measurable_const).union
      (measurableSet_eq_fun hy1 measurable_const)).inter <|
    (measurableSet_le hd0 hd1).inter <|
    measurableSet_eq_fun ((hout true).sub (hout false))
      ((hd1.sub hd0).mul hy1)

private lemma witnessPotentialKernel_ae_good
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∀ᵐ o ∂witnessPotentialKernel s p x,
      fullY0 o = 0 ∧ (fullY1 o = 0 ∨ fullY1 o = 1) ∧
      boolReal (fullD0 o) ≤ boolReal (fullD1 o) ∧
      derivedAssignmentOutcome o true - derivedAssignmentOutcome o false =
        (boolReal (fullD1 o) - boolReal (fullD0 o)) * fullY1 o := by
  letI : IsProbabilityMeasure (witnessPotentialKernel s p x) :=
    witnessPotentialKernel_probability s hp0 hp1
  show ∀ᵐ o ∂witnessPotentialKernel s p x,
    o ∈ {o : FullData 𝒳 | witnessGood o}
  rw [ae_mem_iff_measure_eq measurableSet_witnessGood.nullMeasurableSet]
  rw [witnessPotentialKernel_event_eq_one s hp0 hp1
    {o : FullData 𝒳 | witnessGood o} measurableSet_witnessGood]
  · rw [measure_univ]
  · intro complier common y
    cases complier <;> cases common <;> cases y <;>
      simp [witnessGood, witnessFullPack, fullY0, fullY1, fullD0, fullD1,
        boolReal, derivedAssignmentOutcome, potentialOutcome, potentialReceipt]

private lemma witnessPotentialKernel_receipt_integral
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∫ o, (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂witnessPotentialKernel s p x = p x := by
  let f : FullData 𝒳 → ℝ :=
    fun o => boolReal (fullD1 o) - boolReal (fullD0 o)
  have hfmeas : Measurable f := by
    unfold f
    have hd0 : Measurable (fun o : FullData 𝒳 => boolReal (fullD0 o)) := by
      unfold boolReal
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_fst.comp (measurable_snd.comp measurable_snd))
          measurable_const) measurable_const measurable_const
    have hd1 : Measurable (fun o : FullData 𝒳 => boolReal (fullD1 o)) := by
      unfold boolReal
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_fst.comp
            (measurable_snd.comp (measurable_snd.comp measurable_snd)))
          measurable_const) measurable_const measurable_const
    exact hd1.sub hd0
  letI : IsProbabilityMeasure (witnessCoin (p x)) :=
    witnessCoin_probability hp0 hp1
  letI : IsProbabilityMeasure (witnessCoin (1 / 2)) :=
    witnessCoin_probability (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (witnessPotentialKernel s p x) :=
    witnessPotentialKernel_probability s hp0 hp1
  have hf : Integrable f (witnessPotentialKernel s p x) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    simp only [Real.norm_eq_abs]
    cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
      norm_num [f, boolReal, h0, h1]
  have hf₂ : ∀ᵐ complier ∂witnessCoin (p x),
      Integrable (fun common =>
        ∫ y, f (witnessFullPack s x complier common y)
          ∂witnessCoin (1 / 2)) (witnessCoin (1 / 2)) := by
    filter_upwards with complier
    exact Integrable.of_finite
  have hf' : Integrable (fun complier =>
      ∫ common, ∫ y, f (witnessFullPack s x complier common y)
        ∂witnessCoin (1 / 2) ∂witnessCoin (1 / 2))
      (witnessCoin (p x)) :=
    Integrable.of_finite
  have hcollapse :=
    Causalean.Mathlib.MeasureTheory.integral_bind_bind_map
      (m := witnessCoin (p x))
      (κ₁ := fun _ : Bool => witnessCoin (1 / 2))
      (κ₂ := fun _ _ : Bool => witnessCoin (1 / 2))
      (g := fun complier common y =>
        witnessFullPack s x complier common y)
      (f := f)
      (fun _ _ => measurable_of_finite _)
      (fun _ => measurable_of_finite _)
      (measurable_of_finite _) hf
  rw [show witnessPotentialKernel s p x =
      (witnessCoin (p x)).bind fun complier =>
        (witnessCoin (1 / 2)).bind fun common =>
          (witnessCoin (1 / 2)).map
            (witnessFullPack s x complier common) by rfl]
  rw [hcollapse]
  simp_rw [witnessCoin_integral (p := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)]
  rw [witnessCoin_integral hp0 hp1]
  simp [f, witnessFullPack, fullD0, fullD1, boolReal]

private noncomputable def witnessOutcomeContrast (o : FullData 𝒳) : ℝ :=
  (boolReal (fullD1 o) - boolReal (fullD0 o)) *
    if fullY1 o = 1 then 1 else 0

private lemma measurable_witnessOutcomeContrast :
    Measurable (witnessOutcomeContrast : FullData 𝒳 → ℝ) := by
  have hd0 : Measurable (fun o : FullData 𝒳 => boolReal (fullD0 o)) := by
    unfold boolReal
    exact Measurable.ite
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const) measurable_const measurable_const
  have hd1 : Measurable (fun o : FullData 𝒳 => boolReal (fullD1 o)) := by
    unfold boolReal
    exact Measurable.ite
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const) measurable_const measurable_const
  have hy1 : Measurable (fun o : FullData 𝒳 => fullY1 o) :=
    measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact (hd1.sub hd0).mul <| Measurable.ite
    (measurableSet_eq_fun hy1 measurable_const)
    measurable_const measurable_const

private lemma witnessPotentialKernel_outcome_integral
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∫ o, witnessOutcomeContrast o ∂witnessPotentialKernel s p x =
      p x / 2 := by
  letI : IsProbabilityMeasure (witnessCoin (p x)) :=
    witnessCoin_probability hp0 hp1
  letI : IsProbabilityMeasure (witnessCoin (1 / 2)) :=
    witnessCoin_probability (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (witnessPotentialKernel s p x) :=
    witnessPotentialKernel_probability s hp0 hp1
  have hf : Integrable (witnessOutcomeContrast : FullData 𝒳 → ℝ)
      (witnessPotentialKernel s p x) := by
    refine Integrable.of_bound
      measurable_witnessOutcomeContrast.aestronglyMeasurable 1 ?_
    filter_upwards with o
    unfold witnessOutcomeContrast
    by_cases hy : fullY1 o = 1
    · cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
        norm_num [boolReal, hy, h0, h1]
    · simp [hy]
  have hf₂ : ∀ᵐ complier ∂witnessCoin (p x),
      Integrable (fun common =>
        ∫ y, witnessOutcomeContrast
          (witnessFullPack s x complier common y)
          ∂witnessCoin (1 / 2)) (witnessCoin (1 / 2)) := by
    filter_upwards with complier
    exact Integrable.of_finite
  have hf' : Integrable (fun complier =>
      ∫ common, ∫ y, witnessOutcomeContrast
        (witnessFullPack s x complier common y)
        ∂witnessCoin (1 / 2) ∂witnessCoin (1 / 2))
      (witnessCoin (p x)) :=
    Integrable.of_finite
  have hcollapse :=
    Causalean.Mathlib.MeasureTheory.integral_bind_bind_map
      (m := witnessCoin (p x))
      (κ₁ := fun _ : Bool => witnessCoin (1 / 2))
      (κ₂ := fun _ _ : Bool => witnessCoin (1 / 2))
      (g := fun complier common y =>
        witnessFullPack s x complier common y)
      (f := witnessOutcomeContrast)
      (fun _ _ => measurable_of_finite _)
      (fun _ => measurable_of_finite _)
      (measurable_of_finite _) hf
  rw [show witnessPotentialKernel s p x =
      (witnessCoin (p x)).bind fun complier =>
        (witnessCoin (1 / 2)).bind fun common =>
          (witnessCoin (1 / 2)).map
            (witnessFullPack s x complier common) by rfl]
  rw [hcollapse]
  simp_rw [witnessCoin_integral (p := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)]
  rw [witnessCoin_integral hp0 hp1]
  simp [witnessOutcomeContrast, witnessFullPack, fullD0, fullD1,
    fullY1, boolReal]
  ring

private lemma witnessPotentialKernel_receipt_indicator_integral
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A},
        (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂witnessPotentialKernel s p x =
      A.indicator p x := by
  letI : IsProbabilityMeasure (witnessPotentialKernel s p x) :=
    witnessPotentialKernel_probability s hp0 hp1
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  by_cases hx : x ∈ A
  · have hmem : ∀ᵐ o ∂witnessPotentialKernel s p x, fullX o ∈ A := by
      show ∀ᵐ o ∂witnessPotentialKernel s p x,
        o ∈ {o : FullData 𝒳 | fullX o ∈ A}
      rw [ae_mem_iff_measure_eq hset.nullMeasurableSet]
      rw [witnessPotentialKernel_fullX s hp0 hp1 A hA,
        Set.indicator_of_mem hx]
      rw [measure_univ]
      rfl
    rw [← integral_indicator hset]
    calc
      ∫ o, {o | fullX o ∈ A}.indicator
          (fun o => boolReal (fullD1 o) - boolReal (fullD0 o)) o
          ∂witnessPotentialKernel s p x =
          ∫ o, (boolReal (fullD1 o) - boolReal (fullD0 o))
            ∂witnessPotentialKernel s p x := by
              apply integral_congr_ae
              filter_upwards [hmem] with o ho
              simp [ho]
      _ = p x := witnessPotentialKernel_receipt_integral s hp0 hp1
      _ = A.indicator p x := by simp [hx]
  · have hzero :
        witnessPotentialKernel s p x {o | fullX o ∈ A} = 0 := by
      rw [witnessPotentialKernel_fullX s hp0 hp1 A hA,
        Set.indicator_of_notMem hx]
    rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]
    simp [hx]

private lemma witnessPotentialKernel_outcome_indicator_integral
    (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A}, witnessOutcomeContrast o
        ∂witnessPotentialKernel s p x =
      A.indicator (fun x => p x / 2) x := by
  letI : IsProbabilityMeasure (witnessPotentialKernel s p x) :=
    witnessPotentialKernel_probability s hp0 hp1
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  by_cases hx : x ∈ A
  · have hmem : ∀ᵐ o ∂witnessPotentialKernel s p x, fullX o ∈ A := by
      show ∀ᵐ o ∂witnessPotentialKernel s p x,
        o ∈ {o : FullData 𝒳 | fullX o ∈ A}
      rw [ae_mem_iff_measure_eq hset.nullMeasurableSet]
      rw [witnessPotentialKernel_fullX s hp0 hp1 A hA,
        Set.indicator_of_mem hx, measure_univ]
      rfl
    rw [← integral_indicator hset]
    calc
      ∫ o, {o | fullX o ∈ A}.indicator witnessOutcomeContrast o
          ∂witnessPotentialKernel s p x =
          ∫ o, witnessOutcomeContrast o
            ∂witnessPotentialKernel s p x := by
              apply integral_congr_ae
              filter_upwards [hmem] with o ho
              simp [ho]
      _ = p x / 2 := witnessPotentialKernel_outcome_integral s hp0 hp1
      _ = A.indicator (fun x => p x / 2) x := by simp [hx]
  · have hzero :
        witnessPotentialKernel s p x {o | fullX o ∈ A} = 0 := by
      rw [witnessPotentialKernel_fullX s hp0 hp1 A hA,
        Set.indicator_of_notMem hx]
    rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]
    simp [hx]

private lemma witnessPopulationMeasure_receipt_integral
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A},
        (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂witnessPopulationMeasure s μ p =
      ∫ x in A, p x ∂μ := by
  have hprob : IsProbabilityMeasure (witnessPopulationMeasure s μ p) :=
    witnessPopulationMeasure_probability s hpmeas hp
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  let f : FullData 𝒳 → ℝ := fun o =>
    {o | fullX o ∈ A}.indicator
      (fun o => boolReal (fullD1 o) - boolReal (fullD0 o)) o
  have hfmeas : Measurable f := by
    apply Measurable.indicator
    · have hd0 : Measurable (fun o : FullData 𝒳 => boolReal (fullD0 o)) := by
        unfold boolReal
        exact Measurable.ite
          (measurableSet_eq_fun
            (measurable_fst.comp (measurable_snd.comp measurable_snd))
            measurable_const) measurable_const measurable_const
      have hd1 : Measurable (fun o : FullData 𝒳 => boolReal (fullD1 o)) := by
        unfold boolReal
        exact Measurable.ite
          (measurableSet_eq_fun
            (measurable_fst.comp
              (measurable_snd.comp (measurable_snd.comp measurable_snd)))
            measurable_const) measurable_const measurable_const
      exact hd1.sub hd0
    · exact hA.preimage measurable_fullX
  have hf : Integrable f (witnessPopulationMeasure s μ p) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    by_cases ho : fullX o ∈ A
    · change ‖f o‖ ≤ 1
      cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
        norm_num [f, boolReal, ho, h0, h1]
    · simp [f, ho]
  rw [← integral_indicator (μ := witnessPopulationMeasure s μ p) hset]
  change ∫ o, f o ∂witnessPopulationMeasure s μ p = ∫ x in A, p x ∂μ
  unfold witnessPopulationMeasure
  rw [Causalean.Mathlib.MeasureTheory.integral_bind
    (measurable_witnessPotentialKernel s hpmeas) hf]
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with x
  rw [integral_indicator hset]
  exact witnessPotentialKernel_receipt_indicator_integral
    s (hp x).1 (hp x).2 A hA

private lemma witnessPopulationMeasure_outcomeContrast_integral
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A}, witnessOutcomeContrast o
        ∂witnessPopulationMeasure s μ p =
      ∫ x in A, p x / 2 ∂μ := by
  letI : IsProbabilityMeasure (witnessPopulationMeasure s μ p) :=
    witnessPopulationMeasure_probability s hpmeas hp
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  let f : FullData 𝒳 → ℝ :=
    fun o => {o | fullX o ∈ A}.indicator witnessOutcomeContrast o
  have hfmeas : Measurable f :=
    measurable_witnessOutcomeContrast.indicator hset
  have hf : Integrable f (witnessPopulationMeasure s μ p) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    by_cases ho : fullX o ∈ A
    · dsimp [f]
      have homem : o ∈ {o : FullData 𝒳 | fullX o ∈ A} := ho
      rw [Set.indicator_of_mem homem]
      unfold witnessOutcomeContrast
      by_cases hy : fullY1 o = 1
      · cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
          norm_num [boolReal, hy, h0, h1]
      · simp [hy]
    · simp [f, ho]
  rw [← integral_indicator (μ := witnessPopulationMeasure s μ p) hset]
  change ∫ o, f o ∂witnessPopulationMeasure s μ p =
    ∫ x in A, p x / 2 ∂μ
  unfold witnessPopulationMeasure
  rw [Causalean.Mathlib.MeasureTheory.integral_bind
    (measurable_witnessPotentialKernel s hpmeas) hf]
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with x
  rw [integral_indicator hset]
  exact witnessPotentialKernel_outcome_indicator_integral
    s (hp x).1 (hp x).2 A hA

private lemma witnessPopulationMeasure_ae_good
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ᵐ o ∂witnessPopulationMeasure s μ p, witnessGood o := by
  have hprob : IsProbabilityMeasure (witnessPopulationMeasure s μ p) :=
    witnessPopulationMeasure_probability s hpmeas hp
  show ∀ᵐ o ∂witnessPopulationMeasure s μ p,
    o ∈ {o : FullData 𝒳 | witnessGood o}
  rw [ae_mem_iff_measure_eq measurableSet_witnessGood.nullMeasurableSet]
  unfold witnessPopulationMeasure
  letI : IsProbabilityMeasure (μ.bind (witnessPotentialKernel s p)) := by
    simpa only [witnessPopulationMeasure] using hprob
  rw [Measure.bind_apply measurableSet_witnessGood
    (measurable_witnessPotentialKernel s hpmeas).aemeasurable]
  have hkernel (x : 𝒳) :
      witnessPotentialKernel s p x {o : FullData 𝒳 | witnessGood o} = 1 := by
    apply witnessPotentialKernel_event_eq_one s (hp x).1 (hp x).2
      {o : FullData 𝒳 | witnessGood o} measurableSet_witnessGood
    intro complier common y
    cases complier <;> cases common <;> cases y <;>
      simp [witnessGood, witnessFullPack, fullY0, fullY1, fullD0, fullD1,
        boolReal, derivedAssignmentOutcome, potentialOutcome, potentialReceipt]
  simp_rw [hkernel]
  rw [lintegral_const, measure_univ, measure_univ]
  simp

private lemma witnessPopulationMeasure_complier
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    (witnessPopulationMeasure s μ p
      {o | fullD1 o = true ∧ fullD0 o = false}).toReal =
      ∫ x, p x ∂μ := by
  have hset : MeasurableSet {o : FullData 𝒳 |
      fullD1 o = true ∧ fullD0 o = false} :=
    (measurableSet_eq_fun
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const)
  have hpint : Integrable p μ := by
    refine Integrable.of_bound hpmeas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hp x).1]
    exact (hp x).2
  have hp0 : 0 ≤ᵐ[μ] p := Filter.Eventually.of_forall fun x => (hp x).1
  have hmeasure :
      witnessPopulationMeasure s μ p
          {o | fullD1 o = true ∧ fullD0 o = false} =
        ENNReal.ofReal (∫ x, p x ∂μ) := by
    unfold witnessPopulationMeasure
    rw [Measure.bind_apply hset
      (measurable_witnessPotentialKernel s hpmeas).aemeasurable]
    simp_rw [witnessPotentialKernel_complier s (hp _).1 (hp _).2]
    rw [← ofReal_integral_eq_lintegral_ofReal hpint hp0]
  rw [hmeasure, ENNReal.toReal_ofReal (integral_nonneg_of_ae hp0)]

private lemma witnessPopulationMeasure_outcome_integral
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A},
        (derivedAssignmentOutcome o true - derivedAssignmentOutcome o false)
        ∂witnessPopulationMeasure s μ p =
      ∫ x in A, p x / 2 ∂μ := by
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  rw [← integral_indicator hset]
  calc
    ∫ o, {o | fullX o ∈ A}.indicator
        (fun o => derivedAssignmentOutcome o true -
          derivedAssignmentOutcome o false) o
        ∂witnessPopulationMeasure s μ p =
        ∫ o, {o | fullX o ∈ A}.indicator witnessOutcomeContrast o
          ∂witnessPopulationMeasure s μ p := by
            apply integral_congr_ae
            filter_upwards [witnessPopulationMeasure_ae_good s hpmeas hp]
              with o ho
            rcases ho.2.1 with hy | hy
            · by_cases hxo : fullX o ∈ A
              · simp [hxo, ho.2.2.2, witnessOutcomeContrast, hy]
              · simp [hxo]
            · by_cases hxo : fullX o ∈ A
              · simp [hxo, ho.2.2.2, witnessOutcomeContrast, hy]
              · simp [hxo]
    _ = ∫ o in {o | fullX o ∈ A}, witnessOutcomeContrast o
          ∂witnessPopulationMeasure s μ p := integral_indicator hset
    _ = ∫ x in A, p x / 2 ∂μ :=
      witnessPopulationMeasure_outcomeContrast_integral s hpmeas hp A hA

private lemma witnessPopulationMeasure_map_fullX
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    (witnessPopulationMeasure s μ p).map fullX = μ := by
  ext A hA
  rw [Measure.map_apply measurable_fullX hA]
  unfold witnessPopulationMeasure
  rw [Measure.bind_apply (hA.preimage measurable_fullX)
    (measurable_witnessPotentialKernel s hpmeas).aemeasurable]
  change (∫⁻ a, witnessPotentialKernel s p a {o | fullX o ∈ A} ∂μ) = μ A
  simp_rw [witnessPotentialKernel_fullX s (hp _).1 (hp _).2 A hA]
  rw [lintegral_indicator hA]
  simp

private lemma witnessPopulationMeasure_setIntegral_fullX
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (f : 𝒳 → ℝ) (hf : Measurable f)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A}, f (fullX o)
        ∂witnessPopulationMeasure s μ p =
      ∫ x in A, f x ∂μ := by
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  rw [← integral_indicator hset, ← integral_indicator hA]
  change ∫ o, (A.indicator f) (fullX o)
      ∂witnessPopulationMeasure s μ p =
    ∫ x, A.indicator f x ∂μ
  rw [← integral_map measurable_fullX.aemeasurable
    (hf.indicator hA).aestronglyMeasurable]
  rw [witnessPopulationMeasure_map_fullX s hpmeas hp]

private lemma witnessPopulationMeasure_population_mass
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s t : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    witnessPopulationMeasure s μ p {o | fullS o = t} =
      if s = t then 1 else 0 := by
  unfold witnessPopulationMeasure
  have hset : MeasurableSet {o : FullData 𝒳 | fullS o = t} :=
    measurableSet_eq_fun measurable_fullS measurable_const
  rw [Measure.bind_apply hset
    (measurable_witnessPotentialKernel s hpmeas).aemeasurable]
  simp_rw [witnessPotentialKernel_fullS s t (hp _).1 (hp _).2]
  split_ifs <;> simp

private lemma witnessPopulationMeasure_inter_population
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (s t : Bool)
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set (FullData 𝒳)) (hA : MeasurableSet A) :
    witnessPopulationMeasure s μ p ({o | fullS o = t} ∩ A) =
      if s = t then witnessPopulationMeasure s μ p A else 0 := by
  letI : IsProbabilityMeasure (witnessPopulationMeasure s μ p) :=
    witnessPopulationMeasure_probability s hpmeas hp
  have hst : MeasurableSet {o : FullData 𝒳 | fullS o = t} :=
    measurableSet_eq_fun measurable_fullS measurable_const
  by_cases heq : s = t
  · rw [if_pos heq, Set.inter_comm,
      ← Measure.restrict_apply hA]
    rw [Measure.restrict_eq_self_of_ae_mem]
    rw [ae_mem_iff_measure_eq hst.nullMeasurableSet]
    rw [witnessPopulationMeasure_population_mass s t hpmeas hp,
      if_pos heq, measure_univ]
  · rw [if_neg heq, Set.inter_comm,
      ← Measure.restrict_apply hA]
    have hz : witnessPopulationMeasure s μ p {o | fullS o = t} = 0 := by
      rw [witnessPopulationMeasure_population_mass s t hpmeas hp,
        if_neg heq]
    rw [Measure.restrict_eq_zero.mpr hz]
    rfl

private lemma witnessFullMeasure_cond
    {μS μT : Measure 𝒳} [IsProbabilityMeasure μS] [IsProbabilityMeasure μT]
    {p : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (s : Bool) :
    ProbabilityTheory.cond (witnessFullMeasure μS μT p)
        {o | fullS o = s} =
      if s then witnessPopulationMeasure true μS p
      else witnessPopulationMeasure false μT p := by
  ext A hA
  have hs : MeasurableSet {o : FullData 𝒳 | fullS o = s} :=
    measurableSet_eq_fun measurable_fullS measurable_const
  rw [ProbabilityTheory.cond_apply hs]
  unfold witnessFullMeasure
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [witnessPopulationMeasure_population_mass true s hpmeas hp,
    witnessPopulationMeasure_population_mass false s hpmeas hp,
    witnessPopulationMeasure_inter_population true s hpmeas hp A hA,
    witnessPopulationMeasure_inter_population false s hpmeas hp A hA]
  cases s <;> simp
  all_goals
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

private lemma witnessPotentialKernelH_event
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (B : Set (FullData 𝒳)) (hB : MeasurableSet B) (q : Prop)
    [Decidable q]
    (hpack : ∀ complier common y,
      witnessFullPack s x complier common y ∈ B ↔ q) :
    witnessPotentialKernelH h s p x B = if q then 1 else 0 := by
  have hh' := abs_le.mp hh
  have hy0 : 0 ≤ 1 / 2 + h := by linarith
  have hy1 : 1 / 2 + h ≤ 1 := by linarith
  unfold witnessPotentialKernelH
  letI : IsProbabilityMeasure (witnessCoin (p x)) :=
    witnessCoin_probability hp0 hp1
  letI : IsProbabilityMeasure (witnessCoin (1 / 2)) :=
    witnessCoin_probability (by norm_num) (by norm_num)
  have hmap (complier common : Bool) :
      (witnessCoin (if complier then 1 / 2 + h else 1 / 2)).map
          (witnessFullPack s x complier common) B =
        if q then 1 else 0 := by
    have hq0 : 0 ≤ if complier then 1 / 2 + h else 1 / 2 := by
      cases complier
      · norm_num
      · simpa using hy0
    have hq1 : (if complier then 1 / 2 + h else 1 / 2) ≤ 1 := by
      cases complier
      · norm_num
      · simpa using hy1
    letI : IsProbabilityMeasure
        (witnessCoin (if complier then 1 / 2 + h else 1 / 2)) :=
      witnessCoin_probability hq0 hq1
    rw [Measure.map_apply (measurable_of_finite _) hB]
    by_cases hq : q
    · have heq :
          (witnessFullPack s x complier common) ⁻¹' B = Set.univ := by
        ext y
        simp [hpack complier common y, hq]
      rw [heq, measure_univ, if_pos hq]
    · have heq :
          (witnessFullPack s x complier common) ⁻¹' B = ∅ := by
        ext y
        simp [hpack complier common y, hq]
      rw [heq, measure_empty, if_neg hq]
  have hcommon (complier : Bool) :
      (witnessCoin (1 / 2)).bind (fun common =>
        (witnessCoin (if complier then 1 / 2 + h else 1 / 2)).map
          (witnessFullPack s x complier common)) B =
        if q then 1 else 0 := by
    rw [Measure.bind_apply hB (measurable_of_finite _).aemeasurable]
    simp_rw [hmap complier]
    rw [lintegral_const, measure_univ]
    split_ifs <;> simp
  rw [Measure.bind_apply hB (measurable_of_finite _).aemeasurable]
  simp_rw [hcommon]
  rw [lintegral_const, measure_univ]
  split_ifs <;> simp

private lemma witnessPotentialKernelH_fullX
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    witnessPotentialKernelH h s p x {o | fullX o ∈ A} =
      A.indicator 1 x := by
  classical
  rw [witnessPotentialKernelH_event h s hh hp0 hp1
    {o : FullData 𝒳 | fullX o ∈ A}
    (hA.preimage measurable_fullX) (x ∈ A)]
  · by_cases hx : x ∈ A <;> simp [hx]
  · intro complier common y
    simp [witnessFullPack, fullX]

private lemma witnessPotentialKernelH_fullS
    (h : ℝ) (s t : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    witnessPotentialKernelH h s p x {o | fullS o = t} =
      if s = t then 1 else 0 := by
  apply witnessPotentialKernelH_event h s hh hp0 hp1
    {o : FullData 𝒳 | fullS o = t}
    (measurableSet_eq_fun measurable_fullS measurable_const) (s = t)
  intro complier common y
  simp [witnessFullPack, fullS]

private lemma witnessPopulationMeasureH_map_fullX
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    (witnessPopulationMeasureH h s μ p).map fullX = μ := by
  ext A hA
  rw [Measure.map_apply measurable_fullX hA]
  unfold witnessPopulationMeasureH
  rw [Measure.bind_apply (hA.preimage measurable_fullX)
    (measurable_witnessPotentialKernelH h s hpmeas).aemeasurable]
  change (∫⁻ a, witnessPotentialKernelH h s p a
    {o | fullX o ∈ A} ∂μ) = μ A
  simp_rw [witnessPotentialKernelH_fullX h s hh
    (hp _).1 (hp _).2 A hA]
  rw [lintegral_indicator hA]
  simp

private lemma witnessPopulationMeasureH_population_mass
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s t : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    witnessPopulationMeasureH h s μ p {o | fullS o = t} =
      if s = t then 1 else 0 := by
  unfold witnessPopulationMeasureH
  have hset : MeasurableSet {o : FullData 𝒳 | fullS o = t} :=
    measurableSet_eq_fun measurable_fullS measurable_const
  rw [Measure.bind_apply hset
    (measurable_witnessPotentialKernelH h s hpmeas).aemeasurable]
  simp_rw [witnessPotentialKernelH_fullS h s t hh
    (hp _).1 (hp _).2]
  split_ifs <;> simp

private lemma witnessPopulationMeasureH_inter_population
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s t : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set (FullData 𝒳)) (hA : MeasurableSet A) :
    witnessPopulationMeasureH h s μ p ({o | fullS o = t} ∩ A) =
      if s = t then witnessPopulationMeasureH h s μ p A else 0 := by
  letI : IsProbabilityMeasure (witnessPopulationMeasureH h s μ p) :=
    witnessPopulationMeasureH_probability h s hh hpmeas hp
  have hst : MeasurableSet {o : FullData 𝒳 | fullS o = t} :=
    measurableSet_eq_fun measurable_fullS measurable_const
  by_cases heq : s = t
  · rw [if_pos heq, Set.inter_comm, ← Measure.restrict_apply hA]
    rw [Measure.restrict_eq_self_of_ae_mem]
    rw [ae_mem_iff_measure_eq hst.nullMeasurableSet]
    rw [witnessPopulationMeasureH_population_mass h s t hh hpmeas hp,
      if_pos heq, measure_univ]
  · rw [if_neg heq, Set.inter_comm, ← Measure.restrict_apply hA]
    have hz : witnessPopulationMeasureH h s μ p {o | fullS o = t} = 0 := by
      rw [witnessPopulationMeasureH_population_mass h s t hh hpmeas hp,
        if_neg heq]
    rw [Measure.restrict_eq_zero.mpr hz]
    rfl

private lemma witnessFullMeasureH_cond
    {μS μT : Measure 𝒳} [IsProbabilityMeasure μS] [IsProbabilityMeasure μT]
    {h : ℝ} {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hpmeas : Measurable p) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (s : Bool) :
    ProbabilityTheory.cond (witnessFullMeasureH h μS μT p)
        {o | fullS o = s} =
      if s then witnessPopulationMeasureH h true μS p
      else witnessPopulationMeasureH h false μT p := by
  ext A hA
  have hs : MeasurableSet {o : FullData 𝒳 | fullS o = s} :=
    measurableSet_eq_fun measurable_fullS measurable_const
  rw [ProbabilityTheory.cond_apply hs]
  unfold witnessFullMeasureH
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [witnessPopulationMeasureH_population_mass h true s hh hpmeas hp,
    witnessPopulationMeasureH_population_mass h false s hh hpmeas hp,
    witnessPopulationMeasureH_inter_population h true s hh hpmeas hp A hA,
    witnessPopulationMeasureH_inter_population h false s hh hpmeas hp A hA]
  cases s <;> simp
  all_goals
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

private lemma witnessPotentialKernelH_complier
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    witnessPotentialKernelH h s p x
        {o | fullD1 o = true ∧ fullD0 o = false} =
      ENNReal.ofReal (p x) := by
  have hh' := abs_le.mp hh
  have hy0 : 0 ≤ 1 / 2 + h := by linarith
  have hy1 : 1 / 2 + h ≤ 1 := by linarith
  unfold witnessPotentialKernelH
  rw [witnessCoin_bind]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  have hset : MeasurableSet {o : FullData 𝒳 |
      fullD1 o = true ∧ fullD0 o = false} :=
    (measurableSet_eq_fun
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ hset]
  simp only [witnessFullPack, fullD0, fullD1, Set.indicator]
  have hcoin (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
      ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
    rw [← ENNReal.ofReal_add hq0 (sub_nonneg.mpr hq1)]
    convert ENNReal.ofReal_one using 1 <;> ring
  have hhalf := hcoin (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hshift := hcoin (1 / 2 + h) hy0 hy1
  simp only [Bool.true_eq, if_true, Bool.false_eq_true, if_false,
    Set.mem_setOf_eq, true_and, false_and, Bool.true_eq_false,
    Pi.one_apply, mul_one, mul_zero, add_zero]
  rw [hshift]
  simpa using congrArg (fun z : ENNReal => ENNReal.ofReal (p x) * z) hhalf

private lemma witnessPotentialKernelH_inter_fullX
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A)
    (C : Set (FullData 𝒳)) (hC : MeasurableSet C) :
    witnessPotentialKernelH h s p x
        {o | fullX o ∈ A ∧ o ∈ C} =
      A.indicator (fun y => witnessPotentialKernelH h s p y C) x := by
  let ν := witnessPotentialKernelH h s p x
  letI : IsProbabilityMeasure ν :=
    witnessPotentialKernelH_probability h s hh hp0 hp1
  have hXA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  by_cases hx : x ∈ A
  · have hfull : ν {o : FullData 𝒳 | fullX o ∈ A} = ν Set.univ := by
      rw [witnessPotentialKernelH_fullX h s hh hp0 hp1 A hA,
        Set.indicator_of_mem hx, measure_univ]
      simp
    have hae : ∀ᵐ o ∂ν, fullX o ∈ A := by
      show ∀ᵐ o ∂ν, o ∈ {o : FullData 𝒳 | fullX o ∈ A}
      rw [ae_mem_iff_measure_eq hXA.nullMeasurableSet]
      simpa using hfull
    have hinter :
        {o : FullData 𝒳 | fullX o ∈ A ∧ o ∈ C} =
          {o | fullX o ∈ A} ∩ C := rfl
    rw [hinter, Set.inter_comm, ← Measure.restrict_apply hC]
    have hr : ν.restrict {o : FullData 𝒳 | fullX o ∈ A} = ν :=
      Measure.restrict_eq_self_of_ae_mem hae
    rw [hr]
    simp [ν, hx]
  · have hzero : ν {o : FullData 𝒳 | fullX o ∈ A} = 0 := by
      rw [witnessPotentialKernelH_fullX h s hh hp0 hp1 A hA,
        Set.indicator_of_notMem hx]
    have hsub :
        {o : FullData 𝒳 | fullX o ∈ A ∧ o ∈ C} ⊆
          {o : FullData 𝒳 | fullX o ∈ A} := fun _ ho => ho.1
    rw [measure_mono_null hsub hzero]
    simp [hx]

private lemma witnessPotentialKernelH_always
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    witnessPotentialKernelH h s p x
        {o | fullD0 o = true ∧ fullD1 o = true} =
      ENNReal.ofReal ((1 - p x) / 2) := by
  have hh' := abs_le.mp hh
  have hy0 : 0 ≤ 1 / 2 + h := by linarith
  have hy1 : 1 / 2 + h ≤ 1 := by linarith
  unfold witnessPotentialKernelH
  rw [witnessCoin_bind]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  have hset : MeasurableSet {o : FullData 𝒳 |
      fullD0 o = true ∧ fullD1 o = true} :=
    (measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ hset]
  simp only [witnessFullPack, fullD0, fullD1, Set.indicator]
  have hcoin (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
      ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
    rw [← ENNReal.ofReal_add hq0 (sub_nonneg.mpr hq1)]
    convert ENNReal.ofReal_one using 1 <;> ring
  have hhalf := hcoin (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hshift := hcoin (1 / 2 + h) hy0 hy1
  have hsubp : 0 ≤ 1 - p x := sub_nonneg.mpr hp1
  simp only [Bool.true_eq, if_true, Bool.false_eq_true, if_false,
    Set.mem_setOf_eq, true_and, false_and,
    Pi.one_apply, mul_one, mul_zero, add_zero]
  rw [hhalf]
  simp only [zero_add, mul_one]
  rw [← ENNReal.ofReal_mul hsubp]
  congr 1
  ring

private lemma witnessPotentialKernelH_never
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    witnessPotentialKernelH h s p x
        {o | fullD0 o = false ∧ fullD1 o = false} =
      ENNReal.ofReal ((1 - p x) / 2) := by
  have hswap :
      {o : FullData 𝒳 | fullD0 o = false ∧ fullD1 o = false} =
        {o | fullD1 o = false ∧ fullD0 o = false} := by
    ext o
    simp [and_comm]
  rw [hswap]
  have hh' := abs_le.mp hh
  have hy0 : 0 ≤ 1 / 2 + h := by linarith
  have hy1 : 1 / 2 + h ≤ 1 := by linarith
  unfold witnessPotentialKernelH
  rw [witnessCoin_bind]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  have hset : MeasurableSet {o : FullData 𝒳 |
      fullD1 o = false ∧ fullD0 o = false} :=
    (measurableSet_eq_fun
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const)
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ hset]
  simp only [witnessFullPack, fullD0, fullD1, Set.indicator]
  have hcoin (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
      ENNReal.ofReal q + ENNReal.ofReal (1 - q) = 1 := by
    rw [← ENNReal.ofReal_add hq0 (sub_nonneg.mpr hq1)]
    convert ENNReal.ofReal_one using 1 <;> ring
  have hhalf := hcoin (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hshift := hcoin (1 / 2 + h) hy0 hy1
  have hsubp : 0 ≤ 1 - p x := sub_nonneg.mpr hp1
  simp only [Bool.true_eq, if_true, Bool.false_eq_true, if_false,
    Set.mem_setOf_eq, true_and, false_and,
    Pi.one_apply, mul_one, mul_zero, add_zero]
  rw [hhalf]
  simp only [zero_add, mul_one]
  rw [← ENNReal.ofReal_mul hsubp]
  congr 1
  ring

private lemma witnessPotentialKernelH_integral
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (f : FullData 𝒳 → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ o, ‖f o‖ ≤ C) :
    ∫ o, f o ∂witnessPotentialKernelH h s p x =
      ∫ complier, ∫ common, ∫ y,
        f (witnessFullPack s x complier common y)
          ∂witnessCoin (if complier then 1 / 2 + h else 1 / 2)
        ∂witnessCoin (1 / 2) ∂witnessCoin (p x) := by
  have hh' := abs_le.mp hh
  have hy0 : 0 ≤ 1 / 2 + h := by linarith
  have hy1 : 1 / 2 + h ≤ 1 := by linarith
  letI : IsProbabilityMeasure (witnessCoin (p x)) :=
    witnessCoin_probability hp0 hp1
  letI : IsProbabilityMeasure (witnessCoin (1 / 2)) :=
    witnessCoin_probability (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (witnessPotentialKernelH h s p x) :=
    witnessPotentialKernelH_probability h s hh hp0 hp1
  have hq (complier : Bool) :
      0 ≤ (if complier then 1 / 2 + h else 1 / 2) ∧
        (if complier then 1 / 2 + h else 1 / 2) ≤ 1 := by
    cases complier
    · norm_num
    · simpa using And.intro hy0 hy1
  have hfint : Integrable f (witnessPotentialKernelH h s p x) := by
    exact Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have hf₂ : ∀ᵐ complier ∂witnessCoin (p x),
      Integrable (fun common =>
        ∫ y, f (witnessFullPack s x complier common y)
          ∂witnessCoin (if complier then 1 / 2 + h else 1 / 2))
        (witnessCoin (1 / 2)) := by
    filter_upwards with complier
    exact Integrable.of_finite
  have hf' : Integrable (fun complier =>
      ∫ common, ∫ y, f (witnessFullPack s x complier common y)
        ∂witnessCoin (if complier then 1 / 2 + h else 1 / 2)
        ∂witnessCoin (1 / 2)) (witnessCoin (p x)) :=
    Integrable.of_finite
  exact Causalean.Mathlib.MeasureTheory.integral_bind_bind_map
    (m := witnessCoin (p x))
    (κ₁ := fun _ : Bool => witnessCoin (1 / 2))
    (κ₂ := fun complier _ : Bool =>
      witnessCoin (if complier then 1 / 2 + h else 1 / 2))
    (g := fun complier common y => witnessFullPack s x complier common y)
    (f := f) (fun _ _ => measurable_of_finite _)
    (fun _ => measurable_of_finite _) (measurable_of_finite _) hfint

private lemma witnessPotentialKernelH_ae_good
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∀ᵐ o ∂witnessPotentialKernelH h s p x, witnessGood o := by
  letI : IsProbabilityMeasure (witnessPotentialKernelH h s p x) :=
    witnessPotentialKernelH_probability h s hh hp0 hp1
  show ∀ᵐ o ∂witnessPotentialKernelH h s p x,
    o ∈ {o : FullData 𝒳 | witnessGood o}
  rw [ae_mem_iff_measure_eq measurableSet_witnessGood.nullMeasurableSet]
  rw [witnessPotentialKernelH_event h s hh hp0 hp1
    {o : FullData 𝒳 | witnessGood o} measurableSet_witnessGood True]
  · simp
  · intro complier common y
    cases complier <;> cases common <;> cases y <;>
      simp [witnessGood, witnessFullPack, fullY0, fullY1, fullD0, fullD1,
        boolReal, derivedAssignmentOutcome, potentialOutcome, potentialReceipt]

private lemma witnessPopulationMeasureH_ae_good
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ᵐ o ∂witnessPopulationMeasureH h s μ p, witnessGood o := by
  have hprob : IsProbabilityMeasure (witnessPopulationMeasureH h s μ p) :=
    witnessPopulationMeasureH_probability h s hh hpmeas hp
  show ∀ᵐ o ∂witnessPopulationMeasureH h s μ p,
    o ∈ {o : FullData 𝒳 | witnessGood o}
  rw [ae_mem_iff_measure_eq measurableSet_witnessGood.nullMeasurableSet]
  unfold witnessPopulationMeasureH
  letI : IsProbabilityMeasure
      (μ.bind (witnessPotentialKernelH h s p)) := by
    simpa only [witnessPopulationMeasureH] using hprob
  rw [Measure.bind_apply measurableSet_witnessGood
    (measurable_witnessPotentialKernelH h s hpmeas).aemeasurable]
  have hkernel (x : 𝒳) :
      witnessPotentialKernelH h s p x
          {o : FullData 𝒳 | witnessGood o} = 1 := by
    rw [witnessPotentialKernelH_event h s hh (hp x).1 (hp x).2
      {o : FullData 𝒳 | witnessGood o} measurableSet_witnessGood True]
    · simp
    · intro complier common y
      cases complier <;> cases common <;> cases y <;>
        simp [witnessGood, witnessFullPack, fullY0, fullY1, fullD0, fullD1,
          boolReal, derivedAssignmentOutcome, potentialOutcome,
          potentialReceipt]
  simp_rw [hkernel]
  rw [lintegral_const, measure_univ, measure_univ]
  simp

private lemma witnessPotentialKernelH_receipt_integral
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∫ o, (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂witnessPotentialKernelH h s p x = p x := by
  let f : FullData 𝒳 → ℝ :=
    fun o => boolReal (fullD1 o) - boolReal (fullD0 o)
  have hf : Measurable f := by
    unfold f
    have hd0 : Measurable (fun o : FullData 𝒳 => boolReal (fullD0 o)) := by
      unfold boolReal
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_fst.comp (measurable_snd.comp measurable_snd))
          measurable_const) measurable_const measurable_const
    have hd1 : Measurable (fun o : FullData 𝒳 => boolReal (fullD1 o)) := by
      unfold boolReal
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_fst.comp
            (measurable_snd.comp (measurable_snd.comp measurable_snd)))
          measurable_const) measurable_const measurable_const
    exact hd1.sub hd0
  rw [witnessPotentialKernelH_integral h s hh hp0 hp1 f hf 1]
  · have hh' := abs_le.mp hh
    have hq (complier : Bool) :
        0 ≤ (if complier then 1 / 2 + h else 1 / 2) ∧
          (if complier then 1 / 2 + h else 1 / 2) ≤ 1 := by
      cases complier
      · norm_num
      · simp only [if_true]
        constructor <;> linarith
    simp_rw [witnessCoin_integral (hq _).1 (hq _).2]
    simp_rw [witnessCoin_integral (p := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)]
    rw [witnessCoin_integral hp0 hp1]
    simp [f, witnessFullPack, fullD0, fullD1, boolReal]
  · intro o
    cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
      norm_num [f, boolReal, h0, h1]

private lemma witnessPotentialKernelH_outcome_integral
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∫ o, witnessOutcomeContrast o ∂witnessPotentialKernelH h s p x =
      p x * (1 / 2 + h) := by
  rw [witnessPotentialKernelH_integral h s hh hp0 hp1
    witnessOutcomeContrast measurable_witnessOutcomeContrast 1]
  · have hh' := abs_le.mp hh
    have hq (complier : Bool) :
        0 ≤ (if complier then 1 / 2 + h else 1 / 2) ∧
          (if complier then 1 / 2 + h else 1 / 2) ≤ 1 := by
      cases complier
      · norm_num
      · simp only [if_true]
        constructor <;> linarith
    simp_rw [witnessCoin_integral (hq _).1 (hq _).2]
    simp_rw [witnessCoin_integral (p := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)]
    rw [witnessCoin_integral hp0 hp1]
    simp [witnessOutcomeContrast, witnessFullPack, fullD0, fullD1,
      fullY1, boolReal]
    left
    ring
  · intro o
    unfold witnessOutcomeContrast
    by_cases hy : fullY1 o = 1
    · cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
        norm_num [boolReal, hy, h0, h1]
    · simp [hy]

private lemma witnessPotentialKernelH_indicator_integral
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1)
    (f : FullData 𝒳 → ℝ) (r : ℝ)
    (hvalue : ∫ o, f o ∂witnessPotentialKernelH h s p x = r)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A}, f o
        ∂witnessPotentialKernelH h s p x =
      A.indicator (fun _ => r) x := by
  letI : IsProbabilityMeasure (witnessPotentialKernelH h s p x) :=
    witnessPotentialKernelH_probability h s hh hp0 hp1
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  by_cases hx : x ∈ A
  · have hmem : ∀ᵐ o ∂witnessPotentialKernelH h s p x, fullX o ∈ A := by
      show ∀ᵐ o ∂witnessPotentialKernelH h s p x,
        o ∈ {o : FullData 𝒳 | fullX o ∈ A}
      rw [ae_mem_iff_measure_eq hset.nullMeasurableSet]
      rw [witnessPotentialKernelH_fullX h s hh hp0 hp1 A hA,
        Set.indicator_of_mem hx, measure_univ]
      simp
    rw [← integral_indicator hset]
    calc
      ∫ o, {o | fullX o ∈ A}.indicator f o
          ∂witnessPotentialKernelH h s p x =
          ∫ o, f o ∂witnessPotentialKernelH h s p x := by
            apply integral_congr_ae
            filter_upwards [hmem] with o ho
            simp [ho]
      _ = r := hvalue
      _ = A.indicator (fun _ => r) x := by simp [hx]
  · have hzero :
        witnessPotentialKernelH h s p x {o | fullX o ∈ A} = 0 := by
      rw [witnessPotentialKernelH_fullX h s hh hp0 hp1 A hA,
        Set.indicator_of_notMem hx]
    rw [Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]
    simp [hx]

private lemma witnessPopulationMeasureH_setIntegral
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (f : FullData 𝒳 → ℝ) (hf : Measurable f) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ o, ‖f o‖ ≤ C) (r : 𝒳 → ℝ)
    (hr : ∀ x, ∫ o, f o ∂witnessPotentialKernelH h s p x = r x)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A}, f o
        ∂witnessPopulationMeasureH h s μ p =
      ∫ x in A, r x ∂μ := by
  letI : IsProbabilityMeasure (witnessPopulationMeasureH h s μ p) :=
    witnessPopulationMeasureH_probability h s hh hpmeas hp
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  let F : FullData 𝒳 → ℝ := fun o => {o | fullX o ∈ A}.indicator f o
  have hFmeas : Measurable F := hf.indicator hset
  have hFint : Integrable F (witnessPopulationMeasureH h s μ p) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable C ?_
    filter_upwards with o
    by_cases ho : fullX o ∈ A
    · simpa [F, ho] using hC o
    · simpa [F, ho] using hC0
  rw [← integral_indicator hset]
  change ∫ o, F o ∂witnessPopulationMeasureH h s μ p =
    ∫ x in A, r x ∂μ
  unfold witnessPopulationMeasureH
  rw [Causalean.Mathlib.MeasureTheory.integral_bind
    (measurable_witnessPotentialKernelH h s hpmeas) hFint]
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with x
  rw [integral_indicator hset]
  exact witnessPotentialKernelH_indicator_integral h s hh
    (hp x).1 (hp x).2 f (r x) (hr x) A hA

private lemma witnessPopulationMeasureH_receipt_integral
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A},
        (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂witnessPopulationMeasureH h s μ p =
      ∫ x in A, p x ∂μ := by
  let f : FullData 𝒳 → ℝ :=
    fun o => boolReal (fullD1 o) - boolReal (fullD0 o)
  have hf : Measurable f := by
    unfold f
    have hd0 : Measurable (fun o : FullData 𝒳 => boolReal (fullD0 o)) := by
      unfold boolReal
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_fst.comp (measurable_snd.comp measurable_snd))
          measurable_const) measurable_const measurable_const
    have hd1 : Measurable (fun o : FullData 𝒳 => boolReal (fullD1 o)) := by
      unfold boolReal
      exact Measurable.ite
        (measurableSet_eq_fun
          (measurable_fst.comp
            (measurable_snd.comp (measurable_snd.comp measurable_snd)))
          measurable_const) measurable_const measurable_const
    exact hd1.sub hd0
  exact witnessPopulationMeasureH_setIntegral h s hh hpmeas hp
    f hf 1 (by norm_num)
    (fun o => by
      cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
        norm_num [f, boolReal, h0, h1])
    p (fun x => witnessPotentialKernelH_receipt_integral h s hh
      (hp x).1 (hp x).2) A hA

private lemma witnessPopulationMeasureH_outcome_integral
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A},
        (derivedAssignmentOutcome o true - derivedAssignmentOutcome o false)
        ∂witnessPopulationMeasureH h s μ p =
      ∫ x in A, p x * (1 / 2 + h) ∂μ := by
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  rw [← integral_indicator hset]
  calc
    ∫ o, {o | fullX o ∈ A}.indicator
        (fun o => derivedAssignmentOutcome o true -
          derivedAssignmentOutcome o false) o
        ∂witnessPopulationMeasureH h s μ p =
        ∫ o, {o | fullX o ∈ A}.indicator witnessOutcomeContrast o
          ∂witnessPopulationMeasureH h s μ p := by
            apply integral_congr_ae
            filter_upwards [witnessPopulationMeasureH_ae_good
              h s hh hpmeas hp] with o ho
            rcases ho.2.1 with hy | hy
            · by_cases hxo : fullX o ∈ A
              · simp [hxo, ho.2.2.2, witnessOutcomeContrast, hy]
              · simp [hxo]
            · by_cases hxo : fullX o ∈ A
              · simp [hxo, ho.2.2.2, witnessOutcomeContrast, hy]
              · simp [hxo]
    _ = ∫ o in {o | fullX o ∈ A}, witnessOutcomeContrast o
          ∂witnessPopulationMeasureH h s μ p := integral_indicator hset
    _ = ∫ x in A, p x * (1 / 2 + h) ∂μ := by
      exact witnessPopulationMeasureH_setIntegral h s hh hpmeas hp
        witnessOutcomeContrast measurable_witnessOutcomeContrast 1
        (by norm_num)
        (fun o => by
          unfold witnessOutcomeContrast
          by_cases hy : fullY1 o = 1
          · cases h0 : fullD0 o <;> cases h1 : fullD1 o <;>
              norm_num [boolReal, hy, h0, h1]
          · simp [hy])
        (fun x => p x * (1 / 2 + h))
        (fun x => witnessPotentialKernelH_outcome_integral h s hh
          (hp x).1 (hp x).2) A hA

private lemma witnessPopulationMeasureH_complier
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    (witnessPopulationMeasureH h s μ p
      {o | fullD1 o = true ∧ fullD0 o = false}).toReal =
      ∫ x, p x ∂μ := by
  have hset : MeasurableSet {o : FullData 𝒳 |
      fullD1 o = true ∧ fullD0 o = false} :=
    (measurableSet_eq_fun
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
        measurable_const)
  have hpint : Integrable p μ := by
    refine Integrable.of_bound hpmeas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hp x).1]
    exact (hp x).2
  have hp0 : 0 ≤ᵐ[μ] p := Filter.Eventually.of_forall fun x => (hp x).1
  have hmeasure :
      witnessPopulationMeasureH h s μ p
          {o | fullD1 o = true ∧ fullD0 o = false} =
        ENNReal.ofReal (∫ x, p x ∂μ) := by
    unfold witnessPopulationMeasureH
    rw [Measure.bind_apply hset
      (measurable_witnessPotentialKernelH h s hpmeas).aemeasurable]
    simp_rw [witnessPotentialKernelH_complier h s hh (hp _).1 (hp _).2]
    rw [← ofReal_integral_eq_lintegral_ofReal hpint hp0]
  rw [hmeasure, ENNReal.toReal_ofReal (integral_nonneg_of_ae hp0)]

private lemma witnessPopulationMeasureH_setIntegral_fullX
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (f : 𝒳 → ℝ) (hf : Measurable f)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A}, f (fullX o)
        ∂witnessPopulationMeasureH h s μ p =
      ∫ x in A, f x ∂μ := by
  have hset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  rw [← integral_indicator hset, ← integral_indicator hA]
  change ∫ o, (A.indicator f) (fullX o)
      ∂witnessPopulationMeasureH h s μ p =
    ∫ x, A.indicator f x ∂μ
  rw [← integral_map measurable_fullX.aemeasurable
    (hf.indicator hA).aestronglyMeasurable]
  rw [witnessPopulationMeasureH_map_fullX h s hh hpmeas hp]

private lemma witnessPopulationMeasureH_event_on
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (C : Set (FullData 𝒳)) (hC : MeasurableSet C)
    (r : 𝒳 → ℝ) (hrmeas : Measurable r)
    (hr0 : ∀ x, 0 ≤ r x) (hr1 : ∀ x, r x ≤ 1)
    (hkernel : ∀ x, witnessPotentialKernelH h s p x C =
      ENNReal.ofReal (r x))
    (A : Set 𝒳) (hA : MeasurableSet A) :
    (witnessPopulationMeasureH h s μ p
      {o | fullX o ∈ A ∧ o ∈ C}).toReal =
      ∫ x in A, r x ∂μ := by
  have hrint : Integrable r μ := by
    refine Integrable.of_bound hrmeas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hr0 x)]
    exact hr1 x
  have hr0ae : 0 ≤ᵐ[μ.restrict A] r :=
    (ae_restrict_iff' hA).2
      (Filter.Eventually.of_forall fun x _ => hr0 x)
  have hset : MeasurableSet {o : FullData 𝒳 |
      fullX o ∈ A ∧ o ∈ C} :=
    (hA.preimage measurable_fullX).inter hC
  have hmeasure :
      witnessPopulationMeasureH h s μ p
          {o | fullX o ∈ A ∧ o ∈ C} =
        ENNReal.ofReal (∫ x in A, r x ∂μ) := by
    unfold witnessPopulationMeasureH
    rw [Measure.bind_apply hset
      (measurable_witnessPotentialKernelH h s hpmeas).aemeasurable]
    simp_rw [witnessPotentialKernelH_inter_fullX h s hh
      (hp _).1 (hp _).2 A hA C hC, hkernel]
    rw [lintegral_indicator hA]
    rw [← ofReal_integral_eq_lintegral_ofReal hrint.integrableOn hr0ae]
  rw [hmeasure, ENNReal.toReal_ofReal
    (integral_nonneg_of_ae hr0ae)]

private lemma witnessPopulationMeasureH_complier_on
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    (witnessPopulationMeasureH h s μ p
      {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = true}).toReal =
      ∫ x in A, p x ∂μ := by
  let C : Set (FullData 𝒳) :=
    {o | fullD0 o = false ∧ fullD1 o = true}
  have hC : MeasurableSet C := by
    unfold C
    exact (measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const)
  have hevent :
      {o : FullData 𝒳 |
        fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = true} =
      {o | fullX o ∈ A ∧ o ∈ C} := by
    ext o
    simp [C, and_assoc]
  rw [hevent]
  apply witnessPopulationMeasureH_event_on h s hh hpmeas hp C hC
    p hpmeas (fun x => (hp x).1) (fun x => (hp x).2)
  · intro x
    have hswap :
        C = {o : FullData 𝒳 |
          fullD1 o = true ∧ fullD0 o = false} := by
      ext o
      simp [C, and_comm]
    rw [hswap]
    exact witnessPotentialKernelH_complier h s hh (hp x).1 (hp x).2
  · exact hA

private lemma witnessPopulationMeasureH_always_on
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    (witnessPopulationMeasureH h s μ p
      {o | fullX o ∈ A ∧ fullD0 o = true ∧ fullD1 o = true}).toReal =
      ∫ x in A, (1 - p x) / 2 ∂μ := by
  let C : Set (FullData 𝒳) :=
    {o | fullD0 o = true ∧ fullD1 o = true}
  have hC : MeasurableSet C := by
    unfold C
    exact (measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const)
  have hevent :
      {o : FullData 𝒳 |
        fullX o ∈ A ∧ fullD0 o = true ∧ fullD1 o = true} =
      {o | fullX o ∈ A ∧ o ∈ C} := by
    ext o
    simp [C, and_assoc]
  rw [hevent]
  apply witnessPopulationMeasureH_event_on h s hh hpmeas hp C hC
    (fun x => (1 - p x) / 2) ((measurable_const.sub hpmeas).div_const 2)
  · intro x
    exact div_nonneg (sub_nonneg.mpr (hp x).2) (by norm_num)
  · intro x
    nlinarith [(hp x).1]
  · intro x
    exact witnessPotentialKernelH_always h s hh (hp x).1 (hp x).2
  · exact hA

private lemma witnessPopulationMeasureH_never_on
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    (witnessPopulationMeasureH h s μ p
      {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = false}).toReal =
      ∫ x in A, (1 - p x) / 2 ∂μ := by
  let C : Set (FullData 𝒳) :=
    {o | fullD0 o = false ∧ fullD1 o = false}
  have hC : MeasurableSet C := by
    unfold C
    exact (measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const)
  have hevent :
      {o : FullData 𝒳 |
        fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = false} =
      {o | fullX o ∈ A ∧ o ∈ C} := by
    ext o
    simp [C, and_assoc]
  rw [hevent]
  apply witnessPopulationMeasureH_event_on h s hh hpmeas hp C hC
    (fun x => (1 - p x) / 2) ((measurable_const.sub hpmeas).div_const 2)
  · intro x
    exact div_nonneg (sub_nonneg.mpr (hp x).2) (by norm_num)
  · intro x
    nlinarith [(hp x).1]
  · intro x
    exact witnessPotentialKernelH_never h s hh (hp x).1 (hp x).2
  · exact hA

private lemma witnessPopulationMeasureH_complierY_on
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = true},
        fullY1 o ∂witnessPopulationMeasureH h s μ p =
      ∫ x in A, p x * (1 / 2 + h) ∂μ := by
  have hXA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  have hE : MeasurableSet {o : FullData 𝒳 |
      fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = true} :=
    hXA.inter <| (measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const)
  rw [← integral_indicator hE]
  calc
    ∫ o, {o : FullData 𝒳 |
        fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = true}.indicator
          fullY1 o ∂witnessPopulationMeasureH h s μ p =
      ∫ o, {o : FullData 𝒳 | fullX o ∈ A}.indicator
        (fun o => derivedAssignmentOutcome o true -
          derivedAssignmentOutcome o false) o
        ∂witnessPopulationMeasureH h s μ p := by
      apply integral_congr_ae
      filter_upwards [witnessPopulationMeasureH_ae_good
        h s hh hpmeas hp] with o ho
      simp only [Set.indicator, Set.mem_setOf_eq]
      rw [ho.2.2.2]
      by_cases hx : fullX o ∈ A
      · by_cases h0 : fullD0 o = false <;>
          by_cases h1 : fullD1 o = true
        · simp [hx, h0, h1, boolReal]
        · simp [hx, h0, h1, boolReal]
        · simp [hx, h0, h1, boolReal]
        · have hmono := ho.2.2.1
          simp [h0, h1, boolReal] at hmono
          norm_num at hmono
      · simp [hx]
    _ = ∫ o in {o | fullX o ∈ A},
        (derivedAssignmentOutcome o true - derivedAssignmentOutcome o false)
        ∂witnessPopulationMeasureH h s μ p := integral_indicator hXA
    _ = _ := witnessPopulationMeasureH_outcome_integral h s hh
      hpmeas hp A hA

private noncomputable def witnessAlwaysY (o : FullData 𝒳) : ℝ :=
  if fullD0 o = true ∧ fullD1 o = true ∧ fullY1 o = 1 then 1 else 0

private noncomputable def witnessNeverY (o : FullData 𝒳) : ℝ :=
  if fullD0 o = false ∧ fullD1 o = false ∧ fullY1 o = 1 then 1 else 0

private lemma measurable_witnessAlwaysY :
    Measurable (witnessAlwaysY : FullData 𝒳 → ℝ) := by
  unfold witnessAlwaysY
  have hd0 : MeasurableSet {o : FullData 𝒳 | fullD0 o = true} :=
    measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const
  have hd1 : MeasurableSet {o : FullData 𝒳 | fullD1 o = true} :=
    measurableSet_eq_fun
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_const
  have hy1 : MeasurableSet {o : FullData 𝒳 | fullY1 o = (1 : ℝ)} :=
    measurableSet_eq_fun
      (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
      measurable_const
  apply Measurable.ite
  · exact hd0.inter (hd1.inter hy1)
  · exact measurable_const
  · exact measurable_const

private lemma measurable_witnessNeverY :
    Measurable (witnessNeverY : FullData 𝒳 → ℝ) := by
  unfold witnessNeverY
  have hd0 : MeasurableSet {o : FullData 𝒳 | fullD0 o = false} :=
    measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const
  have hd1 : MeasurableSet {o : FullData 𝒳 | fullD1 o = false} :=
    measurableSet_eq_fun
      (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_const
  have hy1 : MeasurableSet {o : FullData 𝒳 | fullY1 o = (1 : ℝ)} :=
    measurableSet_eq_fun
      (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
      measurable_const
  apply Measurable.ite
  · exact hd0.inter (hd1.inter hy1)
  · exact measurable_const
  · exact measurable_const

private lemma witnessPotentialKernelH_alwaysY_integral
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∫ o, witnessAlwaysY o ∂witnessPotentialKernelH h s p x =
      (1 - p x) / 4 := by
  rw [witnessPotentialKernelH_integral h s hh hp0 hp1
    witnessAlwaysY measurable_witnessAlwaysY 1]
  · have hh' := abs_le.mp hh
    have hq (complier : Bool) :
        0 ≤ (if complier then 1 / 2 + h else 1 / 2) ∧
          (if complier then 1 / 2 + h else 1 / 2) ≤ 1 := by
      cases complier
      · norm_num
      · simp only [if_true]
        constructor <;> linarith
    simp_rw [witnessCoin_integral (hq _).1 (hq _).2]
    simp_rw [witnessCoin_integral (p := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)]
    rw [witnessCoin_integral hp0 hp1]
    simp [witnessAlwaysY, witnessFullPack, fullD0, fullD1, fullY1,
      boolReal]
    ring
  · intro o
    unfold witnessAlwaysY
    split_ifs <;> norm_num

private lemma witnessPotentialKernelH_neverY_integral
    (h : ℝ) (s : Bool) {p : 𝒳 → ℝ} {x : 𝒳}
    (hh : |h| ≤ 1 / 4) (hp0 : 0 ≤ p x) (hp1 : p x ≤ 1) :
    ∫ o, witnessNeverY o ∂witnessPotentialKernelH h s p x =
      (1 - p x) / 4 := by
  rw [witnessPotentialKernelH_integral h s hh hp0 hp1
    witnessNeverY measurable_witnessNeverY 1]
  · have hh' := abs_le.mp hh
    have hq (complier : Bool) :
        0 ≤ (if complier then 1 / 2 + h else 1 / 2) ∧
          (if complier then 1 / 2 + h else 1 / 2) ≤ 1 := by
      cases complier
      · norm_num
      · simp only [if_true]
        constructor <;> linarith
    simp_rw [witnessCoin_integral (hq _).1 (hq _).2]
    simp_rw [witnessCoin_integral (p := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)]
    rw [witnessCoin_integral hp0 hp1]
    simp [witnessNeverY, witnessFullPack, fullD0, fullD1, fullY1,
      boolReal]
    ring
  · intro o
    unfold witnessNeverY
    split_ifs <;> norm_num

private lemma witnessPopulationMeasureH_alwaysY_on
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A ∧ fullD0 o = true ∧ fullD1 o = true},
        fullY1 o ∂witnessPopulationMeasureH h s μ p =
      ∫ x in A, (1 - p x) / 4 ∂μ := by
  have hXA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  have hE : MeasurableSet {o : FullData 𝒳 |
      fullX o ∈ A ∧ fullD0 o = true ∧ fullD1 o = true} := by
    exact hXA.inter <| (measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const)
  rw [← integral_indicator hE]
  calc
    ∫ o, {o : FullData 𝒳 |
        fullX o ∈ A ∧ fullD0 o = true ∧ fullD1 o = true}.indicator
          fullY1 o ∂witnessPopulationMeasureH h s μ p =
      ∫ o in {o : FullData 𝒳 | fullX o ∈ A}, witnessAlwaysY o
        ∂witnessPopulationMeasureH h s μ p := by
      rw [← integral_indicator hXA]
      apply integral_congr_ae
      filter_upwards [witnessPopulationMeasureH_ae_good
        h s hh hpmeas hp] with o ho
      rcases ho.2.1 with hy | hy
      · simp only [Set.indicator, Set.mem_setOf_eq]
        by_cases hx : fullX o ∈ A <;>
          by_cases h0 : fullD0 o = true <;>
          by_cases h1 : fullD1 o = true <;>
          simp [witnessAlwaysY, hy, hx, h0, h1]
      · simp only [Set.indicator, Set.mem_setOf_eq]
        by_cases hx : fullX o ∈ A <;>
          by_cases h0 : fullD0 o = true <;>
          by_cases h1 : fullD1 o = true <;>
          simp [witnessAlwaysY, hy, hx, h0, h1]
    _ = _ := by
      exact witnessPopulationMeasureH_setIntegral h s hh hpmeas hp
        witnessAlwaysY measurable_witnessAlwaysY 1 (by norm_num)
        (fun o => by unfold witnessAlwaysY; split_ifs <;> norm_num)
        (fun x => (1 - p x) / 4)
        (fun x => witnessPotentialKernelH_alwaysY_integral h s hh
          (hp x).1 (hp x).2) A hA

private lemma witnessPopulationMeasureH_neverY_on
    {μ : Measure 𝒳} [IsProbabilityMeasure μ] (h : ℝ) (s : Bool)
    {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4) (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ o in {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = false},
        fullY1 o ∂witnessPopulationMeasureH h s μ p =
      ∫ x in A, (1 - p x) / 4 ∂μ := by
  have hXA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  have hE : MeasurableSet {o : FullData 𝒳 |
      fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = false} := by
    exact hXA.inter <| (measurableSet_eq_fun
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      measurable_const).inter
      (measurableSet_eq_fun
        (measurable_fst.comp
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))
        measurable_const)
  rw [← integral_indicator hE]
  calc
    ∫ o, {o : FullData 𝒳 |
        fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = false}.indicator
          fullY1 o ∂witnessPopulationMeasureH h s μ p =
      ∫ o in {o : FullData 𝒳 | fullX o ∈ A}, witnessNeverY o
        ∂witnessPopulationMeasureH h s μ p := by
      rw [← integral_indicator hXA]
      apply integral_congr_ae
      filter_upwards [witnessPopulationMeasureH_ae_good
        h s hh hpmeas hp] with o ho
      rcases ho.2.1 with hy | hy
      · simp only [Set.indicator, Set.mem_setOf_eq]
        by_cases hx : fullX o ∈ A <;>
          by_cases h0 : fullD0 o = false <;>
          by_cases h1 : fullD1 o = false <;>
          simp [witnessNeverY, hy, hx, h0, h1]
      · simp only [Set.indicator, Set.mem_setOf_eq]
        by_cases hx : fullX o ∈ A <;>
          by_cases h0 : fullD0 o = false <;>
          by_cases h1 : fullD1 o = false <;>
          simp [witnessNeverY, hy, hx, h0, h1]
    _ = _ := by
      exact witnessPopulationMeasureH_setIntegral h s hh hpmeas hp
        witnessNeverY measurable_witnessNeverY 1 (by norm_num)
        (fun o => by unfold witnessNeverY; split_ifs <;> norm_num)
        (fun x => (1 - p x) / 4)
        (fun x => witnessPotentialKernelH_neverY_integral h s hh
          (hp x).1 (hp x).2) A hA

private lemma witnessAssignmentKernel_fst
    {e : 𝒳 → ℝ} {o : FullData 𝒳}
    (he0 : 0 ≤ e (fullX o)) (he1 : e (fullX o) ≤ 1)
    (A : Set (FullData 𝒳)) (hA : MeasurableSet A) :
    ((witnessCoin (e (fullX o))).map (fun z => (o, z)))
        {q | q.1 ∈ A} =
      A.indicator 1 o := by
  have hpair : Measurable (fun z : Bool => (o, z)) := measurable_of_finite _
  have hset : MeasurableSet {q : AssignedFullData 𝒳 | q.1 ∈ A} :=
    hA.preimage measurable_fst
  rw [Measure.map_apply hpair hset]
  letI : IsProbabilityMeasure (witnessCoin (e (fullX o))) :=
    witnessCoin_probability he0 he1
  by_cases ho : o ∈ A
  · convert measure_univ (μ := witnessCoin (e (fullX o))) using 1 <;>
      simp [ho]
  · convert measure_empty (μ := witnessCoin (e (fullX o))) using 1 <;>
      simp [ho]

private lemma witnessAssignmentKernel_event
    {e : 𝒳 → ℝ} {o : FullData 𝒳}
    (he0 : 0 ≤ e (fullX o)) (he1 : e (fullX o) ≤ 1)
    (A : Set (FullData 𝒳)) (hA : MeasurableSet A) (z : Bool) :
    ((witnessCoin (e (fullX o))).map (fun z => (o, z)))
        {q | q.1 ∈ A ∧ q.2 = z} =
      ENNReal.ofReal (A.indicator
        (fun o => if z then e (fullX o) else 1 - e (fullX o)) o) := by
  have hpair : Measurable (fun z : Bool => (o, z)) := measurable_of_finite _
  have hset : MeasurableSet {q : AssignedFullData 𝒳 |
      q.1 ∈ A ∧ q.2 = z} :=
    (hA.preimage measurable_fst).inter
      (measurableSet_eq_fun measurable_snd measurable_const)
  rw [Measure.map_apply hpair hset]
  unfold witnessCoin Causalean.Mathlib.Probability.bernoulliBool
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, smul_eq_mul]
  by_cases ho : o ∈ A
  · cases z <;> simp [ho, he0, sub_nonneg.mpr he1]
  · simp [ho]

private lemma witnessAssignedMeasure_event
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1)
    (A : Set (FullData 𝒳)) (hA : MeasurableSet A) (z : Bool) :
    (witnessAssignedMeasure μS p e {q | q.1 ∈ A ∧ q.2 = z}).toReal =
      ∫ o in A, (if z then e (fullX o) else 1 - e (fullX o))
        ∂witnessPopulationMeasure true μS p := by
  let q : FullData 𝒳 → ℝ :=
    fun o => if z then e (fullX o) else 1 - e (fullX o)
  have hqmeas : Measurable q := by
    unfold q
    exact Measurable.ite
      (measurableSet_eq_fun measurable_const measurable_const)
      (hemeas.comp measurable_fullX)
      (measurable_const.sub (hemeas.comp measurable_fullX))
  let f : FullData 𝒳 → ℝ := A.indicator q
  have hfmeas : Measurable f := hqmeas.indicator hA
  have hf0 : 0 ≤ᵐ[witnessPopulationMeasure true μS p] f := by
    filter_upwards with o
    by_cases ho : o ∈ A
    · rw [show f o = q o by simp [f, ho]]
      cases z <;> simp [q, (he _).1, (he _).2]
    · simp [f, ho]
  letI : IsProbabilityMeasure (witnessPopulationMeasure true μS p) :=
    witnessPopulationMeasure_probability true hpmeas hp
  have hfint : Integrable f (witnessPopulationMeasure true μS p) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    by_cases ho : o ∈ A
    · rw [show f o = q o by simp [f, ho]]
      cases z <;> simp [q, Real.norm_eq_abs, abs_of_nonneg,
        (he _).1, (he _).2]
    · simp [f, ho]
  have hset : MeasurableSet {q : AssignedFullData 𝒳 |
      q.1 ∈ A ∧ q.2 = z} :=
    (hA.preimage measurable_fst).inter
      (measurableSet_eq_fun measurable_snd measurable_const)
  have hmeasure :
      witnessAssignedMeasure μS p e {q | q.1 ∈ A ∧ q.2 = z} =
        ENNReal.ofReal (∫ o, f o ∂witnessPopulationMeasure true μS p) := by
    unfold witnessAssignedMeasure
    rw [Measure.bind_apply hset
      (measurable_witnessAssignmentKernel hemeas).aemeasurable]
    simp_rw [witnessAssignmentKernel_event (he _).1 (he _).2 A hA z]
    rw [← ofReal_integral_eq_lintegral_ofReal hfint hf0]
  rw [hmeasure, ENNReal.toReal_ofReal (integral_nonneg_of_ae hf0)]
  rw [integral_indicator hA]

private lemma witnessAssignedMeasure_map_fst
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    (witnessAssignedMeasure μS p e).map Prod.fst =
      witnessPopulationMeasure true μS p := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  unfold witnessAssignedMeasure
  rw [Measure.bind_apply (hA.preimage measurable_fst)
    (measurable_witnessAssignmentKernel hemeas).aemeasurable]
  change (∫⁻ o, ((witnessCoin (e (fullX o))).map (fun z => (o, z)))
    {q | q.1 ∈ A} ∂witnessPopulationMeasure true μS p) =
      witnessPopulationMeasure true μS p A
  simp_rw [witnessAssignmentKernel_fst (he _).1 (he _).2 A hA]
  rw [lintegral_indicator hA]
  simp

private lemma witnessAssignedMeasureH_map_fst
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {h : ℝ} {p e : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    (witnessAssignedMeasureH h μS p e).map Prod.fst =
      witnessPopulationMeasureH h true μS p := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  unfold witnessAssignedMeasureH
  rw [Measure.bind_apply (hA.preimage measurable_fst)
    (measurable_witnessAssignmentKernel hemeas).aemeasurable]
  change (∫⁻ o, ((witnessCoin (e (fullX o))).map (fun z => (o, z)))
    {q | q.1 ∈ A} ∂witnessPopulationMeasureH h true μS p) =
      witnessPopulationMeasureH h true μS p A
  simp_rw [witnessAssignmentKernel_fst (he _).1 (he _).2 A hA]
  rw [lintegral_indicator hA]
  simp

private lemma witnessAssignedMeasureH_event
    (h : ℝ) (hh : |h| ≤ 1 / 4)
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1)
    (A : Set (FullData 𝒳)) (hA : MeasurableSet A) (z : Bool) :
    (witnessAssignedMeasureH h μS p e
      {q | q.1 ∈ A ∧ q.2 = z}).toReal =
      ∫ o in A, (if z then e (fullX o) else 1 - e (fullX o))
        ∂witnessPopulationMeasureH h true μS p := by
  let q : FullData 𝒳 → ℝ :=
    fun o => if z then e (fullX o) else 1 - e (fullX o)
  have hqmeas : Measurable q := by
    unfold q
    exact Measurable.ite
      (measurableSet_eq_fun measurable_const measurable_const)
      (hemeas.comp measurable_fullX)
      (measurable_const.sub (hemeas.comp measurable_fullX))
  let f : FullData 𝒳 → ℝ := A.indicator q
  have hfmeas : Measurable f := hqmeas.indicator hA
  have hf0 : 0 ≤ᵐ[witnessPopulationMeasureH h true μS p] f := by
    filter_upwards with o
    by_cases ho : o ∈ A
    · rw [show f o = q o by simp [f, ho]]
      cases z <;> simp [q, (he _).1, (he _).2]
    · simp [f, ho]
  letI : IsProbabilityMeasure (witnessPopulationMeasureH h true μS p) :=
    witnessPopulationMeasureH_probability h true hh hpmeas hp
  have hfint : Integrable f (witnessPopulationMeasureH h true μS p) := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    by_cases ho : o ∈ A
    · rw [show f o = q o by simp [f, ho]]
      cases z <;> simp [q, Real.norm_eq_abs, abs_of_nonneg,
        (he _).1, (he _).2]
    · simp [f, ho]
  have hset : MeasurableSet {q : AssignedFullData 𝒳 |
      q.1 ∈ A ∧ q.2 = z} :=
    (hA.preimage measurable_fst).inter
      (measurableSet_eq_fun measurable_snd measurable_const)
  have hmeasure :
      witnessAssignedMeasureH h μS p e {q | q.1 ∈ A ∧ q.2 = z} =
        ENNReal.ofReal
          (∫ o, f o ∂witnessPopulationMeasureH h true μS p) := by
    unfold witnessAssignedMeasureH
    rw [Measure.bind_apply hset
      (measurable_witnessAssignmentKernel hemeas).aemeasurable]
    simp_rw [witnessAssignmentKernel_event (he _).1 (he _).2 A hA z]
    rw [← ofReal_integral_eq_lintegral_ofReal hfint hf0]
  rw [hmeasure, ENNReal.toReal_ofReal (integral_nonneg_of_ae hf0)]
  rw [integral_indicator hA]

private lemma witnessAssignedMeasureH_ae_good
    (h : ℝ) {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    ∀ᵐ q ∂witnessAssignedMeasureH h μS p e, witnessGood q.1 := by
  have hgood := witnessPopulationMeasureH_ae_good
    (μ := μS) h true hh hpmeas hp
  rw [← witnessAssignedMeasureH_map_fst (μS := μS) (h := h)
    (p := p) (e := e) hh hpmeas hemeas hp he] at hgood
  exact (ae_map_iff measurable_fst.aemeasurable
    measurableSet_witnessGood).1 hgood

private lemma witnessAssignedMeasure_ae_good
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) :
    ∀ᵐ q ∂witnessAssignedMeasure μS p e, witnessGood q.1 := by
  have hgood := witnessPopulationMeasure_ae_good
    (μ := μS) (p := p) true hpmeas hp
  rw [← witnessAssignedMeasure_map_fst (μS := μS) (p := p) (e := e)
    hpmeas hemeas hp he] at hgood
  exact (ae_map_iff measurable_fst.aemeasurable measurableSet_witnessGood).1 hgood

private lemma measurable_observeSource :
    Measurable (observeSource : AssignedFullData 𝒳 → SourceObs 𝒳) := by
  unfold observeSource potentialReceipt potentialOutcome
  have hfull : Measurable (fun q : AssignedFullData 𝒳 => q.1) := measurable_fst
  have hz : Measurable (fun q : AssignedFullData 𝒳 => q.2) := measurable_snd
  have hd0 : Measurable (fun q : AssignedFullData 𝒳 => fullD0 q.1) := by
    exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp hfull
  have hd1 : Measurable (fun q : AssignedFullData 𝒳 => fullD1 q.1) := by
    exact (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd))).comp hfull
  have hd : Measurable (fun q : AssignedFullData 𝒳 =>
      if q.2 then fullD1 q.1 else fullD0 q.1) :=
    Measurable.ite (measurableSet_eq_fun hz measurable_const) hd1 hd0
  have hy0 : Measurable (fun q : AssignedFullData 𝒳 => fullY0 q.1) := by
    exact (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))).comp hfull
  have hy1 : Measurable (fun q : AssignedFullData 𝒳 => fullY1 q.1) := by
    exact (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd)))).comp hfull
  have hy : Measurable (fun q : AssignedFullData 𝒳 =>
      if (if q.2 then fullD1 q.1 else fullD0 q.1)
        then fullY1 q.1 else fullY0 q.1) :=
    Measurable.ite (measurableSet_eq_fun hd measurable_const) hy1 hy0
  exact (measurable_fullX.comp hfull).prodMk <| hz.prodMk <| hd.prodMk hy

private noncomputable def witnessSourceObsKernelH (h : ℝ)
    (p e : 𝒳 → ℝ) (x : 𝒳) : Measure (SourceObs 𝒳) :=
  (witnessPotentialKernelH h true p x).bind fun o =>
    (witnessCoin (e (fullX o))).map fun z => observeSource (o, z)

private def witnessObservedPack (x : 𝒳) (complier common y z : Bool) :
    SourceObs 𝒳 :=
  let d := if complier then z else common
  (x, z, d, if d then boolReal y else 0)

private noncomputable def witnessObservedCoinKernelH (h : ℝ)
    (p e : 𝒳 → ℝ) (x : 𝒳) : Measure (SourceObs 𝒳) :=
  (witnessCoin (p x)).bind fun complier =>
    (witnessCoin (1 / 2)).bind fun common =>
      (witnessCoin (if complier then 1 / 2 + h else 1 / 2)).bind fun y =>
        (witnessCoin (e x)).map fun z =>
          witnessObservedPack x complier common y z

private noncomputable def witnessSourceLikelihoodRatio (h : ℝ)
    (p : 𝒳 → ℝ) (o : SourceObs 𝒳) : ℝ :=
  if o.2.1 = true ∧ o.2.2.1 = true then
    if o.2.2.2 = 1 then
      1 + 4 * p o.1 * h / (1 + p o.1)
    else if o.2.2.2 = 0 then
      1 - 4 * p o.1 * h / (1 + p o.1)
    else 1
  else 1

private lemma measurable_witnessSourceLikelihoodRatio (h : ℝ)
    {p : 𝒳 → ℝ} (hp : Measurable p) :
    Measurable (witnessSourceLikelihoodRatio h p) := by
  unfold witnessSourceLikelihoodRatio
  have hz : Measurable (fun o : SourceObs 𝒳 => o.2.1) :=
    measurable_fst.comp measurable_snd
  have hd : Measurable (fun o : SourceObs 𝒳 => o.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hy : Measurable (fun o : SourceObs 𝒳 => o.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hp' : Measurable (fun o : SourceObs 𝒳 => p o.1) :=
    hp.comp measurable_fst
  have hzd : MeasurableSet {o : SourceObs 𝒳 |
      o.2.1 = true ∧ o.2.2.1 = true} :=
    (measurableSet_eq_fun hz measurable_const).inter
      (measurableSet_eq_fun hd measurable_const)
  have hy1 : MeasurableSet {o : SourceObs 𝒳 | o.2.2.2 = 1} :=
    measurableSet_eq_fun hy measurable_const
  have hy0 : MeasurableSet {o : SourceObs 𝒳 | o.2.2.2 = 0} :=
    measurableSet_eq_fun hy measurable_const
  exact Measurable.ite hzd
    (Measurable.ite hy1
      (by fun_prop)
      (Measurable.ite hy0 (by fun_prop) measurable_const))
    measurable_const

private lemma witnessSourceLikelihoodRatio_nonneg
    (h : ℝ) {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ o, 0 ≤ witnessSourceLikelihoodRatio h p o := by
  intro o
  unfold witnessSourceLikelihoodRatio
  split_ifs with hzd hy1 hy0
  · have hden : 0 < 1 + p o.1 := by linarith [(hp o.1).1]
    have hh' := abs_le.mp hh
    have hmul := mul_le_mul_of_nonneg_left hh'.1 (hp o.1).1
    have hlower : -(1 + p o.1) ≤ 4 * p o.1 * h := by
      nlinarith
    have hdiv : -1 ≤ 4 * p o.1 * h / (1 + p o.1) :=
      (le_div_iff₀ hden).2 (by nlinarith)
    linarith
  · have hden : 0 < 1 + p o.1 := by linarith [(hp o.1).1]
    have hh' := abs_le.mp hh
    have hmul := mul_le_mul_of_nonneg_left hh'.2 (hp o.1).1
    have hupper : 4 * p o.1 * h ≤ 1 + p o.1 := by
      nlinarith
    have hdiv : 4 * p o.1 * h / (1 + p o.1) ≤ 1 :=
      (div_le_one hden).2 hupper
    linarith
  all_goals norm_num

private lemma witnessSourceLikelihoodRatio_sq_dev_le_one
    (h : ℝ) {p : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    ∀ o, ‖(witnessSourceLikelihoodRatio h p o - 1) ^ 2‖ ≤ 1 := by
  intro o
  have hden : 0 < 1 + p o.1 := by linarith [(hp o.1).1]
  have hratio :
      |4 * p o.1 * h / (1 + p o.1)| ≤ 1 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (hp o.1).1, abs_of_pos hden]
    apply (div_le_one hden).2
    have hm := mul_le_mul_of_nonneg_left hh (hp o.1).1
    nlinarith
  unfold witnessSourceLikelihoodRatio
  split_ifs <;>
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  all_goals try norm_num
  all_goals exact hratio

private lemma measurable_witnessSourceObsKernelH (h : ℝ)
    {p e : 𝒳 → ℝ} (hp : Measurable p) (he : Measurable e) :
    Measurable (witnessSourceObsKernelH h p e) := by
  unfold witnessSourceObsKernelH
  have hinner : Measurable (fun o : FullData 𝒳 =>
      (witnessCoin (e (fullX o))).map fun z => observeSource (o, z)) := by
    simp_rw [witnessCoin_map]
    have hpack (z : Bool) :
        Measurable (fun o : FullData 𝒳 => observeSource (o, z)) :=
      measurable_observeSource.comp (measurable_id.prodMk measurable_const)
    have hefull : Measurable (fun o : FullData 𝒳 => e (fullX o)) :=
      he.comp measurable_fullX
    exact (measurable_variable_smul_measure
      (ENNReal.measurable_ofReal.comp hefull)
      (Measure.measurable_dirac.comp (hpack true))).add
        (measurable_variable_smul_measure
          (ENNReal.measurable_ofReal.comp (measurable_const.sub hefull))
          (Measure.measurable_dirac.comp (hpack false)))
  exact (Measure.measurable_bind' hinner).comp
    (measurable_witnessPotentialKernelH h true hp)

private lemma witnessSourceObsKernelH_eq_coinKernel
    (h : ℝ) {p e : 𝒳 → ℝ} (he : Measurable e) (x : 𝒳) :
    witnessSourceObsKernelH h p e x =
      witnessObservedCoinKernelH h p e x := by
  have hinner : Measurable (fun o : FullData 𝒳 =>
      (witnessCoin (e (fullX o))).map fun z => observeSource (o, z)) := by
    simp_rw [witnessCoin_map]
    have hpack (z : Bool) :
        Measurable (fun o : FullData 𝒳 => observeSource (o, z)) :=
      measurable_observeSource.comp (measurable_id.prodMk measurable_const)
    have hefull : Measurable (fun o : FullData 𝒳 => e (fullX o)) := by
      exact he.comp measurable_fullX
    exact (measurable_variable_smul_measure
      (ENNReal.measurable_ofReal.comp hefull)
      (Measure.measurable_dirac.comp (hpack true))).add
        (measurable_variable_smul_measure
          (ENNReal.measurable_ofReal.comp (measurable_const.sub hefull))
          (Measure.measurable_dirac.comp (hpack false)))
  ext A hA
  have hfiber : Measurable (fun o : FullData 𝒳 =>
      ENNReal.ofReal (e (fullX o)) *
          Measure.dirac (observeSource (o, true)) A +
        ENNReal.ofReal (1 - e (fullX o)) *
          Measure.dirac (observeSource (o, false)) A) := by
    simpa [witnessCoin_map, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul] using (Measure.measurable_coe hA).comp hinner
  unfold witnessSourceObsKernelH witnessPotentialKernelH
    witnessObservedCoinKernelH
  rw [Measure.bind_apply hA hinner.aemeasurable]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    lintegral_add_measure, lintegral_smul_measure]
  simp_rw [lintegral_dirac' _ hfiber]
  simp [Measure.dirac_apply' _ hA, witnessObservedPack, witnessFullPack,
    observeSource, potentialReceipt, potentialOutcome, fullX, fullD0, fullD1,
    fullY0, fullY1]

set_option maxHeartbeats 800000 in
private lemma witnessObservedCoinKernelH_eq_withDensity
    (h : ℝ) {p e : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hh : |h| ≤ 1 / 4) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (x : 𝒳) :
    witnessObservedCoinKernelH h p e x =
      (witnessObservedCoinKernelH 0 p e x).withDensity
        (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h p) := by
  classical
  ext A hA
  rw [withDensity_apply _ hA]
  have hratio : Measurable
      (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h p) :=
    ENNReal.measurable_ofReal.comp
      (measurable_witnessSourceLikelihoodRatio h hpmeas)
  have hind : Measurable (A.indicator
      (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h p)) :=
    hratio.indicator hA
  have hind_mul (o : SourceObs 𝒳) :
      A.indicator (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h p) o =
        (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h p) o *
          A.indicator (1 : SourceObs 𝒳 → ENNReal) o := by
    by_cases ho : o ∈ A <;> simp [ho]
  let ind : SourceObs 𝒳 → NNReal := fun o => if o ∈ A then 1 else 0
  have hind_coe (o : SourceObs 𝒳) :
      A.indicator (1 : SourceObs 𝒳 → ENNReal) o =
        (ind o : ENNReal) := by
    by_cases ho : o ∈ A <;> simp [ind, ho]
  have hh' := abs_le.mp hh
  have hyplus : 0 ≤ 1 / 2 + h := by linarith
  have hyminus : 0 ≤ 1 - (1 / 2 + h) := by linarith
  have hden : 0 < 1 + p x := by linarith [(hp x).1]
  have hrplus :
      0 ≤ 1 + 4 * p x * h / (1 + p x) := by
    simpa [witnessSourceLikelihoodRatio] using
      witnessSourceLikelihoodRatio_nonneg h hh hp (x, true, true, 1)
  have hrminus :
      0 ≤ 1 - 4 * p x * h / (1 + p x) := by
    simpa [witnessSourceLikelihoodRatio] using
      witnessSourceLikelihoodRatio_nonneg h hh hp (x, true, true, 0)
  unfold witnessObservedCoinKernelH
  rw [← lintegral_indicator hA]
  simp_rw [witnessCoin_bind, witnessCoin_map]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    lintegral_add_measure, lintegral_smul_measure]
  simp_rw [lintegral_dirac' _ hind]
  simp [Measure.dirac_apply' _ hA, witnessObservedPack,
    witnessSourceLikelihoodRatio, Function.comp_apply, boolReal]
  simp_rw [hind_mul]
  simp [witnessSourceLikelihoodRatio, Function.comp_apply]
  simp_rw [hind_coe]
  simp only [ENNReal.ofReal, ← ENNReal.coe_inv_two]
  norm_cast
  apply NNReal.eq
  norm_num [Real.coe_toNNReal, (hp x).1, (hp x).2, (he x).1, (he x).2,
    hyplus, hyminus, hrplus, hrminus]
  field_simp [hden.ne']
  ring

private lemma witnessObservedCoinKernelH_probability
    (h : ℝ) {p e : 𝒳 → ℝ} (hh : |h| ≤ 1 / 4)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (x : 𝒳) :
    IsProbabilityMeasure (witnessObservedCoinKernelH h p e x) := by
  have hh' := abs_le.mp hh
  letI : IsProbabilityMeasure (witnessCoin (p x)) :=
    witnessCoin_probability (hp x).1 (hp x).2
  letI : IsProbabilityMeasure (witnessCoin (1 / 2)) :=
    witnessCoin_probability (by norm_num) (by norm_num)
  have hout (c : Bool) :
      IsProbabilityMeasure
        (witnessCoin (if c then 1 / 2 + h else 1 / 2)) := by
    cases c
    · simpa using
        (witnessCoin_probability (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    · simpa using
        (witnessCoin_probability (p := 1 / 2 + h) (by linarith) (by linarith))
  have hassign :
      ∀ c common y, IsProbabilityMeasure
        ((witnessCoin (e x)).map fun z =>
          witnessObservedPack x c common y z) := by
    intro c common y
    letI : IsProbabilityMeasure (witnessCoin (e x)) :=
      witnessCoin_probability (he x).1 (he x).2
    exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  have hy (c common : Bool) :
      IsProbabilityMeasure
        ((witnessCoin (if c then 1 / 2 + h else 1 / 2)).bind fun y =>
          (witnessCoin (e x)).map fun z =>
            witnessObservedPack x c common y z) := by
    letI := hout c
    exact isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
      (Filter.Eventually.of_forall fun y => hassign c common y)
  have hcommon (c : Bool) :
      IsProbabilityMeasure
        ((witnessCoin (1 / 2)).bind fun common =>
          (witnessCoin (if c then 1 / 2 + h else 1 / 2)).bind fun y =>
            (witnessCoin (e x)).map fun z =>
              witnessObservedPack x c common y z) := by
    exact isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
      (Filter.Eventually.of_forall fun common => hy c common)
  unfold witnessObservedCoinKernelH
  exact isProbabilityMeasure_bind (measurable_of_finite _).aemeasurable
    (Filter.Eventually.of_forall hcommon)

private lemma witnessObservedCoinKernelH_chiIntegral
    (h : ℝ) {p e : 𝒳 → ℝ} (hpmeas : Measurable p)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (he : ∀ x, 0 ≤ e x ∧ e x ≤ 1) (x : 𝒳) :
    ∫ o, (witnessSourceLikelihoodRatio h p o - 1) ^ 2
        ∂witnessObservedCoinKernelH 0 p e x =
      8 * e x * p x ^ 2 * h ^ 2 / (1 + p x) := by
  have hden : 1 + p x ≠ 0 := by linarith [(hp x).1]
  let f : SourceObs 𝒳 → ℝ :=
    fun o => (witnessSourceLikelihoodRatio h p o - 1) ^ 2
  have hfmeas : Measurable f :=
    ((measurable_witnessSourceLikelihoodRatio h hpmeas).sub_const 1).pow_const 2
  have hdir (o : SourceObs 𝒳) : Integrable f (Measure.dirac o) :=
    integrable_dirac' hfmeas.stronglyMeasurable (by simp [enorm])
  have hmap (c common y : Bool) :
      Integrable f ((witnessCoin (e x)).map fun z =>
        witnessObservedPack x c common y z) := by
    rw [witnessCoin_map]
    apply Integrable.add_measure
    · exact Integrable.smul_measure (hdir _) (by finiteness)
    · exact Integrable.smul_measure (hdir _) (by finiteness)
  have hy (c common : Bool) :
      Integrable f
        ((witnessCoin (if c then 1 / 2 + 0 else 1 / 2)).bind fun y =>
          (witnessCoin (e x)).map fun z =>
            witnessObservedPack x c common y z) := by
    rw [witnessCoin_bind]
    apply Integrable.add_measure
    · exact Integrable.smul_measure (hmap c common true) (by finiteness)
    · exact Integrable.smul_measure (hmap c common false) (by finiteness)
  have hcommon (c : Bool) :
      Integrable f
        ((witnessCoin (1 / 2)).bind fun common =>
          (witnessCoin (if c then 1 / 2 + 0 else 1 / 2)).bind fun y =>
            (witnessCoin (e x)).map fun z =>
              witnessObservedPack x c common y z) := by
    rw [witnessCoin_bind]
    apply Integrable.add_measure
    · exact Integrable.smul_measure (hy c true) (by finiteness)
    · exact Integrable.smul_measure (hy c false) (by finiteness)
  have houter :
      Integrable f (witnessObservedCoinKernelH 0 p e x) := by
    unfold witnessObservedCoinKernelH
    rw [witnessCoin_bind]
    apply Integrable.add_measure
    · exact Integrable.smul_measure (hcommon true) (by finiteness)
    · exact Integrable.smul_measure (hcommon false) (by finiteness)
  change ∫ o, f o ∂witnessObservedCoinKernelH 0 p e x = _
  unfold witnessObservedCoinKernelH
  rw [Causalean.Mathlib.MeasureTheory.integral_bind
    (measurable_of_finite _) houter]
  rw [witnessCoin_integral (hp x).1 (hp x).2]
  have hmapIntegral (c common y : Bool) :
      (∫ o, f o ∂(witnessCoin (e x)).map fun z =>
          witnessObservedPack x c common y z) =
        e x * f (witnessObservedPack x c common y true) +
          (1 - e x) * f (witnessObservedPack x c common y false) := by
    rw [integral_map (measurable_of_finite _).aemeasurable
      hfmeas.aestronglyMeasurable]
    exact witnessCoin_integral (he x).1 (he x).2 _
  have hyIntegral (c common : Bool) :
      (∫ o, f o
          ∂(witnessCoin (if c then 1 / 2 + 0 else 1 / 2)).bind fun y =>
            (witnessCoin (e x)).map fun z =>
              witnessObservedPack x c common y z) =
        (if c then 1 / 2 + 0 else 1 / 2) *
            (e x * f (witnessObservedPack x c common true true) +
              (1 - e x) * f (witnessObservedPack x c common true false)) +
          (1 - (if c then 1 / 2 + 0 else 1 / 2)) *
            (e x * f (witnessObservedPack x c common false true) +
              (1 - e x) * f (witnessObservedPack x c common false false)) := by
    rw [Causalean.Mathlib.MeasureTheory.integral_bind
      (measurable_of_finite _) (hy c common)]
    rw [witnessCoin_integral]
    · rw [hmapIntegral, hmapIntegral]
    · cases c <;> norm_num
    · cases c <;> norm_num
  have hcommonIntegral (c : Bool) :
      (∫ o, f o ∂(witnessCoin (1 / 2)).bind fun common =>
          (witnessCoin (if c then 1 / 2 + 0 else 1 / 2)).bind fun y =>
            (witnessCoin (e x)).map fun z =>
              witnessObservedPack x c common y z) =
        (1 / 2 : ℝ) *
            ((if c then 1 / 2 + 0 else 1 / 2) *
                (e x * f (witnessObservedPack x c true true true) +
                  (1 - e x) * f (witnessObservedPack x c true true false)) +
              (1 - (if c then 1 / 2 + 0 else 1 / 2)) *
                (e x * f (witnessObservedPack x c true false true) +
                  (1 - e x) * f (witnessObservedPack x c true false false))) +
          (1 - 1 / 2) *
            ((if c then 1 / 2 + 0 else 1 / 2) *
                (e x * f (witnessObservedPack x c false true true) +
                  (1 - e x) * f (witnessObservedPack x c false true false)) +
              (1 - (if c then 1 / 2 + 0 else 1 / 2)) *
                (e x * f (witnessObservedPack x c false false true) +
                  (1 - e x) * f (witnessObservedPack x c false false false))) := by
    rw [Causalean.Mathlib.MeasureTheory.integral_bind
      (measurable_of_finite _) (hcommon c)]
    rw [witnessCoin_integral (by norm_num) (by norm_num)]
    rw [hyIntegral, hyIntegral]
  rw [hcommonIntegral, hcommonIntegral]
  simp [f, witnessObservedPack, witnessSourceLikelihoodRatio, boolReal]
  field_simp [hden]
  ring

private noncomputable def witnessInstrumentScore (e : 𝒳 → ℝ)
    (q : AssignedFullData 𝒳) : ℝ :=
  if q.2 then 1 / e (fullX q.1) else -1 / (1 - e (fullX q.1))

private lemma measurable_witnessInstrumentScore {e : 𝒳 → ℝ}
    (he : Measurable e) :
    Measurable (witnessInstrumentScore e : AssignedFullData 𝒳 → ℝ) := by
  unfold witnessInstrumentScore
  have hz : Measurable (fun q : AssignedFullData 𝒳 => q.2) := measurable_snd
  have hex : Measurable (fun q : AssignedFullData 𝒳 => e (fullX q.1)) :=
    he.comp (measurable_fullX.comp measurable_fst)
  exact Measurable.ite (measurableSet_eq_fun hz measurable_const)
    (measurable_const.div hex)
    (measurable_const.div (measurable_const.sub hex))

private lemma measurable_assignedOutcome :
    Measurable (fun q : AssignedFullData 𝒳 =>
      derivedAssignmentOutcome q.1 q.2) := by
  unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
  have hz : Measurable (fun q : AssignedFullData 𝒳 => q.2) := measurable_snd
  have hd0 : Measurable (fun q : AssignedFullData 𝒳 => fullD0 q.1) :=
    (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp measurable_fst
  have hd1 : Measurable (fun q : AssignedFullData 𝒳 => fullD1 q.1) :=
    (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))).comp
        measurable_fst
  have hd : Measurable (fun q : AssignedFullData 𝒳 =>
      if q.2 then fullD1 q.1 else fullD0 q.1) :=
    Measurable.ite (measurableSet_eq_fun hz measurable_const) hd1 hd0
  have hy0 : Measurable (fun q : AssignedFullData 𝒳 => fullY0 q.1) :=
    (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))).comp
        measurable_fst
  have hy1 : Measurable (fun q : AssignedFullData 𝒳 => fullY1 q.1) :=
    (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))).comp
        measurable_fst
  exact Measurable.ite (measurableSet_eq_fun hd measurable_const) hy1 hy0

private lemma measurable_assignedReceipt :
    Measurable (fun q : AssignedFullData 𝒳 =>
      boolReal (potentialReceipt q.1 q.2)) := by
  unfold potentialReceipt boolReal
  have hz : Measurable (fun q : AssignedFullData 𝒳 => q.2) := measurable_snd
  have hd0 : Measurable (fun q : AssignedFullData 𝒳 => fullD0 q.1) :=
    (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp measurable_fst
  have hd1 : Measurable (fun q : AssignedFullData 𝒳 => fullD1 q.1) :=
    (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))).comp
        measurable_fst
  have hd : Measurable (fun q : AssignedFullData 𝒳 =>
      if q.2 then fullD1 q.1 else fullD0 q.1) :=
    Measurable.ite (measurableSet_eq_fun hz measurable_const) hd1 hd0
  exact Measurable.ite (measurableSet_eq_fun hd measurable_const)
    measurable_const measurable_const

private lemma witnessAssignmentKernel_score_outcome_integral
    {e : 𝒳 → ℝ} (heMeas : Measurable e) (o : FullData 𝒳)
    (he0 : 0 < e (fullX o)) (he1 : e (fullX o) < 1) :
    ∫ q, witnessInstrumentScore e q * derivedAssignmentOutcome q.1 q.2
        ∂(witnessCoin (e (fullX o))).map (fun z => (o, z)) =
      derivedAssignmentOutcome o true - derivedAssignmentOutcome o false := by
  have hf : Measurable (fun q : AssignedFullData 𝒳 =>
      witnessInstrumentScore e q * derivedAssignmentOutcome q.1 q.2) :=
    (measurable_witnessInstrumentScore heMeas).mul measurable_assignedOutcome
  rw [integral_map (measurable_of_finite _).aemeasurable
    hf.aestronglyMeasurable]
  rw [witnessCoin_integral he0.le he1.le]
  simp [witnessInstrumentScore, he0.ne', (sub_pos.mpr he1).ne']
  field_simp [(sub_pos.mpr he1).ne']
  <;> ring

private lemma witnessAssignmentKernel_score_receipt_integral
    {e : 𝒳 → ℝ} (heMeas : Measurable e) (o : FullData 𝒳)
    (he0 : 0 < e (fullX o)) (he1 : e (fullX o) < 1) :
    ∫ q, witnessInstrumentScore e q * boolReal (potentialReceipt q.1 q.2)
        ∂(witnessCoin (e (fullX o))).map (fun z => (o, z)) =
      boolReal (fullD1 o) - boolReal (fullD0 o) := by
  have hf : Measurable (fun q : AssignedFullData 𝒳 =>
      witnessInstrumentScore e q * boolReal (potentialReceipt q.1 q.2)) :=
    (measurable_witnessInstrumentScore heMeas).mul measurable_assignedReceipt
  rw [integral_map (measurable_of_finite _).aemeasurable
    hf.aestronglyMeasurable]
  rw [witnessCoin_integral he0.le he1.le]
  simp [witnessInstrumentScore, potentialReceipt, he0.ne',
    (sub_pos.mpr he1).ne']
  field_simp [(sub_pos.mpr he1).ne']
  <;> ring

private lemma witnessInstrumentScore_abs_le
    {e : 𝒳 → ℝ} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (q : AssignedFullData 𝒳)
    (he0 : epsilon ≤ e (fullX q.1))
    (he1 : e (fullX q.1) ≤ 1 - epsilon) :
    |witnessInstrumentScore e q| ≤ 1 / epsilon := by
  cases hz : q.2
  · simp only [witnessInstrumentScore, hz, Bool.false_eq_true, ↓reduceIte]
    rw [show -1 / (1 - e (fullX q.1)) =
      -(1 / (1 - e (fullX q.1))) by ring]
    rw [abs_neg, abs_of_pos (one_div_pos.mpr (by linarith))]
    apply one_div_le_one_div_of_le hepsilon
    linarith
  · simp only [witnessInstrumentScore, hz, ↓reduceIte]
    rw [abs_of_pos (one_div_pos.mpr (hepsilon.trans_le he0))]
    exact one_div_le_one_div_of_le hepsilon he0

private lemma witnessGood_assignedOutcome_abs_le
    (q : AssignedFullData 𝒳) (hq : witnessGood q.1) :
    |derivedAssignmentOutcome q.1 q.2| ≤ 1 := by
  rcases hq.2.1 with hy | hy
  · cases hd : potentialReceipt q.1 q.2 <;>
      simp [derivedAssignmentOutcome, potentialOutcome, hd, hy, hq.1]
  · cases hd : potentialReceipt q.1 q.2 <;>
      simp [derivedAssignmentOutcome, potentialOutcome, hd, hy, hq.1]

private lemma witnessAssignedMeasure_score_outcome_integral
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (he : ∀ x, epsilon ≤ e x ∧ e x ≤ 1 - epsilon)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ q in {q | fullX q.1 ∈ A},
        witnessInstrumentScore e q * derivedAssignmentOutcome q.1 q.2
        ∂witnessAssignedMeasure μS p e =
      ∫ o in {o | fullX o ∈ A},
        (derivedAssignmentOutcome o true - derivedAssignmentOutcome o false)
        ∂witnessPopulationMeasure true μS p := by
  have he01 : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := fun x =>
    ⟨hepsilon.le.trans (he x).1,
      (he x).2.trans (sub_le_self 1 hepsilon.le)⟩
  letI : IsProbabilityMeasure (witnessAssignedMeasure μS p e) :=
    witnessAssignedMeasure_probability hpmeas hemeas hp he01
  have hset : MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
    hA.preimage (measurable_fullX.comp measurable_fst)
  have hXset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  let F : AssignedFullData 𝒳 → ℝ := fun q =>
    {q | fullX q.1 ∈ A}.indicator
      (fun q => witnessInstrumentScore e q *
        derivedAssignmentOutcome q.1 q.2) q
  have hFmeas : Measurable F :=
    ((measurable_witnessInstrumentScore hemeas).mul
      measurable_assignedOutcome).indicator hset
  have hFint : Integrable F (witnessAssignedMeasure μS p e) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable (1 / epsilon) ?_
    filter_upwards [witnessAssignedMeasure_ae_good hpmeas hemeas hp he01]
      with q hq
    by_cases hqA : fullX q.1 ∈ A
    · have hmem : q ∈ {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} := hqA
      rw [show F q = witnessInstrumentScore e q *
          derivedAssignmentOutcome q.1 q.2 by simp [F, hmem]]
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |witnessInstrumentScore e q| *
            |derivedAssignmentOutcome q.1 q.2| ≤
            (1 / epsilon) * 1 := mul_le_mul
              (witnessInstrumentScore_abs_le hepsilon q (he _).1 (he _).2)
              (witnessGood_assignedOutcome_abs_le q hq)
              (abs_nonneg _) (by positivity)
        _ = 1 / epsilon := by ring
    · have hb : 0 ≤ 1 / epsilon := one_div_nonneg.mpr hepsilon.le
      simpa [F, hqA] using hb
  rw [← integral_indicator hset]
  change ∫ q, F q ∂witnessAssignedMeasure μS p e = _
  unfold witnessAssignedMeasure
  rw [Causalean.Mathlib.MeasureTheory.integral_bind_map
    (m := witnessPopulationMeasure true μS p)
    (κ := fun o => witnessCoin (e (fullX o)))
    (g := fun o z => (o, z)) (f := F)
    (fun _ => measurable_of_finite _)
    (measurable_witnessAssignmentKernel hemeas) hFint]
  rw [← integral_indicator hXset]
  apply integral_congr_ae
  filter_upwards with o
  by_cases ho : fullX o ∈ A
  · have hmem : (o, true) ∈
        {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} := ho
    have hFval : (fun z => F (o, z)) = fun z =>
        witnessInstrumentScore e (o, z) *
          derivedAssignmentOutcome o z := by
      funext z
      simp [F, ho]
    rw [hFval]
    have he0o : 0 < e (fullX o) := hepsilon.trans_le (he _).1
    have he1o : e (fullX o) < 1 :=
      lt_of_le_of_lt (he _).2 (by linarith)
    rw [witnessCoin_integral he0o.le he1o.le]
    simp [witnessInstrumentScore, he0o.ne', (sub_pos.mpr he1o).ne', ho]
    field_simp [(sub_pos.mpr he1o).ne']
    <;> ring
  · have hFval : (fun z => F (o, z)) = fun _ => 0 := by
      funext z
      simp [F, ho]
    rw [hFval]
    simp [ho]

private lemma witnessAssignedMeasure_score_receipt_integral
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (he : ∀ x, epsilon ≤ e x ∧ e x ≤ 1 - epsilon)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ q in {q | fullX q.1 ∈ A},
        witnessInstrumentScore e q * boolReal (potentialReceipt q.1 q.2)
        ∂witnessAssignedMeasure μS p e =
      ∫ o in {o | fullX o ∈ A},
        (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂witnessPopulationMeasure true μS p := by
  have he01 : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := fun x =>
    ⟨hepsilon.le.trans (he x).1,
      (he x).2.trans (sub_le_self 1 hepsilon.le)⟩
  letI : IsProbabilityMeasure (witnessAssignedMeasure μS p e) :=
    witnessAssignedMeasure_probability hpmeas hemeas hp he01
  have hset : MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
    hA.preimage (measurable_fullX.comp measurable_fst)
  have hXset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  let F : AssignedFullData 𝒳 → ℝ := fun q =>
    {q | fullX q.1 ∈ A}.indicator
      (fun q => witnessInstrumentScore e q *
        boolReal (potentialReceipt q.1 q.2)) q
  have hFmeas : Measurable F :=
    ((measurable_witnessInstrumentScore hemeas).mul
      measurable_assignedReceipt).indicator hset
  have hFint : Integrable F (witnessAssignedMeasure μS p e) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable (1 / epsilon) ?_
    filter_upwards with q
    by_cases hqA : fullX q.1 ∈ A
    · have hmem : q ∈ {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} := hqA
      rw [show F q = witnessInstrumentScore e q *
          boolReal (potentialReceipt q.1 q.2) by simp [F, hmem]]
      rw [Real.norm_eq_abs, abs_mul]
      have hr : |boolReal (potentialReceipt q.1 q.2)| ≤ 1 := by
        cases potentialReceipt q.1 q.2 <;> norm_num [boolReal]
      calc
        |witnessInstrumentScore e q| *
            |boolReal (potentialReceipt q.1 q.2)| ≤
            (1 / epsilon) * 1 := mul_le_mul
              (witnessInstrumentScore_abs_le hepsilon q (he _).1 (he _).2)
              hr (abs_nonneg _) (by positivity)
        _ = 1 / epsilon := by ring
    · have hb : 0 ≤ 1 / epsilon := one_div_nonneg.mpr hepsilon.le
      simpa [F, hqA] using hb
  rw [← integral_indicator hset]
  change ∫ q, F q ∂witnessAssignedMeasure μS p e = _
  unfold witnessAssignedMeasure
  rw [Causalean.Mathlib.MeasureTheory.integral_bind_map
    (m := witnessPopulationMeasure true μS p)
    (κ := fun o => witnessCoin (e (fullX o)))
    (g := fun o z => (o, z)) (f := F)
    (fun _ => measurable_of_finite _)
    (measurable_witnessAssignmentKernel hemeas) hFint]
  rw [← integral_indicator hXset]
  apply integral_congr_ae
  filter_upwards with o
  by_cases ho : fullX o ∈ A
  · have hFval : (fun z => F (o, z)) = fun z =>
        witnessInstrumentScore e (o, z) *
          boolReal (potentialReceipt o z) := by
      funext z
      simp [F, ho]
    rw [hFval]
    have he0o : 0 < e (fullX o) := hepsilon.trans_le (he _).1
    have he1o : e (fullX o) < 1 :=
      lt_of_le_of_lt (he _).2 (by linarith)
    rw [witnessCoin_integral he0o.le he1o.le]
    simp [witnessInstrumentScore, potentialReceipt, he0o.ne',
      (sub_pos.mpr he1o).ne', ho]
    field_simp [(sub_pos.mpr he1o).ne']
    <;> ring
  · have hFval : (fun z => F (o, z)) = fun _ => 0 := by
      funext z
      simp [F, ho]
    rw [hFval]
    simp [ho]

private lemma witnessAssignedMeasureH_score_outcome_integral
    (h : ℝ) (hh : |h| ≤ 1 / 4)
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (he : ∀ x, epsilon ≤ e x ∧ e x ≤ 1 - epsilon)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ q in {q | fullX q.1 ∈ A},
        witnessInstrumentScore e q * derivedAssignmentOutcome q.1 q.2
        ∂witnessAssignedMeasureH h μS p e =
      ∫ o in {o | fullX o ∈ A},
        (derivedAssignmentOutcome o true - derivedAssignmentOutcome o false)
        ∂witnessPopulationMeasureH h true μS p := by
  have he01 : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := fun x =>
    ⟨hepsilon.le.trans (he x).1,
      (he x).2.trans (sub_le_self 1 hepsilon.le)⟩
  letI : IsProbabilityMeasure (witnessAssignedMeasureH h μS p e) :=
    witnessAssignedMeasureH_probability hh hpmeas hemeas hp he01
  have hset : MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
    hA.preimage (measurable_fullX.comp measurable_fst)
  have hXset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  let F : AssignedFullData 𝒳 → ℝ := fun q =>
    {q | fullX q.1 ∈ A}.indicator
      (fun q => witnessInstrumentScore e q *
        derivedAssignmentOutcome q.1 q.2) q
  have hFmeas : Measurable F :=
    ((measurable_witnessInstrumentScore hemeas).mul
      measurable_assignedOutcome).indicator hset
  have hFint : Integrable F (witnessAssignedMeasureH h μS p e) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable
      (1 / epsilon) ?_
    filter_upwards [witnessAssignedMeasureH_ae_good h hh hpmeas
      hemeas hp he01] with q hq
    by_cases hqA : fullX q.1 ∈ A
    · have hmem : q ∈ {q : AssignedFullData 𝒳 |
          fullX q.1 ∈ A} := hqA
      rw [show F q = witnessInstrumentScore e q *
          derivedAssignmentOutcome q.1 q.2 by simp [F, hmem]]
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |witnessInstrumentScore e q| *
            |derivedAssignmentOutcome q.1 q.2| ≤
            (1 / epsilon) * 1 := mul_le_mul
              (witnessInstrumentScore_abs_le hepsilon q (he _).1 (he _).2)
              (witnessGood_assignedOutcome_abs_le q hq)
              (abs_nonneg _) (by positivity)
        _ = 1 / epsilon := by ring
    · have hb : 0 ≤ 1 / epsilon := one_div_nonneg.mpr hepsilon.le
      simpa [F, hqA] using hb
  rw [← integral_indicator hset]
  change ∫ q, F q ∂witnessAssignedMeasureH h μS p e = _
  unfold witnessAssignedMeasureH
  rw [Causalean.Mathlib.MeasureTheory.integral_bind_map
    (m := witnessPopulationMeasureH h true μS p)
    (κ := fun o => witnessCoin (e (fullX o)))
    (g := fun o z => (o, z)) (f := F)
    (fun _ => measurable_of_finite _)
    (measurable_witnessAssignmentKernel hemeas) hFint]
  rw [← integral_indicator hXset]
  apply integral_congr_ae
  filter_upwards with o
  by_cases ho : fullX o ∈ A
  · have hFval : (fun z => F (o, z)) = fun z =>
        witnessInstrumentScore e (o, z) *
          derivedAssignmentOutcome o z := by
      funext z
      simp [F, ho]
    rw [hFval]
    have he0o : 0 < e (fullX o) := hepsilon.trans_le (he _).1
    have he1o : e (fullX o) < 1 :=
      lt_of_le_of_lt (he _).2 (by linarith)
    rw [witnessCoin_integral he0o.le he1o.le]
    simp [witnessInstrumentScore, he0o.ne', (sub_pos.mpr he1o).ne', ho]
    field_simp [(sub_pos.mpr he1o).ne']
    <;> ring
  · have hFval : (fun z => F (o, z)) = fun _ => 0 := by
      funext z
      simp [F, ho]
    rw [hFval]
    simp [ho]

private lemma witnessAssignedMeasureH_score_receipt_integral
    (h : ℝ) (hh : |h| ≤ 1 / 4)
    {μS : Measure 𝒳} [IsProbabilityMeasure μS]
    {p e : 𝒳 → ℝ} (hpmeas : Measurable p) (hemeas : Measurable e)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (he : ∀ x, epsilon ≤ e x ∧ e x ≤ 1 - epsilon)
    (A : Set 𝒳) (hA : MeasurableSet A) :
    ∫ q in {q | fullX q.1 ∈ A},
        witnessInstrumentScore e q * boolReal (potentialReceipt q.1 q.2)
        ∂witnessAssignedMeasureH h μS p e =
      ∫ o in {o | fullX o ∈ A},
        (boolReal (fullD1 o) - boolReal (fullD0 o))
        ∂witnessPopulationMeasureH h true μS p := by
  have he01 : ∀ x, 0 ≤ e x ∧ e x ≤ 1 := fun x =>
    ⟨hepsilon.le.trans (he x).1,
      (he x).2.trans (sub_le_self 1 hepsilon.le)⟩
  letI : IsProbabilityMeasure (witnessAssignedMeasureH h μS p e) :=
    witnessAssignedMeasureH_probability hh hpmeas hemeas hp he01
  have hset : MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
    hA.preimage (measurable_fullX.comp measurable_fst)
  have hXset : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  let F : AssignedFullData 𝒳 → ℝ := fun q =>
    {q | fullX q.1 ∈ A}.indicator
      (fun q => witnessInstrumentScore e q *
        boolReal (potentialReceipt q.1 q.2)) q
  have hFmeas : Measurable F :=
    ((measurable_witnessInstrumentScore hemeas).mul
      measurable_assignedReceipt).indicator hset
  have hFint : Integrable F (witnessAssignedMeasureH h μS p e) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable
      (1 / epsilon) ?_
    filter_upwards with q
    by_cases hqA : fullX q.1 ∈ A
    · have hmem : q ∈ {q : AssignedFullData 𝒳 |
          fullX q.1 ∈ A} := hqA
      rw [show F q = witnessInstrumentScore e q *
          boolReal (potentialReceipt q.1 q.2) by simp [F, hmem]]
      rw [Real.norm_eq_abs, abs_mul]
      have hr : |boolReal (potentialReceipt q.1 q.2)| ≤ 1 := by
        cases potentialReceipt q.1 q.2 <;> norm_num [boolReal]
      calc
        |witnessInstrumentScore e q| *
            |boolReal (potentialReceipt q.1 q.2)| ≤
            (1 / epsilon) * 1 := mul_le_mul
              (witnessInstrumentScore_abs_le hepsilon q (he _).1 (he _).2)
              hr (abs_nonneg _) (by positivity)
        _ = 1 / epsilon := by ring
    · have hb : 0 ≤ 1 / epsilon := one_div_nonneg.mpr hepsilon.le
      simpa [F, hqA] using hb
  rw [← integral_indicator hset]
  change ∫ q, F q ∂witnessAssignedMeasureH h μS p e = _
  unfold witnessAssignedMeasureH
  rw [Causalean.Mathlib.MeasureTheory.integral_bind_map
    (m := witnessPopulationMeasureH h true μS p)
    (κ := fun o => witnessCoin (e (fullX o)))
    (g := fun o z => (o, z)) (f := F)
    (fun _ => measurable_of_finite _)
    (measurable_witnessAssignmentKernel hemeas) hFint]
  rw [← integral_indicator hXset]
  apply integral_congr_ae
  filter_upwards with o
  by_cases ho : fullX o ∈ A
  · have hFval : (fun z => F (o, z)) = fun z =>
        witnessInstrumentScore e (o, z) *
          boolReal (potentialReceipt o z) := by
      funext z
      simp [F, ho]
    rw [hFval]
    have he0o : 0 < e (fullX o) := hepsilon.trans_le (he _).1
    have he1o : e (fullX o) < 1 :=
      lt_of_le_of_lt (he _).2 (by linarith)
    rw [witnessCoin_integral he0o.le he1o.le]
    simp [witnessInstrumentScore, potentialReceipt, he0o.ne',
      (sub_pos.mpr he1o).ne', ho]
    field_simp [(sub_pos.mpr he1o).ne']
    <;> ring
  · have hFval : (fun z => F (o, z)) = fun _ => 0 := by
      funext z
      simp [F, ho]
    rw [hFval]
    simp [ho]

private noncomputable def witnessArray (μS μT : ℕ → Measure 𝒳)
    (p e : ℕ → 𝒳 → ℝ) (hp : ∀ n, Measurable (p n))
    (he : ∀ n, Measurable (e n)) : TransportedArray 𝒳 where
  fullLaw n := witnessFullMeasure (μS n) (μT n) (p n)
  assignedSourceLaw n := witnessAssignedMeasure (μS n) (p n) (e n)
  propensity := e
  propensity_measurable := he
  assignmentOutcome _ z o := derivedAssignmentOutcome o z
  assignmentOutcome_measurable := by
    intro n z
    unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
    have hd : Measurable (fun o : FullData 𝒳 =>
        if z then fullD1 o else fullD0 o) :=
      Measurable.ite (measurableSet_eq_fun measurable_const measurable_const)
        (measurable_fst.comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))
        (measurable_fst.comp (measurable_snd.comp
          measurable_snd))
    exact Measurable.ite (measurableSet_eq_fun hd measurable_const)
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd))))
      (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  assignmentContrast n _ x := p n x / 2
  assignmentContrast_measurable := fun n s => (hp n).div_const 2
  receiptContrast n _ x := p n x
  receiptContrast_measurable := fun n s => hp n

private noncomputable def witnessArrayH (h : ℝ)
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hp : ∀ n, Measurable (p n))
    (he : ∀ n, Measurable (e n)) : TransportedArray 𝒳 where
  fullLaw n := witnessFullMeasureH h (μS n) (μT n) (p n)
  assignedSourceLaw n := witnessAssignedMeasureH h (μS n) (p n) (e n)
  propensity := e
  propensity_measurable := he
  assignmentOutcome _ z o := derivedAssignmentOutcome o z
  assignmentOutcome_measurable := by
    intro n z
    unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
    have hd : Measurable (fun o : FullData 𝒳 =>
        if z then fullD1 o else fullD0 o) :=
      Measurable.ite (measurableSet_eq_fun measurable_const measurable_const)
        (measurable_fst.comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    exact Measurable.ite (measurableSet_eq_fun hd measurable_const)
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp measurable_snd))))
      (measurable_fst.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  assignmentContrast n _ x := p n x * (1 / 2 + h)
  assignmentContrast_measurable :=
    fun n s => (hp n).mul_const (1 / 2 + h)
  receiptContrast n _ x := p n x
  receiptContrast_measurable := fun n s => hp n

private lemma witnessArrayH_zero
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hp : ∀ n, Measurable (p n)) (he : ∀ n, Measurable (e n)) :
    witnessArrayH 0 μS μT p e hp he = witnessArray μS μT p e hp he := by
  simp [witnessArrayH, witnessArray, witnessFullMeasureH_zero,
    witnessAssignedMeasureH_zero]
  funext n s x
  ring

private lemma witnessArrayH_sourceObsLaw_eq_bind
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ m, Measurable (p m)) (hemeas : ∀ m, Measurable (e m))
    (n : ℕ) :
    sourceObsLaw (witnessArrayH h μS μT p e hpmeas hemeas) n =
      (μS n).bind (witnessSourceObsKernelH h (p n) (e n)) := by
  ext A hA
  unfold sourceObsLaw witnessArrayH witnessAssignedMeasureH
    witnessPopulationMeasureH
  rw [Measure.map_apply measurable_observeSource hA]
  rw [Measure.bind_apply (hA.preimage measurable_observeSource)
    (measurable_witnessAssignmentKernel (hemeas n)).aemeasurable]
  rw [Measure.bind_apply hA
    (measurable_witnessSourceObsKernelH h (hpmeas n) (hemeas n)).aemeasurable]
  have hinner : Measurable (fun o : FullData 𝒳 =>
      (witnessCoin (e n (fullX o))).map fun z => observeSource (o, z)) := by
    simp_rw [witnessCoin_map]
    have hpack (z : Bool) :
        Measurable (fun o : FullData 𝒳 => observeSource (o, z)) :=
      measurable_observeSource.comp (measurable_id.prodMk measurable_const)
    have hefull : Measurable (fun o : FullData 𝒳 =>
        e n (fullX o)) := (hemeas n).comp measurable_fullX
    exact (measurable_variable_smul_measure
      (ENNReal.measurable_ofReal.comp hefull)
      (Measure.measurable_dirac.comp (hpack true))).add
        (measurable_variable_smul_measure
          (ENNReal.measurable_ofReal.comp (measurable_const.sub hefull))
          (Measure.measurable_dirac.comp (hpack false)))
  have hlin :
      (∫⁻ o, ((witnessCoin (e n (fullX o))).map fun z => (o, z))
          (observeSource ⁻¹' A)
          ∂(μS n).bind (witnessPotentialKernelH h true (p n))) =
        ∫⁻ o, ((witnessCoin (e n (fullX o))).map fun z =>
          observeSource (o, z)) A
          ∂(μS n).bind (witnessPotentialKernelH h true (p n)) := by
    apply lintegral_congr
    intro o
    rw [Measure.map_apply (measurable_of_finite _)
      (hA.preimage measurable_observeSource)]
    rw [Measure.map_apply (measurable_of_finite _) hA]
    rfl
  rw [hlin]
  rw [Measure.lintegral_bind
    (m := μS n) (μ := witnessPotentialKernelH h true (p n))
    (f := fun o => ((witnessCoin (e n (fullX o))).map fun z =>
      observeSource (o, z)) A)
    (measurable_witnessPotentialKernelH h true (hpmeas n)).aemeasurable
    ((Measure.measurable_coe hA).comp hinner).aemeasurable]
  apply lintegral_congr
  intro x
  unfold witnessSourceObsKernelH
  rw [Measure.bind_apply hA
    hinner.aemeasurable]

private lemma witnessArrayH_sourceObsLaw_probability
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ m, Measurable (p m)) (hemeas : ∀ m, Measurable (e m))
    (hμS : ∀ m, IsProbabilityMeasure (μS m))
    (hh : |h| ≤ 1 / 4) (hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1)
    (he : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1) (n : ℕ) :
    IsProbabilityMeasure
      (sourceObsLaw (witnessArrayH h μS μT p e hpmeas hemeas) n) := by
  letI := hμS n
  rw [witnessArrayH_sourceObsLaw_eq_bind]
  apply isProbabilityMeasure_bind
    (measurable_witnessSourceObsKernelH h (hpmeas n) (hemeas n)).aemeasurable
  filter_upwards with x
  rw [witnessSourceObsKernelH_eq_coinKernel h (hemeas n) x]
  exact witnessObservedCoinKernelH_probability h hh (hp n) (he n) x

private lemma witnessArrayH_sourceObsLaw_eq_withDensity
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ m, Measurable (p m)) (hemeas : ∀ m, Measurable (e m))
    (hh : |h| ≤ 1 / 4) (hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1)
    (he : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1) (n : ℕ) :
    sourceObsLaw (witnessArrayH h μS μT p e hpmeas hemeas) n =
      (sourceObsLaw (witnessArrayH 0 μS μT p e hpmeas hemeas) n).withDensity
        (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h (p n)) := by
  rw [witnessArrayH_sourceObsLaw_eq_bind,
    witnessArrayH_sourceObsLaw_eq_bind]
  ext A hA
  rw [withDensity_apply _ hA]
  rw [← lintegral_indicator hA]
  rw [Measure.bind_apply hA
    (measurable_witnessSourceObsKernelH h (hpmeas n) (hemeas n)).aemeasurable]
  rw [Measure.lintegral_bind
    (measurable_witnessSourceObsKernelH 0 (hpmeas n) (hemeas n)).aemeasurable
    ((ENNReal.measurable_ofReal.comp
      (measurable_witnessSourceLikelihoodRatio h (hpmeas n))).indicator
        hA).aemeasurable]
  apply lintegral_congr
  intro x
  rw [witnessSourceObsKernelH_eq_coinKernel h (hemeas n) x,
    witnessSourceObsKernelH_eq_coinKernel 0 (hemeas n) x]
  rw [witnessObservedCoinKernelH_eq_withDensity h (hpmeas n) hh
    (hp n) (he n) x]
  rw [withDensity_apply _ hA]
  rw [lintegral_indicator hA]

private lemma witnessArrayH_source_chiSq_eq
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ m, Measurable (p m)) (hemeas : ∀ m, Measurable (e m))
    (hμS : ∀ m, IsProbabilityMeasure (μS m))
    (hh : |h| ≤ 1 / 4) (hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1)
    (he : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1) (n : ℕ) :
    Causalean.Stat.chiSqDiv
        (sourceObsLaw (witnessArrayH h μS μT p e hpmeas hemeas) n)
        (sourceObsLaw (witnessArrayH 0 μS μT p e hpmeas hemeas) n) =
      ∫ x, 8 * e n x * p n x ^ 2 * h ^ 2 / (1 + p n x) ∂μS n := by
  let Ph := sourceObsLaw
    (witnessArrayH h μS μT p e hpmeas hemeas) n
  let P0 := sourceObsLaw
    (witnessArrayH 0 μS μT p e hpmeas hemeas) n
  letI : IsProbabilityMeasure P0 := by
    exact witnessArrayH_sourceObsLaw_probability 0 μS μT p e hpmeas hemeas
      hμS (by norm_num) hp he n
  let f : SourceObs 𝒳 → ℝ :=
    fun o => (witnessSourceLikelihoodRatio h (p n) o - 1) ^ 2
  have hfmeas : Measurable f :=
    ((measurable_witnessSourceLikelihoodRatio h (hpmeas n)).sub_const 1).pow_const 2
  have hfint : Integrable f P0 := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    exact witnessSourceLikelihoodRatio_sq_dev_le_one h hh (hp n) o
  have hfintbind :
      Integrable f ((μS n).bind
        (witnessSourceObsKernelH 0 (p n) (e n))) := by
    rw [← witnessArrayH_sourceObsLaw_eq_bind 0 μS μT p e hpmeas hemeas n]
    exact hfint
  have hdensity :
      Ph = P0.withDensity
        (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h (p n)) := by
    exact witnessArrayH_sourceObsLaw_eq_withDensity h μS μT p e hpmeas
      hemeas hh hp he n
  have hrn :
      (fun o => ((Ph.rnDeriv P0 o).toReal - 1) ^ 2) =ᵐ[P0] f := by
    rw [hdensity]
    have hratioMeas : Measurable
        (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h (p n)) :=
      ENNReal.measurable_ofReal.comp
        (measurable_witnessSourceLikelihoodRatio h (hpmeas n))
    filter_upwards [Measure.rnDeriv_withDensity P0 hratioMeas] with o ho
    rw [ho]
    simp only [f, Function.comp_apply,
      ENNReal.toReal_ofReal
        (witnessSourceLikelihoodRatio_nonneg h hh (hp n) o)]
  unfold Causalean.Stat.chiSqDiv
  change (∫ o, ((Ph.rnDeriv P0 o).toReal - 1) ^ 2 ∂P0) = _
  rw [integral_congr_ae hrn]
  rw [show P0 = (μS n).bind
      (witnessSourceObsKernelH 0 (p n) (e n)) by
    exact witnessArrayH_sourceObsLaw_eq_bind 0 μS μT p e hpmeas hemeas n]
  rw [Causalean.Mathlib.MeasureTheory.integral_bind
    (measurable_witnessSourceObsKernelH 0 (hpmeas n) (hemeas n)) hfintbind]
  apply integral_congr_ae
  filter_upwards with x
  rw [witnessSourceObsKernelH_eq_coinKernel 0 (hemeas n) x]
  exact witnessObservedCoinKernelH_chiIntegral h (hpmeas n) (hp n) (he n) x

private lemma witnessArrayH_source_ac_integrable
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ m, Measurable (p m)) (hemeas : ∀ m, Measurable (e m))
    (hμS : ∀ m, IsProbabilityMeasure (μS m))
    (hh : |h| ≤ 1 / 4) (hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1)
    (he : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1) (n : ℕ) :
    let Ph := sourceObsLaw
      (witnessArrayH h μS μT p e hpmeas hemeas) n
    let P0 := sourceObsLaw
      (witnessArrayH 0 μS μT p e hpmeas hemeas) n
    Ph ≪ P0 ∧
      Integrable (fun o => ((Ph.rnDeriv P0 o).toReal - 1) ^ 2) P0 := by
  dsimp only
  let Ph := sourceObsLaw
    (witnessArrayH h μS μT p e hpmeas hemeas) n
  let P0 := sourceObsLaw
    (witnessArrayH 0 μS μT p e hpmeas hemeas) n
  let f : SourceObs 𝒳 → ℝ :=
    fun o => (witnessSourceLikelihoodRatio h (p n) o - 1) ^ 2
  letI : IsProbabilityMeasure P0 := by
    exact witnessArrayH_sourceObsLaw_probability 0 μS μT p e hpmeas hemeas
      hμS (by norm_num) hp he n
  have hfmeas : Measurable f :=
    ((measurable_witnessSourceLikelihoodRatio h (hpmeas n)).sub_const 1).pow_const 2
  have hfint : Integrable f P0 := by
    refine Integrable.of_bound hfmeas.aestronglyMeasurable 1 ?_
    filter_upwards with o
    exact witnessSourceLikelihoodRatio_sq_dev_le_one h hh (hp n) o
  have hdensity :
      Ph = P0.withDensity
        (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h (p n)) :=
    witnessArrayH_sourceObsLaw_eq_withDensity h μS μT p e hpmeas
      hemeas hh hp he n
  have hratioMeas : Measurable
      (ENNReal.ofReal ∘ witnessSourceLikelihoodRatio h (p n)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_witnessSourceLikelihoodRatio h (hpmeas n))
  have hrn :
      (fun o => ((Ph.rnDeriv P0 o).toReal - 1) ^ 2) =ᵐ[P0] f := by
    rw [hdensity]
    filter_upwards [Measure.rnDeriv_withDensity P0 hratioMeas] with o ho
    rw [ho]
    simp only [f, Function.comp_apply,
      ENNReal.toReal_ofReal
        (witnessSourceLikelihoodRatio_nonneg h hh (hp n) o)]
  constructor
  · change Ph ≪ P0
    rw [hdensity]
    exact withDensity_absolutelyContinuous P0 _
  · change Integrable (fun o => ((Ph.rnDeriv P0 o).toReal - 1) ^ 2) P0
    exact hfint.congr hrn.symm

private lemma witnessArray_populationLaw
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) (s : Bool) :
    populationLaw (witnessArray μS μT p e hpmeas hemeas) n s =
      if s then witnessPopulationMeasure true (μS n) (p n)
      else witnessPopulationMeasure false (μT n) (p n) := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  exact witnessFullMeasure_cond (hpmeas n) (hp n) s

private lemma witnessArray_assigned_map_fst
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (he : ∀ n x, 0 ≤ e n x ∧ e n x ≤ 1)
    (n : ℕ) :
    ((witnessArray μS μT p e hpmeas hemeas).assignedSourceLaw n).map Prod.fst =
      populationLaw (witnessArray μS μT p e hpmeas hemeas) n true := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  rw [witnessArray_populationLaw μS μT p e hpmeas hemeas hμS
    hμT hp n true]
  exact witnessAssignedMeasure_map_fst (hpmeas n) (hemeas n) (hp n) (he n)

private lemma witnessArray_sourceXLaw
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (he : ∀ n x, 0 ≤ e n x ∧ e n x ≤ 1)
    (n : ℕ) :
    sourceXLaw (witnessArray μS μT p e hpmeas hemeas) n = μS n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  unfold sourceXLaw sourceObsLaw
  rw [Measure.map_map measurable_fst measurable_observeSource]
  change Measure.map (fun q : AssignedFullData 𝒳 => fullX q.1)
    ((witnessArray μS μT p e hpmeas hemeas).assignedSourceLaw n) = μS n
  rw [show (fun q : AssignedFullData 𝒳 => fullX q.1) =
      fullX ∘ Prod.fst by rfl, ← Measure.map_map measurable_fullX measurable_fst]
  rw [witnessArray_assigned_map_fst μS μT p e hpmeas hemeas hμS hμT hp he n]
  rw [witnessArray_populationLaw μS μT p e hpmeas hemeas hμS
    hμT hp n true]
  exact witnessPopulationMeasure_map_fullX true (hpmeas n) (hp n)

private lemma witnessArray_targetXLaw
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    targetXLaw (witnessArray μS μT p e hpmeas hemeas) n = μT n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  unfold targetXLaw populationXLaw
  rw [witnessArray_populationLaw μS μT p e hpmeas hemeas hμS hμT hp n false]
  exact witnessPopulationMeasure_map_fullX false (hpmeas n) (hp n)

private lemma witnessArrayH_fullLaw_probability
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1) (n : ℕ) :
    IsProbabilityMeasure
      ((witnessArrayH h μS μT p e hpmeas hemeas).fullLaw n) := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  exact witnessFullMeasureH_probability hh (hpmeas n) (hp n)

private lemma witnessArrayH_assignedSourceLaw_probability
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (he : ∀ n x, 0 ≤ e n x ∧ e n x ≤ 1) (n : ℕ) :
    IsProbabilityMeasure
      ((witnessArrayH h μS μT p e hpmeas hemeas).assignedSourceLaw n) := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  exact witnessAssignedMeasureH_probability hh (hpmeas n) (hemeas n)
    (hp n) (he n)

private lemma witnessArrayH_populationLaw
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) (s : Bool) :
    populationLaw (witnessArrayH h μS μT p e hpmeas hemeas) n s =
      if s then witnessPopulationMeasureH h true (μS n) (p n)
      else witnessPopulationMeasureH h false (μT n) (p n) := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  exact witnessFullMeasureH_cond hh (hpmeas n) (hp n) s

private lemma witnessArrayH_assigned_map_fst
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (he : ∀ n x, 0 ≤ e n x ∧ e n x ≤ 1)
    (n : ℕ) :
    ((witnessArrayH h μS μT p e hpmeas hemeas).assignedSourceLaw n).map
        Prod.fst =
      populationLaw (witnessArrayH h μS μT p e hpmeas hemeas) n true := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp n true]
  exact witnessAssignedMeasureH_map_fst hh (hpmeas n) (hemeas n)
    (hp n) (he n)

private lemma witnessArrayH_sourceXLaw
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (he : ∀ n x, 0 ≤ e n x ∧ e n x ≤ 1)
    (n : ℕ) :
    sourceXLaw (witnessArrayH h μS μT p e hpmeas hemeas) n = μS n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  unfold sourceXLaw sourceObsLaw
  rw [Measure.map_map measurable_fst measurable_observeSource]
  change Measure.map (fun q : AssignedFullData 𝒳 => fullX q.1)
    ((witnessArrayH h μS μT p e hpmeas hemeas).assignedSourceLaw n) = μS n
  rw [show (fun q : AssignedFullData 𝒳 => fullX q.1) =
      fullX ∘ Prod.fst by rfl, ← Measure.map_map measurable_fullX measurable_fst]
  rw [witnessArrayH_assigned_map_fst h μS μT p e hpmeas hemeas
    hμS hμT hh hp he n]
  rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp n true]
  exact witnessPopulationMeasureH_map_fullX h true hh (hpmeas n) (hp n)

private lemma witnessArrayH_targetXLaw
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    targetXLaw (witnessArrayH h μS μT p e hpmeas hemeas) n = μT n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  unfold targetXLaw populationXLaw
  rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp n false]
  exact witnessPopulationMeasureH_map_fullX h false hh (hpmeas n) (hp n)

private lemma witnessArrayH_populationXLaw
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) (s : Bool) :
    populationXLaw (witnessArrayH h μS μT p e hpmeas hemeas) n s =
      if s then μS n else μT n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  unfold populationXLaw
  rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp n s]
  cases s
  · exact witnessPopulationMeasureH_map_fullX h false hh
      (hpmeas n) (hp n)
  · exact witnessPopulationMeasureH_map_fullX h true hh
      (hpmeas n) (hp n)

private lemma witnessArrayH_ivRandomization
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (he : ∀ n x, 0 ≤ e n x ∧ e n x ≤ 1)
    (n : ℕ) :
    IVRandomization (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  intro A hA z
  letI : IsProbabilityMeasure (μS n) := hμS n
  change (witnessAssignedMeasureH h (μS n) (p n) (e n)
    {q | q.1 ∈ A ∧ q.2 = z}).toReal =
      ∫ o in A, (if z then e n (fullX o) else 1 - e n (fullX o))
        ∂populationLaw (witnessArrayH h μS μT p e hpmeas hemeas) n true
  rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp n true]
  exact witnessAssignedMeasureH_event h hh (hpmeas n) (hemeas n)
    (hp n) (he n) A hA z

private lemma witnessArrayH_sourceObservation
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (he : ∀ n x, epsilon ≤ e n x ∧ e n x ≤ 1 - epsilon)
    (n : ℕ) :
    SourceObservation (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  /-
  intro A hA
  let P := witnessArrayH h μS μT p e hpmeas hemeas
  have he01all : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  have hFullA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  have hEvent : MeasurableSet {o : SourceObs 𝒳 |
      o.1 ∈ A ∧ o.2.1 = true} :=
    (hA.preimage measurable_fst).inter
      (measurableSet_eq_fun
        (measurable_fst.comp measurable_snd) measurable_const)
  unfold sourceObsLaw
  rw [Measure.map_apply measurable_observeSource hEvent]
  change (witnessAssignedMeasureH h (μS n) (p n) (e n)
    {q | q.1 ∈ {o : FullData 𝒳 | fullX o ∈ A} ∧ q.2 = true}).toReal =
      ∫ x in A, e n x ∂sourceXLaw P n
  rw [witnessAssignedMeasureH_event h hh (hpmeas n) (hemeas n)
    (hp n) (he01all n) _ hFullA true]
  simp only [if_true]
  rw [witnessPopulationMeasureH_setIntegral_fullX h true hh
    (hpmeas n) (hp n) (e n) (hemeas n) A hA]
  rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp he01all n]
  -/

  /- PRIOR PROOF (carry-over): the former strengthened
  `SourceObservation` bundle. -/
  /-
  let P := witnessArrayH h μS μT p e hpmeas hemeas
  have he01all : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  refine ⟨?_, ?_⟩
  · exact witnessArrayH_assigned_map_fst h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01all n
  · intro A hA
    have hFullA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
      hA.preimage measurable_fullX
    have hEvent : MeasurableSet {o : SourceObs 𝒳 |
        o.1 ∈ A ∧ o.2.1 = true} :=
      (hA.preimage measurable_fst).inter
        (measurableSet_eq_fun
          (measurable_fst.comp measurable_snd) measurable_const)
    unfold sourceObsLaw
    rw [Measure.map_apply measurable_observeSource hEvent]
    change (witnessAssignedMeasureH h (μS n) (p n) (e n)
      {q | q.1 ∈ {o : FullData 𝒳 | fullX o ∈ A} ∧ q.2 = true}).toReal =
        ∫ x in A, e n x ∂sourceXLaw P n
    rw [witnessAssignedMeasureH_event h hh (hpmeas n) (hemeas n)
      (hp n) (he01all n) _ hFullA true]
    simp only [if_true]
    rw [witnessPopulationMeasureH_setIntegral_fullX h true hh
      (hpmeas n) (hp n) (e n) (hemeas n) A hA]
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01all n]
  -/

  -- Restored proof of the full source-observation bundle.

  let P := witnessArrayH h μS μT p e hpmeas hemeas
  letI : IsProbabilityMeasure (μS n) := hμS n
  have he01all : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  have hAssigned : IsProbabilityMeasure (P.assignedSourceLaw n) := by
    exact witnessArrayH_assignedSourceLaw_probability h μS μT p e
      hpmeas hemeas hμS hh hp he01all n
  letI : IsProbabilityMeasure (P.assignedSourceLaw n) := hAssigned
  have hObs : IsProbabilityMeasure (sourceObsLaw P n) := by
    unfold sourceObsLaw
    exact Measure.isProbabilityMeasure_map measurable_observeSource.aemeasurable
  refine ⟨hAssigned, hObs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hYset : MeasurableSet {o : SourceObs 𝒳 |
        o.2.2.2 ∈ Set.Icc (0 : ℝ) 1} :=
      measurableSet_Icc.preimage
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
    unfold sourceObsLaw
    rw [ae_map_iff measurable_observeSource.aemeasurable hYset]
    filter_upwards [witnessAssignedMeasureH_ae_good h hh
      (hpmeas n) (hemeas n) (hp n) (he01all n)] with q hq
    rcases hq.2.1 with hy | hy
    · cases q.2 <;> cases fullD0 q.1 <;> cases fullD1 q.1 <;>
        simp [observeSource, potentialOutcome, potentialReceipt, hy, hq.1] <;>
        (constructor <;> split_ifs <;> norm_num)
    · cases q.2 <;> cases fullD0 q.1 <;> cases fullD1 q.1 <;>
        simp [observeSource, potentialOutcome, potentialReceipt, hy, hq.1] <;>
        (constructor <;> split_ifs <;> norm_num)
  · exact witnessArrayH_assigned_map_fst h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01all n
  · intro A hA
    have hFullA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
      hA.preimage measurable_fullX
    have hEvent : MeasurableSet {o : SourceObs 𝒳 |
        o.1 ∈ A ∧ o.2.1 = true} :=
      (hA.preimage measurable_fst).inter
        (measurableSet_eq_fun
          (measurable_fst.comp measurable_snd) measurable_const)
    unfold sourceObsLaw
    rw [Measure.map_apply measurable_observeSource hEvent]
    change (witnessAssignedMeasureH h (μS n) (p n) (e n)
      {q | q.1 ∈ {o : FullData 𝒳 | fullX o ∈ A} ∧ q.2 = true}).toReal =
        ∫ x in A, e n x ∂sourceXLaw P n
    rw [witnessAssignedMeasureH_event h hh (hpmeas n) (hemeas n)
      (hp n) (he01all n) _ hFullA true]
    simp only [if_true]
    rw [witnessPopulationMeasureH_setIntegral_fullX h true hh
      (hpmeas n) (hp n) (e n) (hemeas n) A hA]
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01all n]
  · intro A hA
    have hSourceSet : MeasurableSet {o : SourceObs 𝒳 | o.1 ∈ A} :=
      hA.preimage measurable_fst
    rw [← integral_indicator hSourceSet]
    unfold sourceObsLaw
    rw [integral_map measurable_observeSource.aemeasurable <| by
      have hs : Measurable (fun o : SourceObs 𝒳 =>
          instrumentScore P n o * o.2.2.2) := by
        have hz : Measurable (fun o : SourceObs 𝒳 => o.2.1) :=
          measurable_fst.comp measurable_snd
        have hex : Measurable (fun o : SourceObs 𝒳 => e n o.1) :=
          (hemeas n).comp measurable_fst
        have hscore : Measurable (fun o : SourceObs 𝒳 =>
            if o.2.1 then 1 / e n o.1 else -1 / (1 - e n o.1)) :=
          Measurable.ite (measurableSet_eq_fun hz measurable_const)
            (measurable_const.div hex)
            (measurable_const.div (measurable_const.sub hex))
        exact hscore.mul
          (measurable_snd.comp (measurable_snd.comp measurable_snd))
      exact (hs.indicator hSourceSet).aestronglyMeasurable]
    have hcomp : (fun q : AssignedFullData 𝒳 =>
        {o : SourceObs 𝒳 | o.1 ∈ A}.indicator
          (fun o => instrumentScore P n o * o.2.2.2) (observeSource q)) =
        fun q => {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
          (fun q => witnessInstrumentScore (e n) q *
            derivedAssignmentOutcome q.1 q.2) q := by
      funext q
      rfl
    rw [hcomp]
    have hAssignedSet :
        MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
      hA.preimage (measurable_fullX.comp measurable_fst)
    change ∫ q, {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
        (fun q => witnessInstrumentScore (e n) q *
          derivedAssignmentOutcome q.1 q.2) q
        ∂witnessAssignedMeasureH h (μS n) (p n) (e n) =
      ∫ x in A, p n x * (1 / 2 + h) ∂sourceXLaw P n
    rw [integral_indicator hAssignedSet]
    rw [witnessAssignedMeasureH_score_outcome_integral h hh
      (hpmeas n) (hemeas n) (hp n) hepsilon (he n) A hA]
    rw [witnessPopulationMeasureH_outcome_integral h true hh
      (hpmeas n) (hp n) A hA]
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01all n]
  · filter_upwards with x
    change -1 ≤ p n x * (1 / 2 + h) ∧
      p n x * (1 / 2 + h) ≤ 1
    have habs := abs_le.mp hh
    constructor
    · nlinarith [(hp n x).1]
    · nlinarith [(hp n x).1, (hp n x).2]
  · intro A hA
    have hSourceSet : MeasurableSet {o : SourceObs 𝒳 | o.1 ∈ A} :=
      hA.preimage measurable_fst
    rw [← integral_indicator hSourceSet]
    unfold sourceObsLaw
    rw [integral_map measurable_observeSource.aemeasurable <| by
      have hs : Measurable (fun o : SourceObs 𝒳 =>
          instrumentScore P n o * boolReal o.2.2.1) := by
        have hz : Measurable (fun o : SourceObs 𝒳 => o.2.1) :=
          measurable_fst.comp measurable_snd
        have hex : Measurable (fun o : SourceObs 𝒳 => e n o.1) :=
          (hemeas n).comp measurable_fst
        have hscore : Measurable (fun o : SourceObs 𝒳 =>
            if o.2.1 then 1 / e n o.1 else -1 / (1 - e n o.1)) :=
          Measurable.ite (measurableSet_eq_fun hz measurable_const)
            (measurable_const.div hex)
            (measurable_const.div (measurable_const.sub hex))
        have hd : Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
          unfold boolReal
          exact Measurable.ite
            (measurableSet_eq_fun
              (measurable_fst.comp
                (measurable_snd.comp measurable_snd)) measurable_const)
            measurable_const measurable_const
        exact hscore.mul hd
      exact (hs.indicator hSourceSet).aestronglyMeasurable]
    have hcomp : (fun q : AssignedFullData 𝒳 =>
        {o : SourceObs 𝒳 | o.1 ∈ A}.indicator
          (fun o => instrumentScore P n o * boolReal o.2.2.1)
          (observeSource q)) =
        fun q => {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
          (fun q => witnessInstrumentScore (e n) q *
            boolReal (potentialReceipt q.1 q.2)) q := by
      funext q
      rfl
    rw [hcomp]
    have hAssignedSet :
        MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
      hA.preimage (measurable_fullX.comp measurable_fst)
    change ∫ q, {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
        (fun q => witnessInstrumentScore (e n) q *
          boolReal (potentialReceipt q.1 q.2)) q
        ∂witnessAssignedMeasureH h (μS n) (p n) (e n) =
      ∫ x in A, p n x ∂sourceXLaw P n
    rw [integral_indicator hAssignedSet]
    rw [witnessAssignedMeasureH_score_receipt_integral h hh
      (hpmeas n) (hemeas n) (hp n) hepsilon (he n) A hA]
    rw [witnessPopulationMeasureH_receipt_integral h true hh
      (hpmeas n) (hp n) A hA]
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01all n]
  · filter_upwards with x
    exact hp n x


private lemma witnessArrayH_fullDataSupport
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    FullDataSupport (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  have hprob := witnessArrayH_fullLaw_probability h μS μT p e hpmeas
    hemeas hμS hμT hh hp n
  refine ⟨hprob, ?_⟩
  have hS := witnessPopulationMeasureH_ae_good
    (μ := μS n) h true hh (hpmeas n) (hp n)
  have hT := witnessPopulationMeasureH_ae_good
    (μ := μT n) h false hh (hpmeas n) (hp n)
  have hgood :
      ∀ᵐ o ∂witnessFullMeasureH h (μS n) (μT n) (p n),
        witnessGood o := by
    rw [ae_iff] at hS hT ⊢
    unfold witnessFullMeasureH
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hS, hT]
    simp
  filter_upwards [hgood] with o ho
  rcases ho.2.1 with hy | hy
  · simp [ho.1, hy]
  · simp [ho.1, hy]

private lemma witnessArrayH_populationPresence
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    PopulationPresence (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  intro s
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  change 0 < (witnessFullMeasureH h (μS n) (μT n) (p n)
    {o | fullS o = s}).toReal
  unfold witnessFullMeasureH
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [witnessPopulationMeasureH_population_mass h true s hh
      (hpmeas n) (hp n),
    witnessPopulationMeasureH_population_mass h false s hh
      (hpmeas n) (hp n)]
  cases s <;> norm_num

private lemma witnessArrayH_ivExclusion
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (n : ℕ) :
    IVExclusion (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  intro s z
  rfl

private lemma witnessArrayH_ivMonotonicity
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    IVMonotonicity (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  intro s
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp n s]
  cases s
  · filter_upwards [witnessPopulationMeasureH_ae_good h false hh
      (hpmeas n) (hp n)] with o ho
    exact ho.2.2.1
  · filter_upwards [witnessPopulationMeasureH_ae_good h true hh
      (hpmeas n) (hp n)] with o ho
    exact ho.2.2.1

private lemma witnessArrayH_receiptTransport
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    ReceiptTransport (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  constructor
  · intro s A hA
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n s]
    rw [witnessArrayH_populationXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n s]
    cases s
    · exact witnessPopulationMeasureH_receipt_integral h false hh
        (hpmeas n) (hp n) A hA
    · exact witnessPopulationMeasureH_receipt_integral h true hh
        (hpmeas n) (hp n) A hA
  · rfl

private lemma witnessArrayH_outcomeTransport
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    OutcomeTransport (witnessArrayH h μS μT p e hpmeas hemeas) n := by
  constructor
  · intro s A hA
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n s]
    rw [witnessArrayH_populationXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n s]
    cases s
    · exact witnessPopulationMeasureH_outcome_integral h false hh
        (hpmeas n) (hp n) A hA
    · exact witnessPopulationMeasureH_outcome_integral h true hh
        (hpmeas n) (hp n) A hA
  · rfl

private lemma witnessArray_ivRandomization
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (he : ∀ n x, 0 ≤ e n x ∧ e n x ≤ 1)
    (n : ℕ) :
    IVRandomization (witnessArray μS μT p e hpmeas hemeas) n := by
  intro A hA z
  letI : IsProbabilityMeasure (μS n) := hμS n
  change (witnessAssignedMeasure (μS n) (p n) (e n)
    {q | q.1 ∈ A ∧ q.2 = z}).toReal =
      ∫ o in A, (if z then e n (fullX o) else 1 - e n (fullX o))
        ∂populationLaw (witnessArray μS μT p e hpmeas hemeas) n true
  rw [witnessArray_populationLaw μS μT p e hpmeas hemeas
    hμS hμT hp n true]
  exact witnessAssignedMeasure_event (hpmeas n) (hemeas n)
    (hp n) (he n) A hA z

private lemma witnessArray_sourceObservation
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (he : ∀ n x, epsilon ≤ e n x ∧ e n x ≤ 1 - epsilon)
    (n : ℕ) :
    SourceObservation (witnessArray μS μT p e hpmeas hemeas) n := by
  /-
  intro A hA
  let P := witnessArray μS μT p e hpmeas hemeas
  have he01all : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  have he01 : ∀ x, 0 ≤ e n x ∧ e n x ≤ 1 := fun x =>
    he01all n x
  have hFullA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
    hA.preimage measurable_fullX
  have hEvent : MeasurableSet {o : SourceObs 𝒳 |
      o.1 ∈ A ∧ o.2.1 = true} :=
    (hA.preimage measurable_fst).inter
      (measurableSet_eq_fun
        (measurable_fst.comp measurable_snd) measurable_const)
  unfold sourceObsLaw
  rw [Measure.map_apply measurable_observeSource hEvent]
  change (witnessAssignedMeasure (μS n) (p n) (e n)
    {q | q.1 ∈ {o : FullData 𝒳 | fullX o ∈ A} ∧ q.2 = true}).toReal =
      ∫ x in A, e n x ∂sourceXLaw P n
  rw [witnessAssignedMeasure_event (hpmeas n) (hemeas n)
    (hp n) he01 {o : FullData 𝒳 | fullX o ∈ A} hFullA true]
  simp only [if_pos rfl]
  simp only [if_true]
  rw [witnessPopulationMeasure_setIntegral_fullX true
    (hpmeas n) (hp n) (e n) (hemeas n) A hA]
  rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
    hμS hμT hp he01all n]
  -/

  /- PRIOR PROOF (carry-over): the former strengthened
  `SourceObservation` bundle. -/
  /-
  let P := witnessArray μS μT p e hpmeas hemeas
  have he01all : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  have he01 : ∀ x, 0 ≤ e n x ∧ e n x ≤ 1 := fun x =>
    he01all n x
  refine ⟨?_, ?_⟩
  · exact witnessArray_assigned_map_fst μS μT p e hpmeas hemeas
      hμS hμT hp he01all n
  · intro A hA
    have hFullA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
      hA.preimage measurable_fullX
    have hEvent : MeasurableSet {o : SourceObs 𝒳 |
        o.1 ∈ A ∧ o.2.1 = true} :=
      (hA.preimage measurable_fst).inter
        (measurableSet_eq_fun
          (measurable_fst.comp measurable_snd) measurable_const)
    unfold sourceObsLaw
    rw [Measure.map_apply measurable_observeSource hEvent]
    change (witnessAssignedMeasure (μS n) (p n) (e n)
      {q | q.1 ∈ {o : FullData 𝒳 | fullX o ∈ A} ∧ q.2 = true}).toReal =
        ∫ x in A, e n x ∂sourceXLaw P n
    rw [witnessAssignedMeasure_event (hpmeas n) (hemeas n)
      (hp n) he01 {o : FullData 𝒳 | fullX o ∈ A} hFullA true]
    simp only [if_pos rfl]
    simp only [if_true]
    rw [witnessPopulationMeasure_setIntegral_fullX true
      (hpmeas n) (hp n) (e n) (hemeas n) A hA]
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01all n]
  -/

  -- Restored proof of the full source-observation bundle.

  let P := witnessArray μS μT p e hpmeas hemeas
  letI : IsProbabilityMeasure (μS n) := hμS n
  have he01all : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  have he01 : ∀ x, 0 ≤ e n x ∧ e n x ≤ 1 := fun x =>
    he01all n x
  have hAssigned : IsProbabilityMeasure (P.assignedSourceLaw n) := by
    change IsProbabilityMeasure (witnessAssignedMeasure (μS n) (p n) (e n))
    exact witnessAssignedMeasure_probability (hpmeas n) (hemeas n)
      (hp n) he01
  letI : IsProbabilityMeasure (P.assignedSourceLaw n) := hAssigned
  have hObs : IsProbabilityMeasure (sourceObsLaw P n) := by
    unfold sourceObsLaw
    exact Measure.isProbabilityMeasure_map measurable_observeSource.aemeasurable
  refine ⟨hAssigned, hObs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hYset : MeasurableSet {o : SourceObs 𝒳 |
        o.2.2.2 ∈ Set.Icc (0 : ℝ) 1} :=
      measurableSet_Icc.preimage
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
    unfold sourceObsLaw
    rw [ae_map_iff measurable_observeSource.aemeasurable hYset]
    filter_upwards [witnessAssignedMeasure_ae_good
      (μS := μS n) (p := p n) (e := e n)
      (hpmeas n) (hemeas n) (hp n) he01] with q hq
    rcases hq.2.1 with hy | hy
    · cases q.2 <;> cases fullD0 q.1 <;> cases fullD1 q.1 <;>
        simp [observeSource, potentialOutcome, potentialReceipt, hy, hq.1] <;>
        (constructor <;> split_ifs <;> norm_num)
    · cases q.2 <;> cases fullD0 q.1 <;> cases fullD1 q.1 <;>
        simp [observeSource, potentialOutcome, potentialReceipt, hy, hq.1] <;>
        (constructor <;> split_ifs <;> norm_num)
  · exact witnessArray_assigned_map_fst μS μT p e hpmeas hemeas
      hμS hμT hp he01all n
  · intro A hA
    have hFullA : MeasurableSet {o : FullData 𝒳 | fullX o ∈ A} :=
      hA.preimage measurable_fullX
    have hEvent : MeasurableSet {o : SourceObs 𝒳 |
        o.1 ∈ A ∧ o.2.1 = true} :=
      (hA.preimage measurable_fst).inter
        (measurableSet_eq_fun
          (measurable_fst.comp measurable_snd) measurable_const)
    unfold sourceObsLaw
    rw [Measure.map_apply measurable_observeSource hEvent]
    change (witnessAssignedMeasure (μS n) (p n) (e n)
      {q | q.1 ∈ {o : FullData 𝒳 | fullX o ∈ A} ∧ q.2 = true}).toReal =
        ∫ x in A, e n x ∂sourceXLaw P n
    rw [witnessAssignedMeasure_event (hpmeas n) (hemeas n)
      (hp n) he01 {o : FullData 𝒳 | fullX o ∈ A} hFullA true]
    simp only [if_pos rfl]
    simp only [if_true]
    rw [witnessPopulationMeasure_setIntegral_fullX true
      (hpmeas n) (hp n) (e n) (hemeas n) A hA]
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01all n]
  · intro A hA
    have hSourceSet : MeasurableSet {o : SourceObs 𝒳 | o.1 ∈ A} :=
      hA.preimage measurable_fst
    rw [← integral_indicator hSourceSet]
    unfold sourceObsLaw
    rw [integral_map measurable_observeSource.aemeasurable <| by
      have hs : Measurable (fun o : SourceObs 𝒳 =>
          instrumentScore P n o * o.2.2.2) := by
        have hz : Measurable (fun o : SourceObs 𝒳 => o.2.1) :=
          measurable_fst.comp measurable_snd
        have hex : Measurable (fun o : SourceObs 𝒳 => e n o.1) :=
          (hemeas n).comp measurable_fst
        have hscore : Measurable (fun o : SourceObs 𝒳 =>
            if o.2.1 then 1 / e n o.1 else -1 / (1 - e n o.1)) :=
          Measurable.ite (measurableSet_eq_fun hz measurable_const)
            (measurable_const.div hex)
            (measurable_const.div (measurable_const.sub hex))
        exact hscore.mul
          (measurable_snd.comp (measurable_snd.comp measurable_snd))
      exact (hs.indicator hSourceSet).aestronglyMeasurable]
    have hcomp : (fun q : AssignedFullData 𝒳 =>
        {o : SourceObs 𝒳 | o.1 ∈ A}.indicator
          (fun o => instrumentScore P n o * o.2.2.2) (observeSource q)) =
        fun q => {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
          (fun q => witnessInstrumentScore (e n) q *
            derivedAssignmentOutcome q.1 q.2) q := by
      funext q
      rfl
    rw [hcomp]
    have hAssignedSet :
        MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
      hA.preimage (measurable_fullX.comp measurable_fst)
    change ∫ q, {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
        (fun q => witnessInstrumentScore (e n) q *
          derivedAssignmentOutcome q.1 q.2) q
        ∂witnessAssignedMeasure (μS n) (p n) (e n) =
      ∫ x in A, p n x / 2 ∂sourceXLaw P n
    rw [integral_indicator hAssignedSet]
    change ∫ q in {q | fullX q.1 ∈ A},
        witnessInstrumentScore (e n) q *
          derivedAssignmentOutcome q.1 q.2
        ∂witnessAssignedMeasure (μS n) (p n) (e n) =
      ∫ x in A, p n x / 2 ∂sourceXLaw P n
    rw [witnessAssignedMeasure_score_outcome_integral
      (hpmeas n) (hemeas n) (hp n) hepsilon (he n) A hA]
    rw [witnessPopulationMeasure_outcome_integral true
      (hpmeas n) (hp n) A hA]
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01all n]
  · filter_upwards with x
    change -1 ≤ p n x / 2 ∧ p n x / 2 ≤ 1
    constructor <;> nlinarith [(hp n x).1, (hp n x).2]
  · intro A hA
    have hSourceSet : MeasurableSet {o : SourceObs 𝒳 | o.1 ∈ A} :=
      hA.preimage measurable_fst
    rw [← integral_indicator hSourceSet]
    unfold sourceObsLaw
    rw [integral_map measurable_observeSource.aemeasurable <| by
      have hs : Measurable (fun o : SourceObs 𝒳 =>
          instrumentScore P n o * boolReal o.2.2.1) := by
        have hz : Measurable (fun o : SourceObs 𝒳 => o.2.1) :=
          measurable_fst.comp measurable_snd
        have hex : Measurable (fun o : SourceObs 𝒳 => e n o.1) :=
          (hemeas n).comp measurable_fst
        have hscore : Measurable (fun o : SourceObs 𝒳 =>
            if o.2.1 then 1 / e n o.1 else -1 / (1 - e n o.1)) :=
          Measurable.ite (measurableSet_eq_fun hz measurable_const)
            (measurable_const.div hex)
            (measurable_const.div (measurable_const.sub hex))
        have hd : Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
          unfold boolReal
          exact Measurable.ite
            (measurableSet_eq_fun
              (measurable_fst.comp
                (measurable_snd.comp measurable_snd)) measurable_const)
            measurable_const measurable_const
        exact hscore.mul hd
      exact (hs.indicator hSourceSet).aestronglyMeasurable]
    have hcomp : (fun q : AssignedFullData 𝒳 =>
        {o : SourceObs 𝒳 | o.1 ∈ A}.indicator
          (fun o => instrumentScore P n o * boolReal o.2.2.1)
          (observeSource q)) =
        fun q => {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
          (fun q => witnessInstrumentScore (e n) q *
            boolReal (potentialReceipt q.1 q.2)) q := by
      funext q
      rfl
    rw [hcomp]
    have hAssignedSet :
        MeasurableSet {q : AssignedFullData 𝒳 | fullX q.1 ∈ A} :=
      hA.preimage (measurable_fullX.comp measurable_fst)
    change ∫ q, {q : AssignedFullData 𝒳 | fullX q.1 ∈ A}.indicator
        (fun q => witnessInstrumentScore (e n) q *
          boolReal (potentialReceipt q.1 q.2)) q
        ∂witnessAssignedMeasure (μS n) (p n) (e n) =
      ∫ x in A, p n x ∂sourceXLaw P n
    rw [integral_indicator hAssignedSet]
    change ∫ q in {q | fullX q.1 ∈ A},
        witnessInstrumentScore (e n) q *
          boolReal (potentialReceipt q.1 q.2)
        ∂witnessAssignedMeasure (μS n) (p n) (e n) =
      ∫ x in A, p n x ∂sourceXLaw P n
    rw [witnessAssignedMeasure_score_receipt_integral
      (hpmeas n) (hemeas n) (hp n) hepsilon (he n) A hA]
    rw [witnessPopulationMeasure_receipt_integral true
      (hpmeas n) (hp n) A hA]
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01all n]
  · filter_upwards with x
    change 0 ≤ p n x ∧ p n x ≤ 1
    exact hp n x


private lemma witnessArray_populationXLaw
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) (s : Bool) :
    populationXLaw (witnessArray μS μT p e hpmeas hemeas) n s =
      if s then μS n else μT n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  unfold populationXLaw
  rw [witnessArray_populationLaw μS μT p e hpmeas hemeas hμS hμT hp n s]
  cases s
  · exact witnessPopulationMeasure_map_fullX false (hpmeas n) (hp n)
  · exact witnessPopulationMeasure_map_fullX true (hpmeas n) (hp n)

private lemma witnessArray_receiptTransport
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    ReceiptTransport (witnessArray μS μT p e hpmeas hemeas) n := by
  constructor
  · intro s A hA
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [witnessArray_populationLaw μS μT p e hpmeas hemeas
      hμS hμT hp n s]
    rw [witnessArray_populationXLaw μS μT p e hpmeas hemeas
      hμS hμT hp n s]
    cases s
    · exact witnessPopulationMeasure_receipt_integral false
        (hpmeas n) (hp n) A hA
    · exact witnessPopulationMeasure_receipt_integral true
        (hpmeas n) (hp n) A hA
  · rfl

private lemma witnessArray_outcomeTransport
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    OutcomeTransport (witnessArray μS μT p e hpmeas hemeas) n := by
  constructor
  · intro s A hA
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [witnessArray_populationLaw μS μT p e hpmeas hemeas
      hμS hμT hp n s]
    rw [witnessArray_populationXLaw μS μT p e hpmeas hemeas
      hμS hμT hp n s]
    cases s
    · exact witnessPopulationMeasure_outcome_integral false
        (hpmeas n) (hp n) A hA
    · exact witnessPopulationMeasure_outcome_integral true
        (hpmeas n) (hp n) A hA
  · rfl

private lemma witnessArray_fullDataSupport
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    FullDataSupport (witnessArray μS μT p e hpmeas hemeas) n := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  have hprob : IsProbabilityMeasure
      ((witnessArray μS μT p e hpmeas hemeas).fullLaw n) := by
    change IsProbabilityMeasure (witnessFullMeasure (μS n) (μT n) (p n))
    exact witnessFullMeasure_probability (hpmeas n) (hp n)
  refine ⟨hprob, ?_⟩
  have hS := witnessPopulationMeasure_ae_good
    (μ := μS n) (p := p n) true (hpmeas n) (hp n)
  have hT := witnessPopulationMeasure_ae_good
    (μ := μT n) (p := p n) false (hpmeas n) (hp n)
  have hgood :
      ∀ᵐ o ∂witnessFullMeasure (μS n) (μT n) (p n), witnessGood o := by
    rw [ae_iff] at hS hT ⊢
    unfold witnessFullMeasure
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hS, hT]
    simp
  filter_upwards [hgood] with o ho
  rcases ho.2.1 with hy | hy
  · simp [ho.1, hy]
  · simp [ho.1, hy]

private lemma witnessArray_populationPresence
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    PopulationPresence (witnessArray μS μT p e hpmeas hemeas) n := by
  intro s
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  change 0 < (witnessFullMeasure (μS n) (μT n) (p n)
    {o | fullS o = s}).toReal
  unfold witnessFullMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [witnessPopulationMeasure_population_mass true s (hpmeas n) (hp n),
    witnessPopulationMeasure_population_mass false s (hpmeas n) (hp n)]
  cases s <;> norm_num

private lemma witnessArray_ivExclusion
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (n : ℕ) :
    IVExclusion (witnessArray μS μT p e hpmeas hemeas) n := by
  intro s z
  rfl

private lemma witnessArray_ivMonotonicity
    (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (n : ℕ) :
    IVMonotonicity (witnessArray μS μT p e hpmeas hemeas) n := by
  intro s
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  rw [witnessArray_populationLaw μS μT p e hpmeas hemeas
    hμS hμT hp n s]
  cases s
  · filter_upwards [witnessPopulationMeasure_ae_good false
      (hpmeas n) (hp n)] with o ho
    exact ho.2.2.1
  · filter_upwards [witnessPopulationMeasure_ae_good true
      (hpmeas n) (hp n)] with o ho
    exact ho.2.2.1

private lemma target_eq_withDensity_of_integral
    {μ ν : Measure 𝒳} {w : 𝒳 → ℝ}
    (hwmeas : Measurable w) (hwint : Integrable w μ)
    (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hν : ∀ A, MeasurableSet A →
      ν A = ENNReal.ofReal (∫ x in A, w x ∂μ)) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
  ext A hA
  rw [withDensity_apply _ hA]
  rw [← ofReal_integral_eq_lintegral_ofReal hwint.integrableOn
    ((ae_restrict_iff' hA).2
      (Filter.Eventually.mono hw0 fun _ hx _ => hx))]
  exact hν A hA

private lemma transportWeight_eq_of_integral
    {μ ν : Measure 𝒳} [IsProbabilityMeasure μ]
    {w : 𝒳 → ℝ}
    (hwmeas : Measurable w) (hwint : Integrable w μ)
    (hw0 : ∀ x, 0 ≤ w x)
    (hν : ∀ A, MeasurableSet A →
      ν A = ENNReal.ofReal (∫ x in A, w x ∂μ)) :
    (fun x => (ν.rnDeriv μ x).toReal) =ᵐ[μ] w := by
  have hEq := target_eq_withDensity_of_integral hwmeas hwint
    (Filter.Eventually.of_forall hw0) hν
  rw [hEq]
  filter_upwards [Measure.rnDeriv_withDensity μ
    (ENNReal.measurable_ofReal.comp hwmeas)] with x hx
  have hx' : (μ.withDensity (fun x => ENNReal.ofReal (w x))).rnDeriv μ x =
      ENNReal.ofReal (w x) := by
    simpa only [Function.comp_apply] using hx
  rw [hx', ENNReal.toReal_ofReal (hw0 x)]

private lemma witnessArray_mem_transportedIVClass
    (μS μT : ℕ → Measure 𝒳) (w p e : ℕ → 𝒳 → ℝ)
    (N k : ℕ → ℕ) (c epsilon : ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hwmeas : ∀ n, Measurable (w n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (he : ∀ n x, epsilon ≤ e n x ∧ e n x ≤ 1 - epsilon)
    (hw : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 2 * (k n : ℝ))
    (hw2 : ∀ n, ∫ x, (w n x) ^ 2 ∂μS n ≤ (k n : ℝ))
    (htransport : ∀ n A, MeasurableSet A →
      μT n A = ENNReal.ofReal (∫ x in A, w n x ∂μS n))
    (hc : 0 < c)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0))
    (hfirst : Tendsto (fun n => ∫ x, w n x * p n x ∂μS n)
      atTop (𝓝 0))
    (n : ℕ) (hpos : 0 < ∫ x, p n x ∂μT n) :
    TransportedIVClass
      (witnessArray μS μT p e hpmeas hemeas) N k c epsilon n := by
  let P := witnessArray μS μT p e hpmeas hemeas
  have he01 : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.1.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.1.le)⟩
  have hwint (m : ℕ) : Integrable (w m) (μS m) := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    refine Integrable.of_bound (hwmeas m).aestronglyMeasurable
      (2 * (k m : ℝ)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hw m x).1]
    exact (hw m x).2
  have hrn (m : ℕ) :
      (fun x => ((μT m).rnDeriv (μS m) x).toReal) =ᵐ[μS m] w m := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    exact transportWeight_eq_of_integral (hwmeas m) (hwint m)
      (fun x => (hw m x).1) (htransport m)
  have hobs :=
    witnessArray_sourceObservation μS μT p e hpmeas hemeas hμS hμT hp
      hepsilon.1 he n
  refine
    { fullDataSupport :=
        witnessArray_fullDataSupport μS μT p e hpmeas hemeas hμS hμT hp n
      populationPresence :=
        witnessArray_populationPresence μS μT p e hpmeas hemeas hμS hμT hp n
      twoSampleArray := ?_
      instrumentOverlap := ?_
      sourceObservation := ⟨hobs.1, hobs.2.2.2.1, hobs.2.2.2.2.1⟩
      ivRandomization :=
        witnessArray_ivRandomization μS μT p e hpmeas hemeas hμS hμT hp
          he01 n
      ivExclusion := witnessArray_ivExclusion μS μT p e hpmeas hemeas n
      ivMonotonicity :=
        witnessArray_ivMonotonicity μS μT p e hpmeas hemeas hμS hμT hp n
      outcomeTransport :=
        witnessArray_outcomeTransport μS μT p e hpmeas hemeas hμS hμT hp n
      receiptTransport :=
        witnessArray_receiptTransport μS μT p e hpmeas hemeas hμS hμT hp n
      targetComplierPositivity := ?_
      transportDomination := ?_
      weightEnvelope := ?_
      weightSecondMoment := ?_
      degradingArray := ?_ }
  · refine ⟨hc, ?_, ?_, hN⟩
    · intro m
      letI : IsProbabilityMeasure
          ((witnessArray μS μT p e hpmeas hemeas).assignedSourceLaw m) := by
        exact witnessAssignedMeasure_probability (hpmeas m) (hemeas m)
          (hp m) (he01 m)
      unfold sourceObsLaw
      exact Measure.isProbabilityMeasure_map
        measurable_observeSource.aemeasurable
    · intro m
      letI : IsProbabilityMeasure (μS m) := hμS m
      letI : IsProbabilityMeasure (μT m) := hμT m
      rw [witnessArray_targetXLaw μS μT p e hpmeas hemeas
        hμS hμT hp m]
      exact hμT m
  · exact ⟨hepsilon.1, hepsilon.2,
      Filter.Eventually.of_forall fun x => he n x⟩
  · unfold TargetComplierPositivity targetComplierShare
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [witnessArray_populationLaw μS μT p e hpmeas hemeas
      hμS hμT hp n false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [witnessPopulationMeasure_complier false (hpmeas n) (hp n)]
    exact hpos
  · letI : IsProbabilityMeasure (μS n) := hμS n
    unfold TransportDomination
    rw [witnessArray_targetXLaw μS μT p e hpmeas hemeas hμS hμT hp n]
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    rw [target_eq_withDensity_of_integral (hwmeas n) (hwint n)
      (Filter.Eventually.of_forall fun x => (hw n x).1) (htransport n)]
    exact withDensity_absolutelyContinuous (μS n)
      (fun x => ENNReal.ofReal (w n x))
  · unfold WeightEnvelope
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    unfold transportWeight
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    rw [witnessArray_targetXLaw μS μT p e hpmeas hemeas hμS hμT hp n]
    filter_upwards [hrn n] with x hx
    rw [hx]
    exact hw n x
  · unfold WeightSecondMoment kishDispersion transportWeight
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    rw [witnessArray_targetXLaw μS μT p e hpmeas hemeas hμS hμT hp n]
    calc
      ∫ x, ((μT n).rnDeriv (μS n) x).toReal ^ 2 ∂μS n =
          ∫ x, (w n x) ^ 2 ∂μS n :=
        integral_congr_ae <| (hrn n).fun_comp fun z => z ^ 2
      _ ≤ (k n : ℝ) := hw2 n
  · refine ⟨hkInf, hkRoot, ?_⟩
    have hfirstEq : (fun m => transportedFirstStage P m) =
          fun m => ∫ x, w m x * p m x ∂μS m := by
      funext m
      letI : IsProbabilityMeasure (μS m) := hμS m
      letI : IsProbabilityMeasure (μT m) := hμT m
      have hobsM := witnessArray_sourceObservation μS μT p e hpmeas hemeas
        hμS hμT hp hepsilon.1 he m
      have henv : WeightEnvelope P k m := by
        unfold WeightEnvelope P transportWeight
        rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
          hμS hμT hp he01 m]
        rw [witnessArray_targetXLaw μS μT p e hpmeas hemeas hμS hμT hp m]
        filter_upwards [hrn m] with x hx
        rw [hx]
        exact hw m x
      rw [transportedFirstStage_eq_weighted_deltaD P k epsilon m
        hobsM ⟨hepsilon.1, hepsilon.2,
          Filter.Eventually.of_forall fun x => he m x⟩ henv]
      change (∫ x, transportWeight P m x * p m x ∂sourceXLaw P m) = _
      rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
        hμS hμT hp he01 m]
      unfold transportWeight P
      rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
        hμS hμT hp he01 m]
      rw [witnessArray_targetXLaw μS μT p e hpmeas hemeas hμS hμT hp m]
      apply integral_congr_ae
      filter_upwards [hrn m] with x hx
      rw [hx]
    change Tendsto (fun m => transportedFirstStage P m) atTop (𝓝 0)
    rw [hfirstEq]
    exact hfirst

private lemma witnessArrayH_mem_transportedIVClass
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (w p e : ℕ → 𝒳 → ℝ)
    (N k : ℕ → ℕ) (c epsilon : ℝ)
    (hpmeas : ∀ n, Measurable (p n)) (hemeas : ∀ n, Measurable (e n))
    (hwmeas : ∀ n, Measurable (w n))
    (hμS : ∀ n, IsProbabilityMeasure (μS n))
    (hμT : ∀ n, IsProbabilityMeasure (μT n))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ n x, 0 ≤ p n x ∧ p n x ≤ 1)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (he : ∀ n x, epsilon ≤ e n x ∧ e n x ≤ 1 - epsilon)
    (hw : ∀ n x, 0 ≤ w n x ∧ w n x ≤ 2 * (k n : ℝ))
    (hw2 : ∀ n, ∫ x, (w n x) ^ 2 ∂μS n ≤ (k n : ℝ))
    (htransport : ∀ n A, MeasurableSet A →
      μT n A = ENNReal.ofReal (∫ x in A, w n x ∂μS n))
    (hc : 0 < c)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0))
    (hfirst : Tendsto (fun n => ∫ x, w n x * p n x ∂μS n)
      atTop (𝓝 0))
    (n : ℕ) (hpos : 0 < ∫ x, p n x ∂μT n) :
    TransportedIVClass
      (witnessArrayH h μS μT p e hpmeas hemeas) N k c epsilon n := by
  let P := witnessArrayH h μS μT p e hpmeas hemeas
  have he01 : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.1.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.1.le)⟩
  have hwint (m : ℕ) : Integrable (w m) (μS m) := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    refine Integrable.of_bound (hwmeas m).aestronglyMeasurable
      (2 * (k m : ℝ)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hw m x).1]
    exact (hw m x).2
  have hrn (m : ℕ) :
      (fun x => ((μT m).rnDeriv (μS m) x).toReal) =ᵐ[μS m] w m := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    exact transportWeight_eq_of_integral (hwmeas m) (hwint m)
      (fun x => (hw m x).1) (htransport m)
  have hobs :=
    witnessArrayH_sourceObservation h μS μT p e hpmeas hemeas
      hμS hμT hh hp hepsilon.1 he n
  refine
    { fullDataSupport :=
        witnessArrayH_fullDataSupport h μS μT p e hpmeas hemeas
          hμS hμT hh hp n
      populationPresence :=
        witnessArrayH_populationPresence h μS μT p e hpmeas hemeas
          hμS hμT hh hp n
      twoSampleArray := ?_
      instrumentOverlap := ?_
      sourceObservation := ⟨hobs.1, hobs.2.2.2.1, hobs.2.2.2.2.1⟩
      ivRandomization :=
        witnessArrayH_ivRandomization h μS μT p e hpmeas hemeas
          hμS hμT hh hp he01 n
      ivExclusion := witnessArrayH_ivExclusion h μS μT p e
        hpmeas hemeas n
      ivMonotonicity :=
        witnessArrayH_ivMonotonicity h μS μT p e hpmeas hemeas
          hμS hμT hh hp n
      outcomeTransport :=
        witnessArrayH_outcomeTransport h μS μT p e hpmeas hemeas
          hμS hμT hh hp n
      receiptTransport :=
        witnessArrayH_receiptTransport h μS μT p e hpmeas hemeas
          hμS hμT hh hp n
      targetComplierPositivity := ?_
      transportDomination := ?_
      weightEnvelope := ?_
      weightSecondMoment := ?_
      degradingArray := ?_ }
  · refine ⟨hc, ?_, ?_, hN⟩
    · intro m
      letI : IsProbabilityMeasure
          ((witnessArrayH h μS μT p e hpmeas hemeas).assignedSourceLaw m) := by
        exact witnessArrayH_assignedSourceLaw_probability h μS μT p e
          hpmeas hemeas hμS hh hp he01 m
      unfold sourceObsLaw
      exact Measure.isProbabilityMeasure_map
        measurable_observeSource.aemeasurable
    · intro m
      letI : IsProbabilityMeasure (μS m) := hμS m
      letI : IsProbabilityMeasure (μT m) := hμT m
      rw [witnessArrayH_targetXLaw h μS μT p e hpmeas hemeas
        hμS hμT hh hp m]
      exact hμT m
  · exact ⟨hepsilon.1, hepsilon.2,
      Filter.Eventually.of_forall fun x => he n x⟩
  · unfold TargetComplierPositivity targetComplierShare
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n false]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [witnessPopulationMeasureH_complier h false hh
      (hpmeas n) (hp n)]
    exact hpos
  · letI : IsProbabilityMeasure (μS n) := hμS n
    unfold TransportDomination
    rw [witnessArrayH_targetXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n]
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01 n]
    rw [target_eq_withDensity_of_integral (hwmeas n) (hwint n)
      (Filter.Eventually.of_forall fun x => (hw n x).1) (htransport n)]
    exact withDensity_absolutelyContinuous (μS n)
      (fun x => ENNReal.ofReal (w n x))
  · unfold WeightEnvelope
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01 n]
    unfold transportWeight
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01 n]
    rw [witnessArrayH_targetXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n]
    filter_upwards [hrn n] with x hx
    rw [hx]
    exact hw n x
  · unfold WeightSecondMoment kishDispersion transportWeight
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp he01 n]
    rw [witnessArrayH_targetXLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n]
    calc
      ∫ x, ((μT n).rnDeriv (μS n) x).toReal ^ 2 ∂μS n =
          ∫ x, (w n x) ^ 2 ∂μS n :=
        integral_congr_ae <| (hrn n).fun_comp fun z => z ^ 2
      _ ≤ (k n : ℝ) := hw2 n
  · refine ⟨hkInf, hkRoot, ?_⟩
    have hfirstEq : (fun m => transportedFirstStage P m) =
          fun m => ∫ x, w m x * p m x ∂μS m := by
      funext m
      letI : IsProbabilityMeasure (μS m) := hμS m
      letI : IsProbabilityMeasure (μT m) := hμT m
      have hobsM := witnessArrayH_sourceObservation h μS μT p e hpmeas hemeas
        hμS hμT hh hp hepsilon.1 he m
      have henv : WeightEnvelope P k m := by
        unfold WeightEnvelope P transportWeight
        rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
          hμS hμT hh hp he01 m]
        rw [witnessArrayH_targetXLaw h μS μT p e hpmeas hemeas
          hμS hμT hh hp m]
        filter_upwards [hrn m] with x hx
        rw [hx]
        exact hw m x
      rw [transportedFirstStage_eq_weighted_deltaD P k epsilon m
        hobsM ⟨hepsilon.1, hepsilon.2,
          Filter.Eventually.of_forall fun x => he m x⟩ henv]
      change (∫ x, transportWeight P m x * p m x ∂sourceXLaw P m) = _
      rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
        hμS hμT hh hp he01 m]
      unfold transportWeight P
      rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
        hμS hμT hh hp he01 m]
      rw [witnessArrayH_targetXLaw h μS μT p e hpmeas hemeas
        hμS hμT hh hp m]
      apply integral_congr_ae
      filter_upwards [hrn m] with x hx
      rw [hx]
    change Tendsto (fun m => transportedFirstStage P m) atTop (𝓝 0)
    rw [hfirstEq]
    exact hfirst

/-- Geometry-side Kish dispersion. -/
noncomputable def geometryKish (g : Geometry 𝒳) (n : ℕ) : ℝ :=
  ∫ x, (g.weight n x) ^ 2 ∂g.sourceX n

/-- First-stage value displayed by the fixed-strength construction. -/
noncomputable def geometryMu (g : Geometry 𝒳) (t0 : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (t0 * geometryKish g n / (n : ℝ))

/-- Compliance probability supplied by the geometry handle. -/
noncomputable def geometryCompliance (g : Geometry 𝒳) (t0 : ℝ)
    (n : ℕ) : 𝒳 → ℝ :=
  fun x => geometryMu g t0 n * g.weight n x / geometryKish g n

private lemma geometryKish_pos
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon : ℝ)
    (hg : AdmissibleGeometry g k epsilon) (n : ℕ) :
    0 < geometryKish g n := by
  letI : IsProbabilityMeasure (g.sourceX n) := hg.1 n
  have hw2int : Integrable (fun x => (g.weight n x) ^ 2) (g.sourceX n) := by
    refine Integrable.of_bound
      ((g.weight_measurable n).pow_const 2).aestronglyMeasurable
      ((2 * (k n : ℝ)) ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (hg.2.2.2.2.2.1 n x).1 (by positivity)).2
      (hg.2.2.2.2.2.1 n x).2
  have hnonneg : 0 ≤ geometryKish g n := by
    exact integral_nonneg fun x => sq_nonneg (g.weight n x)
  refine hnonneg.lt_of_ne ?_
  intro hzero
  have hsquareZero :
      (fun x => (g.weight n x) ^ 2) =ᵐ[g.sourceX n] 0 := by
    exact (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg (g.weight n x)) hw2int).mp hzero.symm
  have hweightZero : g.weight n =ᵐ[g.sourceX n] 0 := by
    filter_upwards [hsquareZero] with x hx
    simpa using (sq_eq_zero_iff.mp hx)
  have := integral_congr_ae hweightZero
  rw [hg.2.2.2.2.2.2.1 n] at this
  simp at this

private lemma one_le_geometryKish
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon : ℝ)
    (hg : AdmissibleGeometry g k epsilon) (n : ℕ) :
    1 ≤ geometryKish g n := by
  letI : IsProbabilityMeasure (g.sourceX n) := hg.1 n
  have hwint : Integrable (g.weight n) (g.sourceX n) := by
    refine Integrable.of_bound (g.weight_measurable n).aestronglyMeasurable
      (2 * (k n : ℝ)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg.2.2.2.2.2.1 n x).1]
    exact (hg.2.2.2.2.2.1 n x).2
  have hw2int : Integrable (fun x => (g.weight n x) ^ 2) (g.sourceX n) := by
    refine Integrable.of_bound
      ((g.weight_measurable n).pow_const 2).aestronglyMeasurable
      ((2 * (k n : ℝ)) ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (hg.2.2.2.2.2.1 n x).1 (by positivity)).2
      (hg.2.2.2.2.2.1 n x).2
  have hvar : 0 ≤ ∫ x, (g.weight n x - 1) ^ 2 ∂g.sourceX n :=
    integral_nonneg fun x => sq_nonneg (g.weight n x - 1)
  have hrewrite :
      (∫ x, (g.weight n x - 1) ^ 2 ∂g.sourceX n) =
        geometryKish g n - 1 := by
    have htwo : Integrable (fun x => 2 * g.weight n x) (g.sourceX n) :=
      hwint.const_mul 2
    rw [show (fun x => (g.weight n x - 1) ^ 2) =
        fun x => (g.weight n x) ^ 2 - 2 * g.weight n x + 1 by
          funext x
          ring]
    change (∫ x, ((fun y => (g.weight n y) ^ 2) -
      (fun y => 2 * g.weight n y)) x + (fun _ => (1 : ℝ)) x
        ∂g.sourceX n) = _
    rw [integral_add (hw2int.sub htwo) (integrable_const 1)]
    change (∫ x, (g.weight n x) ^ 2 - 2 * g.weight n x
      ∂g.sourceX n) + (∫ _x, (1 : ℝ) ∂g.sourceX n) = _
    rw [integral_sub hw2int htwo, integral_const_mul, integral_const,
      probReal_univ, geometryKish, hg.2.2.2.2.2.2.1 n]
    simp only [one_smul]
    ring
  rw [hrewrite] at hvar
  linarith

private lemma geometryCompliance_measurable
    (g : Geometry 𝒳) (t0 : ℝ) (n : ℕ) :
    Measurable (geometryCompliance g t0 n) := by
  exact ((g.weight_measurable n).const_mul _).div_const _

private lemma geometry_firstStage
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon t0 : ℝ)
    (hg : AdmissibleGeometry g k epsilon) (n : ℕ) :
    (∫ x, g.weight n x * geometryCompliance g t0 n x ∂g.sourceX n) =
      geometryMu g t0 n := by
  have hkish : geometryKish g n ≠ 0 :=
    ne_of_gt (geometryKish_pos g k epsilon hg n)
  calc
    (∫ x, g.weight n x * geometryCompliance g t0 n x ∂g.sourceX n) =
        ∫ x, (geometryMu g t0 n / geometryKish g n) *
          (g.weight n x) ^ 2 ∂g.sourceX n := by
            apply integral_congr_ae
            filter_upwards with x
            simp only [geometryCompliance]
            ring
    _ = (geometryMu g t0 n / geometryKish g n) *
          geometryKish g n := by
            rw [integral_const_mul, geometryKish]
    _ = geometryMu g t0 n := by field_simp

private lemma geometry_strength
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon t0 : ℝ)
    (ht0 : 0 < t0) (hg : AdmissibleGeometry g k epsilon)
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * geometryMu g t0 n ^ 2 / geometryKish g n = t0 := by
  have hkish := geometryKish_pos g k epsilon hg n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [geometryMu, Real.sq_sqrt (div_nonneg
    (mul_nonneg ht0.le hkish.le) hnreal.le)]
  field_simp

private lemma geometryCompliance_sq_integral
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon t0 : ℝ)
    (hg : AdmissibleGeometry g k epsilon) (n : ℕ) :
    ∫ x, geometryCompliance g t0 n x ^ 2 ∂g.sourceX n =
      geometryMu g t0 n ^ 2 / geometryKish g n := by
  have hkish : geometryKish g n ≠ 0 :=
    ne_of_gt (geometryKish_pos g k epsilon hg n)
  calc
    ∫ x, geometryCompliance g t0 n x ^ 2 ∂g.sourceX n =
        ∫ x, (geometryMu g t0 n ^ 2 / geometryKish g n ^ 2) *
          g.weight n x ^ 2 ∂g.sourceX n := by
      apply integral_congr_ae
      filter_upwards with x
      unfold geometryCompliance
      field_simp [hkish]
    _ = (geometryMu g t0 n ^ 2 / geometryKish g n ^ 2) *
        geometryKish g n := by
      rw [integral_const_mul, geometryKish]
    _ = geometryMu g t0 n ^ 2 / geometryKish g n := by
      field_simp [hkish]

private lemma geometryMu_tendsto_zero
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon t0 : ℝ)
    (ht0 : 0 < t0) (hg : AdmissibleGeometry g k epsilon)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0)) :
    Tendsto (geometryMu g t0) atTop (𝓝 0) := by
  have hsqrtTop :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinvSqrt :
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  have hkn : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    have hEq : (fun n : ℕ => (k n : ℝ) / (n : ℝ)) =
        fun n => ((k n : ℝ) / Real.sqrt n) * (Real.sqrt n)⁻¹ := by
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        field_simp [hs, Real.sq_sqrt (Nat.cast_nonneg n)]
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [hEq]
    simpa using hkRoot.mul hinvSqrt
  have hupper :
      Tendsto (fun n : ℕ => Real.sqrt (t0 * ((k n : ℝ) / (n : ℝ))))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hkn).sqrt
  refine squeeze_zero' (Filter.Eventually.of_forall fun n =>
    Real.sqrt_nonneg _) (Filter.Eventually.of_forall fun n => ?_) hupper
  ·
    rw [geometryMu]
    apply Real.sqrt_le_sqrt
    by_cases hn : n = 0
    · simp [hn]
    · rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ ht0.le
      exact div_le_div_of_nonneg_right
        (hg.2.2.2.2.2.2.2.1 n) (Nat.cast_nonneg n)

private lemma geometryCompliance_eventually_valid
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon t0 : ℝ)
    (ht0 : 0 < t0) (hg : AdmissibleGeometry g k epsilon)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ x,
      0 ≤ geometryCompliance g t0 n x ∧
        geometryCompliance g t0 n x ≤ 1 := by
  have hthreshold : 0 < (2 * Real.sqrt t0)⁻¹ := by positivity
  have hsmall :
      ∀ᶠ n in atTop,
        (k n : ℝ) / Real.sqrt n < (2 * Real.sqrt t0)⁻¹ :=
    (tendsto_order.1 hkRoot).2 _ hthreshold
  filter_upwards [hsmall, eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hnsmall hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
  have hkish := geometryKish_pos g k epsilon hg n
  have hsqrtK : 0 < Real.sqrt (geometryKish g n) :=
    Real.sqrt_pos.2 hkish
  have hsqrtK1 : 1 ≤ Real.sqrt (geometryKish g n) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (one_le_geometryKish g k epsilon hg n)
  have hpform (x : 𝒳) :
      geometryCompliance g t0 n x =
      Real.sqrt t0 * g.weight n x /
          (Real.sqrt (n : ℝ) * Real.sqrt (geometryKish g n)) := by
    rw [geometryCompliance, geometryMu,
      Real.sqrt_div (mul_nonneg ht0.le hkish.le),
      Real.sqrt_mul ht0.le]
    field_simp
    rw [Real.sq_sqrt hkish.le]
    ring
  intro x
  rw [hpform]
  constructor
  · exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (hg.2.2.2.2.2.1 n x).1)
      (mul_nonneg hsqrtN.le hsqrtK.le)
  · calc
      Real.sqrt t0 * g.weight n x /
            (Real.sqrt (n : ℝ) * Real.sqrt (geometryKish g n))
          ≤ Real.sqrt t0 * (2 * (k n : ℝ)) /
            (Real.sqrt (n : ℝ) * Real.sqrt (geometryKish g n)) := by
              gcongr
              exact (hg.2.2.2.2.2.1 n x).2
      _ ≤ Real.sqrt t0 * (2 * (k n : ℝ)) / Real.sqrt (n : ℝ) := by
              apply div_le_div_of_nonneg_left
              · positivity
              · exact hsqrtN
              · simpa using mul_le_mul_of_nonneg_left hsqrtK1 hsqrtN.le
      _ ≤ 1 := by
              apply (div_le_iff₀ hsqrtN).2
              have hden : 0 < 2 * Real.sqrt t0 := by positivity
              rw [inv_eq_one_div] at hnsmall
              have hcross :=
                (div_lt_div_iff₀ hsqrtN hden).mp
                  hnsmall
              nlinarith

/-- Potential coordinates `(D(0),D(1),Y(0),Y(1))` conditional on `X`. -/
abbrev PotentialCoordinates := Bool × Bool × ℝ × ℝ

/-- Collects a unit's two potential treatment receipts and two potential outcomes into its potential-coordinate vector. -/
def potentialCoordinates (o : FullData 𝒳) : PotentialCoordinates :=
  (fullD0 o, fullD1 o, fullY0 o, fullY1 o)

private lemma measurable_potentialCoordinates :
    Measurable (potentialCoordinates : FullData 𝒳 → PotentialCoordinates) := by
  unfold potentialCoordinates fullD0 fullD1 fullY0 fullY1
  fun_prop

private lemma witnessPotentialKernelH_coordinates
    (h : ℝ) (s t : Bool) (p : 𝒳 → ℝ) (x : 𝒳) :
    (witnessPotentialKernelH h s p x).map potentialCoordinates =
      (witnessPotentialKernelH h t p x).map potentialCoordinates := by
  unfold witnessPotentialKernelH
  simp_rw [witnessCoin_bind, witnessCoin_map]
  simp only [Measure.map_add _ _ measurable_potentialCoordinates,
    Measure.map_smul, Measure.map_dirac' measurable_potentialCoordinates,
    potentialCoordinates, witnessFullPack, fullD0, fullD1, fullY0, fullY1]

/-- Geometry covariate marginal for the selected population. -/
def geometryPopulationX (g : Geometry 𝒳) (n : ℕ) (s : Bool) : Measure 𝒳 :=
  if s then g.sourceX n else g.targetX n

private lemma witnessArrayH_equalConditionalKernel
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ m, Measurable (p m)) (hemeas : ∀ m, Measurable (e m))
    (hμS : ∀ m, IsProbabilityMeasure (μS m))
    (hμT : ∀ m, IsProbabilityMeasure (μT m))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1)
    (g : Geometry 𝒳) (n : ℕ)
    (hsource : μS n = g.sourceX n) (htarget : μT n = g.targetX n) :
    ∃ K : 𝒳 → Measure PotentialCoordinates,
      (∀ x, IsProbabilityMeasure (K x)) ∧
      (∀ B, MeasurableSet B → Measurable fun x => K x B) ∧
      ∀ s A B, MeasurableSet A → MeasurableSet B →
        populationLaw
            (witnessArrayH h μS μT p e hpmeas hemeas) n s
            {o | fullX o ∈ A ∧ potentialCoordinates o ∈ B} =
          ∫⁻ x in A, K x B ∂geometryPopulationX g n s := by
  let K : 𝒳 → Measure PotentialCoordinates := fun x =>
    (witnessPotentialKernelH h true (p n) x).map potentialCoordinates
  refine ⟨K, ?_, ?_, ?_⟩
  · intro x
    letI : IsProbabilityMeasure
        (witnessPotentialKernelH h true (p n) x) :=
      witnessPotentialKernelH_probability h true hh
        (hp n x).1 (hp n x).2
    exact Measure.isProbabilityMeasure_map
      (μ := witnessPotentialKernelH h true (p n) x)
      measurable_potentialCoordinates.aemeasurable
  · intro B hB
    unfold K
    simp_rw [Measure.map_apply measurable_potentialCoordinates hB]
    exact (Measure.measurable_coe
      (hB.preimage measurable_potentialCoordinates)).comp
        (measurable_witnessPotentialKernelH h true (hpmeas n))
  · intro s A B hA hB
    have hC : MeasurableSet
        (potentialCoordinates ⁻¹' B : Set (FullData 𝒳)) :=
      hB.preimage measurable_potentialCoordinates
    have hEvent :
        MeasurableSet {o : FullData 𝒳 |
          fullX o ∈ A ∧ potentialCoordinates o ∈ B} :=
      (hA.preimage measurable_fullX).inter hC
    have hEvent' :
        MeasurableSet {o : FullData 𝒳 |
          fullX o ∈ A ∧ o ∈ potentialCoordinates ⁻¹' B} :=
      (hA.preimage measurable_fullX).inter hC
    rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hh hp n s]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      unfold witnessPopulationMeasureH
      change (μT n).bind (witnessPotentialKernelH h false (p n))
          {o | fullX o ∈ A ∧
            o ∈ (potentialCoordinates ⁻¹' B)} =
        ∫⁻ x in A, K x B ∂geometryPopulationX g n false
      rw [Measure.bind_apply hEvent'
        (measurable_witnessPotentialKernelH h false
          (hpmeas n)).aemeasurable]
      simp_rw [witnessPotentialKernelH_inter_fullX h false hh
        (hp n _).1 (hp n _).2 A hA
        (potentialCoordinates ⁻¹' B) hC]
      rw [lintegral_indicator hA]
      simp only [geometryPopulationX, Bool.false_eq_true, ↓reduceIte]
      rw [← htarget]
      apply lintegral_congr
      intro x
      change (witnessPotentialKernelH h false (p n) x)
          (potentialCoordinates ⁻¹' B) = K x B
      rw [← Measure.map_apply measurable_potentialCoordinates hB]
      exact congrArg (fun ν : Measure PotentialCoordinates => ν B)
        (witnessPotentialKernelH_coordinates h false true (p n) x)
    · simp only [↓reduceIte]
      unfold witnessPopulationMeasureH
      change (μS n).bind (witnessPotentialKernelH h true (p n))
          {o | fullX o ∈ A ∧
            o ∈ (potentialCoordinates ⁻¹' B)} =
        ∫⁻ x in A, K x B ∂geometryPopulationX g n true
      rw [Measure.bind_apply hEvent'
        (measurable_witnessPotentialKernelH h true
          (hpmeas n)).aemeasurable]
      simp_rw [witnessPotentialKernelH_inter_fullX h true hh
        (hp n _).1 (hp n _).2 A hA
        (potentialCoordinates ⁻¹' B) hC]
      rw [lintegral_indicator hA]
      simp only [geometryPopulationX, ↓reduceIte]
      rw [← hsource]
      apply lintegral_congr
      intro x
      change (witnessPotentialKernelH h true (p n) x)
          (potentialCoordinates ⁻¹' B) = K x B
      rw [← Measure.map_apply measurable_potentialCoordinates hB]

private lemma witnessArrayH_targetCACE
    (h : ℝ) (μS μT : ℕ → Measure 𝒳) (p e : ℕ → 𝒳 → ℝ)
    (hpmeas : ∀ m, Measurable (p m)) (hemeas : ∀ m, Measurable (e m))
    (hμS : ∀ m, IsProbabilityMeasure (μS m))
    (hμT : ∀ m, IsProbabilityMeasure (μT m))
    (hh : |h| ≤ 1 / 4)
    (hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1)
    (n : ℕ) (hpos : 0 < ∫ x, p n x ∂μT n) :
    targetCACE (witnessArrayH h μS μT p e hpmeas hemeas) n =
      1 / 2 + h := by
  letI : IsProbabilityMeasure (μS n) := hμS n
  letI : IsProbabilityMeasure (μT n) := hμT n
  rw [targetCACE, targetComplierShare]
  rw [witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
    hμS hμT hh hp n false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [witnessPopulationMeasureH_complier h false hh
    (hpmeas n) (hp n)]
  have hnum :
      ∫ o, (fullY1 o - fullY0 o) *
          (if fullD1 o = true ∧ fullD0 o = false then 1 else 0)
          ∂witnessPopulationMeasureH h false (μT n) (p n) =
        ∫ o, (derivedAssignmentOutcome o true -
          derivedAssignmentOutcome o false)
          ∂witnessPopulationMeasureH h false (μT n) (p n) := by
    apply integral_congr_ae
    filter_upwards [witnessPopulationMeasureH_ae_good
      h false hh (hpmeas n) (hp n)] with o ho
    rw [ho.2.2.2, ho.1]
    by_cases h0 : fullD0 o = false <;>
      by_cases h1 : fullD1 o = true
    · simp [h0, h1, boolReal]
    · simp [h0, h1, boolReal]
    · simp [h0, h1, boolReal]
    · have hmono := ho.2.2.1
      simp [h0, h1, boolReal] at hmono
      norm_num at hmono
  rw [hnum]
  have hout := witnessPopulationMeasureH_outcome_integral
    (μ := μT n) h false hh (hpmeas n) (hp n) Set.univ
      MeasurableSet.univ
  simp only [Set.mem_univ, Set.setOf_true, Measure.restrict_univ] at hout
  rw [hout, integral_mul_const]
  apply (div_eq_iff hpos.ne').2
  ring

/-- The named least-favourable continuum attached to a geometry and strength.
The compliance probability is clamped only to make the array globally valid;
on the eventual geometry range the clamp is inactive. -/
noncomputable def geometryWitnessFamily (g : Geometry 𝒳) (t0 h : ℝ) :
    TransportedArray 𝒳 :=
  witnessArrayH h g.sourceX g.targetX
    (fun m x => min 1 (geometryCompliance g t0 m x)) g.propensity
    (fun m => measurable_const.min (geometryCompliance_measurable g t0 m))
    g.propensity_measurable

/-- The source-observation chi-square divergence between a geometry witness at perturbation level `h` and its zero-perturbation counterpart is bounded by eight times the squared perturbation, scaled by the geometry's signal and inverse Kish dispersion. -/
lemma geometryWitnessFamily_source_chiSq_bound
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon t0 : ℝ)
    (hepsilon : 0 < epsilon) (hg : AdmissibleGeometry g k epsilon)
    (n : ℕ) (h : ℝ) (hh : |h| ≤ 1 / 4)
    (hvalid : ∀ x, 0 ≤ geometryCompliance g t0 n x ∧
      geometryCompliance g t0 n x ≤ 1) :
    Causalean.Stat.chiSqDiv
        (sourceObsLaw (geometryWitnessFamily g t0 h) n)
        (sourceObsLaw (geometryWitnessFamily g t0 0) n) ≤
      8 * geometryMu g t0 n ^ 2 * h ^ 2 / geometryKish g n := by
  let p : ℕ → 𝒳 → ℝ :=
    fun m x => min 1 (geometryCompliance g t0 m x)
  have hpmeas : ∀ m, Measurable (p m) := fun m =>
    measurable_const.min (geometryCompliance_measurable g t0 m)
  have hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1 := by
    intro m x
    have hcomp : 0 ≤ geometryCompliance g t0 m x := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (hg.2.2.2.2.2.1 m x).1)
        (geometryKish_pos g k epsilon hg m).le
    exact ⟨le_min (by norm_num) hcomp, min_le_left _ _⟩
  have he01 : ∀ m x, 0 ≤ g.propensity m x ∧ g.propensity m x ≤ 1 :=
    fun m x => ⟨hepsilon.le.trans (hg.2.2.2.2.1 m x).1,
      (hg.2.2.2.2.1 m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  have hchi :
      Causalean.Stat.chiSqDiv
          (sourceObsLaw (geometryWitnessFamily g t0 h) n)
          (sourceObsLaw (geometryWitnessFamily g t0 0) n) =
        ∫ x, 8 * g.propensity n x * p n x ^ 2 * h ^ 2 /
          (1 + p n x) ∂g.sourceX n := by
    change Causalean.Stat.chiSqDiv
        (sourceObsLaw (witnessArrayH h g.sourceX g.targetX p g.propensity
          hpmeas g.propensity_measurable) n)
        (sourceObsLaw (witnessArrayH 0 g.sourceX g.targetX p g.propensity
          hpmeas g.propensity_measurable) n) = _
    exact witnessArrayH_source_chiSq_eq h g.sourceX g.targetX p g.propensity
      hpmeas g.propensity_measurable hg.1 hh hp he01 n
  rw [hchi]
  let F : 𝒳 → ℝ := fun x =>
    8 * g.propensity n x * p n x ^ 2 * h ^ 2 / (1 + p n x)
  let G : 𝒳 → ℝ := fun x =>
    8 * geometryCompliance g t0 n x ^ 2 * h ^ 2
  letI : IsProbabilityMeasure (g.sourceX n) := hg.1 n
  have hFmeas : Measurable F := by
    dsimp [F]
    exact ((((g.propensity_measurable n).const_mul 8).mul
      ((hpmeas n).pow_const 2)).mul_const (h ^ 2)).div
        (measurable_const.add (hpmeas n))
  have hGmeas : Measurable G := by
    dsimp [G]
    exact (((geometryCompliance_measurable g t0 n).pow_const 2).const_mul 8).mul_const
      (h ^ 2)
  have hFint : Integrable F (g.sourceX n) := by
    refine Integrable.of_bound hFmeas.aestronglyMeasurable (8 * h ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [F]
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (he01 n x).1)
            (sq_nonneg _)) (sq_nonneg _))
        (by linarith [(hp n x).1]))]
    dsimp [F]
    apply (div_le_iff₀ (by linarith [(hp n x).1])).2
    have hpSq : p n x ^ 2 ≤ 1 :=
      by simpa using
        (sq_le_sq₀ (hp n x).1 (by norm_num)).2 (hp n x).2
    have hep : g.propensity n x * p n x ^ 2 ≤ 1 := by
      calc
        g.propensity n x * p n x ^ 2 ≤ 1 * p n x ^ 2 :=
          mul_le_mul_of_nonneg_right (he01 n x).2 (sq_nonneg _)
        _ ≤ 1 := by simpa using hpSq
    have hnum :
        8 * g.propensity n x * p n x ^ 2 * h ^ 2 ≤ 8 * h ^ 2 := by
      calc
        8 * g.propensity n x * p n x ^ 2 * h ^ 2 =
            (8 * h ^ 2) * (g.propensity n x * p n x ^ 2) := by ring
        _ ≤ (8 * h ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hep (by positivity)
        _ = 8 * h ^ 2 := by ring
    nlinarith [mul_nonneg (by positivity : 0 ≤ 8 * h ^ 2) (hp n x).1]
  have hGint : Integrable G (g.sourceX n) := by
    refine Integrable.of_bound hGmeas.aestronglyMeasurable (8 * h ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [G]; positivity)]
    dsimp [G]
    have hcSq : geometryCompliance g t0 n x ^ 2 ≤ 1 :=
      by simpa using
        (sq_le_sq₀ (hvalid x).1 (by norm_num)).2 (hvalid x).2
    exact mul_le_mul_of_nonneg_right
      (by simpa using
        (mul_le_mul_of_nonneg_left hcSq (by norm_num : (0 : ℝ) ≤ 8)))
      (sq_nonneg h)
  change ∫ x, F x ∂g.sourceX n ≤ _
  calc
    ∫ x, F x ∂g.sourceX n ≤ ∫ x, G x ∂g.sourceX n := by
      apply integral_mono hFint hGint
      intro x
      have hpn : p n x = geometryCompliance g t0 n x :=
        min_eq_right (hvalid x).2
      dsimp [F, G]
      rw [hpn]
      apply (div_le_iff₀ (by linarith [(hvalid x).1])).2
      let A : ℝ := 8 * geometryCompliance g t0 n x ^ 2 * h ^ 2
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hnum :
          8 * g.propensity n x * geometryCompliance g t0 n x ^ 2 * h ^ 2 ≤ A := by
        calc
          8 * g.propensity n x * geometryCompliance g t0 n x ^ 2 * h ^ 2 =
              A * g.propensity n x := by dsimp [A]; ring
          _ ≤ A * 1 := mul_le_mul_of_nonneg_left (he01 n x).2 hA
          _ = A := by ring
      change _ ≤ A * (1 + geometryCompliance g t0 n x)
      nlinarith [mul_nonneg hA (hvalid x).1]
    _ = 8 * geometryMu g t0 n ^ 2 * h ^ 2 /
        geometryKish g n := by
      change (∫ x, 8 * geometryCompliance g t0 n x ^ 2 * h ^ 2
        ∂g.sourceX n) = _
      rw [show (fun x => 8 * geometryCompliance g t0 n x ^ 2 * h ^ 2) =
          fun x => (8 * h ^ 2) * geometryCompliance g t0 n x ^ 2 by
        funext x
        ring]
      rw [integral_const_mul,
        geometryCompliance_sq_integral g k epsilon t0 hg n]
      ring

private lemma geometryWitnessFamily_twoSample_chiSq_bound
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (epsilon t0 : ℝ)
    (hepsilon : 0 < epsilon) (ht0 : 0 < t0)
    (hg : AdmissibleGeometry g k epsilon) (n : ℕ) (hn : 0 < n)
    (h : ℝ) (hh : |h| ≤ 1 / 4)
    (hvalid : ∀ x, 0 ≤ geometryCompliance g t0 n x ∧
      geometryCompliance g t0 n x ≤ 1) :
    1 + Causalean.Stat.chiSqDiv
        (twoSampleLaw (geometryWitnessFamily g t0 h) N n)
        (twoSampleLaw (geometryWitnessFamily g t0 0) N n) ≤
      Real.exp (8 * t0 * h ^ 2) := by
  let p : ℕ → 𝒳 → ℝ :=
    fun m x => min 1 (geometryCompliance g t0 m x)
  have hpmeas : ∀ m, Measurable (p m) := fun m =>
    measurable_const.min (geometryCompliance_measurable g t0 m)
  have hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1 := by
    intro m x
    have hcomp : 0 ≤ geometryCompliance g t0 m x := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (hg.2.2.2.2.2.1 m x).1)
        (geometryKish_pos g k epsilon hg m).le
    exact ⟨le_min (by norm_num) hcomp, min_le_left _ _⟩
  have he01 : ∀ m x, 0 ≤ g.propensity m x ∧ g.propensity m x ≤ 1 :=
    fun m x => ⟨hepsilon.le.trans (hg.2.2.2.2.1 m x).1,
      (hg.2.2.2.2.1 m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  let μh := sourceObsLaw (geometryWitnessFamily g t0 h) n
  let μ0 := sourceObsLaw (geometryWitnessFamily g t0 0) n
  let ρ := Measure.pi (fun _ : Fin (N n) => g.targetX n)
  letI : IsProbabilityMeasure μh := by
    change IsProbabilityMeasure
      (sourceObsLaw (witnessArrayH h g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n)
    exact witnessArrayH_sourceObsLaw_probability h g.sourceX g.targetX p
      g.propensity hpmeas g.propensity_measurable hg.1 hh hp he01 n
  letI : IsProbabilityMeasure μ0 := by
    change IsProbabilityMeasure
      (sourceObsLaw (witnessArrayH 0 g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n)
    exact witnessArrayH_sourceObsLaw_probability 0 g.sourceX g.targetX p
      g.propensity hpmeas g.propensity_measurable hg.1 (by norm_num) hp he01 n
  letI : IsProbabilityMeasure (g.targetX n) := hg.2.1 n
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have htarget (a : ℝ) (ha : |a| ≤ 1 / 4) :
      targetXLaw (geometryWitnessFamily g t0 a) n = g.targetX n := by
    change targetXLaw
      (witnessArrayH a g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n = g.targetX n
    exact witnessArrayH_targetXLaw a g.sourceX g.targetX p g.propensity
      hpmeas g.propensity_measurable hg.1 hg.2.1 ha hp n
  obtain ⟨hac, hint⟩ :
      μh ≪ μ0 ∧
        Integrable (fun o => ((μh.rnDeriv μ0 o).toReal - 1) ^ 2) μ0 := by
    change
      sourceObsLaw (witnessArrayH h g.sourceX g.targetX p g.propensity
          hpmeas g.propensity_measurable) n ≪
        sourceObsLaw (witnessArrayH 0 g.sourceX g.targetX p g.propensity
          hpmeas g.propensity_measurable) n ∧ _
    exact witnessArrayH_source_ac_integrable h g.sourceX g.targetX p
      g.propensity hpmeas g.propensity_measurable hg.1 hh hp he01 n
  have hacPi := Causalean.Stat.pi_iid_absolutelyContinuous μh μ0 hac n
  have hintPi := Causalean.Stat.pi_iid_integrable_sq_dev μh μ0 hac hint n
  have hancillary :
      Causalean.Stat.chiSqDiv
          ((Measure.pi fun _ : Fin n => μh).prod ρ)
          ((Measure.pi fun _ : Fin n => μ0).prod ρ) =
        Causalean.Stat.chiSqDiv
          (Measure.pi fun _ : Fin n => μh)
          (Measure.pi fun _ : Fin n => μ0) :=
    Causalean.Stat.chiSqDiv_prod_ancillary _ _ ρ hacPi hintPi
  have htensor :
      1 + Causalean.Stat.chiSqDiv
          (Measure.pi fun _ : Fin n => μh)
          (Measure.pi fun _ : Fin n => μ0) =
        (1 + Causalean.Stat.chiSqDiv μh μ0) ^ n :=
    Causalean.Stat.one_add_chiSqDiv_pi_iid_general μh μ0 hac hint n
  have hsource :
      Causalean.Stat.chiSqDiv μh μ0 ≤
        8 * geometryMu g t0 n ^ 2 * h ^ 2 / geometryKish g n := by
    exact geometryWitnessFamily_source_chiSq_bound g k epsilon t0
      hepsilon hg n h hh hvalid
  have hexponent :
      (n : ℝ) * Causalean.Stat.chiSqDiv μh μ0 ≤ 8 * t0 * h ^ 2 := by
    calc
      (n : ℝ) * Causalean.Stat.chiSqDiv μh μ0 ≤
          (n : ℝ) *
            (8 * geometryMu g t0 n ^ 2 * h ^ 2 / geometryKish g n) :=
        mul_le_mul_of_nonneg_left hsource (Nat.cast_nonneg n)
      _ = 8 * t0 * h ^ 2 := by
        have hs := geometry_strength g k epsilon t0 ht0 hg n hn
        calc
          (n : ℝ) *
                (8 * geometryMu g t0 n ^ 2 * h ^ 2 /
                  geometryKish g n) =
              8 * ((n : ℝ) * geometryMu g t0 n ^ 2 /
                geometryKish g n) * h ^ 2 := by ring
          _ = 8 * t0 * h ^ 2 := by rw [hs]
  change 1 + Causalean.Stat.chiSqDiv
      ((Measure.pi fun _ : Fin n => μh).prod
        (Measure.pi fun _ : Fin (N n) =>
          targetXLaw (geometryWitnessFamily g t0 h) n))
      ((Measure.pi fun _ : Fin n => μ0).prod
        (Measure.pi fun _ : Fin (N n) =>
          targetXLaw (geometryWitnessFamily g t0 0) n)) ≤ _
  rw [htarget h hh, htarget 0 (by norm_num)]
  change 1 + Causalean.Stat.chiSqDiv
      ((Measure.pi fun _ : Fin n => μh).prod ρ)
      ((Measure.pi fun _ : Fin n => μ0).prod ρ) ≤ _
  rw [hancillary, htensor]
  calc
    (1 + Causalean.Stat.chiSqDiv μh μ0) ^ n ≤
        (Real.exp (Causalean.Stat.chiSqDiv μh μ0)) ^ n := by
      gcongr
      · exact add_nonneg zero_le_one Causalean.Stat.chiSqDiv_nonneg
      · simpa [add_comm] using Real.add_one_le_exp
          (Causalean.Stat.chiSqDiv μh μ0)
    _ = Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μh μ0) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (8 * t0 * h ^ 2) := Real.exp_le_exp.mpr hexponent

private lemma geometryWitnessFamily_twoSample_ac_integrable
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (epsilon t0 : ℝ)
    (hepsilon : 0 < epsilon) (hg : AdmissibleGeometry g k epsilon)
    (n : ℕ) (h : ℝ) (hh : |h| ≤ 1 / 4) :
    let Ph := twoSampleLaw (geometryWitnessFamily g t0 h) N n
    let P0 := twoSampleLaw (geometryWitnessFamily g t0 0) N n
    Ph ≪ P0 ∧
      Integrable (fun o => ((Ph.rnDeriv P0 o).toReal - 1) ^ 2) P0 := by
  dsimp only
  let p : ℕ → 𝒳 → ℝ :=
    fun m x => min 1 (geometryCompliance g t0 m x)
  have hpmeas : ∀ m, Measurable (p m) := fun m =>
    measurable_const.min (geometryCompliance_measurable g t0 m)
  have hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1 := by
    intro m x
    have hcomp : 0 ≤ geometryCompliance g t0 m x := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (hg.2.2.2.2.2.1 m x).1)
        (geometryKish_pos g k epsilon hg m).le
    exact ⟨le_min (by norm_num) hcomp, min_le_left _ _⟩
  have he01 : ∀ m x, 0 ≤ g.propensity m x ∧ g.propensity m x ≤ 1 :=
    fun m x => ⟨hepsilon.le.trans (hg.2.2.2.2.1 m x).1,
      (hg.2.2.2.2.1 m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  let μh := sourceObsLaw (geometryWitnessFamily g t0 h) n
  let μ0 := sourceObsLaw (geometryWitnessFamily g t0 0) n
  let μπ := Measure.pi (fun _ : Fin n => μh)
  let μ0π := Measure.pi (fun _ : Fin n => μ0)
  let ρ := Measure.pi (fun _ : Fin (N n) => g.targetX n)
  letI : IsProbabilityMeasure μh := by
    change IsProbabilityMeasure
      (sourceObsLaw (witnessArrayH h g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n)
    exact witnessArrayH_sourceObsLaw_probability h g.sourceX g.targetX p
      g.propensity hpmeas g.propensity_measurable hg.1 hh hp he01 n
  letI : IsProbabilityMeasure μ0 := by
    change IsProbabilityMeasure
      (sourceObsLaw (witnessArrayH 0 g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n)
    exact witnessArrayH_sourceObsLaw_probability 0 g.sourceX g.targetX p
      g.propensity hpmeas g.propensity_measurable hg.1 (by norm_num) hp he01 n
  letI : IsProbabilityMeasure (g.targetX n) := hg.2.1 n
  letI : IsProbabilityMeasure μπ := by dsimp [μπ]; infer_instance
  letI : IsProbabilityMeasure μ0π := by dsimp [μ0π]; infer_instance
  letI : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have htarget (a : ℝ) (ha : |a| ≤ 1 / 4) :
      targetXLaw (geometryWitnessFamily g t0 a) n = g.targetX n := by
    change targetXLaw
      (witnessArrayH a g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n = g.targetX n
    exact witnessArrayH_targetXLaw a g.sourceX g.targetX p g.propensity
      hpmeas g.propensity_measurable hg.1 hg.2.1 ha hp n
  obtain ⟨hac, hint⟩ :
      μh ≪ μ0 ∧
        Integrable (fun o => ((μh.rnDeriv μ0 o).toReal - 1) ^ 2) μ0 := by
    change
      sourceObsLaw (witnessArrayH h g.sourceX g.targetX p g.propensity
          hpmeas g.propensity_measurable) n ≪
        sourceObsLaw (witnessArrayH 0 g.sourceX g.targetX p g.propensity
          hpmeas g.propensity_measurable) n ∧ _
    exact witnessArrayH_source_ac_integrable h g.sourceX g.targetX p
      g.propensity hpmeas g.propensity_measurable hg.1 hh hp he01 n
  have hacPi : μπ ≪ μ0π := by
    exact Causalean.Stat.pi_iid_absolutelyContinuous μh μ0 hac n
  have hintPi :
      Integrable (fun o => ((μπ.rnDeriv μ0π o).toReal - 1) ^ 2) μ0π := by
    exact Causalean.Stat.pi_iid_integrable_sq_dev μh μ0 hac hint n
  have hacFull : μπ.prod ρ ≪ μ0π.prod ρ :=
    hacPi.prod (Measure.AbsolutelyContinuous.refl ρ)
  have hrnProd :
      (μπ.prod ρ).rnDeriv (μ0π.prod ρ) =ᵐ[μ0π.prod ρ]
        fun z => μπ.rnDeriv μ0π z.1 * ρ.rnDeriv ρ z.2 :=
    Causalean.Stat.rnDeriv_prod_eq μπ μ0π ρ ρ hacPi
      (Measure.AbsolutelyContinuous.refl ρ)
  have hrhoProd :
      (fun z : (Fin n → SourceObs 𝒳) × (Fin (N n) → 𝒳) =>
        (ρ.rnDeriv ρ z.2).toReal) =ᵐ[μ0π.prod ρ] (fun _ => (1 : ℝ)) := by
    refine (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun
        ((Measure.measurable_rnDeriv ρ ρ).ennreal_toReal.comp measurable_snd)
        measurable_const)).2 ?_
    filter_upwards with x
    filter_upwards [ρ.rnDeriv_self] with y hy
    simp [hy]
  have hfullEq :
      (fun z => (((μπ.prod ρ).rnDeriv (μ0π.prod ρ) z).toReal - 1) ^ 2)
        =ᵐ[μ0π.prod ρ]
      fun z => ((μπ.rnDeriv μ0π z.1).toReal - 1) ^ 2 := by
    filter_upwards [hrnProd, hrhoProd] with z hz hρ
    rw [hz, ENNReal.toReal_mul, hρ, mul_one]
  have hintFull :
      Integrable
        (fun z => (((μπ.prod ρ).rnDeriv (μ0π.prod ρ) z).toReal - 1) ^ 2)
        (μ0π.prod ρ) :=
    (hintPi.comp_fst ρ).congr hfullEq.symm
  change
    twoSampleLaw (geometryWitnessFamily g t0 h) N n ≪
      twoSampleLaw (geometryWitnessFamily g t0 0) N n ∧ _
  unfold twoSampleLaw
  rw [htarget h hh, htarget 0 (by norm_num)]
  change μπ.prod ρ ≪ μ0π.prod ρ ∧
    Integrable
      (fun z => (((μπ.prod ρ).rnDeriv (μ0π.prod ρ) z).toReal - 1) ^ 2)
      (μ0π.prod ρ)
  exact ⟨hacFull, hintFull⟩

private lemma geometryWitnessFamily_twoSample_probability
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (epsilon t0 : ℝ)
    (hepsilon : 0 < epsilon) (hg : AdmissibleGeometry g k epsilon)
    (n : ℕ) (h : ℝ) (hh : |h| ≤ 1 / 4) :
    IsProbabilityMeasure
      (twoSampleLaw (geometryWitnessFamily g t0 h) N n) := by
  let p : ℕ → 𝒳 → ℝ :=
    fun m x => min 1 (geometryCompliance g t0 m x)
  have hpmeas : ∀ m, Measurable (p m) := fun m =>
    measurable_const.min (geometryCompliance_measurable g t0 m)
  have hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1 := by
    intro m x
    have hcomp : 0 ≤ geometryCompliance g t0 m x := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (hg.2.2.2.2.2.1 m x).1)
        (geometryKish_pos g k epsilon hg m).le
    exact ⟨le_min (by norm_num) hcomp, min_le_left _ _⟩
  have he01 : ∀ m x, 0 ≤ g.propensity m x ∧ g.propensity m x ≤ 1 :=
    fun m x => ⟨hepsilon.le.trans (hg.2.2.2.2.1 m x).1,
      (hg.2.2.2.2.1 m x).2.trans (sub_le_self 1 hepsilon.le)⟩
  letI : IsProbabilityMeasure
      (sourceObsLaw (geometryWitnessFamily g t0 h) n) := by
    change IsProbabilityMeasure
      (sourceObsLaw (witnessArrayH h g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n)
    exact witnessArrayH_sourceObsLaw_probability h g.sourceX g.targetX p
      g.propensity hpmeas g.propensity_measurable hg.1 hh hp he01 n
  letI : IsProbabilityMeasure (g.targetX n) := hg.2.1 n
  have htarget :
      targetXLaw (geometryWitnessFamily g t0 h) n = g.targetX n := by
    change targetXLaw
      (witnessArrayH h g.sourceX g.targetX p g.propensity
        hpmeas g.propensity_measurable) n = g.targetX n
    exact witnessArrayH_targetXLaw h g.sourceX g.targetX p g.propensity
      hpmeas g.propensity_measurable hg.1 hg.2.1 hh hp n
  unfold twoSampleLaw
  rw [htarget]
  infer_instance

private lemma geometryWitnessFamily_twoSample_tv_bound
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (epsilon alpha t0 rho : ℝ)
    (hepsilon : 0 < epsilon) (halpha : 0 < alpha ∧ alpha < 1)
    (ht0 : 0 < t0) (hrho : rho = (1 - alpha) / 8)
    (hg : AdmissibleGeometry g k epsilon) (n : ℕ) (hn : 0 < n)
    (h : ℝ)
    (hh : |h| ≤ min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ)))
    (hvalid : ∀ x, 0 ≤ geometryCompliance g t0 n x ∧
      geometryCompliance g t0 n x ≤ 1) :
    Causalean.Stat.tvDist
        (twoSampleLaw (geometryWitnessFamily g t0 h) N n)
        (twoSampleLaw (geometryWitnessFamily g t0 0) N n) ≤
      2 * rho := by
  have hhQuarter : |h| ≤ 1 / 4 := hh.trans (min_le_left _ _)
  have hhScale : |h| ≤ rho * t0 ^ (-1 / 2 : ℝ) :=
    hh.trans (min_le_right _ _)
  have hrhoPos : 0 < rho := by rw [hrho]; linarith
  have hrhoLe : rho ≤ 1 / 8 := by rw [hrho]; linarith
  have hrpow :
      t0 * (t0 ^ (-1 / 2 : ℝ)) ^ 2 = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_mul ht0.le]
    norm_num [Real.rpow_neg_one, ht0.ne']
  have hscaleSq :
      h ^ 2 ≤ (rho * t0 ^ (-1 / 2 : ℝ)) ^ 2 := by
    have hright : 0 ≤ rho * t0 ^ (-1 / 2 : ℝ) :=
      mul_nonneg hrhoPos.le (Real.rpow_nonneg ht0.le _)
    have hs := (sq_le_sq₀ (abs_nonneg h) hright).2 hhScale
    simpa [sq_abs] using hs
  have ht0hSq : t0 * h ^ 2 ≤ rho ^ 2 := by
    calc
      t0 * h ^ 2 ≤
          t0 * (rho * t0 ^ (-1 / 2 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hscaleSq ht0.le
      _ = rho ^ 2 * (t0 * (t0 ^ (-1 / 2 : ℝ)) ^ 2) := by ring
      _ = rho ^ 2 := by rw [hrpow, mul_one]
  let v := 8 * t0 * h ^ 2
  let u := 8 * rho ^ 2
  have hvu : v ≤ u := by dsimp [v, u]; nlinarith
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hrhoSqLe : rho ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    exact (sq_le_sq₀ hrhoPos.le (by norm_num)).2 hrhoLe
  have huLe : u ≤ 1 := by dsimp [u]; nlinarith
  have hnormU : ‖u‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hu0] using huLe
  have hexpPoly : Real.exp u - 1 ≤ u + u ^ 2 := by
    have hrem := Real.norm_exp_sub_one_sub_id_le hnormU
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu0] at hrem
    have hlower :
        Real.exp u - 1 - u ≤ |Real.exp u - 1 - u| :=
      le_abs_self _
    nlinarith
  have huPoly : u + u ^ 2 ≤ 9 * rho ^ 2 := by
    have hfourth :
        64 * rho ^ 4 ≤ rho ^ 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_left hrhoSqLe (sq_nonneg rho)
      norm_num at hmul ⊢
      nlinarith [hmul]
    dsimp [u]
    nlinarith
  have hchiOne :=
    geometryWitnessFamily_twoSample_chiSq_bound g N k epsilon t0
      hepsilon ht0 hg n hn h hhQuarter hvalid
  have hchiExp :
      Causalean.Stat.chiSqDiv
          (twoSampleLaw (geometryWitnessFamily g t0 h) N n)
          (twoSampleLaw (geometryWitnessFamily g t0 0) N n) ≤
        Real.exp v - 1 := by
    dsimp [v]
    linarith
  have hchiNine :
      Causalean.Stat.chiSqDiv
          (twoSampleLaw (geometryWitnessFamily g t0 h) N n)
          (twoSampleLaw (geometryWitnessFamily g t0 0) N n) ≤
        9 * rho ^ 2 := by
    calc
      _ ≤ Real.exp v - 1 := hchiExp
      _ ≤ Real.exp u - 1 := by
        linarith [Real.exp_le_exp.mpr hvu]
      _ ≤ u + u ^ 2 := hexpPoly
      _ ≤ 9 * rho ^ 2 := huPoly
  obtain ⟨hac, hint⟩ :=
    geometryWitnessFamily_twoSample_ac_integrable g N k epsilon t0
      hepsilon hg n h hhQuarter
  letI : IsProbabilityMeasure
      (twoSampleLaw (geometryWitnessFamily g t0 h) N n) :=
    geometryWitnessFamily_twoSample_probability g N k epsilon t0
      hepsilon hg n h hhQuarter
  letI : IsProbabilityMeasure
      (twoSampleLaw (geometryWitnessFamily g t0 0) N n) :=
    geometryWitnessFamily_twoSample_probability g N k epsilon t0
      hepsilon hg n 0 (by norm_num)
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    (twoSampleLaw (geometryWitnessFamily g t0 h) N n)
    (twoSampleLaw (geometryWitnessFamily g t0 0) N n) hac hint
  have hsqrt :
      Real.sqrt
          (Causalean.Stat.chiSqDiv
            (twoSampleLaw (geometryWitnessFamily g t0 h) N n)
            (twoSampleLaw (geometryWitnessFamily g t0 0) N n)) ≤
        3 * rho := by
    calc
      _ ≤ Real.sqrt (9 * rho ^ 2) := Real.sqrt_le_sqrt hchiNine
      _ = Real.sqrt ((3 * rho) ^ 2) := by congr 1 <;> ring
      _ = |3 * rho| := Real.sqrt_sq_eq_abs _
      _ = 3 * rho := abs_of_pos (mul_pos (by norm_num) hrhoPos)
  linarith

-- @node: def:least-favorable-witness
/-- The continuum family `Q_{n,h}^g`.  Each population has the same conditional
potential-data kernel given `X`, integrated against `g.sourceX` in the source
and `g.targetX` in the target. Compliance types have probabilities `p_n`,
`(1-p_n)/2`, `(1-p_n)/2`; `Y(0)=0`; and binary `Y(1)` has mean `1/2+h` for
compliers and `1/2` otherwise. -/
noncomputable def leastFavorableWitness
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (c epsilon alpha t0 rho : ℝ)
    (n : ℕ) (h : ℝ) (P : TransportedArray 𝒳) : Prop :=
  AdmissibleGeometry g k epsilon ∧
  0 < alpha ∧ alpha < 1 ∧ -- @realizes \alpha(noncoverage level in (0,1))
  0 < t0 ∧ -- @realizes t_0(positive fixed-strength threshold)
  rho = (1 - alpha) / 8 ∧
  |h| ≤ min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ)) ∧
  fixedGeometrySlice P g N k c epsilon n ∧
  (∃ K : 𝒳 → Measure PotentialCoordinates,
    (∀ x, IsProbabilityMeasure (K x)) ∧
    (∀ B, MeasurableSet B → Measurable fun x => K x B) ∧
    ∀ s A B, MeasurableSet A → MeasurableSet B →
      populationLaw P n s
          {o | fullX o ∈ A ∧ potentialCoordinates o ∈ B} =
        ∫⁻ x in A, K x B ∂geometryPopulationX g n s) ∧
  transportedFirstStage P n = geometryMu g t0 n ∧
    -- @realizes \mu_n(fixed-strength witness first stage; range inherited from class membership)
  effectiveStrength P n = t0 ∧
  targetCACE P n = 1 / 2 + h ∧
  (∀ s : Bool, ∀ᵐ o ∂populationLaw P n s,
    fullY0 o = 0 ∧ (fullY1 o = 0 ∨ fullY1 o = 1)) ∧
  (∀ s : Bool, ∀ A, MeasurableSet A →
    (populationLaw P n s
      {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = true}).toReal =
      ∫ x in A, geometryCompliance g t0 n x ∂geometryPopulationX g n s) ∧
  (∀ s : Bool, ∀ A, MeasurableSet A →
    (populationLaw P n s
      {o | fullX o ∈ A ∧ fullD0 o = true ∧ fullD1 o = true}).toReal =
      ∫ x in A, (1 - geometryCompliance g t0 n x) / 2
        ∂geometryPopulationX g n s) ∧
  (∀ s : Bool, ∀ A, MeasurableSet A →
    (populationLaw P n s
      {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = false}).toReal =
      ∫ x in A, (1 - geometryCompliance g t0 n x) / 2
        ∂geometryPopulationX g n s) ∧
  (∀ s : Bool, ∀ A, MeasurableSet A →
    ∫ o in {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = true},
        fullY1 o ∂populationLaw P n s =
      ∫ x in A, geometryCompliance g t0 n x * (1 / 2 + h)
        ∂geometryPopulationX g n s) ∧
  (∀ s : Bool, ∀ A, MeasurableSet A →
    ∫ o in {o | fullX o ∈ A ∧ fullD0 o = true ∧ fullD1 o = true},
        fullY1 o ∂populationLaw P n s =
      ∫ x in A, (1 - geometryCompliance g t0 n x) / 4
        ∂geometryPopulationX g n s) ∧
  (∀ s : Bool, ∀ A, MeasurableSet A →
    ∫ o in {o | fullX o ∈ A ∧ fullD0 o = false ∧ fullD1 o = false},
        fullY1 o ∂populationLaw P n s =
      ∫ x in A, (1 - geometryCompliance g t0 n x) / 4
        ∂geometryPopulationX g n s)
  -- @realizes \mathfrak g(fixed admissible geometry)
  -- @realizes \rho((1-alpha)/8)
  -- @realizes \theta_T(1/2+h on Q_{n,h}^g)

-- @node: def:geometry-handle
/-- Full fixed-strength geometry handle: admissibility, valid compliance
probabilities, exact first-stage/strength identities, a continuum of witness
laws, and the chi-square/total-variation comparisons with the center. -/
noncomputable def geometryHandle
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (c epsilon alpha t0 rho : ℝ)
    (n : ℕ) : Prop :=
  AdmissibleGeometry g k epsilon ∧
  0 < alpha ∧ alpha < 1 ∧
  0 < t0 ∧ -- @realizes t_0(positive frontier threshold)
  rho = (1 - alpha) / 8 ∧
  (∀ x, 0 ≤ geometryCompliance g t0 n x ∧
    geometryCompliance g t0 n x ≤ 1) ∧
  (∫ x, g.weight n x * geometryCompliance g t0 n x ∂g.sourceX n) =
    geometryMu g t0 n ∧
  (n : ℝ) * geometryMu g t0 n ^ 2 / geometryKish g n = t0 ∧
  ∃ Q : ℝ → TransportedArray 𝒳,
    (∀ h, |h| ≤ min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ)) →
      leastFavorableWitness g N k c epsilon alpha t0 rho n h (Q h)) ∧
    (∀ h, |h| ≤ min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ)) →
      1 + Causalean.Stat.chiSqDiv
          (twoSampleLaw (Q h) N n) (twoSampleLaw (Q 0) N n) ≤
        Real.exp (8 * t0 * h ^ 2)) ∧
    (∀ h, |h| ≤ min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ)) →
      Causalean.Stat.tvDist
          (twoSampleLaw (Q h) N n) (twoSampleLaw (Q 0) N n) ≤ 2 * rho)

/-! ## Inhabitation supplied by the explicit witness construction -/

/-- The continuum construction supplies a member of every sufficiently late
fixed-geometry strength slice.  In particular, lower bounds use an exhibited
law and never a nonemptiness assumption on the model class. -/
lemma fixedGeometrySlice_eventually_inhabited
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (c epsilon t0 : ℝ)
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (ht0 : 0 < t0)
    (hg : AdmissibleGeometry g k epsilon)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ P : TransportedArray 𝒳,
      fixedGeometrySlice P g N k c epsilon n ∧
      t0 ≤ effectiveStrength P n := by
  let μS : ℕ → Measure 𝒳 := g.sourceX
  let μT : ℕ → Measure 𝒳 := g.targetX
  let w : ℕ → 𝒳 → ℝ := g.weight
  let p : ℕ → 𝒳 → ℝ := fun m x =>
    min 1 (geometryCompliance g t0 m x)
  let e : ℕ → 𝒳 → ℝ := g.propensity
  have hpmeas : ∀ m, Measurable (p m) := fun m =>
    measurable_const.min (geometryCompliance_measurable g t0 m)
  have hemeas : ∀ m, Measurable (e m) := g.propensity_measurable
  have hwmeas : ∀ m, Measurable (w m) := g.weight_measurable
  have hμS : ∀ m, IsProbabilityMeasure (μS m) := hg.1
  have hμT : ∀ m, IsProbabilityMeasure (μT m) := hg.2.1
  have hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1 := by
    intro m x
    have hkish := geometryKish_pos g k epsilon hg m
    have hcomp : 0 ≤ geometryCompliance g t0 m x := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (hg.2.2.2.2.2.1 m x).1)
        hkish.le
    exact ⟨le_min (by norm_num) hcomp, min_le_left _ _⟩
  have he : ∀ m x, epsilon ≤ e m x ∧ e m x ≤ 1 - epsilon :=
    hg.2.2.2.2.1
  have hw : ∀ m x, 0 ≤ w m x ∧ w m x ≤ 2 * (k m : ℝ) :=
    hg.2.2.2.2.2.1
  have hw2 : ∀ m, ∫ x, (w m x) ^ 2 ∂μS m ≤ (k m : ℝ) :=
    hg.2.2.2.2.2.2.2.1
  have htransport : ∀ m A, MeasurableSet A →
      μT m A = ENNReal.ofReal (∫ x in A, w m x ∂μS m) :=
    hg.2.2.2.2.2.2.2.2
  have hvalid :=
    geometryCompliance_eventually_valid g k epsilon t0 ht0 hg hkRoot
  have hfirst : Tendsto (fun m => ∫ x, w m x * p m x ∂μS m)
      atTop (𝓝 0) := by
    apply (geometryMu_tendsto_zero g k epsilon t0 ht0 hg hkRoot).congr'
    filter_upwards [hvalid] with m hm
    have hpm : p m = geometryCompliance g t0 m := by
      funext x
      exact min_eq_right (hm x).2
    rw [show w m = g.weight m from rfl, hpm,
      show μS m = g.sourceX m from rfl]
    exact (geometry_firstStage g k epsilon t0 hg m).symm
  filter_upwards [hvalid, eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hnvalid hn
  have hnpos : 0 < n := by omega
  have hpm : p n = geometryCompliance g t0 n := by
    funext x
    exact min_eq_right (hnvalid x).2
  have he01 : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.1.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.1.le)⟩
  have hwint (m : ℕ) : Integrable (w m) (μS m) := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    refine Integrable.of_bound (hwmeas m).aestronglyMeasurable
      (2 * (k m : ℝ)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hw m x).1]
    exact (hw m x).2
  have hrn (m : ℕ) :
      (fun x => ((μT m).rnDeriv (μS m) x).toReal) =ᵐ[μS m] w m := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    exact transportWeight_eq_of_integral (hwmeas m) (hwint m)
      (fun x => (hw m x).1) (htransport m)
  have hmuPos : 0 < geometryMu g t0 n := by
    rw [geometryMu]
    exact Real.sqrt_pos.2 (div_pos
      (mul_pos ht0 (geometryKish_pos g k epsilon hg n))
      (by exact_mod_cast hnpos))
  have hpos : 0 < ∫ x, p n x ∂μT n := by
    letI : IsProbabilityMeasure (μS n) := hμS n
    rw [target_eq_withDensity_of_integral (hwmeas n) (hwint n)
      (Filter.Eventually.of_forall fun x => (hw n x).1) (htransport n)]
    change 0 < ∫ x, p n x
      ∂(μS n).withDensity (fun x => ENNReal.ofReal (w n x))
    rw [show (fun x => ENNReal.ofReal (w n x)) =
      ENNReal.ofReal ∘ w n by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul
      (ENNReal.measurable_ofReal.comp (hwmeas n))
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (p n)]
    have hint :
        (∫ x, ((ENNReal.ofReal ∘ w n) x).toReal • p n x ∂μS n) =
          ∫ x, w n x * p n x ∂μS n := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Function.comp_apply, ENNReal.toReal_ofReal (hw n x).1,
        smul_eq_mul]
    rw [hint, hpm]
    rw [show (∫ x, w n x * geometryCompliance g t0 n x ∂μS n) =
      geometryMu g t0 n by
        simpa [w, μS] using geometry_firstStage g k epsilon t0 hg n]
    exact hmuPos
  let P := witnessArray μS μT p e hpmeas hemeas
  have hIV : TransportedIVClass P N k c epsilon n :=
    witnessArray_mem_transportedIVClass μS μT w p e N k c epsilon
      hpmeas hemeas hwmeas hμS hμT hp hepsilon he hw hw2 htransport
      hc hN hkInf hkRoot hfirst n hpos
  have hsource : sourceXLaw P n = g.sourceX n := by
    unfold P
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
  have htarget : targetXLaw P n = g.targetX n := by
    unfold P
    rw [witnessArray_targetXLaw μS μT p e hpmeas hemeas hμS hμT hp n]
  have hweight :
      transportWeight P n =ᵐ[sourceXLaw P n] g.weight n := by
    rw [hsource]
    unfold transportWeight
    rw [hsource, htarget]
    exact hrn n
  have hweightG :
      transportWeight P n =ᵐ[g.sourceX n] g.weight n := by
    simpa only [hsource] using hweight
  have hpropensity : P.propensity n = g.propensity n := by
    rfl
  have hfirstExact :
      transportedFirstStage P n = geometryMu g t0 n := by
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [transportedFirstStage_eq_weighted_deltaD P k epsilon n
      (sourceObservationFacts_of_class P N k c epsilon n hIV)
      hIV.instrumentOverlap hIV.weightEnvelope]
    change (∫ x, transportWeight P n x * p n x ∂sourceXLaw P n) = _
    rw [hsource]
    calc
      (∫ x, transportWeight P n x * p n x ∂g.sourceX n) =
          ∫ x, w n x * p n x ∂μS n := by
        change (∫ x, transportWeight P n x * p n x ∂μS n) = _
        apply integral_congr_ae
        filter_upwards [hweightG] with x hx
        rw [hx]
      _ = geometryMu g t0 n := by
        rw [hpm]
        simpa [w, μS] using geometry_firstStage g k epsilon t0 hg n
  have hkishExact :
      kishDispersion P n = geometryKish g n := by
    unfold kishDispersion geometryKish
    rw [hsource]
    exact integral_congr_ae (hweightG.fun_comp fun z => z ^ 2)
  refine ⟨P, ⟨hIV, hsource, htarget, hweight, hpropensity⟩, ?_⟩
  rw [effectiveStrength, hfirstExact, hkishExact,
    geometry_strength g k epsilon t0 ht0 hg n hnpos]

/-- The named geometry family is least favourable at every sufficiently late
index throughout the prescribed local range. -/
lemma geometryWitnessFamily_eventually_leastFavorable
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (c epsilon alpha t0 rho : ℝ)
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1) (ht0 : 0 < t0)
    (hrho : rho = (1 - alpha) / 8)
    (hg : AdmissibleGeometry g k epsilon)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ∀ h, |h| ≤ min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ)) →
        leastFavorableWitness g N k c epsilon alpha t0 rho n h
          (geometryWitnessFamily g t0 h) := by
  let μS : ℕ → Measure 𝒳 := g.sourceX
  let μT : ℕ → Measure 𝒳 := g.targetX
  let w : ℕ → 𝒳 → ℝ := g.weight
  let p : ℕ → 𝒳 → ℝ := fun m x =>
    min 1 (geometryCompliance g t0 m x)
  let e : ℕ → 𝒳 → ℝ := g.propensity
  have hpmeas : ∀ m, Measurable (p m) := fun m =>
    measurable_const.min (geometryCompliance_measurable g t0 m)
  have hemeas : ∀ m, Measurable (e m) := g.propensity_measurable
  have hwmeas : ∀ m, Measurable (w m) := g.weight_measurable
  have hμS : ∀ m, IsProbabilityMeasure (μS m) := hg.1
  have hμT : ∀ m, IsProbabilityMeasure (μT m) := hg.2.1
  have hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1 := by
    intro m x
    have hkish := geometryKish_pos g k epsilon hg m
    have hcomp : 0 ≤ geometryCompliance g t0 m x := by
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (hg.2.2.2.2.2.1 m x).1)
        hkish.le
    exact ⟨le_min (by norm_num) hcomp, min_le_left _ _⟩
  have he : ∀ m x, epsilon ≤ e m x ∧ e m x ≤ 1 - epsilon :=
    hg.2.2.2.2.1
  have hw : ∀ m x, 0 ≤ w m x ∧ w m x ≤ 2 * (k m : ℝ) :=
    hg.2.2.2.2.2.1
  have hw2 : ∀ m, ∫ x, (w m x) ^ 2 ∂μS m ≤ (k m : ℝ) :=
    hg.2.2.2.2.2.2.2.1
  have htransport : ∀ m A, MeasurableSet A →
      μT m A = ENNReal.ofReal (∫ x in A, w m x ∂μS m) :=
    hg.2.2.2.2.2.2.2.2
  have hvalid :=
    geometryCompliance_eventually_valid g k epsilon t0 ht0 hg hkRoot
  have hfirst : Tendsto (fun m => ∫ x, w m x * p m x ∂μS m)
      atTop (𝓝 0) := by
    apply (geometryMu_tendsto_zero g k epsilon t0 ht0 hg hkRoot).congr'
    filter_upwards [hvalid] with m hm
    have hpm : p m = geometryCompliance g t0 m := by
      funext x
      exact min_eq_right (hm x).2
    rw [show w m = g.weight m from rfl, hpm,
      show μS m = g.sourceX m from rfl]
    exact (geometry_firstStage g k epsilon t0 hg m).symm
  filter_upwards [hvalid,
    eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hnvalid hn
  have hnpos : 0 < n := by omega
  have hpm : p n = geometryCompliance g t0 n := by
    funext x
    exact min_eq_right (hnvalid x).2
  have he01 : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := fun m x =>
    ⟨hepsilon.1.le.trans (he m x).1,
      (he m x).2.trans (sub_le_self 1 hepsilon.1.le)⟩
  have hwint (m : ℕ) : Integrable (w m) (μS m) := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    refine Integrable.of_bound (hwmeas m).aestronglyMeasurable
      (2 * (k m : ℝ)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hw m x).1]
    exact (hw m x).2
  have hrn (m : ℕ) :
      (fun x => ((μT m).rnDeriv (μS m) x).toReal) =ᵐ[μS m] w m := by
    letI : IsProbabilityMeasure (μS m) := hμS m
    exact transportWeight_eq_of_integral (hwmeas m) (hwint m)
      (fun x => (hw m x).1) (htransport m)
  have hmuPos : 0 < geometryMu g t0 n := by
    rw [geometryMu]
    exact Real.sqrt_pos.2 (div_pos
      (mul_pos ht0 (geometryKish_pos g k epsilon hg n))
      (by exact_mod_cast hnpos))
  have hpos : 0 < ∫ x, p n x ∂μT n := by
    letI : IsProbabilityMeasure (μS n) := hμS n
    rw [target_eq_withDensity_of_integral (hwmeas n) (hwint n)
      (Filter.Eventually.of_forall fun x => (hw n x).1) (htransport n)]
    change 0 < ∫ x, p n x
      ∂(μS n).withDensity (fun x => ENNReal.ofReal (w n x))
    rw [show (fun x => ENNReal.ofReal (w n x)) =
      ENNReal.ofReal ∘ w n by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul
      (ENNReal.measurable_ofReal.comp (hwmeas n))
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (p n)]
    have hint :
        (∫ x, ((ENNReal.ofReal ∘ w n) x).toReal • p n x ∂μS n) =
          ∫ x, w n x * p n x ∂μS n := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Function.comp_apply, ENNReal.toReal_ofReal (hw n x).1,
        smul_eq_mul]
    rw [hint, hpm]
    rw [show (∫ x, w n x * geometryCompliance g t0 n x ∂μS n) =
      geometryMu g t0 n by
        simpa [w, μS] using geometry_firstStage g k epsilon t0 hg n]
    exact hmuPos
  let Q : ℝ → TransportedArray 𝒳 := geometryWitnessFamily g t0
  have hQ (a : ℝ) :
      Q a = witnessArrayH a μS μT p e hpmeas hemeas := by
    rfl
  intro h hh
  change leastFavorableWitness g N k c epsilon alpha t0 rho n h (Q h)
  have hhquarter : |h| ≤ 1 / 4 :=
    hh.trans (min_le_left _ _)
  have hIV : TransportedIVClass (Q h) N k c epsilon n := by
    rw [hQ]
    exact witnessArrayH_mem_transportedIVClass
      h μS μT w p e N k c epsilon hpmeas hemeas hwmeas
      hμS hμT hhquarter hp hepsilon he hw hw2 htransport
      hc hN hkInf hkRoot hfirst n hpos
  have hsource : sourceXLaw (Q h) n = g.sourceX n := by
    unfold Q geometryWitnessFamily
    rw [witnessArrayH_sourceXLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp he01 n]
  have htarget : targetXLaw (Q h) n = g.targetX n := by
    unfold Q geometryWitnessFamily
    rw [witnessArrayH_targetXLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n]
  have hweight :
      transportWeight (Q h) n =ᵐ[sourceXLaw (Q h) n] g.weight n := by
    rw [hsource]
    unfold transportWeight
    rw [hsource, htarget]
    exact hrn n
  have hweightG :
      transportWeight (Q h) n =ᵐ[g.sourceX n] g.weight n := by
    simpa only [hsource] using hweight
  have hpropensity : (Q h).propensity n = g.propensity n := by
    rfl
  have hfirstExact :
      transportedFirstStage (Q h) n = geometryMu g t0 n := by
    letI : IsProbabilityMeasure (μS n) := hμS n
    letI : IsProbabilityMeasure (μT n) := hμT n
    rw [transportedFirstStage_eq_weighted_deltaD (Q h) k epsilon n
      (sourceObservationFacts_of_class (Q h) N k c epsilon n hIV)
      hIV.instrumentOverlap hIV.weightEnvelope]
    change (∫ x, transportWeight (Q h) n x * p n x
      ∂sourceXLaw (Q h) n) = _
    rw [hsource]
    calc
      (∫ x, transportWeight (Q h) n x * p n x ∂g.sourceX n) =
          ∫ x, w n x * p n x ∂μS n := by
        change (∫ x, transportWeight (Q h) n x * p n x ∂μS n) = _
        apply integral_congr_ae
        filter_upwards [hweightG] with x hx
        rw [hx]
      _ = geometryMu g t0 n := by
        rw [hpm]
        simpa [w, μS] using geometry_firstStage g k epsilon t0 hg n
  have hkishExact :
      kishDispersion (Q h) n = geometryKish g n := by
    unfold kishDispersion geometryKish
    rw [hsource]
    exact integral_congr_ae (hweightG.fun_comp fun z => z ^ 2)
  have hslice : fixedGeometrySlice
      (Q h) g N k c epsilon n :=
    ⟨hIV, hsource, htarget, hweight, hpropensity⟩
  refine ⟨hg, halpha.1, halpha.2, ht0, hrho, hh, hslice, ?_,
    hfirstExact, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    exact witnessArrayH_equalConditionalKernel h μS μT p e hpmeas
      hemeas hμS hμT hhquarter hp g n rfl rfl
  · rw [effectiveStrength, hfirstExact, hkishExact,
      geometry_strength g k epsilon t0 ht0 hg n hnpos]
  · rw [hQ]
    exact witnessArrayH_targetCACE h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n hpos
  · intro s
    rw [hQ, witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n s]
    cases s
    · exact witnessPopulationMeasureH_ae_good h false hhquarter
        (hpmeas n) (hp n) |>.mono fun o ho => ⟨ho.1, ho.2.1⟩
    · exact witnessPopulationMeasureH_ae_good h true hhquarter
        (hpmeas n) (hp n) |>.mono fun o ho => ⟨ho.1, ho.2.1⟩
  · intro s A hA
    rw [hQ, witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n s]
    cases s
    · simpa [geometryPopulationX, hpm, μT] using
        witnessPopulationMeasureH_complier_on
          (μ := μT n) h false hhquarter (hpmeas n) (hp n) A hA
    · simpa [geometryPopulationX, hpm, μS] using
        witnessPopulationMeasureH_complier_on
          (μ := μS n) h true hhquarter (hpmeas n) (hp n) A hA
  · intro s A hA
    rw [hQ, witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n s]
    cases s
    · simpa [geometryPopulationX, hpm, μT] using
        witnessPopulationMeasureH_always_on
          (μ := μT n) h false hhquarter (hpmeas n) (hp n) A hA
    · simpa [geometryPopulationX, hpm, μS] using
        witnessPopulationMeasureH_always_on
          (μ := μS n) h true hhquarter (hpmeas n) (hp n) A hA
  · intro s A hA
    rw [hQ, witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n s]
    cases s
    · simpa [geometryPopulationX, hpm, μT] using
        witnessPopulationMeasureH_never_on
          (μ := μT n) h false hhquarter (hpmeas n) (hp n) A hA
    · simpa [geometryPopulationX, hpm, μS] using
        witnessPopulationMeasureH_never_on
          (μ := μS n) h true hhquarter (hpmeas n) (hp n) A hA
  · intro s A hA
    rw [hQ, witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n s]
    cases s
    · simpa [geometryPopulationX, hpm, μT] using
        witnessPopulationMeasureH_complierY_on
          (μ := μT n) h false hhquarter (hpmeas n) (hp n) A hA
    · simpa [geometryPopulationX, hpm, μS] using
        witnessPopulationMeasureH_complierY_on
          (μ := μS n) h true hhquarter (hpmeas n) (hp n) A hA
  · intro s A hA
    rw [hQ, witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n s]
    cases s
    · simpa [geometryPopulationX, hpm, μT] using
        witnessPopulationMeasureH_alwaysY_on
          (μ := μT n) h false hhquarter (hpmeas n) (hp n) A hA
    · simpa [geometryPopulationX, hpm, μS] using
        witnessPopulationMeasureH_alwaysY_on
          (μ := μS n) h true hhquarter (hpmeas n) (hp n) A hA
  · intro s A hA
    rw [hQ, witnessArrayH_populationLaw h μS μT p e hpmeas hemeas
      hμS hμT hhquarter hp n s]
    cases s
    · simpa [geometryPopulationX, hpm, μT] using
        witnessPopulationMeasureH_neverY_on
          (μ := μT n) h false hhquarter (hpmeas n) (hp n) A hA
    · simpa [geometryPopulationX, hpm, μS] using
        witnessPopulationMeasureH_neverY_on
          (μ := μS n) h true hhquarter (hpmeas n) (hp n) A hA

/-- At every sufficiently late index, the clamped construction gives the
paper's full least-favourable family throughout its prescribed local range. -/
lemma leastFavorableWitness_eventually_inhabited
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (c epsilon alpha t0 rho : ℝ)
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1) (ht0 : 0 < t0)
    (hrho : rho = (1 - alpha) / 8)
    (hg : AdmissibleGeometry g k epsilon)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ Q : ℝ → TransportedArray 𝒳,
      ∀ h, |h| ≤ min (1 / 4) (rho * t0 ^ (-1 / 2 : ℝ)) →
        leastFavorableWitness g N k c epsilon alpha t0 rho n h (Q h) := by
  filter_upwards [
    geometryWitnessFamily_eventually_leastFavorable g N k c epsilon alpha
      t0 rho hc hepsilon halpha ht0 hrho hg hN hkPos hkInf hkRoot
  ] with n hn
  exact ⟨geometryWitnessFamily g t0, hn⟩

/-- The named least-favourable family supplies the complete geometry handle,
including its chi-square and total-variation calibration, eventually in `n`. -/
lemma geometryHandle_eventually_inhabited
    (g : Geometry 𝒳) (N k : ℕ → ℕ) (c epsilon alpha t0 rho : ℝ)
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1) (ht0 : 0 < t0)
    (hrho : rho = (1 - alpha) / 8)
    (hg : AdmissibleGeometry g k epsilon)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      geometryHandle g N k c epsilon alpha t0 rho n := by
  have hvalid :=
    geometryCompliance_eventually_valid g k epsilon t0 ht0 hg hkRoot
  have hleast :=
    geometryWitnessFamily_eventually_leastFavorable g N k c epsilon alpha
      t0 rho hc hepsilon halpha ht0 hrho hg hN hkPos hkInf hkRoot
  filter_upwards [hvalid, hleast,
    eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hnvalid hnleast hn
  have hnpos : 0 < n := by omega
  refine ⟨hg, halpha.1, halpha.2, ht0, hrho, hnvalid,
    geometry_firstStage g k epsilon t0 hg n,
    geometry_strength g k epsilon t0 ht0 hg n hnpos,
    geometryWitnessFamily g t0, hnleast, ?_, ?_⟩
  · intro h hh
    exact geometryWitnessFamily_twoSample_chiSq_bound g N k epsilon t0
      hepsilon.1 ht0 hg n hnpos h (hh.trans (min_le_left _ _)) hnvalid
  · intro h hh
    exact geometryWitnessFamily_twoSample_tv_bound g N k epsilon alpha t0 rho
      hepsilon.1 halpha ht0 hrho hg n hnpos h hh hnvalid

private lemma uniformFiniteCellClass_inhabited
    (N k : ℕ → ℕ) (c epsilon : ℝ)
    (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳, ∀ i, MeasurableSet {cell i})
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    ∀ n, ∃ P : TransportedArray 𝒳,
      FiniteCellClass P N k c epsilon n := by
  classical
  choose cell hcell using hCarrier
  let μS : ℕ → Measure 𝒳 := fun m =>
    ∑ i : Fin (k m), (k m : ENNReal)⁻¹ • Measure.dirac (cell m i)
  let μT : ℕ → Measure 𝒳 := μS
  let w : ℕ → 𝒳 → ℝ := fun _ _ => 1
  let p : ℕ → 𝒳 → ℝ := fun m _ => 1 / ((m : ℝ) + 1)
  let e : ℕ → 𝒳 → ℝ := fun _ _ => 1 / 2
  have hpmeas : ∀ m, Measurable (p m) := fun _ => measurable_const
  have hemeas : ∀ m, Measurable (e m) := fun _ => measurable_const
  have hwmeas : ∀ m, Measurable (w m) := fun _ => measurable_const
  have hkinv (m : ℕ) : (k m : ENNReal) * (k m : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hkPos m)))
      (ENNReal.natCast_ne_top (k m))
  have hμS : ∀ m, IsProbabilityMeasure (μS m) := by
    intro m
    rw [isProbabilityMeasure_iff]
    simp [μS, hkinv m]
  have hμT : ∀ m, IsProbabilityMeasure (μT m) := by
    intro m
    exact hμS m
  have hp : ∀ m x, 0 ≤ p m x ∧ p m x ≤ 1 := by
    intro m x
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      norm_num
  have he : ∀ m x, epsilon ≤ e m x ∧ e m x ≤ 1 - epsilon := by
    intro m x
    dsimp [e]
    constructor
    · exact hepsilon.2.le
    · linarith [hepsilon.2]
  have he01 : ∀ m x, 0 ≤ e m x ∧ e m x ≤ 1 := by
    intro m x
    norm_num [e]
  have hw : ∀ m x, 0 ≤ w m x ∧ w m x ≤ 2 * (k m : ℝ) := by
    intro m x
    constructor
    · norm_num [w]
    · have hk1 : (1 : ℝ) ≤ k m := by
        exact_mod_cast hkPos m
      dsimp [w]
      linarith
  have hw2 : ∀ m, ∫ x, (w m x) ^ 2 ∂μS m ≤ (k m : ℝ) := by
    intro m
    letI : IsProbabilityMeasure (μS m) := hμS m
    have hk1 : (1 : ℝ) ≤ k m := by
      exact_mod_cast hkPos m
    simpa [w] using hk1
  have htransport : ∀ m A, MeasurableSet A →
      μT m A = ENNReal.ofReal (∫ x in A, w m x ∂μS m) := by
    intro m A hA
    letI : IsProbabilityMeasure (μS m) := hμS m
    simpa [μT, w] using (ofReal_setIntegral_one (μS m) A).symm
  have hfirst : Tendsto (fun m => ∫ x, w m x * p m x ∂μS m)
      atTop (𝓝 0) := by
    have hEq : (fun m => ∫ x, w m x * p m x ∂μS m) =
        fun m : ℕ => 1 / ((m : ℝ) + 1) := by
      funext m
      letI : IsProbabilityMeasure (μS m) := hμS m
      simp [w, p]
    rw [hEq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  have hpos : 0 < ∫ x, p n x ∂μT n := by
    letI : IsProbabilityMeasure (μT n) := hμT n
    simp [p]
    positivity
  let P := witnessArray μS μT p e hpmeas hemeas
  have hIV : TransportedIVClass P N k c epsilon n :=
    witnessArray_mem_transportedIVClass μS μT w p e N k c epsilon
      hpmeas hemeas hwmeas hμS hμT hp hepsilon he hw hw2 htransport
      hc hN hkInf hkRoot hfirst n hpos
  have hrange : μS n (Set.range (cell n)) = 1 := by
    rw [show Set.range (cell n) = ⋃ i, {cell n i} by
      ext x
      simp]
    simp only [μS, Measure.finset_sum_apply, Measure.smul_apply]
    simp [Measure.dirac_apply_of_mem, hkinv n]
  have hatom (i : Fin (k n)) :
      (μS n {cell n i}).toReal = (k n : ℝ)⁻¹ := by
    simp only [μS, Measure.finset_sum_apply, Measure.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp [ENNReal.toReal_inv]
    · intro j _ hji
      have hne : cell n j ≠ cell n i :=
        fun h => hji ((cell n).injective h)
      rw [Measure.dirac_apply' _ (hcell n i)]
      simp [hne]
    · simp
  refine ⟨P, { hIV with finiteCellSource := ?_ }⟩
  refine ⟨hkPos n, ?_, cell n, hcell n, ?_, ?_, ?_, ?_⟩
  · unfold P
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    exact hμS n
  · unfold P
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    exact hrange
  · intro i
    unfold P
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    exact hatom i
  · unfold P
    rw [witnessArray_sourceXLaw μS μT p e hpmeas hemeas
      hμS hμT hp he01 n]
    rfl
  · filter_upwards with x
    rfl

/-- The uniform finite-cell construction is realizable on any measurable
carrier admitting the required rowwise finite injections.  The injected
`Fin (k n)` image carries full mass, so growing support constrains the measure
rather than identifying the ambient carrier with a finite type. -/
lemma finiteCellClass_inhabited
    (N k : ℕ → ℕ) (c epsilon : ℝ)
    (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳, ∀ i, MeasurableSet {cell i})
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    ∀ n, ∃ P : TransportedArray 𝒳,
      FiniteCellClass P N k c epsilon n := by
  exact uniformFiniteCellClass_inhabited N k c epsilon hCarrier hc hepsilon
    hN hkPos hkInf hkRoot

/-- Forgetting the finite-cell field gives an inhabited main class on the same
arbitrary carrier. -/
lemma transportedIVClass_inhabited
    (N k : ℕ → ℕ) (c epsilon : ℝ)
    (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳, ∀ i, MeasurableSet {cell i})
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    ∀ n, ∃ P : TransportedArray 𝒳,
      TransportedIVClass P N k c epsilon n := by
  intro n
  obtain ⟨P, hP⟩ :=
    finiteCellClass_inhabited N k c epsilon hCarrier hc hepsilon hN hkPos hkInf
      hkRoot n
  exact ⟨P, hP.toTransportedIVClass⟩

/-- The same uniform witness inhabits every regular finite-cell class whose
fixed constants contain the uniform mass `1 / k_n`. -/
lemma regularFiniteCellClass_inhabited
    (N k : ℕ → ℕ) (c epsilon cminus cplus : ℝ)
    (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳, ∀ i, MeasurableSet {cell i})
    (hc : 0 < c) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hcminus : 0 < cminus ∧ cminus ≤ 1) (hcplus : 1 ≤ cplus)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    ∀ n, ∃ P : TransportedArray 𝒳,
      RegularFiniteCellClass P N k c epsilon cminus cplus n := by
  intro n
  obtain ⟨P, hP⟩ :=
    uniformFiniteCellClass_inhabited N k c epsilon hCarrier hc hepsilon hN
      hkPos hkInf hkRoot n
  rcases hP.finiteCellSource with
    ⟨hk, hprob, cell, hcell, hrange, hatom, _, he⟩
  refine ⟨P, hP.toTransportedIVClass, hk, hcminus.1, hcminus.2, hcplus,
    cell, hcell, hrange, ?_⟩
  intro i
  rw [hatom i]
  have hinv : 0 ≤ (k n : ℝ)⁻¹ := by positivity
  constructor
  · simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hcminus.2 hinv
  · simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hcplus hinv

end CausalSmith.Stat.TransportedLateStrengthFrontier
