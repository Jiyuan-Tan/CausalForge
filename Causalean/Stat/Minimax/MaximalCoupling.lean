import Causalean.Stat.Minimax.Scheffe
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Maximal couplings through a measurable compression

This file develops the common-submeasure and coupling construction used by the
coordinatewise direct-product argument.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Causalean.Stat

-- @node: measurableEqOfStandardBorel
/-- Equality is measurable on every standard Borel space. -/
noncomputable def measurableEqOfStandardBorel
    (X : Type*) [MeasurableSpace X] [StandardBorelSpace X] : MeasurableEq X := by
  let e : X → ℝ := MeasureTheory.embeddingReal X
  have he : MeasurableEmbedding e := MeasureTheory.measurableEmbedding_embeddingReal X
  constructor
  rw [show Set.diagonal X = (Prod.map e e) ⁻¹' Set.diagonal ℝ by
    ext p
    simp only [Set.mem_diagonal_iff, Set.mem_preimage, Prod.map_apply]
    exact he.injective.eq_iff.symm]
  exact measurableSet_diagonal.preimage (he.measurable.prodMap he.measurable)

-- @node: tvDist_eq_half_integral_abs_rnDeriv_sub
/-- Scheffé's identity with both probability laws dominated by an arbitrary
finite reference measure. -/
lemma tvDist_eq_half_integral_abs_rnDeriv_sub
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsFiniteMeasure xi] (hmu : mu ≪ xi) (hnu : nu ≪ xi) :
    Causalean.Stat.tvDist mu nu =
      (1 / 2 : ℝ) * ∫ x,
        |(mu.rnDeriv xi x).toReal - (nu.rnDeriv xi x).toReal| ∂xi := by
  let p : X → ℝ := fun x => (mu.rnDeriv xi x).toReal
  let q : X → ℝ := fun x => (nu.rnDeriv xi x).toReal
  let d : X → ℝ := fun x => p x - q x
  have hp : Integrable p xi := Measure.integrable_toReal_rnDeriv
  have hq : Integrable q xi := Measure.integrable_toReal_rnDeriv
  have hd : Integrable d xi := hp.sub hq
  have hd0 : ∫ x, d x ∂xi = 0 := by
    rw [show d = fun x => p x - q x from rfl, integral_sub hp hq]
    rw [show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
      show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hmu,
      Measure.integral_toReal_rnDeriv hnu]
    simp
  apply le_antisymm
  · unfold Causalean.Stat.tvDist
    apply ciSup_le
    rintro ⟨A, hA⟩
    have hgap : mu.real A - nu.real A = ∫ x in A, d x ∂xi := by
      rw [show d = fun x => p x - q x from rfl,
        integral_sub hp.integrableOn hq.integrableOn,
        show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
        show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
        Measure.setIntegral_toReal_rnDeriv hmu,
        Measure.setIntegral_toReal_rnDeriv hnu]
    rw [hgap]
    exact Causalean.Stat.abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
      hd hd0 hA
  · let A : Set X := {x | 0 ≤ d x}
    have hA : MeasurableSet A := by
      dsimp [A, d, p, q]
      exact measurableSet_le measurable_const
        ((Measure.measurable_rnDeriv mu xi).ennreal_toReal.sub
          (Measure.measurable_rnDeriv nu xi).ennreal_toReal)
    have hsplit : ∫ x in A, d x ∂xi + ∫ x in Aᶜ, d x ∂xi = 0 := by
      rw [MeasureTheory.integral_add_compl hA hd, hd0]
    have hpos : 0 ≤ ∫ x in A, d x ∂xi := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      exact hx
    have habs : ∫ x, |d x| ∂xi = 2 * ∫ x in A, d x ∂xi := by
      rw [← MeasureTheory.integral_add_compl hA hd.abs]
      have h1 : ∫ x in A, |d x| ∂xi = ∫ x in A, d x ∂xi := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hA] with x hx
        exact abs_of_nonneg hx
      have h2 : ∫ x in Aᶜ, |d x| ∂xi = -(∫ x in Aᶜ, d x ∂xi) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hA.compl] with x hx
        exact abs_of_nonpos (le_of_not_ge hx)
      rw [h1, h2]
      linarith
    have hgap : mu.real A - nu.real A = ∫ x in A, d x ∂xi := by
      rw [show d = fun x => p x - q x from rfl,
        integral_sub hp.integrableOn hq.integrableOn,
        show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
        show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
        Measure.setIntegral_toReal_rnDeriv hmu,
        Measure.setIntegral_toReal_rnDeriv hnu]
    have htv := Causalean.Stat.abs_measureReal_sub_le_tvDist
      (μ := mu) (ν := nu) hA
    change (1 / 2 : ℝ) * ∫ x, |d x| ∂xi ≤ _
    rw [habs]
    rw [hgap, abs_of_nonneg hpos] at htv
    linarith

/-- The common submeasure obtained by taking the pointwise minimum of two
Radon--Nikodym densities against a finite dominating measure. -/
-- @node: rnCommonPart
noncomputable def rnCommonPart
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) : Measure X :=
  xi.withDensity fun x => min (mu.rnDeriv xi x) (nu.rnDeriv xi x)

-- @node: rnCommonPart_le_left
/-- The RN common part is dominated by its first law. -/
lemma rnCommonPart_le_left
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure xi] (hmu : mu ≪ xi) :
    rnCommonPart mu nu xi ≤ mu := by
  calc
    rnCommonPart mu nu xi ≤ xi.withDensity (mu.rnDeriv xi) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall fun x => min_le_left _ _
    _ = mu := Measure.withDensity_rnDeriv_eq mu xi hmu

-- @node: rnCommonPart_le_right
/-- The RN common part is dominated by its second law. -/
lemma rnCommonPart_le_right
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsFiniteMeasure nu] [IsFiniteMeasure xi] (hnu : nu ≪ xi) :
    rnCommonPart mu nu xi ≤ nu := by
  calc
    rnCommonPart mu nu xi ≤ xi.withDensity (nu.rnDeriv xi) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall fun x => min_le_right _ _
    _ = nu := Measure.withDensity_rnDeriv_eq nu xi hnu

-- @node: rnCommonPart_mass_eq_one_sub_tvDist
/-- The mass of the RN common part is exactly one minus total variation. -/
lemma rnCommonPart_mass_eq_one_sub_tvDist
    {X : Type*} [MeasurableSpace X]
    (mu nu xi : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsFiniteMeasure xi] (hmu : mu ≪ xi) (hnu : nu ≪ xi) :
    rnCommonPart mu nu xi Set.univ =
      ENNReal.ofReal (1 - Causalean.Stat.tvDist mu nu) := by
  let p : X → ℝ := fun x => (mu.rnDeriv xi x).toReal
  let q : X → ℝ := fun x => (nu.rnDeriv xi x).toReal
  have hp : Integrable p xi := Measure.integrable_toReal_rnDeriv
  have hq : Integrable q xi := Measure.integrable_toReal_rnDeriv
  have hformula : ∀ x, min (p x) (q x) =
      (p x + q x - |p x - q x|) / 2 := by
    intro x
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hmin : Integrable (fun x => min (p x) (q x)) xi := by
    refine ((hp.add hq).sub (hp.sub hq).abs |>.div_const 2).congr ?_
    exact Filter.Eventually.of_forall fun x => (hformula x).symm
  have hmin_nonneg : 0 ≤ᵐ[xi] fun x => min (p x) (q x) := by
    filter_upwards [] with x
    exact le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hp_one : ∫ x, p x ∂xi = 1 := by
    rw [show p = fun x => (mu.rnDeriv xi x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hmu]
    simp
  have hq_one : ∫ x, q x ∂xi = 1 := by
    rw [show q = fun x => (nu.rnDeriv xi x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hnu]
    simp
  have hreal : ∫ x, min (p x) (q x) ∂xi =
      1 - Causalean.Stat.tvDist mu nu := by
    have hid : (fun x => min (p x) (q x)) =
        fun x => (p x + q x - |p x - q x|) / 2 := by
      funext x; exact hformula x
    rw [hid, integral_div]
    rw [integral_sub (f := fun x => p x + q x)
      (g := fun x => |p x - q x|) (hp.add hq) (hp.sub hq).abs]
    rw [integral_add hp hq, hp_one, hq_one,
      tvDist_eq_half_integral_abs_rnDeriv_sub mu nu xi hmu hnu]
    ring
  rw [rnCommonPart, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    ∫⁻ x, min (mu.rnDeriv xi x) (nu.rnDeriv xi x) ∂xi =
        ∫⁻ x, ENNReal.ofReal (min (p x) (q x)) ∂xi := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top mu xi,
        Measure.rnDeriv_lt_top nu xi] with x hpx hqx
      simp only [ENNReal.ofReal_min]
      rw [ENNReal.ofReal_toReal hpx.ne, ENNReal.ofReal_toReal hqx.ne]
    _ = ENNReal.ofReal (∫ x, min (p x) (q x) ∂xi) := by
      exact (ofReal_integral_eq_lintegral_ofReal hmin hmin_nonneg).symm
    _ = _ := by rw [hreal]

-- @node: measure_eq_of_tvDist_eq_zero
/-- Probability measures at total-variation distance zero are equal. -/
lemma measure_eq_of_tvDist_eq_zero
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (h : Causalean.Stat.tvDist mu nu = 0) : mu = nu := by
  ext A hA
  have hgap := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := mu) (ν := nu) hA
  rw [h] at hgap
  have hre : mu.real A = nu.real A := by
    have := abs_nonneg (mu.real A - nu.real A)
    rw [abs_nonpos_iff] at hgap
    linarith
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu A) (measure_ne_top nu A)]
  exact hre

/-- A maximal coupling of two laws on the same standard Borel space. -/
-- @node: maximalCoupling
noncomputable def maximalCoupling
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    Measure (X × X) :=
  if hzero : Causalean.Stat.tvDist mu nu = 0 then
    mu.map fun x => (x, x)
  else
    let xi := mu + nu
    let c := rnCommonPart mu nu xi
    let rmu := mu - c
    let rnu := nu - c
    c.map (fun x => (x, x)) +
      (ENNReal.ofReal (Causalean.Stat.tvDist mu nu))⁻¹ • (rmu.prod rnu)

-- @node: residual_mass
private lemma residual_mass
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    let xi := mu + nu
    let c := rnCommonPart mu nu xi
    (mu - c) Set.univ = ENNReal.ofReal (Causalean.Stat.tvDist mu nu) := by
  dsimp
  have hmu : mu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right _
  have hnu : nu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hc : rnCommonPart mu nu (mu + nu) ≤ mu :=
    rnCommonPart_le_left mu nu (mu + nu) hmu
  letI : IsFiniteMeasure (rnCommonPart mu nu (mu + nu)) :=
    isFiniteMeasure_of_le mu hc
  rw [Measure.sub_apply MeasurableSet.univ hc,
    rnCommonPart_mass_eq_one_sub_tvDist mu nu (mu + nu) hmu hnu]
  have htv0 := Causalean.Stat.tvDist_nonneg (μ := mu) (ν := nu)
  have htv1 := Causalean.Stat.tvDist_le_one (μ := mu) (ν := nu)
  rw [measure_univ, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - Causalean.Stat.tvDist mu nu)]
  congr 1
  ring

-- @node: residual_mass_right
private lemma residual_mass_right
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    let xi := mu + nu
    let c := rnCommonPart mu nu xi
    (nu - c) Set.univ = ENNReal.ofReal (Causalean.Stat.tvDist mu nu) := by
  dsimp
  have hmu : mu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right _
  have hnu : nu ≪ mu + nu := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hc : rnCommonPart mu nu (mu + nu) ≤ nu :=
    rnCommonPart_le_right mu nu (mu + nu) hnu
  letI : IsFiniteMeasure (rnCommonPart mu nu (mu + nu)) :=
    isFiniteMeasure_of_le nu hc
  rw [Measure.sub_apply MeasurableSet.univ hc,
    rnCommonPart_mass_eq_one_sub_tvDist mu nu (mu + nu) hmu hnu]
  have htv0 := Causalean.Stat.tvDist_nonneg (μ := mu) (ν := nu)
  have htv1 := Causalean.Stat.tvDist_le_one (μ := mu) (ν := nu)
  rw [measure_univ, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - Causalean.Stat.tvDist mu nu)]
  congr 1
  ring

-- @node: maximalCoupling_map_fst
/-- The first marginal of the maximal coupling is the first law. -/
lemma maximalCoupling_map_fst
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (maximalCoupling mu nu).map Prod.fst = mu := by
  by_cases hzero : Causalean.Stat.tvDist mu nu = 0
  · rw [maximalCoupling, dif_pos hzero,
      Measure.map_map (μ := mu) (f := fun x : X => (x, x))
        (g := Prod.fst) measurable_fst (measurable_id.prodMk measurable_id)]
    change mu.map id = mu
    exact Measure.map_id
  · let xi := mu + nu
    let c := rnCommonPart mu nu xi
    let rmu := mu - c
    let rnu := nu - c
    have hmu : mu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right _
    have hc : c ≤ mu := rnCommonPart_le_left mu nu xi hmu
    letI : IsFiniteMeasure c := isFiniteMeasure_of_le mu hc
    have hrnu : rnu Set.univ =
        ENNReal.ofReal (Causalean.Stat.tvDist mu nu) := residual_mass_right mu nu
    rw [maximalCoupling, dif_neg hzero]
    dsimp only
    rw [Measure.map_add, Measure.map_smul, Measure.map_map, Measure.map_fst_prod,
      hrnu]
    rw [← mul_smul, ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne
        (Causalean.Stat.tvDist_nonneg (μ := mu) (ν := nu)) (Ne.symm hzero)))
      ENNReal.ofReal_ne_top, one_smul]
    rw [show (Prod.fst ∘ fun x : X => (x, x)) = id by rfl, Measure.map_id,
      add_comm, Measure.sub_add_cancel_of_le hc]
    all_goals fun_prop

-- @node: maximalCoupling_map_snd
/-- The second marginal of the maximal coupling is the second law. -/
lemma maximalCoupling_map_snd
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (maximalCoupling mu nu).map Prod.snd = nu := by
  by_cases hzero : Causalean.Stat.tvDist mu nu = 0
  · have heq : mu = nu := measure_eq_of_tvDist_eq_zero mu nu hzero
    rw [maximalCoupling, dif_pos hzero,
      Measure.map_map (μ := mu) (f := fun x : X => (x, x))
        (g := Prod.snd) measurable_snd (measurable_id.prodMk measurable_id)]
    change mu.map id = nu
    rw [Measure.map_id, heq]
  · let xi := mu + nu
    let c := rnCommonPart mu nu xi
    let rmu := mu - c
    let rnu := nu - c
    have hnu : nu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right' _
    have hc : c ≤ nu := rnCommonPart_le_right mu nu xi hnu
    letI : IsFiniteMeasure c := isFiniteMeasure_of_le nu hc
    have hrmu : rmu Set.univ =
        ENNReal.ofReal (Causalean.Stat.tvDist mu nu) := residual_mass mu nu
    rw [maximalCoupling, dif_neg hzero]
    dsimp only
    rw [Measure.map_add, Measure.map_smul, Measure.map_map, Measure.map_snd_prod,
      hrmu]
    rw [← mul_smul, ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne
        (Causalean.Stat.tvDist_nonneg (μ := mu) (ν := nu)) (Ne.symm hzero)))
      ENNReal.ofReal_ne_top, one_smul]
    rw [show (Prod.snd ∘ fun x : X => (x, x)) = id by rfl, Measure.map_id,
      add_comm, Measure.sub_add_cancel_of_le hc]
    all_goals fun_prop

-- @node: maximalCoupling.instIsProbabilityMeasure
noncomputable instance maximalCoupling.instIsProbabilityMeasure
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (maximalCoupling mu nu) := by
  constructor
  have h := congrArg (fun m : Measure X => m Set.univ)
    (maximalCoupling_map_fst mu nu)
  change ((maximalCoupling mu nu).map Prod.fst) Set.univ = mu Set.univ at h
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa using h

-- @node: maximalCoupling_eq_mass_ge
/-- The two coordinates of the maximal coupling agree with probability at
least one minus total variation. -/
lemma maximalCoupling_eq_mass_ge
    {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    ENNReal.ofReal (1 - Causalean.Stat.tvDist mu nu) ≤
      maximalCoupling mu nu {p | p.1 = p.2} := by
  let D : Set (X × X) := {p | p.1 = p.2}
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  change ENNReal.ofReal (1 - Causalean.Stat.tvDist mu nu) ≤
    maximalCoupling mu nu D
  by_cases hzero : Causalean.Stat.tvDist mu nu = 0
  · rw [maximalCoupling, dif_pos hzero, Measure.map_apply
      (μ := mu) (f := fun x : X => (x, x))
      (measurable_id.prodMk measurable_id) hD]
    simp [D, hzero]
  · let xi := mu + nu
    let c := rnCommonPart mu nu xi
    have hmu : mu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right _
    have hnu : nu ≪ xi := Measure.AbsolutelyContinuous.rfl.add_right' _
    have hcmass : c Set.univ =
        ENNReal.ofReal (1 - Causalean.Stat.tvDist mu nu) :=
      rnCommonPart_mass_eq_one_sub_tvDist mu nu xi hmu hnu
    rw [maximalCoupling, dif_neg hzero]
    dsimp only
    rw [Measure.add_apply]
    calc
      ENNReal.ofReal (1 - Causalean.Stat.tvDist mu nu) = c Set.univ := hcmass.symm
      _ = c.map (fun x => (x, x)) D := by
        rw [Measure.map_apply (μ := c) (f := fun x : X => (x, x))
          (measurable_id.prodMk measurable_id) hD]
        congr 1
        ext x
        simp [D]
      _ ≤ c.map (fun x => (x, x)) D +
          ((ENNReal.ofReal (Causalean.Stat.tvDist mu nu))⁻¹ •
            ((mu - c).prod (nu - c))) D := le_add_right le_rfl

/-- A maximal coupling of compressed laws, lifted through the two regular
conditional distributions back to the original observations. -/
-- @node: compressionCoupling
noncomputable def compressionCoupling
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    [MeasurableSpace S] [StandardBorelSpace S]
    (Q0 Q1 : Measure Z) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (compress : Z → S) (hcompress : Measurable compress) : Measure (Z × Z) := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure Q0
  letI mapProb0 : IsProbabilityMeasure (Q0.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  letI mapProb1 : IsProbabilityMeasure (Q1.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  let K0 := ProbabilityTheory.condDistrib id compress Q0
  let K1 := ProbabilityTheory.condDistrib id compress Q1
  let gamma := maximalCoupling (Q0.map compress) (Q1.map compress)
  exact ((K0.comap Prod.fst measurable_fst) ×ₖ
    (K1.comap Prod.snd measurable_snd)) ∘ₘ gamma

-- @node: condDistrib_id_comp_map_compress
private lemma condDistrib_id_comp_map_compress
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableSpace S] [StandardBorelSpace S]
    (Q : Measure Z) [IsProbabilityMeasure Q]
    (compress : Z → S) (hcompress : Measurable compress) :
    ProbabilityTheory.condDistrib id compress Q ∘ₘ (Q.map compress) = Q := by
  simpa using ProbabilityTheory.condDistrib_comp_map
    (μ := Q) (X := compress) (Y := id) hcompress.aemeasurable aemeasurable_id

-- @node: comap_comp_map_measure
private lemma comap_comp_map_measure
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (mu : Measure A) (f : A → B) (hf : Measurable f) (K : Kernel B C) :
    K.comap f hf ∘ₘ mu = K ∘ₘ (mu.map f) := by
  ext E hE
  rw [Measure.bind_apply hE (Kernel.aemeasurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _), lintegral_map
      (K.measurable_coe hE) hf]
  rfl

-- @node: compressionCoupling_map_fst
/-- The first marginal of the lifted compression coupling is the first raw
law. -/
lemma compressionCoupling_map_fst
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    [MeasurableSpace S] [StandardBorelSpace S]
    (Q0 Q1 : Measure Z) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (compress : Z → S) (hcompress : Measurable compress) :
    (compressionCoupling Q0 Q1 compress hcompress).map Prod.fst = Q0 := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure Q0
  letI mapProb0 : IsProbabilityMeasure (Q0.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  letI mapProb1 : IsProbabilityMeasure (Q1.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  let K0 := ProbabilityTheory.condDistrib id compress Q0
  let K1 := ProbabilityTheory.condDistrib id compress Q1
  let gamma := maximalCoupling (Q0.map compress) (Q1.map compress)
  rw [compressionCoupling, Measure.map_comp]
  change (((K0.comap Prod.fst measurable_fst) ×ₖ
      (K1.comap Prod.snd measurable_snd)).map Prod.fst) ∘ₘ gamma = Q0
  rw [← Kernel.fst_eq, Kernel.fst_prod]
  rw [comap_comp_map_measure gamma Prod.fst measurable_fst K0,
    maximalCoupling_map_fst]
  exact condDistrib_id_comp_map_compress Q0 compress hcompress
  all_goals fun_prop

-- @node: compressionCoupling_map_snd
/-- The second marginal of the lifted compression coupling is the second raw
law. -/
lemma compressionCoupling_map_snd
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    [MeasurableSpace S] [StandardBorelSpace S]
    (Q0 Q1 : Measure Z) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (compress : Z → S) (hcompress : Measurable compress) :
    (compressionCoupling Q0 Q1 compress hcompress).map Prod.snd = Q1 := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure Q0
  letI mapProb0 : IsProbabilityMeasure (Q0.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  letI mapProb1 : IsProbabilityMeasure (Q1.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  let K0 := ProbabilityTheory.condDistrib id compress Q0
  let K1 := ProbabilityTheory.condDistrib id compress Q1
  let gamma := maximalCoupling (Q0.map compress) (Q1.map compress)
  rw [compressionCoupling, Measure.map_comp]
  change (((K0.comap Prod.fst measurable_fst) ×ₖ
      (K1.comap Prod.snd measurable_snd)).map Prod.snd) ∘ₘ gamma = Q1
  rw [← Kernel.snd_eq, Kernel.snd_prod]
  rw [comap_comp_map_measure gamma Prod.snd measurable_snd K1,
    maximalCoupling_map_snd]
  exact condDistrib_id_comp_map_compress Q1 compress hcompress
  all_goals fun_prop

-- @node: compressionCoupling_map_compress_pair
/-- Compressing both coordinates of the lifted coupling recovers the maximal
coupling of the compressed laws. -/
lemma compressionCoupling_map_compress_pair
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    [MeasurableSpace S] [StandardBorelSpace S]
    (Q0 Q1 : Measure Z) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (compress : Z → S) (hcompress : Measurable compress)
    [IsProbabilityMeasure (Q0.map compress)] [IsProbabilityMeasure (Q1.map compress)] :
    (compressionCoupling Q0 Q1 compress hcompress).map
        (Prod.map compress compress) =
      maximalCoupling (Q0.map compress) (Q1.map compress) := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure Q0
  letI : Nonempty S := nonempty_of_isProbabilityMeasure (Q0.map compress)
  letI mapProb0 : IsProbabilityMeasure (Q0.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  letI mapProb1 : IsProbabilityMeasure (Q1.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  let K0 := ProbabilityTheory.condDistrib id compress Q0
  let K1 := ProbabilityTheory.condDistrib id compress Q1
  let gamma := maximalCoupling (Q0.map compress) (Q1.map compress)
  have hK0 : K0.map compress =ᵐ[Q0.map compress] Kernel.id := by
    exact (ProbabilityTheory.condDistrib_comp (μ := Q0) (Y := id)
      compress aemeasurable_id hcompress).symm.trans
        (ProbabilityTheory.condDistrib_self (μ := Q0) compress)
  have hK1 : K1.map compress =ᵐ[Q1.map compress] Kernel.id := by
    exact (ProbabilityTheory.condDistrib_comp (μ := Q1) (Y := id)
      compress aemeasurable_id hcompress).symm.trans
        (ProbabilityTheory.condDistrib_self (μ := Q1) compress)
  have hK0gamma : ∀ᵐ p ∂gamma, K0.map compress p.1 = Kernel.id p.1 := by
    rw [← maximalCoupling_map_fst (Q0.map compress) (Q1.map compress)] at hK0
    exact ae_of_ae_map measurable_fst.aemeasurable hK0
  have hK1gamma : ∀ᵐ p ∂gamma, K1.map compress p.2 = Kernel.id p.2 := by
    rw [← maximalCoupling_map_snd (Q0.map compress) (Q1.map compress)] at hK1
    exact ae_of_ae_map measurable_snd.aemeasurable hK1
  rw [compressionCoupling]
  rw [Measure.map_comp _ _ (hcompress.prodMap hcompress)]
  calc
    _ = Kernel.id ∘ₘ gamma := by
      apply Measure.comp_congr
      filter_upwards [hK0gamma, hK1gamma] with p hp0 hp1
      change (((K0.comap Prod.fst measurable_fst) ×ₖ
          (K1.comap Prod.snd measurable_snd)).map
            (Prod.map compress compress)) p = Kernel.id p
      rw [← Kernel.map_prod_map]
      rw [Kernel.prod_apply,
        Kernel.map_apply _ hcompress, Kernel.map_apply _ hcompress,
        Kernel.comap_apply, Kernel.comap_apply, Kernel.id_apply]
      rw [Kernel.map_apply _ hcompress] at hp0 hp1
      rw [hp0, hp1]
      exact Measure.dirac_prod_dirac
      all_goals fun_prop
    _ = gamma := Measure.id_comp

-- @node: compressionCoupling.instIsProbabilityMeasure
noncomputable instance compressionCoupling.instIsProbabilityMeasure
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    [MeasurableSpace S] [StandardBorelSpace S]
    (Q0 Q1 : Measure Z) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (compress : Z → S) (hcompress : Measurable compress) :
    IsProbabilityMeasure (compressionCoupling Q0 Q1 compress hcompress) := by
  constructor
  have h := congrArg (fun m : Measure Z => m Set.univ)
    (compressionCoupling_map_fst Q0 Q1 compress hcompress)
  change ((compressionCoupling Q0 Q1 compress hcompress).map Prod.fst) Set.univ =
    Q0 Set.univ at h
  rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa using h

-- @node: compressionCoupling_equal_compression_mass_ge
/-- In the lifted coupling, the compressed observations agree with probability
at least one minus the total variation of their compressed laws. -/
lemma compressionCoupling_equal_compression_mass_ge
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    [MeasurableSpace S] [StandardBorelSpace S]
    (Q0 Q1 : Measure Z) [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (compress : Z → S) (hcompress : Measurable compress) :
    ENNReal.ofReal
        (1 - Causalean.Stat.tvDist (Q0.map compress) (Q1.map compress)) ≤
      compressionCoupling Q0 Q1 compress hcompress
        {p | compress p.1 = compress p.2} := by
  letI mapProb0 : IsProbabilityMeasure (Q0.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  letI mapProb1 : IsProbabilityMeasure (Q1.map compress) :=
    Measure.isProbabilityMeasure_map hcompress.aemeasurable
  letI : MeasurableEq S := measurableEqOfStandardBorel S
  let D : Set (S × S) := {p | p.1 = p.2}
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  have hmap := compressionCoupling_map_compress_pair Q0 Q1 compress hcompress
  have happ := congrArg (fun m : Measure (S × S) => m D) hmap
  change ((compressionCoupling Q0 Q1 compress hcompress).map
      (Prod.map compress compress)) D =
    maximalCoupling (Q0.map compress) (Q1.map compress) D at happ
  rw [Measure.map_apply (hcompress.prodMap hcompress) hD] at happ
  have hpre : (Prod.map compress compress) ⁻¹' D =
      {p : Z × Z | compress p.1 = compress p.2} := by
    ext p
    rfl
  rw [hpre] at happ
  rw [happ]
  exact maximalCoupling_eq_mass_ge (Q0.map compress) (Q1.map compress)

end Causalean.Stat
