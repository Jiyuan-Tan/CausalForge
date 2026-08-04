import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Learner.PredictionPolytope
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.UniformGibbsSupport
import Causalean.Stat.Concentration.Covering.CoveringNumber
import Causalean.Stat.Concentration.ConditionalProjectionTail
import Causalean.Stat.Concentration.TailBounds.Bernstein
import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Conditional
import Mathlib.Topology.Metrizable.Basic

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators Topology

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

/-- The paper's failure schedule. -/
noncomputable def failureProbability (n : ℕ) (_hn : 1 ≤ n) : ℝ :=
  ((n : ℝ) ^ 2)⁻¹
  -- @realizes \delta_n(domain 1≤n; value δ_n=n⁻² on that domain)

noncomputable def iidProduct {W : Type*} [MeasurableSpace W]
    (μ : Measure W) (hμ : IsProbabilityMeasure μ) (n : ℕ) :
    Measure (Fin n → W) := by
  letI : IsProbabilityMeasure μ := hμ
  exact Measure.pi (fun _ : Fin n => μ)

/-- The finite state-action law `ρ × π` appearing in Zhao et al.'s lemma. -/
noncomputable def finiteContextActionLaw
    (rho : 𝒳 → ℝ) (pi : Policy 𝒳 𝒜) : Measure (𝒳 × 𝒜) :=
  ∑ x, ∑ a,
    (ENNReal.ofReal (rho x * pi x a)) • Measure.dirac (x, a)

/-- Supremum-norm covering number, defined directly by finite nets. -/
noncomputable def supCoveringNumber
    (G : Set (𝒳 → 𝒜 → ℝ)) (u : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ net : Finset (𝒳 → 𝒜 → ℝ), net.card = k ∧
    ∀ g ∈ G, ∃ h ∈ net, ∀ x a, |g x a - h x a| ≤ u}

-- @node: lem:zhao-uniform-square-comparison
/-- Cited interface: Zhao, Ji, Zhao, Zhang, and Gu (2026), Appendix D.1,
Lemma D.1, arXiv:2502.06051v3 (`ZhaoJiZhaoZhangGu2026SharpFDivergence`).
It states the simultaneous empirical-to-population squared-difference bound,
including the `32/(3n)` logarithmic and `10u` remainder terms. -/
def ZhaoUniformSquareComparison : Prop :=
  ∀ (rho : 𝒳 → ℝ) (pi : Policy 𝒳 𝒜)
    (hrho_nonneg : ∀ x, 0 ≤ rho x) (hrho_mass : ∑ x, rho x = 1)
    (hpi : IsPolicy pi)
    (hμ : IsProbabilityMeasure (finiteContextActionLaw rho pi))
    (G : Set (𝒳 → 𝒜 → ℝ)) (n : ℕ) (u delta : ℝ),
    0 < n →
    G ⊆ {g | ∀ x a, g x a ∈ Set.Icc (0 : ℝ) 1} →
    0 < u → u < 1 → 0 < delta → delta < 1 →
    (iidProduct (finiteContextActionLaw rho pi) hμ n).real
      {sample | ∀ g₁ ∈ G, ∀ g₂ ∈ G,
        (∫ w, (g₁ w.1 w.2 - g₂ w.1 w.2) ^ 2
          ∂finiteContextActionLaw rho pi) ≤
          2 / n * ∑ i, (g₁ (sample i).1 (sample i).2 -
            g₂ (sample i).1 (sample i).2) ^ 2 +
          32 / (3 * n) *
            Real.log (2 * supCoveringNumber G u / delta) + 10 * u}
      ≥ 1 - delta

/-- Conditional boundedness, centering, and independence relative to an
arbitrary conditioning sub-σ-field.  Centering is stated fiberwise through
Mathlib's regular conditional-distribution kernel. -/
def ProjectionNoiseConditions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (eps : Fin n → Ω → ℝ) : Prop :=
  (∀ i, Measurable (eps i)) ∧
  (∀ i, ∀ᵐ ω ∂μ, |eps i ω| ≤ 1) ∧
  (∀ i, ∀ᵐ ω ∂μ.trim hm,
    ∫ ω', eps i ω'
      ∂ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m ω = 0) ∧
  ProbabilityTheory.iCondIndepFun m hm eps (μ := μ)

/-- A Gram factorization through at most `r` directions, used as the
finite-dimensional rank bound for the projector. -/
def ProjectorRankAtMost (Pi : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : Prop :=
  ∃ vectors : Fin r → Fin n → ℝ,
    ∀ i j, Pi i j = ∑ k, vectors k i * vectors k j

-- @node: lem:bounded-projection-concentration
lemma bounded_projection_concentration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (eps : Fin n → Ω → ℝ)
    (Pi : Ω → Matrix (Fin n) (Fin n) ℝ)
    (rankBound : ℕ) (zeta : ℝ)
    (hnoise : ProjectionNoiseConditions (mΩ := mΩ) μ m hm eps)
    (hPiMeasurable : ∀ i j, Measurable[m] fun ω => Pi ω i j)
    (hproj : ∀ᵐ ω ∂μ.trim hm,
      Pi ω * Pi ω = Pi ω ∧ (Pi ω).transpose = Pi ω)
    (hrank : ∀ᵐ ω ∂μ.trim hm, ProjectorRankAtMost (Pi ω) rankBound)
    (hzeta : 0 < zeta) :
    ∀ᵐ ω ∂μ.trim hm,
      (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m ω).real
        {ω' |
          8 * (rankBound * Real.log 5 + Real.log (2 / zeta)) <
            ∑ i, (∑ j, Pi ω' i j * eps j ω') ^ 2} ≤ zeta := by
  rcases hnoise with ⟨hmeas, hbound, hcenter, hindep⟩
  have hmeas' : ∀ i, @Measurable Ω ℝ mΩ _ (eps i) :=
    fun i ↦ (hmeas i).mono hm le_rfl
  have hidem : ∀ᵐ ω ∂μ.trim hm, Pi ω * Pi ω = Pi ω :=
    hproj.mono fun _ hω ↦ hω.1
  have hsymm : ∀ᵐ ω ∂μ.trim hm, (Pi ω).transpose = Pi ω :=
    hproj.mono fun _ hω ↦ hω.2
  have hrank' : ∀ᵐ ω ∂μ.trim hm, Matrix.rank (Pi ω) ≤ rankBound := by
    filter_upwards [hrank] with ω hω
    rcases hω with ⟨vectors, hfactor⟩
    exact Causalean.Stat.Concentration.matrix_rank_le_of_gram_factor
      (Pi ω) vectors hfactor
  exact @Causalean.Stat.Concentration.ae_condExpKernel_projection_energy_gt_le
    Ω mΩ _ μ _ m hm n rankBound eps Pi hmeas' hbound hcenter hindep
      hPiMeasurable hsymm hidem hrank' zeta hzeta

/-- Cell count in a finite sample. -/
def cellCount {m : ℕ} (sample : Fin (m ^ 2) → Fin m) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun i => sample i = j).card

-- @node: lem:multinomial-max-count
lemma multinomial_max_count
    (m : ℕ) (hm : 0 < m) (μ : Measure (Fin m))
    (hμ : IsProbabilityMeasure μ)
    (hunif : ∀ j, μ.real {j} = 1 / m) :
    (iidProduct μ hμ (m ^ 2)).real
        {sample | ∃ j, 3 * m < cellCount sample j} ≤
      m * Real.exp (-(m : ℝ) * (3 * Real.log 3 - 2)) ∧
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) * Real.exp (-(m : ℝ) * (3 * Real.log 3 - 2)))
      Filter.atTop (nhds 0) := by
  let ν : Measure (ℕ → Fin m) := Measure.infinitePi (fun _ : ℕ => μ)
  let S : Causalean.Stat.IIDSample (ℕ → Fin m) (Fin m) ν μ :=
    Causalean.Stat.iidSample_infinitePi μ
  let Ψ : (ℕ → Fin m) → (Fin (m ^ 2) → Fin m) :=
    fun ω k => S.Z k ω
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  letI : IsProbabilityMeasure ν := hν
  have hΨ : Measurable Ψ :=
    Causalean.Stat.iidSample_finN_measurable S (m ^ 2)
  have hpush :
      Measure.map Ψ ν = Measure.pi (fun _ : Fin (m ^ 2) => μ) := by
    exact Causalean.Stat.iidSample_finN_pushforward S (m ^ 2)
  have hcell (j : Fin m) :
      (iidProduct μ hμ (m ^ 2)).real
          {sample | 3 * m < cellCount sample j} ≤
        Real.exp (-(m : ℝ) * (3 * Real.log 3 - 2)) := by
    let f : Fin m → ℝ := fun k => if k = j then 1 else 0
    have hf : Measurable f := measurable_of_finite f
    have hf01 : ∀ k, f k ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      simp only [f, Set.mem_Icc]
      split_ifs <;> norm_num
    have hmean : ∫ k, f k ∂μ = 1 / m := by
      rw [show f = ({j} : Set (Fin m)).indicator (fun _ => (1 : ℝ)) by
        funext k
        simp [f, Set.indicator]]
      calc
        (∫ k, ({j} : Set (Fin m)).indicator (fun _ => (1 : ℝ)) k ∂μ) =
            μ.real {j} := by
          simpa only using
            (integral_indicator_one (μ := μ) (MeasurableSet.singleton j))
        _ = 1 / m := hunif j
    have htail :=
      Causalean.Stat.Concentration.boundedCount_upper_tail_of_tilt S hf hf01
        hmean.le (m ^ 2) (Real.log 3) (Real.log_nonneg (by norm_num))
        (a := (3 * m : ℕ))
    have hpre :
        Ψ ⁻¹' {sample | 3 * m < cellCount sample j} =
          {ω | ((3 * m : ℕ) : ℝ) <
            Causalean.Stat.Concentration.bernoulliCount S f (m ^ 2) ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      have hcount :
          (cellCount (Ψ ω) j : ℝ) =
            Causalean.Stat.Concentration.bernoulliCount S f (m ^ 2) ω := by
        simp only [cellCount, Causalean.Stat.Concentration.bernoulliCount,
          Finset.cast_card]
        calc
          (∑ x ∈ Finset.univ.filter (fun i => Ψ ω i = j), (1 : ℝ)) =
              ∑ i : Fin (m ^ 2), if Ψ ω i = j then 1 else 0 := by simp
          _ = ∑ i ∈ Finset.range (m ^ 2),
              if S.Z i ω = j then 1 else 0 := by
            simpa [Ψ] using
              (Fin.sum_univ_eq_sum_range
                (fun i => if S.Z i ω = j then (1 : ℝ) else 0) (m ^ 2))
          _ = ∑ i ∈ Finset.range (m ^ 2), f (S.Z i ω) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [f]
      rw [← hcount, Nat.cast_lt]
    have hset : MeasurableSet {sample : Fin (m ^ 2) → Fin m |
        3 * m < cellCount sample j} :=
      Set.toFinite _ |>.measurableSet
    have hmeasure :
        (iidProduct μ hμ (m ^ 2)).real
            {sample | 3 * m < cellCount sample j} =
          ν.real (Ψ ⁻¹' {sample | 3 * m < cellCount sample j}) := by
      change ((iidProduct μ hμ (m ^ 2))
          {sample | 3 * m < cellCount sample j}).toReal =
        (ν (Ψ ⁻¹' {sample | 3 * m < cellCount sample j})).toReal
      congr 1
      unfold iidProduct
      rw [← hpush, Measure.map_apply hΨ hset]
    rw [hmeasure, hpre]
    calc
      ν.real {ω | ((3 * m : ℕ) : ℝ) <
          Causalean.Stat.Concentration.bernoulliCount S f (m ^ 2) ω}
          ≤ Real.exp
              (-Real.log 3 * ((3 * m : ℕ) : ℝ) +
                ((m ^ 2 : ℕ) : ℝ) *
                  (1 / (m : ℝ) * (Real.exp (Real.log 3) - 1))) := htail
      _ = Real.exp (-(m : ℝ) * (3 * Real.log 3 - 2)) := by
        congr 1
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        push_cast
        have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
        field_simp
        ring
  constructor
  · have hunion :
        {sample : Fin (m ^ 2) → Fin m | ∃ j, 3 * m < cellCount sample j} =
          ⋃ j : Fin m, {sample | 3 * m < cellCount sample j} := by
      ext sample
      simp
    rw [hunion]
    calc
      (iidProduct μ hμ (m ^ 2)).real
          (⋃ j : Fin m, {sample | 3 * m < cellCount sample j})
          ≤ ∑ j : Fin m,
              (iidProduct μ hμ (m ^ 2)).real
                {sample | 3 * m < cellCount sample j} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin m,
              Real.exp (-(m : ℝ) * (3 * Real.log 3 - 2)) := by
        gcongr with j
        exact hcell j
      _ = m * Real.exp (-(m : ℝ) * (3 * Real.log 3 - 2)) := by simp
  · have hc : 0 < 3 * Real.log 3 - 2 := by
      have h23 : Real.log 2 < Real.log 3 :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      nlinarith [Real.log_two_gt_d9]
    have hr0 : 0 ≤ Real.exp (-(3 * Real.log 3 - 2)) :=
      (Real.exp_pos _).le
    have hr1 : Real.exp (-(3 * Real.log 3 - 2)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (neg_neg_of_pos hc)
    convert tendsto_self_mul_const_pow_of_lt_one hr0 hr1 using 1
    ext k
    rw [← Real.exp_nat_mul]
    congr 1
    ring

/-- Gibbs-weighted squared radius used by the stabilized learner. -/
noncomputable def gibbsRadius
    (E : CommonExperiment d 𝒳 𝒜) (g f : 𝒳 → 𝒜 → ℝ) (x : 𝒳) : ℝ :=
  ∑ a,
    (E.reference x a * Real.exp (E.eta * g x a) /
      ∑ b, E.reference x b * Real.exp (E.eta * g x b)) *
      (g x a - f x a) ^ 2

/-- The explicit two-sided radius-comparison remainder. -/
noncomputable def gibbsRadiusRemainder (d n : ℕ) (eta zeta : ℝ) : ℝ :=
  8 / (3 * n) *
    (Real.log (2 / zeta) + 2 * d * Real.log (1 + 4 * n * (eta + 2))) + 3 / n

-- @node: linearReward_mem_predictionPolytope
lemma linearReward_mem_predictionPolytope
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) :
    linearReward P ∈ predictionPolytope E := by
  refine ⟨hshell.linearRealizability.1, P.theta, ?_⟩
  intro x a
  rfl

-- @node: empiricalSeminormSq_sub_triangle
lemma empiricalSeminormSq_sub_triangle
    (sample : LoggedSample n 𝒳 𝒜)
    (f g h : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    empiricalSeminormSq sample (fun x a => f x a - h x a) ≤
      2 * empiricalSeminormSq sample (fun x a => f x a - g x a) +
      2 * empiricalSeminormSq sample (fun x a => g x a - h x a) := by
  unfold empiricalSeminormSq
  by_cases hn : n = 0
  · subst n
    simp
  · have hninv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    calc
      (n : ℝ)⁻¹ * ∑ i,
          (f (sample i).context (sample i).action -
            h (sample i).context (sample i).action) ^ 2 ≤
          (n : ℝ)⁻¹ * ∑ i,
            (2 * (f (sample i).context (sample i).action -
                g (sample i).context (sample i).action) ^ 2 +
              2 * (g (sample i).context (sample i).action -
                h (sample i).context (sample i).action) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hninv
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg
          ((f (sample i).context (sample i).action -
              g (sample i).context (sample i).action) -
            (g (sample i).context (sample i).action -
              h (sample i).context (sample i).action))]
      _ = 2 * ((n : ℝ)⁻¹ * ∑ i,
            (f (sample i).context (sample i).action -
              g (sample i).context (sample i).action) ^ 2) +
          2 * ((n : ℝ)⁻¹ * ∑ i,
            (g (sample i).context (sample i).action -
              h (sample i).context (sample i).action) ^ 2) := by
        rw [Finset.sum_add_distrib]
        simp_rw [← Finset.mul_sum]
        ring

-- @node: lem:uniform-gibbs-radius-comparison
lemma uniform_gibbs_radius_comparison
    (E : CommonExperiment d 𝒳 𝒜)
    (rho : Measure 𝒳) (hrho : IsProbabilityMeasure rho)
    (zeta : ℝ) (hzeta : 0 < zeta) (hn : 0 < n) :
    (iidProduct rho hrho n).real
      {sample | ∀ g ∈ predictionPolytope E, ∀ f ∈ predictionPolytope E,
        (∫ x, gibbsRadius E g f x ∂rho) ≤
            2 * ((n : ℝ)⁻¹ * ∑ i, gibbsRadius E g f (sample i)) +
              gibbsRadiusRemainder d n E.eta zeta ∧
        ((n : ℝ)⁻¹ * ∑ i, gibbsRadius E g f (sample i)) ≤
            2 * (∫ x, gibbsRadius E g f x ∂rho) +
              gibbsRadiusRemainder d n E.eta zeta}
      ≥ 1 - zeta := by
  simpa [iidProduct, gibbsRadius, gibbsRadiusRemainder,
    substrateGibbsRadius, substrateGibbsRemainder] using
    substrate_uniform_gibbs_radius_comparison E rho hrho zeta hzeta hn

end CausalSmith.Stat.ReverseKLTwoCoverage
