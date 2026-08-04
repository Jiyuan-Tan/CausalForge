import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenter
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral

/-!
# Continuous-baseline least-favourable block family

The compressed prior-predictive law on the sufficient statistic `(Z,(Y_b))`
is defined explicitly as a density with respect to counting measure times
finite-dimensional Lebesgue measure.  The paper's full observed-data law on
`(Z,(Y_i^{obs}))` is its pushforward under repetition of each active block
outcome and zero extension to the inactive units.
-/

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

/-- Number of complete active blocks. -/
def blockCount (n d : ℕ) : ℕ := n / d
-- @realizes m(floor n/d)

/-- Number of active units. -/
def activeCount (n d : ℕ) : ℕ := blockCount n d * d
-- @realizes q(m d)

/-- Active population share. -/
noncomputable def activeShare (n d : ℕ) : ℝ :=
  (activeCount n d : ℝ) / n
-- @realizes \rho(q/n)

/-- The complete directed block graph, including loops, on active units;
inactive units are isolated. -/
def blockGraph (n d : ℕ) (j i : Fin n) : Prop :=
  j.val < activeCount n d ∧ i.val < activeCount n d ∧
    j.val / d = i.val / d
-- @realizes G_{n,d}^{\mathrm{blk}}(complete directed blocks with loops)
-- @realizes V_b(active block of size d)
-- @realizes b(block index)

/-- A baseline value indexed by a natural block number, zero outside the
typed block range. -/
noncomputable def baselineAt {m : ℕ} (U : Fin m → ℝ) (b : ℕ) : ℝ :=
  if h : b < m then U ⟨b, h⟩ else 0
-- @realizes U_b(block-specific baseline)

/-- The cosine-squared density on `[-s,s]`. -/
noncomputable def cosSqDensity (s u : ℝ) : ℝ :=
  if |u| ≤ s then s⁻¹ * Real.cos (Real.pi * u / (2 * s)) ^ 2 else 0
-- @realizes f_s(cosine-squared compactly supported density)
-- @realizes s(positive baseline halfwidth B/2)

lemma cosSqDensity_measurable (s : ℝ) :
    Measurable (cosSqDensity s) := by
  rw [show cosSqDensity s =
      Set.indicator (Set.Icc (-s) s)
        (fun u => s⁻¹ * Real.cos (Real.pi * u / (2 * s)) ^ 2) by
    funext u
    rw [cosSqDensity]
    by_cases hu : |u| ≤ s
    · rw [if_pos hu, Set.indicator_of_mem]
      simpa [abs_le] using hu
    · rw [if_neg hu, Set.indicator_of_notMem]
      simpa [abs_le] using hu]
  exact (by fun_prop : Measurable fun u =>
    s⁻¹ * Real.cos (Real.pi * u / (2 * s)) ^ 2).indicator measurableSet_Icc

/-- Establishes the stated mathematical result for cos sq density integrable. -/
lemma cosSqDensity_integrable (s : ℝ) :
    Integrable (cosSqDensity s) := by
  rw [show cosSqDensity s =
      Set.indicator (Set.Icc (-s) s)
        (fun u => s⁻¹ * Real.cos (Real.pi * u / (2 * s)) ^ 2) by
    funext u
    rw [cosSqDensity]
    by_cases hu : |u| ≤ s
    · rw [if_pos hu, Set.indicator_of_mem]
      simpa [abs_le] using hu
    · rw [if_neg hu, Set.indicator_of_notMem]
      simpa [abs_le] using hu]
  exact ((by fun_prop : Continuous fun u =>
      s⁻¹ * Real.cos (Real.pi * u / (2 * s)) ^ 2).continuousOn
    |>.integrableOn_Icc).integrable_indicator measurableSet_Icc

/-- Establishes the stated mathematical result for cos sq density integral one. -/
lemma cosSqDensity_integral_one (s : ℝ) (hs : 0 < s) :
    ∫ u, cosSqDensity s u = 1 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [show cosSqDensity s =
      Set.indicator (Set.Icc (-s) s)
        (fun u => s⁻¹ * Real.cos (Real.pi * u / (2 * s)) ^ 2) by
    funext u
    rw [cosSqDensity]
    by_cases hu : |u| ≤ s
    · rw [if_pos hu, Set.indicator_of_mem]
      simpa [abs_le] using hu
    · rw [if_neg hu, Set.indicator_of_notMem]
      simpa [abs_le] using hu]
  rw [integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : -s ≤ s)]
  rw [intervalIntegral.integral_const_mul]
  have hc : Real.pi / (2 * s) ≠ 0 := div_ne_zero hpi (by positivity)
  rw [show
      (fun u => Real.cos (Real.pi * u / (2 * s)) ^ 2) =
        (fun u => Real.cos ((Real.pi / (2 * s)) * u) ^ 2) by
    funext u
    congr 2
    field_simp]
  rw [intervalIntegral.integral_comp_mul_left
    (fun x => Real.cos x ^ 2) hc]
  rw [show (Real.pi / (2 * s)) * -s = -(Real.pi / 2) by
      field_simp,
    show (Real.pi / (2 * s)) * s = Real.pi / 2 by
      field_simp]
  rw [integral_cos_sq]
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  norm_num [smul_eq_mul]
  field_simp
  noncomm_ring

/-- Establishes the stated mathematical result for cos sq density translate integral one. -/
lemma cosSqDensity_translate_integral_one
    (s c : ℝ) (hs : 0 < s) :
    ∫ u, cosSqDensity s (u - c) = 1 := by
  rw [show (fun u => cosSqDensity s (u - c)) =
      (fun u => cosSqDensity s (u + (-c))) by
    funext u
    congr 2]
  rw [integral_add_right_eq_self]
  exact cosSqDensity_integral_one s hs

/-- Establishes the stated mathematical result for cos sq density translate integrable. -/
lemma cosSqDensity_translate_integrable (s c : ℝ) :
    Integrable (fun u => cosSqDensity s (u - c)) := by
  simpa [sub_eq_add_neg] using
    (cosSqDensity_integrable s).comp_add_right (-c)

/-- Raw coefficient mass of the normalized block representer. -/
noncomputable def representerMass (β : ℕ) (p : ℝ) (d : ℕ) : ℝ :=
  ∑ T ∈ Finset.univ.powerset, |blockRawCoef β p d T|

/-- The paper's exact representer-mass constant
`sup_{d≥1} ∑_T |h_{d,T}|`. -/
noncomputable def representerMassSup (β : ℕ) (p : ℝ) : ℝ :=
  sSup (Set.range fun d : {d : ℕ // 1 ≤ d} =>
    representerMass β p d.1)
-- @realizes H_{\beta,p}(exact supremum over d≥1 of raw-coefficient mass)

/-- The score-aligned tilt amplitude. -/
noncomputable def tiltAmplitude
    (B : ℝ) (β : ℕ) (p : ℝ) (m d : ℕ) : ℝ :=
  B * min ((2 * representerMassSup β p)⁻¹) ((4 * Real.pi)⁻¹) *
    min 1 (Real.sqrt (blockEnergy β p d / m))
-- @realizes \delta(B κ min{1,sqrt(A_d/m)})

/-- Map a global subset to its within-block coordinate subset. -/
noncomputable def localSubset (n d : ℕ) (T : Finset (Fin n)) :
    Finset (Fin d) :=
  if hd : 0 < d then
    T.image (fun j => ⟨j.val % d, Nat.mod_lt _ hd⟩)
  else ∅

/-- The score-aligned coefficient schedule for one fixed baseline vector and
one sign. -/
noncomputable def blockSchedule
    (n d β : ℕ) (B p σ : ℝ)
    (_hσ : σ = -1 ∨ σ = 1) -- @realizes \sigma(range {-1,1})
    (U : Fin (blockCount n d) → ℝ)
    (i : Fin n) (T : Finset (Fin n)) : ℝ :=
  if hi : i.val < activeCount n d then
    if hT : ∀ j ∈ T, j.val < activeCount n d ∧ j.val / d = i.val / d then
      (if T = ∅ then baselineAt U (i.val / d) else 0) +
        σ * tiltAmplitude B β p (blockCount n d) d *
          blockRawCoef β p d (localSubset n d T)
    else 0
  else 0

/-- The independent cosine-squared baseline law on the active block
coefficients. -/
-- @env: S4
noncomputable def blockBaselineLaw (B : ℝ) (m : ℕ) :
    Measure (Fin m → ℝ) :=
  Measure.pi (fun _ : Fin m =>
    volume.withDensity (fun u => ENNReal.ofReal (cosSqDensity (B / 2) u)))

/-- The fuzzy prior on fixed coefficient schedules, obtained by pushing the
independent baseline law through the score-aligned schedule construction. -/
noncomputable def blockSchedulePrior
    (n d β : ℕ) (B p σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
    Measure (Fin n → Finset (Fin n) → ℝ) :=
  Measure.map
    (fun U : Fin (blockCount n d) → ℝ =>
      blockSchedule n d β B p σ hσ U)
    (blockBaselineLaw B (blockCount n d))
-- @realizes \Pi_\sigma(prior on fixed score-aligned schedules)

/-- Mechanical anchor for the complete least-favourable block construction:
block count, active count and share, complete-block graph, and prior on fixed
coefficient schedules. -/
-- @node: def:block-family
noncomputable def blockFamilyBundle
    (n d β : ℕ) (B p σ : ℝ)
    (hB : 0 < B) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hσ : σ = -1 ∨ σ = 1) :
    ℕ × ℕ × ℝ × (Fin n → Fin n → Prop) ×
      Measure (Fin n → Finset (Fin n) → ℝ) :=
  (blockCount n d, activeCount n d, activeShare n d, blockGraph n d,
    blockSchedulePrior n d β B p σ hσ)

/-- Restrict a global assignment to a typed active block. -/
def blockAssignment
    (n d : ℕ) (b : Fin (blockCount n d)) (z : Fin n → Bool) :
    Fin d → Bool :=
  fun j =>
    z ⟨b.val * d + j.val, by
      have hb : b.val < n / d := by
        simpa [blockCount] using b.isLt
      have hj : j.val < d := j.isLt
      have hmul : (n / d) * d ≤ n := Nat.div_mul_le_self n d
      calc
        b.val * d + j.val < b.val * d + d := Nat.add_lt_add_left hj _
        _ = (b.val + 1) * d := by simp [Nat.add_mul]
        _ ≤ (n / d) * d := Nat.mul_le_mul_right d hb
        _ ≤ n := hmul⟩

/-- Product Bernoulli mass of one assignment. -/
noncomputable def assignmentMass (n : ℕ) (p : ℝ) (z : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, if z i then p else 1 - p

/-- Density of the sufficient observed statistic under one prior sign. -/
noncomputable def blockPriorDensity
    (n d β : ℕ) (B p σ : ℝ)
    (x : (Fin n → Bool) × (Fin (blockCount n d) → ℝ)) : ℝ :=
  assignmentMass n p x.1 *
    ∏ b : Fin (blockCount n d),
      cosSqDensity (B / 2)
        (x.2 b - σ * tiltAmplitude B β p (blockCount n d) d *
          blockRepresenter β p d (blockAssignment n d b x.1))
-- @realizes s(halfwidth pinned to B/2 here; positive whenever B > 0)

/-- The common counting-times-Lebesgue dominating measure. -/
noncomputable def blockDominatingMeasure (n d : ℕ) :
    Measure ((Fin n → Bool) × (Fin (blockCount n d) → ℝ)) :=
  Measure.count.prod (Measure.pi (fun _ : Fin (blockCount n d) => volume))

/-- The prior-predictive law of assignment and repeated block outcomes. -/
noncomputable def blockPriorLaw
    (n d β : ℕ) (B p σ : ℝ) :
    Measure ((Fin n → Bool) × (Fin (blockCount n d) → ℝ)) :=
  (blockDominatingMeasure n d).withDensity
    (fun x => ENNReal.ofReal (blockPriorDensity n d β B p σ x))

/-- Repeat each active block's observed outcome across its `d` units and set
the outcomes of the inactive remainder to zero. -/
noncomputable def repeatedBlockOutcome
    (n d : ℕ) (y : Fin (blockCount n d) → ℝ) : Fin n → ℝ :=
  fun i => baselineAt y (i.val / d)

/-- Expand the sufficient observed statistic to the full observed data. -/
noncomputable def repeatedBlockObservedData
    (n d : ℕ)
    (x : (Fin n → Bool) × (Fin (blockCount n d) → ℝ)) :
    (Fin n → Bool) × (Fin n → ℝ) :=
  (x.1, repeatedBlockOutcome n d x.2)

/-- The full prior-predictive law of assignment and all `n` observed
outcomes, obtained from the compressed block-statistic law by the deterministic
repeated-block-outcome map. -/
-- @realizes P_\sigma(prior-predictive Measure on assignments × full observed outcomes)
noncomputable def priorPredictiveLaw
    (n d β : ℕ) (B p σ : ℝ) :
    Measure ((Fin n → Bool) × (Fin n → ℝ)) :=
  Measure.map (repeatedBlockObservedData n d)
    (blockPriorLaw n d β B p σ)

/-- The displayed density representation of `blockPriorLaw`. -/
lemma blockPriorLaw_eq_withDensity
    (n d β : ℕ) (B p σ : ℝ) :
    blockPriorLaw n d β B p σ =
      (blockDominatingMeasure n d).withDensity
        (fun x => ENNReal.ofReal (blockPriorDensity n d β B p σ x)) := by
  rfl

/-- Under the paper's parameter restrictions the prior density integrates to
one against the common dominating measure. -/
lemma blockPriorDensity_integral_one
    (n d β : ℕ) (B p σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdn : d ≤ n)
    (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (hσ : σ = -1 ∨ σ = 1) :
    ∫ x, blockPriorDensity n d β B p σ x ∂blockDominatingMeasure n d = 1 := by
  classical
  let s : ℝ := B / 2
  have hs : 0 < s := by dsimp [s]; linarith
  let shift : (Fin n → Bool) → Fin (blockCount n d) → ℝ :=
    fun z b =>
      σ * tiltAmplitude B β p (blockCount n d) d *
        blockRepresenter β p d (blockAssignment n d b z)
  have hcoord (z : Fin n → Bool) (b : Fin (blockCount n d)) :
      Integrable (fun u => cosSqDensity s (u - shift z b)) volume :=
    cosSqDensity_translate_integrable s (shift z b)
  have hprod (z : Fin n → Bool) :
      Integrable
        (fun y : Fin (blockCount n d) → ℝ =>
          ∏ b, cosSqDensity s (y b - shift z b))
        (Measure.pi (fun _ : Fin (blockCount n d) => volume)) :=
    Integrable.fintype_prod (fun b => hcoord z b)
  have hinner (z : Fin n → Bool) :
      ∫ y, blockPriorDensity n d β B p σ (z, y)
          ∂(Measure.pi (fun _ : Fin (blockCount n d) => volume)) =
        assignmentMass n p z := by
    change ∫ y, assignmentMass n p z *
        ∏ b, cosSqDensity s (y b - shift z b)
          ∂(Measure.pi (fun _ : Fin (blockCount n d) => volume)) =
      assignmentMass n p z
    rw [integral_const_mul]
    rw [show
      (∫ y : Fin (blockCount n d) → ℝ,
          ∏ b, cosSqDensity s (y b - shift z b)
          ∂(Measure.pi (fun _ : Fin (blockCount n d) => volume))) =
        ∏ b, ∫ u, cosSqDensity s (u - shift z b) by
      exact MeasureTheory.integral_fintype_prod_eq_prod
        (fun b u => cosSqDensity s (u - shift z b))]
    have hone : ∀ b : Fin (blockCount n d),
        ∫ u, cosSqDensity s (u - shift z b) = 1 :=
      fun b => cosSqDensity_translate_integral_one s (shift z b) hs
    simp_rw [hone]
    simp
  have hmeas : AEStronglyMeasurable
      (blockPriorDensity n d β B p σ)
      (blockDominatingMeasure n d) := by
    apply Measurable.aestronglyMeasurable
    unfold blockPriorDensity
    apply Measurable.mul
    · exact (measurable_of_finite
        (assignmentMass n p)).comp measurable_fst
    · apply Finset.measurable_prod
      intro b hb
      apply (cosSqDensity_measurable (B / 2)).comp
      apply Measurable.sub
      · exact (measurable_pi_apply b).comp measurable_snd
      · exact (measurable_of_finite (fun z : Fin n → Bool =>
          σ * tiltAmplitude B β p (blockCount n d) d *
            blockRepresenter β p d (blockAssignment n d b z))).comp measurable_fst
  have hfull : Integrable (blockPriorDensity n d β B p σ)
      (blockDominatingMeasure n d) := by
    rw [blockDominatingMeasure] at hmeas ⊢
    rw [integrable_prod_iff hmeas]
    constructor
    · exact Filter.Eventually.of_forall fun z =>
        (hprod z).const_mul (assignmentMass n p z)
    · exact Integrable.of_finite
  rw [blockDominatingMeasure, integral_prod _ hfull]
  simp_rw [hinner]
  rw [MeasureTheory.integral_fintype]
  · have hcount (z : Fin n → Bool) :
        Measure.count.real ({z} : Set (Fin n → Bool)) = 1 := by
      rw [measureReal_def, Measure.count_apply_finite]
      · simp
      · exact Set.finite_singleton z
    simp_rw [hcount, one_smul]
    have hmass :=
      (Causalean.Experimentation.DesignBased.bernoulliDesign
        (fun _ : Fin n => p)
        (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).p_sum
    rw [show (∑ z : Fin n → Bool, assignmentMass n p z) =
        ∑ z : Fin n → Bool,
          (Causalean.Experimentation.DesignBased.bernoulliDesign
            (fun _ : Fin n => p)
            (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).p z by
      apply Finset.sum_congr rfl
      intro z hz
      simp only [assignmentMass,
        Causalean.Experimentation.DesignBased.bernoulliDesign,
        Causalean.Experimentation.DesignBased.prodDesign_p,
        Causalean.Experimentation.DesignBased.coinDesign]
      apply Finset.prod_congr rfl
      intro i hi
      cases z i <;> simp]
    exact hmass
  · exact Integrable.of_finite

end CausalSmith.Experimentation.SnipeDegreeFrontier
