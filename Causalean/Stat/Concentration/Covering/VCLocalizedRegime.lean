import Causalean.Stat.Concentration.Covering.VCCovering
import Causalean.Stat.Concentration.Covering.DudleyEntropy
import Causalean.Stat.Concentration.UniformDeviation.CriticalRadius
import Causalean.Stat.Concentration.Rademacher.Symmetrization
import Causalean.Stat.Concentration.UniformDeviation.UniformDeviationLocalized
import FoML.ExpectationInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
For a binary-indexed function class of VC dimension d, the localized
Rademacher complexity admits the linear sub-root envelope
`psi(r)=C*r*sqrt(d*log n/n)`, with critical radius of order
`sqrt(d*log n/n)`.

This file packages the finite-VC localized regime used by
`localized_uniform_deviation_sharp`.  The elementary envelope facts are proved
fully: linearity gives `SubRoot`, the critical radius is bounded by the slope,
and the squared critical radius is bounded by the corresponding
`d * log n / n` rate.  The empirical-process step is packaged in
`vc_starHullZeroOut_empirical_rademacher_le_linear` and its cardinality-bound
variant, which prove sample-path Dudley/VC covering-inflation bounds for the
localized star-hull-zeroed class.  The file then lifts those sample-path bounds
to population Rademacher upper bounds, `vcLocalizedEnvelope`, and the
`vcLocalizedRegime` bundles consumed by localized uniform-deviation theorems.
-/

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory

universe u v

section Definitions

variable {ι : Type u} {𝒳 : Type v}

/-- A binary factorization of a real-valued class whose realized Boolean
patterns have VC dimension at most `d` on every finite sample. -/
structure BinaryFactoredVCClass (F : ι → 𝒳 → ℝ) (d : ℕ) where
  /-- The Boolean class through which `F` factors on samples. -/
  π : ι → 𝒳 → Bool
  /-- Samplewise factorization through the Boolean labels. -/
  factor : ∀ {n : ℕ} (S : Fin n → 𝒳), ∃ φ : Fin n → Bool → ℝ,
    ∀ i j, F i (S j) = φ j (π i (S j))
  /-- Uniform VC dimension bound for the realized growth family. -/
  vcDim_le : ∀ {n : ℕ} (S : Fin n → 𝒳), (growthFamily π S).vcDim ≤ d

/-- Deterministic prerequisites used by the Dudley step after localization.

The `empirical_radius` field is the samplewise `L2` radius bound needed to run
Dudley with `c = r`; the `totallyBounded` field is the covering-number
precondition for the localized star-hull-zeroed class. -/
structure LocalizedVCDudleyHypotheses
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) where
  empirical_radius : ∀ {n : ℕ} (S : Fin n → 𝒳) {r : ℝ}, 0 ≤ r →
    ∀ p : starHullParam ι, empiricalNorm S (starHullZeroOut F norm r p) ≤ r
  totallyBounded : ∀ {n : ℕ} (S : Fin n → 𝒳) {r : ℝ}, 0 < r →
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S))

private lemma abs_starHullZeroOut_le_of_bound
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ} {B r : ℝ}
    (hbound : ∀ i x, |F i x| ≤ B) (p : starHullParam ι) (x : 𝒳) :
    |starHullZeroOut F norm r p x| ≤ B := by
  rcases p with ⟨a, i⟩
  by_cases hactive : norm (starHullEval F (a, i)) ≤ r
  · calc
      |starHullZeroOut F norm r (a, i) x|
          = |(a : ℝ) * F i x| := by
            simp [starHullZeroOut, hactive, starHullEval]
      _ = (a : ℝ) * |F i x| := by
            rw [abs_mul, abs_of_nonneg a.property.1]
      _ ≤ 1 * |F i x| :=
            mul_le_mul_of_nonneg_right a.property.2 (abs_nonneg _)
      _ ≤ B := by simpa using hbound i x
  · have hB : 0 ≤ B := (abs_nonneg (F i x)).trans (hbound i x)
    simpa [starHullZeroOut, hactive] using hB

private lemma empiricalNorm_le_of_forall_abs_le
    {n : ℕ} (S : Fin n → 𝒳) {f : 𝒳 → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hf : ∀ j : Fin n, |f (S j)| ≤ η) :
    empiricalNorm S f ≤ η := by
  classical
  by_cases hn : n = 0
  · simp [empiricalNorm, hn, hη]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hsum :
        (∑ j : Fin n, (f (S j)) ^ 2) ≤ ∑ _j : Fin n, η ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro j _
      calc
        (f (S j)) ^ 2 = |f (S j)| ^ 2 := by rw [sq_abs]
        _ ≤ η ^ 2 :=
            sq_le_sq.mpr (by simpa [abs_of_nonneg hη] using hf j)
    have harg :
        (1 / (n : ℝ)) * ∑ j : Fin n, (f (S j)) ^ 2 ≤ η ^ 2 := by
      calc
        (1 / (n : ℝ)) * ∑ j : Fin n, (f (S j)) ^ 2
            ≤ (1 / (n : ℝ)) * ∑ _j : Fin n, η ^ 2 :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (1 / (n : ℝ)) * ((n : ℝ) * η ^ 2) := by
              simp
        _ = η ^ 2 := by
              field_simp [Finset.card_fin, hnR.ne']
    calc
      empiricalNorm S f
          = Real.sqrt ((1 / (n : ℝ)) * ∑ j : Fin n, (f (S j)) ^ 2) := rfl
      _ ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt harg
      _ = η := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hη]

private lemma empiricalFunctionSpace_dist_le_of_forall_abs_sub_le
    {G : starHullParam ι → 𝒳 → ℝ} {n : ℕ} {S : Fin n → 𝒳}
    (q q' : EmpiricalFunctionSpace G S) {η : ℝ} (hη : 0 ≤ η)
    (hcoord : ∀ j : Fin n, |G q.index (S j) - G q'.index (S j)| ≤ η) :
    dist q q' ≤ η := by
  have hnorm :
      empiricalNorm S ((q : 𝒳 → ℝ) - (q' : 𝒳 → ℝ)) ≤ η :=
    empiricalNorm_le_of_forall_abs_le S hη (by
      intro j
      simpa [Pi.sub_apply] using hcoord j)
  simpa [instDistEmpiricalFunctionSpace, empiricalDist] using hnorm

private lemma starHullZeroOut_totallyBounded_of_bounded_vc
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ} {B : ℝ}
    (hbound : ∀ i x, |F i x| ≤ B)
    {n : ℕ} (S : Fin n → 𝒳) {r : ℝ} (hr : 0 < r) :
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S)) := by
  classical
  have _hr_nonneg : 0 ≤ r := le_of_lt hr
  let sampleVector :
      EmpiricalFunctionSpace (starHullZeroOut F norm r) S → Fin n → ℝ :=
    fun q j => starHullZeroOut F norm r q.index (S j)
  have hcube :
      TotallyBounded
        (Set.Icc (fun _ : Fin n => -B) (fun _ : Fin n => B) :
          Set (Fin n → ℝ)) :=
    isCompact_Icc.totallyBounded
  refine Metric.totallyBounded_of_finite_discretization
    (s := (Set.univ :
      Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S))) ?_
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  rcases Metric.finite_approx_of_totallyBounded hcube δ hδ with
    ⟨t, ht_subset, ht_finite, ht_cover⟩
  have hmem_cube :
      ∀ q : (Set.univ :
          Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S)),
        sampleVector q.1 ∈
          (Set.Icc (fun _ : Fin n => -B) (fun _ : Fin n => B) :
            Set (Fin n → ℝ)) := by
    intro q
    constructor
    · intro j
      exact neg_le_of_abs_le
        (abs_starHullZeroOut_le_of_bound hbound q.1.index (S j))
    · intro j
      exact le_of_abs_le
        (abs_starHullZeroOut_le_of_bound hbound q.1.index (S j))
  have hnear :
      ∀ q : (Set.univ :
          Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S)),
        ∃ y : (t : Set (Fin n → ℝ)), dist (sampleVector q.1) y.1 < δ := by
    intro q
    have hq := ht_cover (hmem_cube q)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hq
    rcases hq with ⟨y, hy_t, hy_dist⟩
    exact ⟨⟨y, hy_t⟩, hy_dist⟩
  let domain : Set (EmpiricalFunctionSpace (starHullZeroOut F norm r) S) :=
    Set.univ
  let center0 : domain → (t : Set (Fin n → ℝ)) :=
    fun q => Classical.choose (hnear q)
  let center : domain → ULift.{u} (t : Set (Fin n → ℝ)) :=
    fun q => ULift.up (center0 q)
  haveI : Fintype (t : Set (Fin n → ℝ)) := ht_finite.fintype
  refine ⟨ULift.{u} (t : Set (Fin n → ℝ)), inferInstance, center, ?_⟩
  intro q q' hcenter
  have hcenter0 : center0 q = center0 q' := by
    simpa [center] using congrArg ULift.down hcenter
  have hq_near : dist (sampleVector q.1) (center0 q).1 < δ :=
    Classical.choose_spec (hnear q)
  have hq'_near : dist (sampleVector q'.1) (center0 q').1 < δ :=
    Classical.choose_spec (hnear q')
  have hcoord : ∀ j : Fin n,
      |starHullZeroOut F norm r q.1.index (S j) -
        starHullZeroOut F norm r q'.1.index (S j)| ≤ ε / 2 := by
    intro j
    have hjq : dist (sampleVector q.1 j) ((center0 q).1 j) < δ :=
      (dist_le_pi_dist (sampleVector q.1) (center0 q).1 j).trans_lt hq_near
    have hjq' : dist ((center0 q).1 j) (sampleVector q'.1 j) < δ := by
      rw [← hcenter0] at hq'_near
      simpa [dist_comm] using
        (dist_le_pi_dist (sampleVector q'.1) (center0 q).1 j).trans_lt hq'_near
    have hsum :
        dist (sampleVector q.1 j) (sampleVector q'.1 j) < ε / 2 := by
      calc
        dist (sampleVector q.1 j) (sampleVector q'.1 j)
            ≤ dist (sampleVector q.1 j) ((center0 q).1 j) +
                dist ((center0 q).1 j) (sampleVector q'.1 j) :=
              dist_triangle _ _ _
        _ < δ + δ := add_lt_add hjq hjq'
        _ = ε / 2 := by ring
    simpa [Real.dist_eq] using le_of_lt hsum
  have hdist_le :
      dist q.1 q'.1 ≤ ε / 2 :=
    empiricalFunctionSpace_dist_le_of_forall_abs_sub_le q.1 q'.1
      (by positivity) hcoord
  exact lt_of_le_of_lt hdist_le (by linarith)

/-- Assemble the deterministic localized Dudley hypotheses for a bounded
binary-factored VC class once the samplewise empirical-radius bridge is known.

For a population `L²(μ)` localization norm, the `empirical_radius` argument is
the genuine extra bridge: boundedness alone does not imply that every function
with population radius at most `r` has empirical radius at most `r` on every
sample. -/
theorem localizedVCDudleyHypotheses_of_empiricalRadius
    {F : ι → 𝒳 → ℝ} {norm : (𝒳 → ℝ) → ℝ} {B : ℝ}
    (hbound : ∀ i x, |F i x| ≤ B)
    (empirical_radius : ∀ {n : ℕ} (S : Fin n → 𝒳) {r : ℝ}, 0 ≤ r →
      ∀ p : starHullParam ι, empiricalNorm S (starHullZeroOut F norm r p) ≤ r) :
    LocalizedVCDudleyHypotheses F norm where
  empirical_radius := empirical_radius
  totallyBounded := fun {_} S {_} hr =>
    starHullZeroOut_totallyBounded_of_bounded_vc hbound S hr

/-- The finite-VC localized slope is the sample-size dependent coefficient in
the linear localized Rademacher envelope.

It has the displayed order given by the VC dimension, logarithmic sample-size
term, and tuning constant. -/
noncomputable def vcLocalizedSlope (K : ℝ) (d n : ℕ) : ℝ :=
  6 * Real.sqrt ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ))

/-- The finite-VC localized envelope maps a radius to the slope times that
radius. -/
noncomputable def vcLocalizedPsi (K : ℝ) (d n : ℕ) : ℝ → ℝ :=
  fun r => vcLocalizedSlope K d n * r

end Definitions

section ElementaryEnvelope

/-- The rate inside `vcLocalizedSlope` is nonnegative when `K ≥ 0`. -/
lemma vcLocalizedRate_nonneg {K : ℝ} {d n : ℕ} (hK : 0 ≤ K) :
    0 ≤ (K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hone_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      linarith [le_of_lt hnR]
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hone_le
    have hterm : 0 ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by
      exact mul_nonneg (mul_nonneg hK (Nat.cast_nonneg d)) hlog
    have hnum : 0 ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1 := by
      linarith
    exact div_nonneg hnum (le_of_lt hnR)

/-- The finite-VC slope is nonnegative. -/
lemma vcLocalizedSlope_nonneg (K : ℝ) (d n : ℕ) :
    0 ≤ vcLocalizedSlope K d n := by
  unfold vcLocalizedSlope
  positivity

/-- If `K ≥ 0` and `n > 0`, the finite-VC slope is strictly positive. -/
lemma vcLocalizedSlope_pos {K : ℝ} {d n : ℕ} (hK : 0 ≤ K) (hn : 0 < n) :
    0 < vcLocalizedSlope K d n := by
  unfold vcLocalizedSlope
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hone_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith [le_of_lt hnR]
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hone_le
  have hterm : 0 ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by
    exact mul_nonneg (mul_nonneg hK (Nat.cast_nonneg d)) hlog
  have hnum : 0 < K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1 := by
    linarith
  have hfrac :
      0 < (K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ) :=
    div_pos hnum hnR
  have hsqrt :
      0 < Real.sqrt
        ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) :=
    Real.sqrt_pos.mpr hfrac
  nlinarith

/-- The exact square of the finite-VC slope. -/
lemma vcLocalizedSlope_sq {K : ℝ} {d n : ℕ} (hK : 0 ≤ K) :
    vcLocalizedSlope K d n ^ 2 =
      36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
  unfold vcLocalizedSlope
  rw [mul_pow, Real.sq_sqrt (vcLocalizedRate_nonneg (K := K) (d := d) (n := n) hK)]
  ring

/-- A nonnegative linear function is sub-root. -/
lemma linear_subRoot {C : ℝ} (hC : 0 ≤ C) : SubRoot (fun r : ℝ => C * r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact mul_nonneg hC hr
  · intro r₁ r₂ _ hr₁₂
    exact mul_le_mul_of_nonneg_left hr₁₂ hC
  · intro r₁ r₂ hr₁ hr₁₂
    have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hr₁₂
    have h₁ : C * r₁ / r₁ = C := by field_simp [ne_of_gt hr₁]
    have h₂ : C * r₂ / r₂ = C := by field_simp [ne_of_gt hr₂]
    rw [h₁, h₂]

/-- The finite-VC localized envelope is sub-root. -/
lemma vcLocalizedPsi_subRoot (K : ℝ) (d n : ℕ) :
    SubRoot (vcLocalizedPsi K d n) := by
  unfold vcLocalizedPsi
  exact linear_subRoot (vcLocalizedSlope_nonneg K d n)

/-- The critical radius of a positive-slope linear envelope is at most its
slope. -/
lemma criticalRadius_linear_le {C : ℝ} (hC : 0 < C) :
    criticalRadius (fun r : ℝ => C * r) ≤ C := by
  apply criticalRadius_le hC
  rw [pow_two]

/-- The squared critical radius of a positive-slope linear envelope is at most
the squared slope. -/
lemma criticalRadius_linear_sq_le {C : ℝ} (hC : 0 < C) :
    (criticalRadius (fun r : ℝ => C * r)) ^ 2 ≤ C ^ 2 := by
  have hle : criticalRadius (fun r : ℝ => C * r) ≤ C :=
    criticalRadius_linear_le hC
  have hnonneg : 0 ≤ criticalRadius (fun r : ℝ => C * r) :=
    criticalRadius_nonneg _
  nlinarith

/-- The finite-VC critical radius is bounded by the finite-VC slope. -/
lemma criticalRadius_vcLocalizedPsi_le {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    criticalRadius (vcLocalizedPsi K d n) ≤ vcLocalizedSlope K d n := by
  unfold vcLocalizedPsi
  exact criticalRadius_linear_le (vcLocalizedSlope_pos hK hn)

/-- The finite-VC squared critical radius is bounded by the squared slope. -/
lemma criticalRadius_vcLocalizedPsi_sq_le {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    (criticalRadius (vcLocalizedPsi K d n)) ^ 2 ≤
      (vcLocalizedSlope K d n) ^ 2 := by
  unfold vcLocalizedPsi
  exact criticalRadius_linear_sq_le (vcLocalizedSlope_pos hK hn)

/-- The finite-VC squared critical radius has the advertised
`(d * log n) / n`-order upper bound. -/
lemma criticalRadius_vcLocalizedPsi_sq_le_rate {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    (criticalRadius (vcLocalizedPsi K d n)) ^ 2 ≤
      36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
  calc
    (criticalRadius (vcLocalizedPsi K d n)) ^ 2
        ≤ (vcLocalizedSlope K d n) ^ 2 :=
      criticalRadius_vcLocalizedPsi_sq_le hK hn
    _ = 36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) :=
      vcLocalizedSlope_sq hK

end ElementaryEnvelope

section RademacherBridge

variable {Ω : Type*} {ι : Type u} {𝒳 : Type v} [MeasurableSpace Ω]
variable [Nonempty ι] [Countable ι]

omit [Nonempty ι] [Countable ι] in
/-- Binary trace entropy evidence used by the shared localized star-hull
Dudley residual.

The first branch is the VC-dimension route used with
`VCCovering.log_coveringNumber_le`; the second is the direct growth-cardinality
route used with `VCCovering.log_coveringNumber_le_of_card_bound`. -/
def BinaryTraceEntropyControl (π : ι → 𝒳 → Bool) (d : ℕ) : Prop :=
  (∀ {m : ℕ} (S : Fin m → 𝒳), (growthFamily π S).vcDim ≤ d) ∨
  (∀ (m : ℕ) (S : Fin m → 𝒳), (growthFamily π S).card ≤ (m + 1) ^ d)

omit [Nonempty ι] [Countable ι] in
private lemma sum_choose_le_succ_pow (n d : ℕ) :
    (∑ k ∈ Finset.Iic d, n.choose k) ≤ (n + 1) ^ d := by
  calc
    (∑ k ∈ Finset.Iic d, n.choose k) ≤ ∑ k ∈ Finset.Iic d, n ^ k := by
      refine Finset.sum_le_sum ?_
      intro k _hk
      exact Nat.choose_le_pow n k
    _ ≤ ∑ k ∈ Finset.Iic d, d.choose k * n ^ k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk' : k ≤ d := by simpa using hk
      have hchoose_pos : 1 ≤ d.choose k :=
        Nat.succ_le_of_lt (Nat.choose_pos hk')
      simpa [one_mul] using Nat.mul_le_mul_right (n ^ k) hchoose_pos
    _ = (n + 1) ^ d := by
      rw [add_pow]
      simp only [one_pow, mul_one, Nat.cast_id]
      simp only [Nat.mul_comm]
      congr 1
      ext k
      simp

omit [Nonempty ι] [Countable ι] in
private lemma growthFamily_card_le_succ_pow_of_trace
    (π : ι → 𝒳 → Bool) (d n : ℕ)
    (Htrace : BinaryTraceEntropyControl π d) (S : Fin n → 𝒳) :
    (growthFamily π S).card ≤ (n + 1) ^ d := by
  rcases Htrace with hvc | hcard
  · exact le_trans
      (card_growthFamily_le_sum_choose (growthFamily π S) (hvc S))
      (sum_choose_le_succ_pow n d)
  · exact hcard n S

omit [Nonempty ι] [Countable ι] in
private lemma log_two_growth_card_le
    (π : ι → 𝒳 → Bool) (d n : ℕ) (S : Fin n → 𝒳)
    (hcard_pos : 0 < (growthFamily π S).card)
    (hcard : (growthFamily π S).card ≤ (n + 1) ^ d) :
    2 * Real.log (2 * ((growthFamily π S).card : ℝ))
      ≤ 2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2 := by
  let N : ℕ := (growthFamily π S).card
  let M : ℕ := (n + 1) ^ d
  have hleR : (2 : ℝ) * N ≤ 2 * M := by
    exact_mod_cast (Nat.mul_le_mul_left 2 hcard)
  have hlog_le : Real.log (2 * (N : ℝ)) ≤ Real.log (2 * (M : ℝ)) := by
    exact Real.log_le_log (by positivity) hleR
  have hlogM :
      Real.log (2 * (M : ℝ)) =
        Real.log 2 + (d : ℝ) * Real.log ((n : ℝ) + 1) := by
    dsimp [M]
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [Real.log_mul]
    · rw [Real.log_pow]
    · norm_num
    · positivity
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  dsimp [N] at hlog_le
  nlinarith

/-- The absolute empirical Rademacher complexity of a finite class is bounded
by a Massart logarithmic factor times a common radius. -/
lemma empiricalRademacher_withAbs_finiteClass_le
    {ι' Z : Type*} {m : ℕ} (hm : 0 < m) (H : ι' → Z → ℝ) (S' : Fin m → Z)
    (f : Finset ι') (hf : f.Nonempty) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (hradius : ∀ i ∈ f,
      Real.sqrt (∑ k : Fin m, ((m : ℝ)⁻¹ * |H i (S' k)|) ^ 2) ≤ ρ) :
    empiricalRademacherComplexity m (F_on H f) S'
      ≤ ρ * Real.sqrt (2 * Real.log (2 * (f.card : ℝ))) := by
  classical
  let Hd : ι' × Bool → Z → ℝ := fun jb z =>
    if jb.2 then H jb.1 z else -H jb.1 z
  let fd : Finset (ι' × Bool) := f.product (Finset.univ : Finset Bool)
  have hfd_nonempty : fd.Nonempty := by
    rcases hf with ⟨i, hi⟩
    refine ⟨(i, true), ?_⟩
    simp [fd, hi]
  have hpoint :
      empiricalRademacherComplexity m (F_on H f) S'
        ≤ empiricalRademacherComplexity_without_abs m (F_on Hd fd) S' := by
    haveI : Nonempty {j // j ∈ f} := by
      rcases hf with ⟨i, hi⟩
      exact ⟨⟨i, hi⟩⟩
    unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum ?_
    intro σ _
    refine ciSup_le ?_
    intro j
    let x : ℝ :=
      (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) * F_on H f j (S' k)
    have htrue :
        x =
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd ⟨(j.1, true), by simp [fd, j.2]⟩ (S' k) := by
      simp [x, Hd, F_on]
    have hfalse :
        -x =
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd ⟨(j.1, false), by simp [fd, j.2]⟩ (S' k) := by
      simp [x, Hd, F_on, Finset.mul_sum]
    have hle_true :
        x ≤
          ⨆ jb : {jb // jb ∈ fd},
            (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
              F_on Hd fd jb (S' k) := by
      rw [htrue]
      exact le_ciSup
        (Finite.bddAbove_range fun jb : {jb // jb ∈ fd} =>
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd jb (S' k))
        ⟨(j.1, true), by simp [fd, j.2]⟩
    have hle_false :
        -x ≤
          ⨆ jb : {jb // jb ∈ fd},
            (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
              F_on Hd fd jb (S' k) := by
      rw [hfalse]
      exact le_ciSup
        (Finite.bddAbove_range fun jb : {jb // jb ∈ fd} =>
          (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
            F_on Hd fd jb (S' k))
        ⟨(j.1, false), by simp [fd, j.2]⟩
    have hlower :
        -(⨆ jb : {jb // jb ∈ fd},
            (m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) *
              F_on Hd fd jb (S' k)) ≤ x := by
      linarith
    simpa [x] using abs_le.mpr ⟨hlower, hle_true⟩
  have hpointwise :
      ∀ i ∈ fd, ∀ j : Fin m, |Hd i (S' j)| ≤ (m : ℝ) * ρ := by
    intro i hi j
    rcases i with ⟨i, b⟩
    have hi_f : i ∈ f := by
      simpa [fd] using (Finset.mem_product.mp hi).1
    have hterm :
        ((m : ℝ)⁻¹ * |H i (S' j)|) ^ 2
          ≤ ∑ k : Fin m, ((m : ℝ)⁻¹ * |H i (S' k)|) ^ 2 := by
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun k : Fin m => ((m : ℝ)⁻¹ * |H i (S' k)|) ^ 2)
        (by intro k _; exact sq_nonneg _)
        (by simp)
    have hscaled :
        (m : ℝ)⁻¹ * |H i (S' j)| ≤ ρ := by
      have hsqrt :=
        (Real.sqrt_le_sqrt hterm).trans (hradius i hi_f)
      have hnonneg : 0 ≤ (m : ℝ)⁻¹ * |H i (S' j)| := by
        exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) (abs_nonneg _)
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg] using hsqrt
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hmR)
    have hcancel : (m : ℝ) * ((m : ℝ)⁻¹ * |H i (S' j)|) = |H i (S' j)| := by
      field_simp [ne_of_gt hmR]
    have hH : |H i (S' j)| ≤ (m : ℝ) * ρ := by
      simpa [hcancel, mul_assoc] using hmul
    by_cases hb : b = true
    · simp [Hd, hb, hH]
    · have hbfalse : b = false := by cases b <;> simp at hb ⊢
      simpa [Hd, hbfalse, abs_neg] using hH
  have hmass :
      empiricalRademacherComplexity_without_abs m (F_on Hd fd) S'
        ≤
      (Finset.sup' fd hfd_nonempty fun j =>
          Real.sqrt (∑ i : Fin m,
            ((m : ℝ)⁻¹ * |Hd j (S' i)|) ^ 2)) *
        Real.sqrt (2 * Real.log fd.card) := by
    rw [empiricalRademacherComplexity_without_abs_eq_empiricalRademacherComplexity_pmf_without_abs]
    exact massart_lemma_pmf (F := Hd) (S := S') fd hfd_nonempty hm
      ((m : ℝ) * ρ) hpointwise hfd_nonempty
  have hsup :
      (Finset.sup' fd hfd_nonempty fun j =>
          Real.sqrt (∑ i : Fin m,
            ((m : ℝ)⁻¹ * |Hd j (S' i)|) ^ 2)) ≤ ρ := by
    refine Finset.sup'_le _ _ ?_
    intro jb hjb
    rcases jb with ⟨i, b⟩
    have hi_f : i ∈ f := by
      simpa [fd] using (Finset.mem_product.mp hjb).1
    by_cases hb : b = true
    · simpa [Hd, hb] using hradius i hi_f
    · have hbfalse : b = false := by cases b <;> simp at hb ⊢
      simpa [Hd, hbfalse, abs_neg] using hradius i hi_f
  have hcard : (fd.card : ℝ) = 2 * (f.card : ℝ) := by
    simp [fd, Nat.cast_mul, mul_comm]
  calc
    empiricalRademacherComplexity m (F_on H f) S'
        ≤ empiricalRademacherComplexity_without_abs m (F_on Hd fd) S' := hpoint
    _ ≤
        (Finset.sup' fd hfd_nonempty fun j =>
          Real.sqrt (∑ i : Fin m,
            ((m : ℝ)⁻¹ * |Hd j (S' i)|) ^ 2)) *
        Real.sqrt (2 * Real.log fd.card) := hmass
    _ ≤ ρ * Real.sqrt (2 * Real.log fd.card) :=
        mul_le_mul_of_nonneg_right hsup (Real.sqrt_nonneg _)
    _ = ρ * Real.sqrt (2 * Real.log (2 * (f.card : ℝ))) := by
        rw [hcard]

private lemma empiricalRademacherComplexity_F_on_univ_eq
    {ι' Z : Type*} [Fintype ι'] [Nonempty ι']
    {m : ℕ} (H : ι' → Z → ℝ) (S' : Fin m → Z) :
    empiricalRademacherComplexity m (F_on H (Finset.univ : Finset ι')) S'
      = empiricalRademacherComplexity m H S' := by
  classical
  unfold empiricalRademacherComplexity
  apply congrArg
  refine Finset.sum_congr rfl ?_
  intro σ _
  haveI : Nonempty {j // j ∈ (Finset.univ : Finset ι')} := by
    rcases (inferInstance : Nonempty ι') with ⟨i⟩
    exact ⟨⟨i, by simp⟩⟩
  apply le_antisymm
  · refine ciSup_le ?_
    intro i
    exact le_ciSup
      (Finite.bddAbove_range fun j : ι' =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) * H j (S' k)|)
      i.1
  · refine ciSup_le ?_
    intro i
    have hidx : i ∈ (Finset.univ : Finset ι') := by simp
    exact le_ciSup
      (Finite.bddAbove_range fun j : {j // j ∈ (Finset.univ : Finset ι')} =>
        |(m : ℝ)⁻¹ * ∑ k : Fin m, (σ k : ℝ) * F_on H (Finset.univ : Finset ι') j (S' k)|)
      ⟨i, hidx⟩

private lemma empiricalNorm_const_mul
    {𝒳 : Type*} {n : ℕ} (S : Fin n → 𝒳) (c : ℝ) (hc : 0 ≤ c)
    (f : 𝒳 → ℝ) :
    empiricalNorm S (fun x => c * f x) = c * empiricalNorm S f := by
  classical
  unfold empiricalNorm
  have hsum :
      (∑ i : Fin n, (c * f (S i)) ^ 2)
        = c ^ 2 * ∑ i : Fin n, (f (S i)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hnonneg :
      0 ≤ (1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2 := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  calc
    Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (c * f (S i)) ^ 2)
        = Real.sqrt (c ^ 2 * ((1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2)) := by
          rw [hsum]
          ring_nf
    _ = Real.sqrt (c ^ 2) *
          Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg c)]
    _ = c * Real.sqrt ((1 / (n : ℝ)) * ∑ i : Fin n, (f (S i)) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

private lemma ciSup_mul_const_of_le_one {A : Type*} [Nonempty A]
    (c : A → ℝ) (b : ℝ) (hc_le : ∀ a, c a ≤ 1) (hb : 0 ≤ b) :
    (⨆ a : A, c a * b) = (⨆ a : A, c a) * b := by
  classical
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hc_le a
  have hcb_bdd : BddAbove (Set.range fun a : A => c a * b) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨a, rfl⟩
    calc
      c a * b ≤ 1 * b := mul_le_mul_of_nonneg_right (hc_le a) hb
      _ = b := one_mul b
  apply le_antisymm
  · refine ciSup_le ?_
    intro a
    exact mul_le_mul_of_nonneg_right (le_ciSup hc_bdd a) hb
  · by_cases hb0 : b = 0
    · simp [hb0]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hsup_le : (⨆ a : A, c a) ≤ (⨆ a : A, c a * b) / b := by
        refine ciSup_le ?_
        intro a
        exact (le_div_iff₀ hbpos).mpr (le_ciSup hcb_bdd a)
      exact (le_div_iff₀ hbpos).mp hsup_le

/-- A representative classifier index is chosen for each realized Boolean
growth-family pattern. -/
noncomputable def growthFamilyRep
    {ι 𝒳 : Type*} {n : ℕ} (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳)
    (A : {A // A ∈ growthFamily π S}) : ι :=
  Classical.choose ((mem_growthFamily_iff (π := π) (S := S) (A := A.1)).mp A.2)

/-- The chosen growth-family representative realizes the pattern it represents. -/
lemma growthFamilyRep_spec
    {ι 𝒳 : Type*} {n : ℕ} (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳)
    (A : {A // A ∈ growthFamily π S}) :
    restrictionPattern (π (growthFamilyRep π S A)) S = A.1 :=
  Classical.choose_spec ((mem_growthFamily_iff (π := π) (S := S) (A := A.1)).mp A.2)

/-- The star-hull pattern coefficient is the largest active scale among
functions with the same realized Boolean pattern. -/
noncomputable def starHullPatternCoeff
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ)
    (A : {A // A ∈ growthFamily π S}) : ℝ :=
  ⨆ i : {i : ι // restrictionPattern (π i) S = A.1},
    starHullZeroOutScaleCoeff F norm r i.1

/-- The star-hull pattern class assigns each realized Boolean pattern its
representative function multiplied by the pattern coefficient. -/
noncomputable def starHullPatternClass
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ) :
    {A // A ∈ growthFamily π S} → 𝒳 → ℝ :=
  fun A x => starHullPatternCoeff F norm π S r A *
    F (growthFamilyRep π S A) x

private lemma starHullZeroOutScaleCoeff_nonneg
    {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (r : ℝ) (i : ι) :
    0 ≤ starHullZeroOutScaleCoeff F norm r i := by
  classical
  let c : Set.Icc (0 : ℝ) 1 → ℝ := fun a =>
    if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    dsimp [c]
    split_ifs
    · exact a.property.2
    · norm_num
  let a0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp [Set.mem_Icc]⟩
  have hval : c a0 = 0 := by simp [c, a0]
  rw [starHullZeroOutScaleCoeff]
  change 0 ≤ ⨆ a : Set.Icc (0 : ℝ) 1, c a
  simpa [hval] using le_ciSup hc_bdd a0

private lemma activeCoeff_le_starHullZeroOutScaleCoeff
    {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (r : ℝ) (a : Set.Icc (0 : ℝ) 1) (i : ι) :
    (if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0)
      ≤ starHullZeroOutScaleCoeff F norm r i := by
  classical
  let c : Set.Icc (0 : ℝ) 1 → ℝ := fun a =>
    if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    dsimp [c]
    split_ifs
    · exact a.property.2
    · norm_num
  rw [starHullZeroOutScaleCoeff]
  exact le_ciSup hc_bdd a

private lemma starHullPatternCoeff_nonneg
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ)
    (A : {A // A ∈ growthFamily π S}) :
    0 ≤ starHullPatternCoeff F norm π S r A := by
  classical
  let rep : {i : ι // restrictionPattern (π i) S = A.1} :=
    ⟨growthFamilyRep π S A, growthFamilyRep_spec π S A⟩
  have hcoeff_le : BddAbove
      (Set.range fun i : {i : ι // restrictionPattern (π i) S = A.1} =>
        starHullZeroOutScaleCoeff F norm r i.1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact starHullZeroOutScaleCoeff_le_one F norm r i.1
  have hrep_le :
      starHullZeroOutScaleCoeff F norm r rep.1
        ≤ starHullPatternCoeff F norm π S r A := by
    rw [starHullPatternCoeff]
    exact le_ciSup hcoeff_le rep
  exact (starHullZeroOutScaleCoeff_nonneg F norm r rep.1).trans hrep_le

private lemma starHullZeroOutScaleCoeff_le_patternCoeff
    {ι 𝒳 : Type*} {n : ℕ} (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool) (S : Fin n → 𝒳) (r : ℝ)
    (A : {A // A ∈ growthFamily π S}) (i : ι)
    (hiA : restrictionPattern (π i) S = A.1) :
    starHullZeroOutScaleCoeff F norm r i
      ≤ starHullPatternCoeff F norm π S r A := by
  classical
  have hcoeff_le : BddAbove
      (Set.range fun i : {i : ι // restrictionPattern (π i) S = A.1} =>
        starHullZeroOutScaleCoeff F norm r i.1) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact starHullZeroOutScaleCoeff_le_one F norm r i.1
  rw [starHullPatternCoeff]
  exact le_ciSup hcoeff_le ⟨i, hiA⟩

private lemma sample_eq_growthFamilyRep_of_pattern
    {ι 𝒳 : Type*} {n : ℕ} {F : ι → 𝒳 → ℝ}
    {π : ι → 𝒳 → Bool} {S : Fin n → 𝒳} {φ : Fin n → Bool → ℝ}
    (hfactorS : ∀ i j, F i (S j) = φ j (π i (S j)))
    (A : {A // A ∈ growthFamily π S}) {i : ι}
    (hiA : restrictionPattern (π i) S = A.1) (k : Fin n) :
    F i (S k) = F (growthFamilyRep π S A) (S k) := by
  rw [hfactorS i k, hfactorS (growthFamilyRep π S A) k]
  apply congrArg (φ k)
  apply Bool.eq_iff_iff.mpr
  rw [← restrictionPattern_mem_iff (p := π i) (S := S) (j := k),
    hiA, ← growthFamilyRep_spec π S A,
    restrictionPattern_mem_iff (p := π (growthFamilyRep π S A)) (S := S) (j := k)]

private lemma starHullZeroOut_empirical_rademacher_le_patternClass
    {ι 𝒳 : Type*} [Nonempty ι] {n : ℕ}
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (S : Fin n → 𝒳) (r : ℝ) :
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
      ≤ empiricalRademacherComplexity n (starHullPatternClass F norm π S r) S := by
  classical
  rcases hfactor S with ⟨φ, hφ⟩
  haveI : Nonempty {A // A ∈ growthFamily π S} := by
    let i0 : ι := Classical.arbitrary ι
    have hmem : restrictionPattern (π i0) S ∈ growthFamily π S := by
      rw [mem_growthFamily_iff]
      exact ⟨i0, rfl⟩
    exact ⟨⟨restrictionPattern (π i0) S, hmem⟩⟩
  unfold empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine ciSup_le ?_
  intro p
  rcases p with ⟨a, i⟩
  let A0 : Finset (Fin n) := restrictionPattern (π i) S
  have hA0 : A0 ∈ growthFamily π S := by
    rw [mem_growthFamily_iff]
    exact ⟨i, rfl⟩
  let A : {A // A ∈ growthFamily π S} := ⟨A0, hA0⟩
  have hiA : restrictionPattern (π i) S = A.1 := rfl
  let active : ℝ := if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0
  let innerI : ℝ :=
    (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)
  let innerRep : ℝ :=
    (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
      F (growthFamilyRep π S A) (S k)
  have hstar :
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r (a, i) (S k)|
        = active * |innerI| := by
    simpa [active, innerI] using
      starHullZeroOut_inner_term_eq F norm r S σ a i
  have hinner : innerI = innerRep := by
    simp [innerI, innerRep,
      sample_eq_growthFamilyRep_of_pattern (F := F) (π := π)
        (S := S) (φ := φ) hφ A hiA]
  have hactive_nonneg : 0 ≤ active := by
    dsimp [active]
    split_ifs
    · exact a.property.1
    · norm_num
  have hscale_le :
      active ≤ starHullZeroOutScaleCoeff F norm r i := by
    simpa [active] using activeCoeff_le_starHullZeroOutScaleCoeff F norm r a i
  have hcoeff_le :
      starHullZeroOutScaleCoeff F norm r i
        ≤ starHullPatternCoeff F norm π S r A :=
    starHullZeroOutScaleCoeff_le_patternCoeff F norm π S r A i hiA
  have hterm_le :
      active * |innerI|
        ≤ starHullPatternCoeff F norm π S r A * |innerRep| := by
    calc
      active * |innerI|
          ≤ starHullZeroOutScaleCoeff F norm r i * |innerI| :=
            mul_le_mul_of_nonneg_right hscale_le (abs_nonneg _)
      _ ≤ starHullPatternCoeff F norm π S r A * |innerI| :=
            mul_le_mul_of_nonneg_right hcoeff_le (abs_nonneg _)
      _ = starHullPatternCoeff F norm π S r A * |innerRep| := by
            rw [hinner]
  have hpattern :
      starHullPatternCoeff F norm π S r A * |innerRep|
        =
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullPatternClass F norm π S r A (S k)| := by
    have hcoeff_nonneg := starHullPatternCoeff_nonneg F norm π S r A
    have hlin :
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullPatternClass F norm π S r A (S k)
          =
        starHullPatternCoeff F norm π S r A * innerRep := by
      dsimp [starHullPatternClass, innerRep]
      calc
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            (starHullPatternCoeff F norm π S r A *
              F (growthFamilyRep π S A) (S k))
            =
          (n : ℝ)⁻¹ * (starHullPatternCoeff F norm π S r A *
            ∑ k : Fin n, (σ k : ℝ) *
              F (growthFamilyRep π S A) (S k)) := by
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
        _ = starHullPatternCoeff F norm π S r A *
            ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              F (growthFamilyRep π S A) (S k)) := by
            ring
    symm
    calc
      |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullPatternClass F norm π S r A (S k)|
          = |starHullPatternCoeff F norm π S r A * innerRep| := by
            rw [hlin]
      _ = starHullPatternCoeff F norm π S r A * |innerRep| := by
            rw [abs_mul, abs_of_nonneg hcoeff_nonneg]
  calc
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        starHullZeroOut F norm r (a, i) (S k)|
        = active * |innerI| := hstar
    _ ≤ starHullPatternCoeff F norm π S r A * |innerRep| := hterm_le
    _ = |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullPatternClass F norm π S r A (S k)| := hpattern
    _ ≤ ⨆ A : {A // A ∈ growthFamily π S},
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullPatternClass F norm π S r A (S k)| := by
        exact le_ciSup
          (Finite.bddAbove_range fun A : {A // A ∈ growthFamily π S} =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullPatternClass F norm π S r A (S k)|)
          A

private lemma sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt
    {𝒳 : Type*} {n : ℕ} (hn : 0 < n) (S : Fin n → 𝒳) (g : 𝒳 → ℝ) :
    Real.sqrt (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
      = empiricalNorm S g / Real.sqrt (n : ℝ) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum :
      (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
        =
      (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
    calc
      (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
          = ∑ k : Fin n, ((n : ℝ)⁻¹) ^ 2 * (g (S k)) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [mul_pow, sq_abs]
      _ = ((n : ℝ)⁻¹) ^ 2 * ∑ k : Fin n, (g (S k)) ^ 2 := by
            rw [Finset.mul_sum]
      _ = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
            ring
  calc
    Real.sqrt (∑ k : Fin n, ((n : ℝ)⁻¹ * |g (S k)|) ^ 2)
        = Real.sqrt ((n : ℝ)⁻¹ *
            ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2)) := by
          rw [hsum]
    _ = Real.sqrt ((n : ℝ)⁻¹) *
          Real.sqrt ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
          rw [Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hnR))]
    _ = (Real.sqrt (n : ℝ))⁻¹ *
          Real.sqrt ((n : ℝ)⁻¹ * ∑ k : Fin n, (g (S k)) ^ 2) := by
          rw [Real.sqrt_inv]
    _ = empiricalNorm S g / Real.sqrt (n : ℝ) := by
          unfold empiricalNorm
          ring

private lemma starHullZeroOutScaleCoeff_mul_empiricalNorm_le
    {ι 𝒳 : Type*} {n : ℕ}
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (Hloc : LocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) {r : ℝ} (hr : 0 ≤ r) (i : ι) :
    starHullZeroOutScaleCoeff F norm r i * empiricalNorm S (F i) ≤ r := by
  classical
  have hnorm_nonneg : 0 ≤ empiricalNorm S (F i) := by
    unfold empiricalNorm
    positivity
  have hmul :
      (⨆ a : Set.Icc (0 : ℝ) 1,
          (if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0) *
            empiricalNorm S (F i))
        =
      starHullZeroOutScaleCoeff F norm r i * empiricalNorm S (F i) := by
    rw [ciSup_mul_const_of_le_one
      (fun a : Set.Icc (0 : ℝ) 1 =>
        if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0)
      (empiricalNorm S (F i))
      (by
        intro a
        dsimp
        split_ifs
        · exact a.property.2
        · norm_num)
      hnorm_nonneg]
    rfl
  rw [← hmul]
  refine ciSup_le ?_
  intro a
  by_cases hactive : norm (starHullEval F (a, i)) ≤ r
  · have hnorm := Hloc.empirical_radius S hr (a, i)
    have heq :
        empiricalNorm S (starHullZeroOut F norm r (a, i))
          = (a : ℝ) * empiricalNorm S (F i) := by
      calc
        empiricalNorm S (starHullZeroOut F norm r (a, i))
            = empiricalNorm S (fun x => (a : ℝ) * F i x) := by
              congr
              funext x
              simp [starHullZeroOut, hactive, starHullEval]
        _ = (a : ℝ) * empiricalNorm S (F i) :=
              empiricalNorm_const_mul S (a : ℝ) a.property.1 (F i)
    simpa [hactive, heq] using hnorm
  · calc
      (if norm (starHullEval F (a, i)) ≤ r then (a : ℝ) else 0) *
          empiricalNorm S (F i) = 0 := by
          simp [hactive]
      _ ≤ r := hr

private lemma starHullPatternCoeff_mul_empiricalNorm_rep_le
    {ι 𝒳 : Type*} {n : ℕ}
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (Hloc : LocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) {r : ℝ} (hr : 0 ≤ r)
    (A : {A // A ∈ growthFamily π S}) :
    starHullPatternCoeff F norm π S r A *
        empiricalNorm S (F (growthFamilyRep π S A)) ≤ r := by
  classical
  rcases hfactor S with ⟨φ, hφ⟩
  let repSub : {i : ι // restrictionPattern (π i) S = A.1} :=
    ⟨growthFamilyRep π S A, growthFamilyRep_spec π S A⟩
  haveI : Nonempty {i : ι // restrictionPattern (π i) S = A.1} := ⟨repSub⟩
  have hnorm_nonneg : 0 ≤ empiricalNorm S (F (growthFamilyRep π S A)) := by
    unfold empiricalNorm
    positivity
  have hmul :
      (⨆ i : {i : ι // restrictionPattern (π i) S = A.1},
          starHullZeroOutScaleCoeff F norm r i.1 *
            empiricalNorm S (F (growthFamilyRep π S A)))
        =
      starHullPatternCoeff F norm π S r A *
        empiricalNorm S (F (growthFamilyRep π S A)) := by
    rw [starHullPatternCoeff]
    rw [ciSup_mul_const_of_le_one
      (fun i : {i : ι // restrictionPattern (π i) S = A.1} =>
        starHullZeroOutScaleCoeff F norm r i.1)
      (empiricalNorm S (F (growthFamilyRep π S A)))
      (fun i => starHullZeroOutScaleCoeff_le_one F norm r i.1)
      hnorm_nonneg]
  rw [← hmul]
  refine ciSup_le ?_
  intro i
  have hnorm_eq :
      empiricalNorm S (F i.1) =
        empiricalNorm S (F (growthFamilyRep π S A)) := by
    have hpoint : ∀ k : Fin n,
        F i.1 (S k) = F (growthFamilyRep π S A) (S k) :=
      sample_eq_growthFamilyRep_of_pattern (F := F) (π := π) (S := S)
        (φ := φ) hφ A i.2
    simp [empiricalNorm, hpoint]
  simpa [hnorm_eq] using
    starHullZeroOutScaleCoeff_mul_empiricalNorm_le F norm Hloc S hr i.1

private lemma starHullPatternClass_radius_le
    {ι 𝒳 : Type*} {n : ℕ} (hn : 0 < n)
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (Hloc : LocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) {r : ℝ} (hr : 0 ≤ r)
    (A : {A // A ∈ growthFamily π S}) :
    Real.sqrt (∑ k : Fin n,
        ((n : ℝ)⁻¹ * |starHullPatternClass F norm π S r A (S k)|)^2)
      ≤ r / Real.sqrt (n : ℝ) := by
  classical
  rw [sqrt_sum_inv_abs_sq_eq_empiricalNorm_div_sqrt hn]
  have hnorm :
      empiricalNorm S (starHullPatternClass F norm π S r A)
        =
      starHullPatternCoeff F norm π S r A *
        empiricalNorm S (F (growthFamilyRep π S A)) := by
    exact empiricalNorm_const_mul S
      (starHullPatternCoeff F norm π S r A)
      (starHullPatternCoeff_nonneg F norm π S r A)
      (F (growthFamilyRep π S A))
  rw [hnorm]
  exact div_le_div_of_nonneg_right
    (starHullPatternCoeff_mul_empiricalNorm_rep_le F norm π hfactor Hloc S hr A)
    (Real.sqrt_nonneg _)

omit [Nonempty ι] [Countable ι] in
private lemma starHullZeroOut_empirical_rademacher_le_growthFamily
    [Nonempty ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    {n : ℕ} (hn : 0 < n)
    (Hloc : LocalizedVCDudleyHypotheses F norm)
    (S : Fin n → 𝒳) (r : ℝ) (hr : 0 ≤ r) :
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
      ≤ r * Real.sqrt
        ((2 * Real.log (2 * ((growthFamily π S).card : ℝ))) / (n : ℝ)) := by
  classical
  let W : {A // A ∈ growthFamily π S} → 𝒳 → ℝ :=
    starHullPatternClass F norm π S r
  have hgf_nonempty : (growthFamily π S).Nonempty := by
    let i0 : ι := Classical.arbitrary ι
    refine ⟨restrictionPattern (π i0) S, ?_⟩
    rw [mem_growthFamily_iff]
    exact ⟨i0, rfl⟩
  haveI : Nonempty {A // A ∈ growthFamily π S} := by
    rcases hgf_nonempty with ⟨A, hA⟩
    exact ⟨⟨A, hA⟩⟩
  have hcollapse :
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ empiricalRademacherComplexity n W S := by
    simpa [W] using
      starHullZeroOut_empirical_rademacher_le_patternClass F norm π hfactor S r
  have hρ_nonneg : 0 ≤ r / Real.sqrt (n : ℝ) :=
    div_nonneg hr (Real.sqrt_nonneg _)
  have hfinite_on :
      empiricalRademacherComplexity n
          (F_on W (Finset.univ : Finset {A // A ∈ growthFamily π S})) S
        ≤
      (r / Real.sqrt (n : ℝ)) *
        Real.sqrt
          (2 * Real.log
            (2 * (((Finset.univ : Finset {A // A ∈ growthFamily π S}).card : ℝ)))) := by
    refine empiricalRademacher_withAbs_finiteClass_le
      (ι' := {A // A ∈ growthFamily π S}) (Z := 𝒳)
      hn W S (Finset.univ : Finset {A // A ∈ growthFamily π S})
      ?_ (r / Real.sqrt (n : ℝ)) hρ_nonneg ?_
    · simpa using
        (Finset.univ_nonempty :
          (Finset.univ : Finset {A // A ∈ growthFamily π S}).Nonempty)
    · intro A _hA
      simpa [W] using
        starHullPatternClass_radius_le hn F norm π hfactor Hloc S hr A
  have hfinite :
      empiricalRademacherComplexity n W S
        ≤
      (r / Real.sqrt (n : ℝ)) *
        Real.sqrt (2 * Real.log (2 * ((growthFamily π S).card : ℝ))) := by
    have hcard :
        (((Finset.univ : Finset {A // A ∈ growthFamily π S}).card : ℝ))
          = ((growthFamily π S).card : ℝ) := by
      simp
    have hfinite_univ := hfinite_on
    rw [empiricalRademacherComplexity_F_on_univ_eq W S] at hfinite_univ
    simpa [hcard] using hfinite_univ
  let L : ℝ := 2 * Real.log (2 * ((growthFamily π S).card : ℝ))
  have hcard_pos : 0 < (growthFamily π S).card := Finset.card_pos.mpr hgf_nonempty
  have hlog_nonneg : 0 ≤ Real.log (2 * ((growthFamily π S).card : ℝ)) := by
    have hcard_one : (1 : ℝ) ≤ ((growthFamily π S).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hcard_pos)
    have hone_le : (1 : ℝ) ≤ 2 * ((growthFamily π S).card : ℝ) := by
      nlinarith
    exact Real.log_nonneg hone_le
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (by norm_num) hlog_nonneg
  calc
    empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ empiricalRademacherComplexity n W S := hcollapse
    _ ≤ (r / Real.sqrt (n : ℝ)) * Real.sqrt L := by
        simpa [L] using hfinite
    _ = r * Real.sqrt (L / (n : ℝ)) := by
        rw [Real.sqrt_div hL_nonneg]
        ring
    _ = r * Real.sqrt
        ((2 * Real.log (2 * ((growthFamily π S).card : ℝ))) / (n : ℝ)) := by
        rfl

omit [Nonempty ι] [Countable ι] in
/-- Massart finite-realization bound for the localized star-hull zero-out
class under binary trace entropy control.

This is the genuine analytic substep: star-hull scale contraction, empirical
radius control, finite Boolean-pattern reduction, and Massart's lemma. -/
lemma starHullZeroOut_empirical_rademacher_massart_vc
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (d n : ℕ)
    (Htrace : BinaryTraceEntropyControl π d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ r * Real.sqrt
          ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)) := by
  intro S r hr
  by_cases hn0 : n = 0
  · subst n
    simp [empiricalRademacherComplexity]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hι : Nonempty ι
    · haveI : Nonempty ι := hι
      have hcard_pos : 0 < (growthFamily π S).card := by
        let i0 : ι := Classical.choice hι
        have hmem : restrictionPattern (π i0) S ∈ growthFamily π S := by
          rw [mem_growthFamily_iff]
          exact ⟨i0, rfl⟩
        exact Finset.card_pos.mpr ⟨_, hmem⟩
      have hcard :
          (growthFamily π S).card ≤ (n + 1) ^ d :=
        growthFamily_card_le_succ_pow_of_trace π d n Htrace S
      have hmass :=
        starHullZeroOut_empirical_rademacher_le_growthFamily
          F norm π hfactor hn Hloc S r hr
      have hlog :=
        log_two_growth_card_le π d n S hcard_pos hcard
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hsqrt :
          Real.sqrt
              ((2 * Real.log (2 * ((growthFamily π S).card : ℝ))) / (n : ℝ))
            ≤
          Real.sqrt
              ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)) := by
        exact Real.sqrt_le_sqrt
          (div_le_div_of_nonneg_right hlog (le_of_lt hnR))
      exact hmass.trans (mul_le_mul_of_nonneg_left hsqrt hr)
    · letI : IsEmpty ι := ⟨fun i => hι ⟨i⟩⟩
      have hzero :
          empiricalRademacherComplexity n (starHullZeroOut F norm r) S = 0 := by
        simp [empiricalRademacherComplexity, starHullParam]
      rw [hzero]
      exact mul_nonneg hr (Real.sqrt_nonneg _)

omit [Nonempty ι] [Countable ι] in
/-- Shared absolute-form Dudley/VC bridge for the localized star-hull class.

This combines star-hull scale contraction, the binary trace entropy control
from `VCCovering`, and the finite-realization Massart bound into the linear
localized Rademacher envelope used by the regime package. -/
lemma absolute_dudley_vc_starHullZeroOut_linear_residual_shared
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Htrace : BinaryTraceEntropyControl π d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K d n r := by
  intro S r hr
  have hmass :=
    starHullZeroOut_empirical_rademacher_massart_vc
      F norm π hfactor d n Htrace Hloc S r hr
  by_cases hn0 : n = 0
  · simpa [vcLocalizedPsi, vcLocalizedSlope, hn0] using hmass
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hK0 : 0 ≤ K := le_trans zero_le_one hK
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := by
      have hone_le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        linarith [le_of_lt hnR]
      exact Real.log_nonneg hone_le
    have hD_nonneg : 0 ≤ (d : ℝ) * Real.log ((n : ℝ) + 1) :=
      mul_nonneg (Nat.cast_nonneg d) hlog
    have hKD :
        (d : ℝ) * Real.log ((n : ℝ) + 1)
          ≤ K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by
      calc
        (d : ℝ) * Real.log ((n : ℝ) + 1)
            = 1 * ((d : ℝ) * Real.log ((n : ℝ) + 1)) := by ring
        _ ≤ K * ((d : ℝ) * Real.log ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hK hD_nonneg
        _ = K * (d : ℝ) * Real.log ((n : ℝ) + 1) := by ring
    have hnum :
        2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2
          ≤ 36 * (K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) := by
      nlinarith
    have hfrac :
        (2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)
          ≤ 36 *
            ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
      have hdiv :=
        div_le_div_of_nonneg_right hnum (le_of_lt hnR)
      simpa [mul_div_assoc, mul_assoc] using hdiv
    have hsqrt :
        Real.sqrt
            ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ))
          ≤
        6 * Real.sqrt
            ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
      calc
        Real.sqrt
            ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ))
            ≤ Real.sqrt
                (36 *
                  ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ))) :=
              Real.sqrt_le_sqrt hfrac
        _ = 6 * Real.sqrt
              ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
              have hsqrt36 : Real.sqrt (36 : ℝ) = 6 := by
                have hsq : (Real.sqrt (36 : ℝ)) ^ 2 = (6 : ℝ) ^ 2 := by
                  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 36)]
                  norm_num
                rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
                · exact h
                · nlinarith [Real.sqrt_nonneg (36 : ℝ)]
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36)]
              rw [hsqrt36]
    calc
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
          ≤ r * Real.sqrt
              ((2 * (d : ℝ) * Real.log ((n : ℝ) + 1) + 2) / (n : ℝ)) :=
            hmass
      _ ≤ r *
          (6 * Real.sqrt
            ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hsqrt hr
      _ = vcLocalizedPsi K d n r := by
            simp [vcLocalizedPsi, vcLocalizedSlope]
            ring

omit [Nonempty ι] [Countable ι] in
/-- VC-dimension specialization of the shared absolute-form Dudley bridge. -/
lemma absolute_dudley_vc_starHullZeroOut_linear_residual
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K d n r :=
  absolute_dudley_vc_starHullZeroOut_linear_residual_shared
    F norm Hvc.π Hvc.factor K d n hK (Or.inl Hvc.vcDim_le) Hloc

omit [Nonempty ι] [Countable ι] in
/-- Cardinality-bound specialization of the shared absolute-form Dudley bridge. -/
lemma absolute_dudley_vc_starHullZeroOut_linear_residual_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K dPi n r :=
  absolute_dudley_vc_starHullZeroOut_linear_residual_shared
    F norm π hfactor K dPi n hK (Or.inr hcard) Hloc

omit [Nonempty ι] [Countable ι] in
/-- The generic finite-VC/Dudley sample-path bridge for the localized
star-hull class.

See `absolute_dudley_vc_starHullZeroOut_linear_residual_shared` for the shared
absolute-form bridge that feeds this finite-VC specialization. -/
lemma vc_starHullZeroOut_empirical_rademacher_le_linear
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K d n r :=
  absolute_dudley_vc_starHullZeroOut_linear_residual F norm K d n hK Hvc Hloc

omit [Nonempty ι] [Countable ι] in
/-- Cardinality-bound sample-path bridge for the localized star-hull class.
This is the direct growth-function analogue of
`vc_starHullZeroOut_empirical_rademacher_le_linear`. -/
lemma vc_starHullZeroOut_empirical_rademacher_le_linear_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ (S : Fin n → 𝒳) (r : ℝ), 0 ≤ r →
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S
        ≤ vcLocalizedPsi K dPi n r :=
  absolute_dudley_vc_starHullZeroOut_linear_residual_of_card
    F norm π hfactor K dPi n hK hcard Hloc

omit [Nonempty ι] [Countable ι] in
/-- The generic finite-VC/Dudley population bridge for the localized star-hull
class. -/
lemma vc_starHullZeroOut_population_rademacher_le_linear
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, 0 ≤ r →
      rademacherComplexity n (starHullZeroOut F norm r) μ X
        ≤ vcLocalizedPsi K d n r := by
  intro r hr
  let C := vcLocalizedPsi K d n r
  have hpoint : ∀ S : Fin n → 𝒳,
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S ≤ C := by
    intro S
    exact vc_starHullZeroOut_empirical_rademacher_le_linear
      F norm K d n hK Hvc Hloc S r hr
  have h_abs : ∀ᵐ ω : Fin n → Ω ∂(Measure.pi fun _ : Fin n => μ),
      |empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω)| ≤ C := by
    exact Filter.Eventually.of_forall fun ω => by
      have hnonneg : 0 ≤ empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω) := by
        unfold empiricalRademacherComplexity
        refine mul_nonneg ?_ ?_
        · positivity
        · refine Finset.sum_nonneg ?_
          intro σ _
          refine Real.iSup_nonneg ?_
          intro p
          exact abs_nonneg _
      rw [abs_of_nonneg hnonneg]
      exact hpoint (X ∘ ω)
  unfold rademacherComplexity
  change ∫ ω : Fin n → Ω,
      empiricalRademacherComplexity n
        (starHullZeroOut F norm r) (X ∘ ω)
        ∂(Measure.pi fun _ : Fin n => μ) ≤ C
  exact le_trans (le_abs_self _)
    (abs_expectation_le_of_abs_le_const h_abs)

omit [Nonempty ι] [Countable ι] in
/-- Cardinality-bound population bridge for the localized star-hull class. -/
lemma vc_starHullZeroOut_population_rademacher_le_linear_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, 0 ≤ r →
      rademacherComplexity n (starHullZeroOut F norm r) μ X
        ≤ vcLocalizedPsi K dPi n r := by
  intro r hr
  let C := vcLocalizedPsi K dPi n r
  have hpoint : ∀ S : Fin n → 𝒳,
      empiricalRademacherComplexity n (starHullZeroOut F norm r) S ≤ C := by
    intro S
    exact vc_starHullZeroOut_empirical_rademacher_le_linear_of_card
      F norm π hfactor K dPi n hK hcard Hloc S r hr
  have h_abs : ∀ᵐ ω : Fin n → Ω ∂(Measure.pi fun _ : Fin n => μ),
      |empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω)| ≤ C := by
    exact Filter.Eventually.of_forall fun ω => by
      have hnonneg : 0 ≤ empiricalRademacherComplexity n
          (starHullZeroOut F norm r) (X ∘ ω) := by
        unfold empiricalRademacherComplexity
        refine mul_nonneg ?_ ?_
        · positivity
        · refine Finset.sum_nonneg ?_
          intro σ _
          refine Real.iSup_nonneg ?_
          intro p
          exact abs_nonneg _
      rw [abs_of_nonneg hnonneg]
      exact hpoint (X ∘ ω)
  unfold rademacherComplexity
  change ∫ ω : Fin n → Ω,
      empiricalRademacherComplexity n
        (starHullZeroOut F norm r) (X ∘ ω)
        ∂(Measure.pi fun _ : Fin n => μ) ≤ C
  exact le_trans (le_abs_self _)
    (abs_expectation_le_of_abs_le_const h_abs)

omit [Nonempty ι] [Countable ι] in
/-- The finite-VC localized envelope upper-bounds population localized
Rademacher complexity. -/
theorem vcLocalizedRademacherUpperBound
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    RademacherUpperBound F norm μ X n (vcLocalizedPsi K d n) := by
  intro r hr
  exact vc_starHullZeroOut_population_rademacher_le_linear
    F norm μ X K d n hK Hvc Hloc r hr

omit [Nonempty ι] [Countable ι] in
/-- The growth-cardinality localized envelope upper-bounds population
localized Rademacher complexity. -/
theorem vcLocalizedRademacherUpperBound_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    RademacherUpperBound F norm μ X n (vcLocalizedPsi K dPi n) := by
  intro r hr
  exact vc_starHullZeroOut_population_rademacher_le_linear_of_card
    F norm π μ X hfactor K dPi n hK hcard Hloc r hr

omit [Nonempty ι] [Countable ι] in
/-- Fixed-`n` finite-VC localized envelope package: sub-root envelope,
localized Rademacher upper bound, critical-radius bound by the slope, and
squared critical-radius rate. -/
theorem vcLocalizedEnvelope
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    SubRoot (vcLocalizedPsi K d n) ∧
      RademacherUpperBound F norm μ X n (vcLocalizedPsi K d n) ∧
      criticalRadius (vcLocalizedPsi K d n) ≤ vcLocalizedSlope K d n ∧
      (criticalRadius (vcLocalizedPsi K d n)) ^ 2 ≤
        36 * ((K * (d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / (n : ℝ)) := by
  refine ⟨vcLocalizedPsi_subRoot K d n, ?_, ?_, ?_⟩
  · exact vcLocalizedRademacherUpperBound F norm μ X K d n hK Hvc Hloc
  · exact criticalRadius_vcLocalizedPsi_le (le_trans zero_le_one hK) hn
  · exact criticalRadius_vcLocalizedPsi_sq_le_rate (le_trans zero_le_one hK) hn

omit [Nonempty ι] [Countable ι] in
/-- Build the `LocalizedRegime` bundle for the localized-deviation theorems
from a bounded finite-VC class and the finite-VC localized envelope. -/
noncomputable def vcLocalizedRegime
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i ω, |F i (X ω)| ≤ b)
    (K : ℝ) (d : ℕ) (hK : (1 : ℝ) ≤ K)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    LocalizedRegime Ω ι 𝒳 F norm μ X where
  b := b
  b_nonneg := hb
  bound := hbound
  ψ := fun n => vcLocalizedPsi K d n
  ψ_subRoot := fun n => vcLocalizedPsi_subRoot K d n
  ψ_ub := fun n => vcLocalizedRademacherUpperBound F norm μ X K d n hK Hvc Hloc

omit [Nonempty ι] [Countable ι] in
/-- Build the `LocalizedRegime` bundle from a direct growth-cardinality bound
on the binary trace family. -/
noncomputable def vcLocalizedRegime_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i ω, |F i (X ω)| ≤ b)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi : ℕ) (hK : (1 : ℝ) ≤ K)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    LocalizedRegime Ω ι 𝒳 F norm μ X where
  b := b
  b_nonneg := hb
  bound := hbound
  ψ := fun n => vcLocalizedPsi K dPi n
  ψ_subRoot := fun n => vcLocalizedPsi_subRoot K dPi n
  ψ_ub := fun n =>
    vcLocalizedRademacherUpperBound_of_card
      F norm π μ X hfactor K dPi n hK hcard Hloc

end RademacherBridge

end Concentration
end Stat
end Causalean
