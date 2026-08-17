import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Basic
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization

/-!
# Run-specific Poissonization specializations

This file specializes the shared finite-sample and de-Poissonization substrate
to the accepted run’s observation law and frontier rate.
-/

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
noncomputable def iidObservationStreamLaw (P : CtyLaw) : Measure (ℕ → Observation) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  exact Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw P.law

/-- The infinite i.i.d. observation stream is a probability law. -/
instance iidObservationStreamLaw_isProbabilityMeasure (P : CtyLaw) :
    IsProbabilityMeasure (iidObservationStreamLaw P) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  unfold iidObservationStreamLaw
  infer_instance

/-- Every finite prefix of the infinite i.i.d. stream has the original product
sample law. -/
lemma iidObservationStreamLaw_map_finPrefix (P : CtyLaw) (n : ℕ) :
    Measure.map (fun z : ℕ → Observation => fun i : Fin n => z i)
        (iidObservationStreamLaw P) = sampleLaw P n := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  simpa [iidObservationStreamLaw, sampleLaw] using
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw_map_finPrefix P.law n)

/-- A mean-`2n` count paired with an independent infinite i.i.d. observation
stream.  The first `n` stream coordinates implement the retained sample on
the successful-count event. -/
noncomputable def poissonIIDStreamLaw (P : CtyLaw) (n : ℕ) :
    Measure (ℕ × (ℕ → Observation)) :=
  by
    letI : IsProbabilityMeasure P.law := P.law_isProbability
    exact Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.poissonIIDStreamLaw P.law (2 * n)

/-- The independent Poisson-count and i.i.d.-stream pairing is a probability
law. -/
instance poissonIIDStreamLaw_isProbabilityMeasure (P : CtyLaw) (n : ℕ) :
    IsProbabilityMeasure (poissonIIDStreamLaw P n) := by
  unfold poissonIIDStreamLaw
  infer_instance

/-- The count coordinate of the stream construction is Poisson with mean
`2n`. -/
lemma poissonIIDStreamLaw_map_count (P : CtyLaw) (n : ℕ) :
    Measure.map Prod.fst (poissonIIDStreamLaw P n) = poissonMeasure (2 * n) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  simpa [poissonIIDStreamLaw] using
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.poissonIIDStreamLaw_map_count
      P.law (2 * n))

/-- Taking the first `n` observations from the stream construction gives
exactly the original i.i.d. sample law. -/
lemma poissonIIDStreamLaw_map_finPrefix (P : CtyLaw) (n : ℕ) :
    Measure.map (fun z : ℕ × (ℕ → Observation) => fun i : Fin n => z.2 i)
        (poissonIIDStreamLaw P n) = sampleLaw P n := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  simpa [poissonIIDStreamLaw, sampleLaw] using
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.poissonIIDStreamLaw_map_finPrefix
      P.law (2 * n) n)

/-- A coupling of a mean-`2n` Poisson count with an exactly i.i.d. retained
sample of size `n`. -/
def MarkedPoissonEmbedding (P : CtyLaw) (n : ℕ) : Prop :=
  ∃ μ : Measure (ℕ × Sample n),
    IsProbabilityMeasure μ ∧
    Measure.map Prod.fst μ = poissonMeasure (2 * n) ∧
    Measure.map Prod.snd μ = sampleLaw P n

/-- The marked mean-`2n` experiment can retain the `n` smallest marks and hence
couple back to an exact `P^n` sample. -/
lemma marked_mean_two_n_poisson_embedding (P : CtyLaw) (n : ℕ) :
    MarkedPoissonEmbedding P n := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let streamMap : ℕ × (ℕ → Observation) → ℕ × Sample n :=
    fun z => (z.1, fun i => z.2 i)
  let mu := Measure.map streamMap (poissonIIDStreamLaw P n)
  have hstreamMap : Measurable streamMap := by fun_prop
  refine ⟨mu, Measure.isProbabilityMeasure_map hstreamMap.aemeasurable, ?_, ?_⟩
  · dsimp [mu]
    rw [Measure.map_map (measurable_fst : Measurable (Prod.fst : ℕ × Sample n → ℕ))
        hstreamMap,
      show Prod.fst ∘ streamMap = Prod.fst by rfl,
      poissonIIDStreamLaw_map_count]
  · dsimp [mu]
    rw [Measure.map_map (measurable_snd :
        Measurable (Prod.snd : ℕ × Sample n → Sample n)) hstreamMap,
      show Prod.snd ∘ streamMap =
        (fun z : ℕ × (ℕ → Observation) => fun i : Fin n => z.2 i) by rfl,
      poissonIIDStreamLaw_map_finPrefix]

/-- Read the first `n` observations from a configuration that is already in
canonical mark order, forgetting the marks. -/
-- @node: canonicalPrefixObservations
lemma poisson_remainder_isLittleO_frontier :
    (fun n : ℕ => Real.exp (-(n : ℝ) * (1 - Real.log 2))) =o[Filter.atTop]
      frontierRate := by
  have ha : 0 < (1 - Real.log 2 : ℝ) := by
    linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hexp :
      (fun n : ℕ => Real.exp (-(1 - Real.log 2) * (n : ℝ))) =o[atTop]
        (fun n : ℕ => Real.rpow (n : ℝ) (-(1 : ℝ) / 4)) := by
    simpa [Function.comp_def] using
      (isLittleO_exp_neg_mul_rpow_atTop ha (-(1 : ℝ) / 4)).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hnpos : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hdom :
      (fun n : ℕ => Real.rpow (n : ℝ) (-(1 : ℝ) / 4)) =O[atTop]
        frontierRate := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hlog, hnpos] with n hlogn hn
    have hnreal : (0 : ℝ) < n := by positivity
    have hbase : (n : ℝ)⁻¹ ≤ Real.log (n : ℝ) / (n : ℝ) := by
      rw [inv_eq_one_div]
      exact (div_le_div_iff_of_pos_right hnreal).2 hlogn
    have hquot : 0 ≤ Real.log (n : ℝ) / (n : ℝ) :=
      div_nonneg (le_trans zero_le_one hlogn) hnreal.le
    have hrpow := Real.rpow_le_rpow (inv_nonneg.mpr hnreal.le) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    change |(n : ℝ) ^ (-(1 : ℝ) / 4)| ≤
      1 * |(Real.log (n : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4)|
    rw [one_mul,
      abs_of_nonneg (Real.rpow_nonneg hnreal.le (-(1 : ℝ) / 4)),
      abs_of_nonneg (Real.rpow_nonneg hquot ((1 : ℝ) / 4)),
      show -(1 : ℝ) / 4 = -(1 / 4 : ℝ) by ring,
      Real.rpow_neg_eq_inv_rpow]
    exact hrpow
  have hexp' :
      (fun n : ℕ => Real.exp (-(n : ℝ) * (1 - Real.log 2))) =o[atTop]
        (fun n : ℕ => Real.rpow (n : ℝ) (-(1 : ℝ) / 4)) := by
    apply hexp.congr'
    · filter_upwards with n
      congr 1
      ring
    · exact EventuallyEq.rfl
  exact hexp'.trans_isBigO hdom


end CausalSmith.Stat.BddUniformLogPenalty
