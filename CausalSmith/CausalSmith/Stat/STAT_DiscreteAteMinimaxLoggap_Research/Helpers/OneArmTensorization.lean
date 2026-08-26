import Causalean.Stat.Minimax.TotalVariation
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open scoped ENNReal BigOperators

/-- Total variation contracts under a measurable deterministic map. -/
lemma tvDist_map_le
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) :
    Causalean.Stat.tvDist (μ.map f) (ν.map f) ≤
      Causalean.Stat.tvDist μ ν := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro A
  rw [Measure.real, Measure.real, Measure.map_apply hf A.2,
    Measure.map_apply hf A.2]
  exact Causalean.Stat.abs_measureReal_sub_le_tvDist (A.2.preimage hf)

lemma pmf_toMeasure_real_apply
    {α : Type*} [MeasurableSpace α] (p : PMF α) {A : Set α}
    (hA : MeasurableSet A) :
    p.toMeasure.real A = ∑' x, A.indicator (fun x => (p x).toReal) x := by
  classical
  rw [Measure.real, PMF.toMeasure_apply p hA,
    ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  · intro x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx, p.apply_ne_top]

/-- On a countable discrete space, statistical total variation is bounded by
the full `ℓ¹` distance between probability masses. -/
lemma tvDist_pmf_toMeasure_le_tsum_abs
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) :
    Causalean.Stat.tvDist p.toMeasure q.toMeasure ≤
      ∑' x, |(p x).toReal - (q x).toReal| := by
  classical
  let fp : α → ℝ := fun x => (p x).toReal
  let fq : α → ℝ := fun x => (q x).toReal
  have hp : Summable fp := ENNReal.summable_toReal <| by
    exact p.tsum_coe_ne_top
  have hq : Summable fq := ENNReal.summable_toReal <| by
    exact q.tsum_coe_ne_top
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro A
  rw [pmf_toMeasure_real_apply p A.2,
    pmf_toMeasure_real_apply q A.2]
  let fA : α → ℝ := A.1.indicator fp
  let gA : α → ℝ := A.1.indicator fq
  have hfA : Summable fA := Summable.of_nonneg_of_le
    (fun x => by by_cases hx : x ∈ A.1 <;>
      simp [fA, Set.indicator, hx, fp, ENNReal.toReal_nonneg])
    (fun x => by by_cases hx : x ∈ A.1 <;>
      simp [fA, Set.indicator, hx, fp, ENNReal.toReal_nonneg]) hp
  have hgA : Summable gA := Summable.of_nonneg_of_le
    (fun x => by by_cases hx : x ∈ A.1 <;>
      simp [gA, Set.indicator, hx, fq, ENNReal.toReal_nonneg])
    (fun x => by by_cases hx : x ∈ A.1 <;>
      simp [gA, Set.indicator, hx, fq, ENNReal.toReal_nonneg]) hq
  rw [← hfA.tsum_sub hgA]
  change ‖∑' x, (fA x - gA x)‖ ≤ ∑' x, ‖fp x - fq x‖
  calc
    _ ≤ ∑' x, ‖fA x - gA x‖ :=
      norm_tsum_le_tsum_norm (hfA.sub hgA).norm
    _ ≤ ∑' x, ‖fp x - fq x‖ := by
      apply Summable.tsum_le_tsum
      · intro x
        by_cases hx : x ∈ A.1 <;> simp [fA, gA, hx]
      · exact (hfA.sub hgA).norm
      · exact (hp.sub hq).norm

/-- Split a full `ℓ¹` difference into a finite low-count region and the two
nonnegative masses on its complement. -/
lemma tsum_abs_sub_le_sum_add_compl
    {α : Type*} (f g : α → ℝ) (S : Finset α)
    (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    ∑' x, |f x - g x| ≤
      (∑ x ∈ S, |f x - g x|) +
        ∑' x : {x // x ∉ S}, (f x + g x) := by
  classical
  have habs : Summable (fun x => |f x - g x|) := (hf.sub hg).abs
  rw [← habs.sum_add_tsum_compl (s := S)]
  gcongr
  apply Summable.tsum_le_tsum
  · intro x
    exact abs_sub_le_iff.mpr ⟨by linarith [hf0 x, hg0 x], by linarith [hf0 x, hg0 x]⟩
  · exact habs.subtype _
  · exact (hf.add hg).subtype _

lemma tsum_abs_pmf_sub_le_sum_add_compl
    {α : Type*} (p q : PMF α) (S : Finset α) :
    ∑' x, |(p x).toReal - (q x).toReal| ≤
      (∑ x ∈ S, |(p x).toReal - (q x).toReal|) +
        ∑' x : {x // x ∉ S}, ((p x).toReal + (q x).toReal) := by
  apply tsum_abs_sub_le_sum_add_compl
  · exact ENNReal.summable_toReal p.tsum_coe_ne_top
  · exact ENNReal.summable_toReal q.tsum_coe_ne_top
  · exact fun _ => ENNReal.toReal_nonneg
  · exact fun _ => ENNReal.toReal_nonneg

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
