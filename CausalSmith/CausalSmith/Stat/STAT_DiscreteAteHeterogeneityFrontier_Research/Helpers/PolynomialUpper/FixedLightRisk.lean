/- Fixed-light expectation, bias, and variance assembly. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Bias
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovarianceAssembly

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory

-- @node: integrable_allBlockOrderedMarkedFactorial
/-- [Each finite-product marked factorial is integrable; this is the finite-law counterpart of the
  infinite-IID `MemLp` certificate used in the covariance proof](goal). -/
lemma integrable_allBlockOrderedMarkedFactorial
    {d m : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a : Bool) (j : ℕ) :
    Integrable (fun s : Fin m → Obs d ↦
      allBlockOrderedMarkedFactorial M s k a j) (productLaw m P.law) := by
  let S0 := Causalean.Stat.iidSample_infinitePi P.law.observedLaw
  have hpush := Causalean.Stat.iidSample_finN_pushforward S0 m
  have hprefix : Measurable (fun ω : ℕ → Obs d ↦ fun i : Fin m ↦ ω i) :=
    Causalean.Stat.iidSample_finN_measurable S0 m
  dsimp [S0, Causalean.Stat.iidSample_infinitePi] at hpush hprefix
  unfold productLaw
  rw [← hpush]
  apply (integrable_map_measure
    (measurable_allBlockOrderedMarkedFactorial M k a j).aestronglyMeasurable
    hprefix.aemeasurable).2
  exact (memLp_allBlockOrderedMarkedFactorial P k a j).integrable one_le_two

-- @node: integral_allBlockLightPolynomialTerm_eq_population
/-- If [the outcome bound is positive](hyp:hB) and [the polynomial degree fits the sample
  block](hyp:hKm), [the exact marked-factorial expectation reconstructs the deterministic
  population polynomial for one light cell](goal). -/
lemma integral_allBlockLightPolynomialTerm_eq_population
    {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d)
    (hB : 0 < B) (hKm : K ≤ m) :
    ∫ s : Fin m → Obs d, allBlockLightPolynomialTerm M B K s k
        ∂(productLaw m P.law) =
      polynomialLightCellPopulationTerm P.law M B K k := by
  unfold allBlockLightPolynomialTerm polynomialLightCellPopulationTerm
  rw [integral_finsetSum]
  · dsimp only
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j + 2 ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    rw [integral_const_mul,
      integral_sub (integrable_allBlockOrderedMarkedFactorial P k true j)
        (integrable_allBlockOrderedMarkedFactorial P k false j),
      integral_allBlockOrderedMarkedFactorial_exact P k true j hjm,
      integral_allBlockOrderedMarkedFactorial_exact P k false j hjm]
    simp only [if_true, Bool.false_eq_true, if_false]
    simp_rw [div_pow]
    rw [pow_succ]
    field_simp [hB.ne']
  · intro j hj
    exact ((integrable_allBlockOrderedMarkedFactorial P k true j).sub
      (integrable_allBlockOrderedMarkedFactorial P k false j)).const_mul _

-- @node: memLp_allBlockLightPolynomialTerm_finite
/-- [A finite-product light-cell polynomial is square-integrable](goal). -/
lemma memLp_allBlockLightPolynomialTerm_finite
    {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) :
    MemLp (fun s : Fin m → Obs d ↦
      allBlockLightPolynomialTerm M B K s k) 2 (productLaw m P.law) := by
  let S0 := Causalean.Stat.iidSample_infinitePi P.law.observedLaw
  have hpush := Causalean.Stat.iidSample_finN_pushforward S0 m
  have hprefix : Measurable (fun ω : ℕ → Obs d ↦ fun i : Fin m ↦ ω i) :=
    Causalean.Stat.iidSample_finN_measurable S0 m
  dsimp [S0, Causalean.Stat.iidSample_infinitePi] at hpush hprefix
  unfold productLaw
  rw [← hpush]
  have heq : (fun s : Fin m → Obs d ↦
      allBlockLightPolynomialTerm M B K s k) =
      allBlockMarkedPolynomialSum M B K {k} := by
    funext s
    simp [allBlockMarkedPolynomialSum]
  apply (memLp_map_measure_iff
    (by
      rw [heq]
      exact (measurable_allBlockMarkedPolynomialSum M B K {k}).aestronglyMeasurable)
    hprefix.aemeasurable).2
  exact memLp_allBlockLightPolynomialTerm P k

-- @node: integral_allBlockMarkedPolynomialSum_eq_population
/-- If [the outcome bound is positive](hyp:hB) and [the polynomial degree fits the sample
  block](hyp:hKm), [summing the cellwise exact expectations reconstructs the population polynomial
  over a deterministic light set](goal). -/
lemma integral_allBlockMarkedPolynomialSum_eq_population
    {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (S : Finset (Fin d))
    (hB : 0 < B) (hKm : K ≤ m) :
    ∫ s : Fin m → Obs d, allBlockMarkedPolynomialSum M B K S s
        ∂(productLaw m P.law) =
      ∑ k ∈ S, polynomialLightCellPopulationTerm P.law M B K k := by
  unfold allBlockMarkedPolynomialSum
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k _ ↦
      integral_allBlockLightPolynomialTerm_eq_population P k hB hKm
  · intro k _
    exact (memLp_allBlockLightPolynomialTerm_finite P k).integrable one_le_two

-- @node: memLp_allBlockMarkedPolynomialSum_finite
/-- [The deterministic finite-product light sum is square-integrable](goal). -/
lemma memLp_allBlockMarkedPolynomialSum_finite
    {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (S : Finset (Fin d)) :
    MemLp (allBlockMarkedPolynomialSum (m := m) M B K S) 2
      (productLaw m P.law) := by
  unfold allBlockMarkedPolynomialSum
  apply memLp_finsetSum
  intro k _
  exact memLp_allBlockLightPolynomialTerm_finite P k

-- @node: fixedLightMarkedPolynomial_error_sq_le
/-- [The exact expectation, Chebyshev bias, and marked-factorial covariance bound combine into the
  fixed-light-set squared-risk inequality](goal). -/
lemma fixedLightMarkedPolynomial_error_sq_le :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, 0 < C_epsilon ∧
    ∀ d m K : ℕ, ∀ M sigma B : ℝ,
      ∀ P : ModelClass d epsilon M sigma, ∀ S : Finset (Fin d),
      2 ≤ K → 0 < B →
      (∀ k ∈ S, P.law.cellMass k ≤ B / 4) →
      4 * (K + 2) ^ 2 ≤ m →
      (4 : ℝ) * (K + 2) / m ≤ 3 * B / 4 →
      ∫ s : Fin m → Obs d,
          (allBlockMarkedPolynomialSum M B K S s -
            ∑ k ∈ S, P.law.cellMass k * cellEffect P.law k / M) ^ 2
          ∂(productLaw m P.law) ≤
        C_epsilon / m + C_epsilon * 6 ^ (2 * K) *
          ((d : ℝ) * B ^ 2 + (d : ℝ) ^ 2 * K ^ 2 * B ^ 2 / m) +
        ((S.card : ℝ) * (B / (epsilon * (K : ℝ) ^ 2))) ^ 2 := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C_epsilon, hC, hcovariance⟩ :=
    linear_mark_factorial_covariance epsilon hepsilon hepsilon_half
  refine ⟨C_epsilon, hC, ?_⟩
  intro d m K M sigma B P S hK hB hlight hm hshift
  let est : (Fin m → Obs d) → ℝ :=
    allBlockMarkedPolynomialSum M B K S
  let target : ℝ :=
    ∑ k ∈ S, P.law.cellMass k * cellEffect P.law k / M
  have hKm : K ≤ m := by
    have haux : K ≤ 4 * (K + 2) ^ 2 := by nlinarith
    omega
  have hest : MemLp est 2 (productLaw m P.law) :=
    memLp_allBlockMarkedPolynomialSum_finite P S
  have hmse :
      (∫ s, (est s - target) ^ 2 ∂(productLaw m P.law)) =
        variance est (productLaw m P.law) +
          ((∫ s, est s ∂(productLaw m P.law)) - target) ^ 2 := by
    have hsq : Integrable (fun s ↦ est s ^ 2) (productLaw m P.law) :=
      hest.integrable_sq
    have hint : Integrable est (productLaw m P.law) :=
      hest.integrable one_le_two
    have hlinear : Integrable (fun s ↦ 2 * target * est s)
        (productLaw m P.law) := hint.const_mul _
    rw [variance_eq_sub hest]
    calc
      ∫ s, (est s - target) ^ 2 ∂(productLaw m P.law) =
          ∫ s, (est s ^ 2 - 2 * target * est s) + target ^ 2
            ∂(productLaw m P.law) := by
        apply integral_congr_ae
        filter_upwards with s
        ring
      _ = (∫ s, est s ^ 2 - 2 * target * est s
              ∂(productLaw m P.law)) +
            (∫ _s, target ^ 2 ∂(productLaw m P.law)) :=
        integral_add (hsq.sub hlinear) (integrable_const _)
      _ = (∫ s, est s ^ 2 ∂(productLaw m P.law)) -
            (∫ s, 2 * target * est s ∂(productLaw m P.law)) +
            target ^ 2 := by
        rw [integral_sub hsq hlinear, integral_const, probReal_univ, one_smul]
      _ = (∫ s, est s ^ 2 ∂(productLaw m P.law)) -
            2 * target * (∫ s, est s ∂(productLaw m P.law)) +
            target ^ 2 := by rw [integral_const_mul]
      _ = (∫ s, (est ^ 2) s ∂(productLaw m P.law)) -
            (∫ s, est s ∂(productLaw m P.law)) ^ 2 +
            ((∫ s, est s ∂(productLaw m P.law)) - target) ^ 2 := by
        simp only [Pi.pow_apply]
        ring
  have hmean :
      (∫ s, est s ∂(productLaw m P.law)) =
        ∑ k ∈ S, polynomialLightCellPopulationTerm P.law M B K k := by
    exact integral_allBlockMarkedPolynomialSum_eq_population P S hB hKm
  have hbiasEq :
      (∫ s, est s ∂(productLaw m P.law)) - target =
        -polynomialFixedLightPopulationBias P.law M B K S := by
    rw [hmean]
    unfold target polynomialFixedLightPopulationBias
    rw [Finset.sum_sub_distrib]
    ring
  have hlightB : ∀ k ∈ S, P.law.cellMass k ≤ B := by
    intro k hk
    exact (hlight k hk).trans (by linarith)
  have habs := polynomialFixedLightPopulationBias_abs_le
    P S (show 0 < K by omega) hB hlightB
  have hbound0 : 0 ≤ (S.card : ℝ) *
      (B / (epsilon * (K : ℝ) ^ 2)) := by positivity
  have hbiasSq :
      ((∫ s, est s ∂(productLaw m P.law)) - target) ^ 2 ≤
        ((S.card : ℝ) * (B / (epsilon * (K : ℝ) ^ 2))) ^ 2 := by
    rw [hbiasEq]
    simp only [neg_sq]
    rw [sq_le_sq]
    rw [abs_of_nonneg hbound0]
    exact habs
  have hvariance := hcovariance d m K M sigma B P S hK hB hlight hm hshift
  change (∫ s, (est s - target) ^ 2 ∂(productLaw m P.law)) ≤ _
  rw [hmse]
  linarith

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
