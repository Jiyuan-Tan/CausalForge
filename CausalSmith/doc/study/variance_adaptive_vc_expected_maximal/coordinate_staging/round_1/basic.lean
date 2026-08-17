import Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Empirical
import Causalean.Stat.Concentration.Rademacher.Rademacher

/-!
# Data for variance-adaptive VC-type maximal inequalities

This module defines the empirical-measure polynomial covering hypothesis,
the countable empirical supremum, and the normalized logarithmic rate used by
the variance-adaptive expected maximal inequality.  The covering hypothesis
only asks about positive-size finite empirical laws, which is the exact input
needed by empirical-metric chaining.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory
open scoped BigOperators

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}

/-- A class has empirical polynomial `L²` covering numbers with constants
`A` and `v` when every positive-size finite empirical law admits a cover of
relative radius `ε` with cardinality at most the real power `(A / ε) ^ v`. -/
def HasPolynomialEmpiricalL2Cover
    (F : ι → 𝒳 → ℝ) (U A v : ℝ) : Prop :=
  ∀ {m : ℕ} (S : Fin m → 𝒳), 0 < m →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ C : Finset ι,
        IsL2Cover (finiteSampleMeasure S) F (ε * U) C ∧
          (C.card : ℝ) ≤ Real.rpow (A / ε) v

/-- The logarithmic complexity used by the maximal inequality is the log of
the larger of Euler's number and the envelope-to-radius ratio `A U / σ`.
This normalization keeps the logarithm at least one. -/
noncomputable def vcMaximalLog (A U σ : ℝ) : ℝ :=
  Real.log (max (Real.exp 1) (A * U / σ))

/-- The variance-adaptive VC-type rate is the sum of a leading
`σ √(v log(AU/σ)/n)` term and a second-order `v U log(AU/σ)/n` term, with a
logarithm normalized to be at least one. -/
noncomputable def vcExpectedMaximalRate
    (U σ A v : ℝ) (n : ℕ) : ℝ :=
  σ * Real.sqrt (v * vcMaximalLog A U σ / (n : ℝ)) +
    v * U * vcMaximalLog A U σ / (n : ℝ)

/-- The fixed numerical constant used by the variance-adaptive VC-type
expected maximal inequality.  Its value is deliberately non-optimized. -/
def varianceAdaptiveVCConstant : ℝ := 16384

/-- The empirical supremum of a countable real-valued class is the largest
absolute difference between its sample average and population mean. -/
noncomputable def countableEmpiricalSup
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {n : ℕ} (S : Fin n → 𝒳) : ℝ :=
  uniformDeviation n F P id S

/-- A uniform polynomial covering certificate over all probability measures
supplies canonically normalized polynomial covering data for every finite
empirical law, with base at least Euler's number and exponent at least one. -/
theorem HasPolynomialL2Cover.hasPolynomialEmpiricalL2Cover
    {F : ι → 𝒳 → ℝ} {U : ℝ}
    (hF : HasPolynomialL2Cover F U) :
    ∃ A v : ℝ, Real.exp 1 ≤ A ∧ 1 ≤ v ∧
      HasPolynomialEmpiricalL2Cover F U A v := by
  /-
  Extract `A₀,p` from `hF.entropy` and take
  `A = max (exp 1) (2 * A₀)` and `v = (p + 1 : ℕ)`.  Instantiate the
  arbitrary-measure certificate at `finiteSampleMeasure S`.  For
  `x = A₀ / ε`, the hypotheses give `1 ≤ x`; hence
  `ceil (x^p) ≤ x^p + 1 ≤ 2*x^p ≤ (A/ε)^(p+1)`.  Rewrite the final natural
  power as `Real.rpow` with `Real.rpow_natCast`.
  -/
  obtain ⟨A₀, p, hA₀, hentropy⟩ := hF.entropy
  refine ⟨max (Real.exp 1) (2 * A₀), ((p + 1 : ℕ) : ℝ), le_max_left _ _, ?_, ?_⟩
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le p)
  · intro m S hm ε hε hε1
    letI : IsProbabilityMeasure (finiteSampleMeasure S) :=
      finiteSampleMeasure_isProbabilityMeasure S hm
    obtain ⟨C, hCcard, hCcover⟩ :=
      hentropy (finiteSampleMeasure S) inferInstance ε hε hε1
    refine ⟨C, hCcover, ?_⟩
    have hx : 1 ≤ A₀ / ε :=
      (one_le_div hε).2 (hε1.trans hA₀)
    have hceil : (Nat.ceil ((A₀ / ε) ^ p) : ℝ) < (A₀ / ε) ^ p + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hxpow : 1 ≤ (A₀ / ε) ^ p := one_le_pow₀ hx
    have hbase : A₀ / ε ≤ max (Real.exp 1) (2 * A₀) / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      exact (by linarith : A₀ ≤ 2 * A₀) |>.trans (le_max_right _ _)
    have htwo : 2 ≤ max (Real.exp 1) (2 * A₀) / ε := by
      apply (le_div_iff₀ hε).2
      calc
        2 * ε ≤ 2 * 1 := by gcongr
        _ ≤ 2 * A₀ := by gcongr
        _ ≤ max (Real.exp 1) (2 * A₀) := le_max_right _ _
    calc
      (C.card : ℝ) ≤ (Nat.ceil ((A₀ / ε) ^ p) : ℝ) := by exact_mod_cast hCcard
      _ ≤ 2 * (A₀ / ε) ^ p := by linarith
      _ ≤ (max (Real.exp 1) (2 * A₀) / ε) ^ (p + 1) := by
        have hp := pow_le_pow_left₀ (by positivity : 0 ≤ A₀ / ε) hbase p
        calc
          2 * (A₀ / ε) ^ p ≤
              (max (Real.exp 1) (2 * A₀) / ε) * (A₀ / ε) ^ p :=
            mul_le_mul_of_nonneg_right htwo (by positivity)
          _ ≤ (max (Real.exp 1) (2 * A₀) / ε) *
              (max (Real.exp 1) (2 * A₀) / ε) ^ p :=
            mul_le_mul_of_nonneg_left hp (by positivity)
          _ = (max (Real.exp 1) (2 * A₀) / ε) ^ (p + 1) := by
            rw [pow_succ]
            ring
      _ = Real.rpow (max (Real.exp 1) (2 * A₀) / ε) ((p + 1 : ℕ) : ℝ) := by
        exact (Real.rpow_natCast _ _).symm

end Causalean.Stat.Concentration
