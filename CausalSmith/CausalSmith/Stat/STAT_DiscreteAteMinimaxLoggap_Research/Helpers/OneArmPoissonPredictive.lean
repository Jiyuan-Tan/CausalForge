import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPoissonTail
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmTensorization
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Discrete Poisson predictive laws for the one-arm converse

This module realizes the three sufficient counts as an actual PMF and mixes
that PMF over a finite parameter prior.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma pmf_toReal_summable {alpha : Type*} (p : PMF alpha) :
    Summable (fun x => (p x).toReal) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

lemma tsum_pmf_toReal_eq_one {alpha : Type*} (p : PMF alpha) :
    ∑' x, (p x).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe]
  norm_num

/-- Product law of the three independent Poisson sufficient counts. -/
noncomputable def triplePoissonPMF (lam11 lam10 lam0 : ℝ≥0) : PMF (Fin 3 → ℕ) :=
  (poissonPMF lam11).bind fun c11 =>
    (poissonPMF lam10).bind fun c10 =>
      (poissonPMF lam0).map fun c0 => ![c11, c10, c0]

lemma triplePoissonPMF_apply (lam11 lam10 lam0 : ℝ≥0) (c : Fin 3 → ℕ) :
    triplePoissonPMF lam11 lam10 lam0 c =
      poissonPMF lam11 (c 0) * poissonPMF lam10 (c 1) * poissonPMF lam0 (c 2) := by
  have hvec (a b d : ℕ) : c = ![a, b, d] ↔
      a = c 0 ∧ b = c 1 ∧ d = c 2 := by
    constructor
    · intro h
      subst c
      simp
    · rintro ⟨rfl, rfl, rfl⟩
      ext i
      fin_cases i <;> rfl
  simp only [triplePoissonPMF, PMF.bind_apply, PMF.map_apply]
  simp_rw [hvec]
  have h2 (a b : ℕ) :
      (∑' d : ℕ, if a = c 0 ∧ b = c 1 ∧ d = c 2 then poissonPMF lam0 d else 0) =
        if a = c 0 ∧ b = c 1 then poissonPMF lam0 (c 2) else 0 := by
    by_cases h : a = c 0 ∧ b = c 1
    · simp [h]
    · rw [if_neg h]
      have hz : (fun d : ℕ =>
          if a = c 0 ∧ b = c 1 ∧ d = c 2 then poissonPMF lam0 d else 0) =
          fun _ => 0 := by
        funext d
        rw [if_neg]
        intro hd
        exact h ⟨hd.1, hd.2.1⟩
      rw [hz, tsum_zero]
  simp_rw [h2]
  have h1 (a : ℕ) :
      (∑' b : ℕ, poissonPMF lam10 b *
        if a = c 0 ∧ b = c 1 then poissonPMF lam0 (c 2) else 0) =
        if a = c 0 then poissonPMF lam10 (c 1) * poissonPMF lam0 (c 2) else 0 := by
    by_cases h : a = c 0
    · subst a
      simp
    · simp [h]
  simp_rw [h1]
  simp
  ring

/-- The concrete triple-Poisson PMF has the real-valued atom used by the
Taylor argument when its three rates are the one-arm sufficient rates. -/
lemma triplePoissonPMF_toReal_eq_triplePoissonMass
    (lam11 lam10 lam0 : ℝ≥0) (sampleScale p pi mu : ℝ)
    (h11 : (lam11 : ℝ) = sampleScale * p * pi * mu)
    (h10 : (lam10 : ℝ) = sampleScale * p * pi * (1 - mu))
    (h0 : (lam0 : ℝ) = sampleScale * p * (1 - pi))
    (c : Fin 3 → ℕ) :
    (triplePoissonPMF lam11 lam10 lam0 c).toReal =
      triplePoissonMass sampleScale p pi mu c := by
  rw [triplePoissonPMF_apply]
  simp only [ENNReal.toReal_mul, ← poissonPMFReal_ofReal_eq_poissonPMF,
    ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  unfold poissonPMFReal triplePoissonMass triplePoissonCoefficient
  rw [h11, h10, h0]
  have hsum : sampleScale * p * pi * mu +
      sampleScale * p * pi * (1 - mu) + sampleScale * p * (1 - pi) =
      sampleScale * p := by ring
  have hexp : Real.exp (-(sampleScale * p * pi * mu)) *
      Real.exp (-(sampleScale * p * pi * (1 - mu))) *
      Real.exp (-(sampleScale * p * (1 - pi))) =
      Real.exp (-(sampleScale * p)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linarith
  calc
    _ = (Real.exp (-(sampleScale * p * pi * mu)) *
          Real.exp (-(sampleScale * p * pi * (1 - mu))) *
          Real.exp (-(sampleScale * p * (1 - pi)))) *
        ((sampleScale * p * pi * mu) ^ c 0 / (Nat.factorial (c 0) : ℝ) *
          (sampleScale * p * pi * (1 - mu)) ^ c 1 / (Nat.factorial (c 1) : ℝ) *
          (sampleScale * p * (1 - pi)) ^ c 2 / (Nat.factorial (c 2) : ℝ)) := by ring
    _ = _ := by rw [hexp]

/-- Finite mixture of triple-count laws. -/
noncomputable def mixedTriplePoissonPMF {ι : Type*} [Fintype ι]
    (ω : PMF ι) (lam11 lam10 lam0 : ι → ℝ≥0) : PMF (Fin 3 → ℕ) :=
  ω.bind fun r => triplePoissonPMF (lam11 r) (lam10 r) (lam0 r)

lemma mixedTriplePoissonPMF_apply {ι : Type*} [Fintype ι]
    (ω : PMF ι) (lam11 lam10 lam0 : ι → ℝ≥0) (c : Fin 3 → ℕ) :
    mixedTriplePoissonPMF ω lam11 lam10 lam0 c =
      ∑ r, ω r * (poissonPMF (lam11 r) (c 0) *
        poissonPMF (lam10 r) (c 1) * poissonPMF (lam0 r) (c 2)) := by
  rw [mixedTriplePoissonPMF, PMF.bind_apply]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro r _
  rw [triplePoissonPMF_apply]

/-- Pointwise identification of the finite predictive PMF with the mixed
real-valued mass used by the Taylor and count-tail lemmas. -/
lemma mixedTriplePoissonPMF_toReal_eq_mixedTriplePoissonMass
    {ι : Type*} [Fintype ι] (ω : PMF ι)
    (lam11 lam10 lam0 : ι → ℝ≥0) (sampleScale : ℝ)
    (p pi mu : ι → ℝ)
    (h11 : ∀ r, (lam11 r : ℝ) = sampleScale * p r * pi r * mu r)
    (h10 : ∀ r, (lam10 r : ℝ) = sampleScale * p r * pi r * (1 - mu r))
    (h0 : ∀ r, (lam0 r : ℝ) = sampleScale * p r * (1 - pi r))
    (c : Fin 3 → ℕ) :
    (mixedTriplePoissonPMF ω lam11 lam10 lam0 c).toReal =
      mixedTriplePoissonMass ω sampleScale p pi mu c := by
  rw [mixedTriplePoissonPMF_apply]
  simp_rw [← triplePoissonPMF_apply]
  unfold mixedTriplePoissonMass
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro r _
    rw [ENNReal.toReal_mul]
    rw [triplePoissonPMF_toReal_eq_triplePoissonMass
      (lam11 r) (lam10 r) (lam0 r) sampleScale (p r) (pi r) (mu r)
      (h11 r) (h10 r) (h0 r) c]
  · intro r _
    exact ENNReal.mul_ne_top (ω.apply_ne_top r)
      ((triplePoissonPMF (lam11 r) (lam10 r) (lam0 r)).apply_ne_top c)

/-- The predictive total variation is controlled by the exact real mass
difference to which the Taylor/count-tail argument applies. -/
lemma tvDist_mixedTriplePoissonPMF_le_tsum_abs_mass
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁)
    (lam11₀ lam10₀ lam0₀ : ι₀ → ℝ≥0)
    (lam11₁ lam10₁ lam0₁ : ι₁ → ℝ≥0)
    (sampleScale : ℝ)
    (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ)
    (h11₀ : ∀ r, (lam11₀ r : ℝ) = sampleScale * p₀ r * pi₀ r * mu₀ r)
    (h10₀ : ∀ r, (lam10₀ r : ℝ) = sampleScale * p₀ r * pi₀ r * (1 - mu₀ r))
    (h0₀ : ∀ r, (lam0₀ r : ℝ) = sampleScale * p₀ r * (1 - pi₀ r))
    (h11₁ : ∀ r, (lam11₁ r : ℝ) = sampleScale * p₁ r * pi₁ r * mu₁ r)
    (h10₁ : ∀ r, (lam10₁ r : ℝ) = sampleScale * p₁ r * pi₁ r * (1 - mu₁ r))
    (h0₁ : ∀ r, (lam0₁ r : ℝ) = sampleScale * p₁ r * (1 - pi₁ r)) :
    Causalean.Stat.tvDist
        (mixedTriplePoissonPMF ω₀ lam11₀ lam10₀ lam0₀).toMeasure
        (mixedTriplePoissonPMF ω₁ lam11₁ lam10₁ lam0₁).toMeasure ≤
      ∑' c, |mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c -
        mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c| := by
  refine (tvDist_pmf_toMeasure_le_tsum_abs
    (mixedTriplePoissonPMF ω₀ lam11₀ lam10₀ lam0₀)
    (mixedTriplePoissonPMF ω₁ lam11₁ lam10₁ lam0₁)).trans_eq ?_
  apply tsum_congr
  intro c
  rw [mixedTriplePoissonPMF_toReal_eq_mixedTriplePoissonMass
      ω₀ lam11₀ lam10₀ lam0₀ sampleScale p₀ pi₀ mu₀
      h11₀ h10₀ h0₀ c,
    mixedTriplePoissonPMF_toReal_eq_mixedTriplePoissonMass
      ω₁ lam11₁ lam10₁ lam0₁ sampleScale p₁ pi₁ mu₁
      h11₁ h10₁ h0₁ c]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
