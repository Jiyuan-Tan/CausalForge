/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.Sequential.Ville
import Causalean.Experimentation.Sequential.AnytimeValid
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Waudby-Smith & Ramdas (2024): confidence sequences by betting

Worked application of the anytime-valid substrate to Waudby-Smith & Ramdas (2024), "Estimating means
of bounded random variables by betting" (JRSS-B).  To test that the mean of a `[0,1]`-bounded data
stream is `m`, a gambler bets a *predictable* fraction `λₙ` of current capital on each new
observation, multiplying capital by `1 + λₙ(Xₙ − m)`.  The resulting **capital process**
`Kₙ(m) = ∏ᵢ (1 + λᵢ(Xᵢ − m))` is, under the null that the conditional mean is `m` and with bets kept
in the range that keeps capital nonnegative, a **test supermartingale** (`IsTestSupermartingale`):
nonnegative, with `K₀ = 1`, and a fair bet cannot grow capital in expectation.  Inverting it —
keeping the values `m` whose capital has not yet reached `1/α` — yields a **confidence sequence**
for the mean with time-uniform coverage `1 − α`, directly via Ville's inequality.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace Causalean
namespace Experimentation
namespace BettingMean

open Sequential

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-- The **betting capital process** for testing that the mean is `m`, with observations `X` and
predictable betting fractions `lam`: `K₀ = 1` and `Kₙ₊₁ = Kₙ · (1 + lamₙ·(Xₙ − m))`. -/
noncomputable def capital (X lam : ℕ → Ω → ℝ) (m : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | (n + 1) => fun ω => capital X lam m n ω * (1 + lam n ω * (X n ω - m))

/-- The betting capital starts at one before any observations are processed. -/
@[simp] lemma capital_zero (X lam : ℕ → Ω → ℝ) (m : ℝ) : capital X lam m 0 = fun _ => 1 := rfl

/-- One step of the betting capital multiplies current wealth by the return
`1 + lam n · (X n − m)`. -/
lemma capital_succ (X lam : ℕ → Ω → ℝ) (m : ℝ) (n : ℕ) :
    capital X lam m (n + 1) = fun ω => capital X lam m n ω * (1 + lam n ω * (X n ω - m)) := rfl

/-- The capital process stays nonnegative provided each bet keeps the per-step factor nonnegative
(`0 ≤ 1 + lamₙ(Xₙ − m)`) — the admissibility constraint on the betting fractions. -/
lemma capital_nonneg {X lam : ℕ → Ω → ℝ} {m : ℝ}
    (hbet : ∀ n ω, 0 ≤ 1 + lam n ω * (X n ω - m)) : ∀ n, 0 ≤ capital X lam m n := by
  intro n
  induction n with
  | zero =>
      rw [capital_zero]
      intro ω
      norm_num
  | succ n ih =>
      rw [capital_succ]
      intro ω
      exact mul_nonneg (ih ω) (hbet n ω)

/-- **The capital process is a test supermartingale** (the Waudby-Smith–Ramdas construction). For an
adapted capital process with predictable bets (`lamₙ` is `ℱ n`-measurable), admissible bet range
(`0 ≤ 1 + lamₙ(Xₙ − m)`), integrability, and conditionally fair increments
(`μ[Xₙ − m | ℱ n] = 0`), the betting capital process is a nonnegative supermartingale with
`E[K₀] ≤ 1`. -/
theorem isTestSupermartingale_capital [IsProbabilityMeasure μ] {X lam : ℕ → Ω → ℝ} {m : ℝ}
    (hadapt : Adapted ℱ (capital X lam m))
    (hlam : ∀ n, StronglyMeasurable[ℱ n] (lam n))
    (hint : ∀ n, Integrable (capital X lam m n) μ)
    (hintX : ∀ n, Integrable (fun ω => X n ω - m) μ)
    (hintInc : ∀ n, Integrable (fun ω => lam n ω * (X n ω - m)) μ)
    (hbet : ∀ n ω, 0 ≤ 1 + lam n ω * (X n ω - m))
    (hfair : ∀ n, μ[fun ω => X n ω - m | ℱ n] =ᵐ[μ] 0) :
    IsTestSupermartingale (capital X lam m) ℱ μ := by
  refine ⟨?super, capital_nonneg hbet, ?init⟩
  · refine (martingale_nat hadapt.stronglyAdapted hint ?_).supermartingale
    intro n
    -- `Kₙ₊₁ = Kₙ · (1 + lamₙ(Xₙ−m))`; pull the `ℱn`-measurable factors `Kₙ`, `lamₙ` out of the
    -- conditional expectation and use the fair-bet condition `μ[Xₙ−m | ℱn] = 0`.
    have hcap : StronglyMeasurable[ℱ n] (capital X lam m n) := hadapt.stronglyAdapted n
    have hgint : Integrable (fun ω => 1 + lam n ω * (X n ω - m)) μ :=
      (integrable_const (1 : ℝ)).add (hintInc n)
    have hcapsucc : capital X lam m (n + 1)
        = capital X lam m n * (fun ω => 1 + lam n ω * (X n ω - m)) := by
      rw [capital_succ]; rfl
    have hfgint : Integrable
        (capital X lam m n * (fun ω => 1 + lam n ω * (X n ω - m))) μ := by
      rw [← hcapsucc]; exact hint (n + 1)
    have hpull : μ[capital X lam m (n + 1) | ℱ n]
        =ᵐ[μ] capital X lam m n * μ[(fun ω => 1 + lam n ω * (X n ω - m)) | ℱ n] := by
      rw [hcapsucc]
      exact condExp_mul_of_stronglyMeasurable_left hcap hfgint hgint
    have hinc : μ[(fun ω => 1 + lam n ω * (X n ω - m)) | ℱ n] =ᵐ[μ] (fun _ => (1 : ℝ)) := by
      have hsplit : (fun ω => 1 + lam n ω * (X n ω - m))
          = (fun _ => (1 : ℝ)) + (fun ω => lam n ω * (X n ω - m)) := by funext ω; rfl
      rw [hsplit]
      refine (condExp_add (integrable_const (1 : ℝ)) (hintInc n) (ℱ n)).trans ?_
      have hc1 : μ[(fun _ => (1 : ℝ)) | ℱ n] = (fun _ => (1 : ℝ)) := condExp_const (ℱ.le n) 1
      have hlampull : μ[(fun ω => lam n ω * (X n ω - m)) | ℱ n]
          =ᵐ[μ] lam n * μ[(fun ω => X n ω - m) | ℱ n] :=
        condExp_mul_of_stronglyMeasurable_left (hlam n) (hintInc n) (hintX n)
      rw [hc1]
      filter_upwards [hlampull, hfair n] with ω h1 h2
      simp only [Pi.add_apply, Pi.mul_apply, h1, h2]
      simp
    refine (hpull.trans ?_).symm
    filter_upwards [hinc] with ω hω
    simp only [Pi.mul_apply, hω, mul_one]
  · rw [capital_zero]
    simp [integral_const]

/-- **Betting confidence sequence (coverage).** If the betting capital process for `m` is already a
test supermartingale, then the cover that keeps `m` while its capital has not reached `1/α` fails at
some time with probability at most `α`. -/
theorem isConfidenceSequence_bettingCI [IsFiniteMeasure μ] {X lam : ℕ → Ω → ℝ} {m : ℝ}
    (hM : IsTestSupermartingale (capital X lam m) ℱ μ) {α : ℝ} (hα : 0 < α) :
    IsConfidenceSequence (confSeqOfWealth (capital X lam m) α) μ α :=
  isConfidenceSequence_confSeqOfWealth hM hα

/-- **Anytime-valid test by betting.** If the betting capital process for `m` is already a test
supermartingale, then the event that its wealth ever reaches `1/α` has probability at most `α`. -/
theorem isAnytimeValid_betting [IsFiniteMeasure μ] {X lam : ℕ → Ω → ℝ} {m : ℝ}
    (hM : IsTestSupermartingale (capital X lam m) ℱ μ) {α : ℝ} (hα : 0 < α) :
    IsAnytimeValid (rejectionRegion (capital X lam m) α) μ α :=
  isAnytimeValid_rejectionRegion hM hα

end BettingMean
end Experimentation
end Causalean
