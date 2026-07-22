/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Convergence in probability for finite randomization designs

A lightweight convergence-in-probability layer for the finite-design probability model, used to
analyze ratio (Hájek) estimators.  Along a sequence of designs `D m : FiniteDesign (Ω m)`, a
sequence of statistics `X m : Ω m → ℝ` converges in probability to a target sequence `c : ℕ → ℝ`
(`TendstoInProb D X c`) if the tail probabilities `Pr(|X m − c m| ≥ ε)` vanish for every `ε > 0`.

The substrate provides:
* `tendstoInProb_of_var` — the Chebyshev consistency engine: if the design variance of `X m`
  vanishes, then `X m → E[X m]` in probability;
* `TendstoInProb.sub` — closure under differences;
* `tendstoInProb_div_one` — the Slutsky ratio step: if `X m → a m`, the denominator `Y m → 1`, and
  the limits `a m` are uniformly bounded, then `X m / Y m → a m`.  This is exactly what turns
  Horvitz–Thompson convergence into Hájek convergence (the realized weight-sum normalizer tends to
  one).
-/

import Causalean.Experimentation.DesignBased.Chebyshev
import Causalean.Experimentation.DesignBased.Risk
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Convergence in probability for finite designs

Finite-design convergence in probability tracks vanishing assignment-tail probabilities along a
sequence of randomization designs.

The predicate `FiniteDesign.TendstoInProb` states convergence of statistics `X m` to targets `c m`
using the design probabilities of absolute-deviation events. The theorem `tendstoInProb_of_var`
turns vanishing randomization variance into convergence to the design mean via Chebyshev's
inequality. The closure result `TendstoInProb.sub` handles differences, and
`tendstoInProb_div_one` is the Hájek/Slutsky ratio step for denominators converging in probability
to one.
-/

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)]

/-- **Convergence in probability** along a sequence of finite designs: `X m` converges in
probability to the target `c m` if `Pr(|X m − c m| ≥ ε) → 0` for every `ε > 0`. -/
def TendstoInProb (D : ∀ m, FiniteDesign (Ω m)) (X : ∀ m, Ω m → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun m => (D m).Pr (fun z => ε ≤ |X m z - c m|)) atTop (𝓝 0)

/-- **Chebyshev consistency engine.** If the design variance of `X m` tends to zero, then `X m`
converges in probability to its design mean `E[X m]`. -/
theorem tendstoInProb_of_var (D : ∀ m, FiniteDesign (Ω m)) (X : ∀ m, Ω m → ℝ)
    (hvar : Tendsto (fun m => (D m).Var (X m)) atTop (𝓝 0)) :
    TendstoInProb D X (fun m => (D m).E (X m)) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hupper : Tendsto (fun m => (D m).Var (X m) / ε ^ 2) atTop (𝓝 0) := by
    simpa using hvar.div_const (ε ^ 2)
  refine squeeze_zero (fun m => ?_) (fun m => ?_) hupper
  · exact (D m).Pr_nonneg _
  · exact (D m).chebyshev (X m) hε

/-- Union bound for two events: `Pr(P ∨ Q) ≤ Pr P + Pr Q`. -/
lemma Pr_or_le {Ω' : Type*} [Fintype Ω'] (D : FiniteDesign Ω') (P Q : Ω' → Prop)
    [DecidablePred P] [DecidablePred Q] :
    D.Pr (fun z => P z ∨ Q z) ≤ D.Pr P + D.Pr Q := by
  unfold FiniteDesign.Pr FiniteDesign.E FiniteDesign.ind
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (D.p_nonneg z)
  by_cases hP : P z <;> by_cases hQ : Q z <;> simp [hP, hQ]

/-- Convergence in probability is closed under differences. -/
theorem TendstoInProb.sub {D : ∀ m, FiniteDesign (Ω m)} {X Y : ∀ m, Ω m → ℝ} {a b : ℕ → ℝ}
    (hX : TendstoInProb D X a) (hY : TendstoInProb D Y b) :
    TendstoInProb D (fun m z => X m z - Y m z) (fun m => a m - b m) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- The combined tail bound: split each event into the two half-deviation events.
  have hbound : ∀ m,
      (D m).Pr (fun z => ε ≤ |(X m z - Y m z) - (a m - b m)|)
        ≤ (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
          + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|) := by
    intro m
    have hmono : (D m).Pr (fun z => ε ≤ |(X m z - Y m z) - (a m - b m)|)
        ≤ (D m).Pr (fun z => (ε / 2 ≤ |X m z - a m|) ∨ (ε / 2 ≤ |Y m z - b m|)) := by
      apply (D m).Pr_mono
      intro z hz
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      have htri : |(X m z - Y m z) - (a m - b m)| ≤ |X m z - a m| + |Y m z - b m| := by
        have : (X m z - Y m z) - (a m - b m) = (X m z - a m) - (Y m z - b m) := by ring
        rw [this]
        exact abs_sub _ _
      linarith
    exact le_trans hmono (Pr_or_le (D m) _ _)
  have hupper : Tendsto
      (fun m => (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
        + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|)) atTop (𝓝 0) := by
    have := (hX (ε / 2) hε2).add (hY (ε / 2) hε2)
    simpa using this
  refine squeeze_zero (fun m => (D m).Pr_nonneg _) hbound hupper

/-- Convergence in probability is closed under sums. -/
theorem TendstoInProb.add {D : ∀ m, FiniteDesign (Ω m)} {X Y : ∀ m, Ω m → ℝ} {a b : ℕ → ℝ}
    (hX : TendstoInProb D X a) (hY : TendstoInProb D Y b) :
    TendstoInProb D (fun m z => X m z + Y m z) (fun m => a m + b m) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hbound : ∀ m,
      (D m).Pr (fun z => ε ≤ |(X m z + Y m z) - (a m + b m)|)
        ≤ (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
          + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|) := by
    intro m
    have hmono : (D m).Pr (fun z => ε ≤ |(X m z + Y m z) - (a m + b m)|)
        ≤ (D m).Pr (fun z => (ε / 2 ≤ |X m z - a m|) ∨ (ε / 2 ≤ |Y m z - b m|)) := by
      apply (D m).Pr_mono
      intro z hz
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      have htri : |(X m z + Y m z) - (a m + b m)| ≤ |X m z - a m| + |Y m z - b m| := by
        have : (X m z + Y m z) - (a m + b m) = (X m z - a m) + (Y m z - b m) := by ring
        rw [this]
        exact abs_add_le _ _
      linarith
    exact le_trans hmono (Pr_or_le (D m) _ _)
  have hupper : Tendsto
      (fun m => (D m).Pr (fun z => ε / 2 ≤ |X m z - a m|)
        + (D m).Pr (fun z => ε / 2 ≤ |Y m z - b m|)) atTop (𝓝 0) := by
    have := (hX (ε / 2) hε2).add (hY (ε / 2) hε2)
    simpa using this
  refine squeeze_zero (fun m => (D m).Pr_nonneg _) hbound hupper

/-- If `X m → 0` in probability then `|X m| → 0` in probability. -/
theorem TendstoInProb.abs {D : ∀ m, FiniteDesign (Ω m)} {X : ∀ m, Ω m → ℝ}
    (h : TendstoInProb D X (fun _ => 0)) :
    TendstoInProb D (fun m z => |X m z|) (fun _ => 0) := by
  intro ε hε
  simpa only [sub_zero, abs_abs] using h ε hε

/-- **Slutsky ratio step.** If `X m → a m` in probability, the denominator `Y m → 1` in
probability, and the limit sequence `a m` is uniformly bounded (`|a m| ≤ M`), then the ratio
`X m / Y m → a m` in probability.  (The realized normalizer tends to one, so dividing by it does not
change the probability limit.) -/
theorem tendstoInProb_div_one (D : ∀ m, FiniteDesign (Ω m)) (X Y : ∀ m, Ω m → ℝ) (a : ℕ → ℝ)
    (M : ℝ) (ha : ∀ m, |a m| ≤ M) (hX : TendstoInProb D X a)
    (hY : TendstoInProb D Y (fun _ => 1)) :
    TendstoInProb D (fun m z => X m z / Y m z) a := by
  intro ε hε
  -- `M' := M + 1` is a strictly positive bound on `|a m|`, avoiding division by zero.
  set M' : ℝ := M + 1 with hM'def
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (ha 0)
  have hM' : 0 < M' := by rw [hM'def]; linarith
  have haM' : ∀ m, |a m| ≤ M' := fun m => le_trans (ha m) (by rw [hM'def]; linarith)
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hε4M' : (0 : ℝ) < ε / (4 * M') := by positivity
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  -- Pointwise inclusion: the ratio-far event is contained in the union of three deviation events.
  have hbound : ∀ m,
      (D m).Pr (fun z => ε ≤ |X m z / Y m z - a m|)
        ≤ (D m).Pr (fun z => (1 : ℝ) / 2 ≤ |Y m z - 1|)
          + ((D m).Pr (fun z => ε / 4 ≤ |X m z - a m|)
            + (D m).Pr (fun z => ε / (4 * M') ≤ |Y m z - 1|)) := by
    intro m
    have hmono : (D m).Pr (fun z => ε ≤ |X m z / Y m z - a m|)
        ≤ (D m).Pr (fun z => ((1 : ℝ) / 2 ≤ |Y m z - 1|) ∨
            ((ε / 4 ≤ |X m z - a m|) ∨ (ε / (4 * M') ≤ |Y m z - 1|))) := by
      apply (D m).Pr_mono
      intro z hz
      -- Split on whether the denominator is close to one.
      by_cases hYclose : (1 : ℝ) / 2 ≤ |Y m z - 1|
      · exact Or.inl hYclose
      · push_neg at hYclose
        refine Or.inr ?_
        -- On `|Y - 1| < 1/2` we have `|Y| ≥ 1/2 > 0`.
        have hYlb : (1 : ℝ) / 2 ≤ |Y m z| := by
          have htri : |Y m z - 1| ≥ |1| - |Y m z| := by
            have := abs_sub_abs_le_abs_sub (1 : ℝ) (Y m z)
            rw [abs_sub_comm] at this
            simpa [abs_sub_comm] using this
          have h1 : |(1 : ℝ)| = 1 := by norm_num
          rw [h1] at htri
          linarith
        have hYpos : (0 : ℝ) < |Y m z| := lt_of_lt_of_le (by norm_num) hYlb
        have hYne : Y m z ≠ 0 := by
          intro h; rw [h] at hYpos; simp at hYpos
        -- `|X/Y - a| = |X - a·Y| / |Y| ≤ 2·|X - a·Y|`.
        have hratio : |X m z / Y m z - a m| = |X m z - a m * Y m z| / |Y m z| := by
          rw [← abs_div]
          congr 1
          field_simp
        have hle2 : |X m z / Y m z - a m| ≤ 2 * |X m z - a m * Y m z| := by
          rw [hratio]
          rw [div_le_iff₀ hYpos]
          calc |X m z - a m * Y m z|
              = |X m z - a m * Y m z| * 1 := by ring
            _ ≤ |X m z - a m * Y m z| * (2 * |Y m z|) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                linarith
            _ = 2 * |X m z - a m * Y m z| * |Y m z| := by ring
        -- `|X - a·Y| ≤ |X - a| + |a|·|Y - 1|`.
        have hsplit : |X m z - a m * Y m z| ≤ |X m z - a m| + |a m| * |Y m z - 1| := by
          have heq : X m z - a m * Y m z = (X m z - a m) + a m * (1 - Y m z) := by ring
          calc |X m z - a m * Y m z|
              = |(X m z - a m) + a m * (1 - Y m z)| := by rw [heq]
            _ ≤ |X m z - a m| + |a m * (1 - Y m z)| := abs_add_le _ _
            _ = |X m z - a m| + |a m| * |1 - Y m z| := by rw [abs_mul]
            _ = |X m z - a m| + |a m| * |Y m z - 1| := by rw [abs_sub_comm (1 : ℝ)]
        -- Combine: `ε ≤ |X/Y - a| ≤ 2|X-a| + 2M'|Y-1|`.
        have hcombine : ε ≤ 2 * |X m z - a m| + 2 * M' * |Y m z - 1| := by
          have haY : |a m| * |Y m z - 1| ≤ M' * |Y m z - 1| :=
            mul_le_mul_of_nonneg_right (haM' m) (abs_nonneg _)
          have : ε ≤ 2 * (|X m z - a m| + |a m| * |Y m z - 1|) :=
            le_trans hz (le_trans hle2 (by linarith [hsplit]))
          nlinarith [haY, abs_nonneg (Y m z - 1)]
        -- Hence one of the two half-bounds holds.
        by_contra hcon
        push_neg at hcon
        obtain ⟨h1, h2⟩ := hcon
        -- `2|X-a| < ε/2` and `2M'|Y-1| < ε/2`, contradicting `hcombine`.
        have hb1 : 2 * |X m z - a m| < ε / 2 := by linarith
        have hb2 : 2 * M' * |Y m z - 1| < ε / 2 := by
          have : |Y m z - 1| < ε / (4 * M') := h2
          have h4M' : (0 : ℝ) < 4 * M' := by linarith
          rw [lt_div_iff₀ h4M'] at this
          nlinarith [this]
        linarith
    refine le_trans hmono ?_
    refine le_trans ((D m).Pr_or_le _ _) ?_
    have := (D m).Pr_or_le (fun z => ε / 4 ≤ |X m z - a m|)
      (fun z => ε / (4 * M') ≤ |Y m z - 1|)
    linarith [this]
  -- The upper bound tends to zero (three vanishing tails).
  have hupper : Tendsto
      (fun m => (D m).Pr (fun z => (1 : ℝ) / 2 ≤ |Y m z - 1|)
        + ((D m).Pr (fun z => ε / 4 ≤ |X m z - a m|)
          + (D m).Pr (fun z => ε / (4 * M') ≤ |Y m z - 1|))) atTop (𝓝 0) := by
    have t1 := hY (1 / 2) hhalf
    have t2 := hX (ε / 4) hε4
    have t3 := hY (ε / (4 * M')) hε4M'
    have := t1.add (t2.add t3)
    simpa using this
  refine squeeze_zero (fun m => (D m).Pr_nonneg _) hbound hupper

/-- **Uniform tightness (bounded in probability).** The statistics `X m` are uniformly tight if,
for every tolerance `η`, there is a single threshold `M` past which the deviation probability
`Pr(M ≤ |X m|)` is at most `η` for every index `m`.  This is the `O_p(1)` counterpart of
`TendstoInProb`, satisfied by a bounded (non-vanishing) factor of a delta-method remainder. -/
def BoundedInProb (D : ∀ m, FiniteDesign (Ω m)) (X : ∀ m, Ω m → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∀ᶠ m in atTop, (D m).Pr (fun z => M ≤ |X m z|) ≤ η

/-- An eventual variance bound together with an eventual mean bound makes a sequence bounded in
probability: if the design variances `Var(X m)` are eventually at most `V` and the means `E(X m)`
eventually lie within `c` of zero, then `X` is uniformly tight. -/
theorem boundedInProb_of_var_bound (D : ∀ m, FiniteDesign (Ω m)) (X : ∀ m, Ω m → ℝ)
    {V c : ℝ} (hV : ∀ᶠ m in atTop, (D m).Var (X m) ≤ V)
    (hc : ∀ᶠ m in atTop, |(D m).E (X m)| ≤ c) :
    BoundedInProb D X := by
  intro η hη
  obtain ⟨m0, hm0⟩ := hV.exists
  have hVnn : 0 ≤ V := le_trans ((D m0).Var_nonneg (X m0)) hm0
  set r : ℝ := V / η + 1 with hrdef
  have hr_pos : 0 < r := by rw [hrdef]; positivity
  have hr2_pos : 0 < r ^ 2 := pow_pos hr_pos 2
  refine ⟨c + r, ?_⟩
  filter_upwards [hV, hc] with m hVm hcm
  have hsub : (D m).Pr (fun z => c + r ≤ |X m z|)
      ≤ (D m).Pr (fun z => r ≤ |X m z - (D m).E (X m)|) := by
    apply (D m).Pr_mono
    intro z hz
    have h1 : |X m z| - |(D m).E (X m)| ≤ |X m z - (D m).E (X m)| :=
      abs_sub_abs_le_abs_sub _ _
    linarith
  refine le_trans hsub (le_trans ((D m).chebyshev (X m) hr_pos) ?_)
  rw [div_le_iff₀ hr2_pos]
  have hkey : η * r = V + η := by rw [hrdef]; field_simp
  have hexp : η * r ^ 2 = (V + η) * r := by rw [pow_two, ← mul_assoc, hkey]
  rw [hexp]
  have hr1 : (1 : ℝ) ≤ r := by
    rw [hrdef]; have : (0 : ℝ) ≤ V / η := by positivity
    linarith
  have hVle : V ≤ (V + η) * r := by
    calc V = V * 1 := (mul_one V).symm
      _ ≤ (V + η) * r := by
          apply mul_le_mul (by linarith) hr1 (by norm_num) (by linarith)
  linarith [hVm]

/-- Scaling a probability-null sequence by a constant keeps it probability-null: if `X m → 0` in
probability then `c · X m → 0` in probability. -/
theorem TendstoInProb.const_mul {D : ∀ m, FiniteDesign (Ω m)} {X : ∀ m, Ω m → ℝ}
    (c : ℝ) (h : TendstoInProb D X (fun _ => 0)) :
    TendstoInProb D (fun m z => c * X m z) (fun _ => 0) := by
  intro ε hε
  have hc1 : 0 < |c| + 1 := by positivity
  have hεc : 0 < ε / (|c| + 1) := by positivity
  have hsub : ∀ m, (D m).Pr (fun z => ε ≤ |c * X m z - (fun _ => (0:ℝ)) m|)
      ≤ (D m).Pr (fun z => ε / (|c| + 1) ≤ |X m z - (fun _ => (0:ℝ)) m|) := by
    intro m
    apply (D m).Pr_mono
    intro z hz
    simp only [sub_zero] at hz ⊢
    rw [abs_mul] at hz
    rw [div_le_iff₀ hc1]
    nlinarith [hz, abs_nonneg (X m z), abs_nonneg c]
  refine squeeze_zero (fun m => (D m).Pr_nonneg _) hsub ?_
  simpa using h (ε / (|c| + 1)) hεc

/-- **Product-tightness (`o_p × O_p = o_p`).** If `U m` converges to zero in probability and `V m`
is uniformly tight (bounded in probability), then the product `U m · V m` converges to zero in
probability.  This is the engine that turns a delta-method remainder — a vanishing factor times a
bounded factor — into an `o_p(1)` term. -/
theorem TendstoInProb.mul_boundedInProb {D : ∀ m, FiniteDesign (Ω m)} {U V : ∀ m, Ω m → ℝ}
    (hU : TendstoInProb D U (fun _ => 0)) (hV : BoundedInProb D V) :
    TendstoInProb D (fun m z => U m z * V m z) (fun _ => 0) := by
  intro ε hε
  simp only [sub_zero]
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [] with m
    exact lt_of_lt_of_le ha ((D m).Pr_nonneg _)
  · intro a ha
    have ha2 : (0 : ℝ) < a / 2 := by linarith
    obtain ⟨M, hM⟩ := hV (a / 2) ha2
    set M' : ℝ := |M| + 1 with hM'def
    have hM' : 0 < M' := by
      rw [hM'def]
      positivity
    have hMle : M ≤ M' := by
      rw [hM'def]
      linarith [le_abs_self M]
    have hMbound : ∀ᶠ m in atTop, (D m).Pr (fun z => M' ≤ |V m z|) ≤ a / 2 := by
      filter_upwards [hM] with m hmm
      refine le_trans ?_ hmm
      apply (D m).Pr_mono
      intro z hz
      exact le_trans hMle hz
    have hbound : ∀ m, (D m).Pr (fun z => ε ≤ |U m z * V m z|)
        ≤ (D m).Pr (fun z => M' ≤ |V m z|)
          + (D m).Pr (fun z => ε / M' ≤ |U m z|) := by
      intro m
      refine le_trans ?_ (Pr_or_le (D m) _ _)
      apply (D m).Pr_mono
      intro z hz
      by_cases hVlarge : M' ≤ |V m z|
      · exact Or.inl hVlarge
      · right
        push_neg at hVlarge
        rw [div_le_iff₀ hM']
        rw [abs_mul] at hz
        have hUpos : 0 < |U m z| := by
          by_contra hUpos
          have hUzero : |U m z| = 0 :=
            le_antisymm (le_of_not_gt hUpos) (abs_nonneg _)
          rw [hUzero, zero_mul] at hz
          linarith
        exact le_of_lt (lt_of_le_of_lt hz
          (mul_lt_mul_of_pos_left hVlarge hUpos))
    have hU' : Tendsto (fun m => (D m).Pr (fun z => ε / M' ≤ |U m z|)) atTop (𝓝 0) := by
      have hεM' : (0 : ℝ) < ε / M' := by positivity
      simpa using hU (ε / M') hεM'
    have htail : ∀ᶠ m in atTop, (D m).Pr (fun z => ε / M' ≤ |U m z|) < a / 2 :=
      (tendsto_order.mp hU').2 (a / 2) ha2
    filter_upwards [htail, hMbound] with m hm hmb
    calc
      (D m).Pr (fun z => ε ≤ |U m z * V m z|)
          ≤ (D m).Pr (fun z => M' ≤ |V m z|)
            + (D m).Pr (fun z => ε / M' ≤ |U m z|) := hbound m
      _ < a := by linarith [hmb]

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
