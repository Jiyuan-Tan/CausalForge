/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Denominator ratio convergence for the bipartite minimax design

The two Hájek denominators `D₁ = ∑ᵢ Tᵢ/πᵢ¹` and `D₀ = ∑ᵢ Cᵢ/πᵢ⁰` have design mean `card O`, so the
normalized ratios `D₁/card O`, `D₀/card O` converge in probability to one.  Equivalently the centered
ratios `D_arm/card O − 1` vanish in probability — the `o_p(1)` factors of the delta-method
ratio-remainder argument (`RatioRemainder.lean`).
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DenominatorMoment
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DenominatorControl

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open scoped BigOperators Topology
open Finset Filter
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.DesignBased.FiniteDesign
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {Ix Ox : ℕ → Type*} [∀ n, Fintype (Ix n)] [∀ n, Fintype (Ox n)]
  [∀ n, DecidableEq (Ix n)] [∀ n, DecidableEq (Ox n)]

/-- The centered treated-denominator ratio `D₁/card Ox − 1` vanishes in probability. -/
lemma treatDenominatorRatioCentered_tendstoInProb_zero
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ)
    (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hreg : Tendsto (fun n => denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ))
      atTop (𝓝 0)) :
    TendstoInProb D
      (fun n z => (Fintype.card (Ox n) : ℝ)⁻¹ * (∑ i, (E n).expT z i / (E n).piT (p n) i) - 1)
      (fun _ => 0) := by
  classical
  let X : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    (Fintype.card (Ox n) : ℝ)⁻¹ * (∑ i, (E n).expT z i / (E n).piT (p n) i) - 1
  change TendstoInProb D X (fun _ => 0)
  have hcard : ∀ᶠ n in atTop, 0 < (Fintype.card (Ox n) : ℝ) := by
    filter_upwards [hcardO.eventually (eventually_ge_atTop 1)] with n hn
    exact_mod_cast hn
  have hvar : Tendsto (fun n => (D n).Var (X n)) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards with n
      exact (D n).Var_nonneg _
    · filter_upwards [hcard] with n hn
      let S : (Ix n → Bool) → ℝ := fun z =>
        ∑ i, (E n).expT z i / (E n).piT (p n) i
      have hpos : ∀ k, 0 < p n k := fun k =>
        lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
      have hbound : (D n).Var S ≤ (Fintype.card (Ox n) : ℝ) *
          (Dbar * denominatorKernelBound (ε n) dbar) := by
        rw [hBern n]
        exact treatDenominator_var_le (E n) (ε n) (B n) dbar Dbar (hε n).1
          (hε n).2 (hdeg n) (hdep n) (p n) (hp0 n) (hp1 n) (hfeas n)
      have hvar_eq : (D n).Var (X n) = (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 *
          (D n).Var S := by
        have hshift : (D n).Var (fun z => (Fintype.card (Ox n) : ℝ)⁻¹ * S z - 1) =
            (D n).Var (fun z => (Fintype.card (Ox n) : ℝ)⁻¹ * S z) := by
          unfold FiniteDesign.Var
          rw [(D n).E_sub, (D n).E_const]
          apply (D n).E_congr
          intro z
          ring
        calc
          (D n).Var (X n) = (D n).Var (fun z =>
              (Fintype.card (Ox n) : ℝ)⁻¹ * S z - 1) := by rfl
          _ = (D n).Var (fun z => (Fintype.card (Ox n) : ℝ)⁻¹ * S z) := hshift
          _ = (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 * (D n).Var S :=
            (D n).Var_const_mul _ _
      calc
        (D n).Var (X n) = (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 * (D n).Var S := hvar_eq
        _ ≤ (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 *
            ((Fintype.card (Ox n) : ℝ) *
              (Dbar * denominatorKernelBound (ε n) dbar)) :=
          mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
        _ = Dbar * (denominatorKernelBound (ε n) dbar /
            (Fintype.card (Ox n) : ℝ)) := by
          field_simp [ne_of_gt hn]
    · simpa using hreg.const_mul Dbar
  have hmean : ∀ᶠ n in atTop, (D n).E (X n) = 0 := by
    filter_upwards [hcard] with n hn
    let S : (Ix n → Bool) → ℝ := fun z =>
      ∑ i, (E n).expT z i / (E n).piT (p n) i
    have hpos : ∀ k, 0 < p n k := fun k =>
      lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
    have hS : (D n).E S = (Fintype.card (Ox n) : ℝ) := by
      rw [hBern n]
      exact treatDenominator_mean (E n) (p n) (hp0 n) (hp1 n) hpos
    calc
      (D n).E (X n) = (D n).E (fun z =>
          (Fintype.card (Ox n) : ℝ)⁻¹ * S z - 1) := by rfl
      _ = (Fintype.card (Ox n) : ℝ)⁻¹ * (D n).E S - 1 := by
        rw [(D n).E_sub, (D n).E_const_mul, (D n).E_const]
      _ = 0 := by
        rw [hS]
        field_simp [ne_of_gt hn]
        ring
  have hprob := tendstoInProb_of_var D X hvar
  intro δ hδ
  refine (hprob δ hδ).congr' ?_
  filter_upwards [hmean] with n hn
  simp [hn]

/-- The centered control-denominator ratio `D₀/card Ox − 1` vanishes in probability. -/
lemma ctrlDenominatorRatioCentered_tendstoInProb_zero
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ)
    (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hreg : Tendsto (fun n => denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ))
      atTop (𝓝 0)) :
    TendstoInProb D
      (fun n z => (Fintype.card (Ox n) : ℝ)⁻¹ * (∑ i, (E n).expC z i / (E n).piC (p n) i) - 1)
      (fun _ => 0) := by
  classical
  let X : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    (Fintype.card (Ox n) : ℝ)⁻¹ * (∑ i, (E n).expC z i / (E n).piC (p n) i) - 1
  change TendstoInProb D X (fun _ => 0)
  have hcard : ∀ᶠ n in atTop, 0 < (Fintype.card (Ox n) : ℝ) := by
    filter_upwards [hcardO.eventually (eventually_ge_atTop 1)] with n hn
    exact_mod_cast hn
  have hvar : Tendsto (fun n => (D n).Var (X n)) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards with n
      exact (D n).Var_nonneg _
    · filter_upwards [hcard] with n hn
      let S : (Ix n → Bool) → ℝ := fun z =>
        ∑ i, (E n).expC z i / (E n).piC (p n) i
      have hlt : ∀ k, p n k < 1 := fun k =>
        lt_of_le_of_lt ((hfeas n).floor k).2 (by linarith [(hε n).1])
      have hbound : (D n).Var S ≤ (Fintype.card (Ox n) : ℝ) *
          (Dbar * denominatorKernelBound (ε n) dbar) := by
        rw [hBern n]
        exact ctrlDenominator_var_le (E n) (ε n) (B n) dbar Dbar (hε n).1
          (hε n).2 (hdeg n) (hdep n) (p n) (hp0 n) (hp1 n) (hfeas n)
      have hvar_eq : (D n).Var (X n) = (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 *
          (D n).Var S := by
        have hshift : (D n).Var (fun z => (Fintype.card (Ox n) : ℝ)⁻¹ * S z - 1) =
            (D n).Var (fun z => (Fintype.card (Ox n) : ℝ)⁻¹ * S z) := by
          unfold FiniteDesign.Var
          rw [(D n).E_sub, (D n).E_const]
          apply (D n).E_congr
          intro z
          ring
        calc
          (D n).Var (X n) = (D n).Var (fun z =>
              (Fintype.card (Ox n) : ℝ)⁻¹ * S z - 1) := by rfl
          _ = (D n).Var (fun z => (Fintype.card (Ox n) : ℝ)⁻¹ * S z) := hshift
          _ = (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 * (D n).Var S :=
            (D n).Var_const_mul _ _
      calc
        (D n).Var (X n) = (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 * (D n).Var S := hvar_eq
        _ ≤ (Fintype.card (Ox n) : ℝ)⁻¹ ^ 2 *
            ((Fintype.card (Ox n) : ℝ) *
              (Dbar * denominatorKernelBound (ε n) dbar)) :=
          mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
        _ = Dbar * (denominatorKernelBound (ε n) dbar /
            (Fintype.card (Ox n) : ℝ)) := by
          field_simp [ne_of_gt hn]
    · simpa using hreg.const_mul Dbar
  have hmean : ∀ᶠ n in atTop, (D n).E (X n) = 0 := by
    filter_upwards [hcard] with n hn
    let S : (Ix n → Bool) → ℝ := fun z =>
      ∑ i, (E n).expC z i / (E n).piC (p n) i
    have hlt : ∀ k, p n k < 1 := fun k =>
      lt_of_le_of_lt ((hfeas n).floor k).2 (by linarith [(hε n).1])
    have hS : (D n).E S = (Fintype.card (Ox n) : ℝ) := by
      rw [hBern n]
      exact ctrlDenominator_mean (E n) (p n) (hp0 n) (hp1 n) hlt
    calc
      (D n).E (X n) = (D n).E (fun z =>
          (Fintype.card (Ox n) : ℝ)⁻¹ * S z - 1) := by rfl
      _ = (Fintype.card (Ox n) : ℝ)⁻¹ * (D n).E S - 1 := by
        rw [(D n).E_sub, (D n).E_const_mul, (D n).E_const]
      _ = 0 := by
        rw [hS]
        field_simp [ne_of_gt hn]
        ring
  have hprob := tendstoInProb_of_var D X hvar
  intro δ hδ
  refine (hprob δ hδ).congr' ?_
  filter_upwards [hmean] with n hn
  simp [hn]

end CausalSmith.Experimentation.BipartiteMinimaxDesign
