import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearClass
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Mathlib.Algebra.Order.Chebyshev
import Causalean.Mathlib.Analysis.WeightedCauchySchwarz
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part2
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part3
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part4
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part5

/-!
# Exact minimax risk and perturbation-energy bounds

Evaluates the local-linear minimax risk exactly, then collects the
design-based Cauchy-Schwarz inequalities and the energy bounds for candidate
weight perturbations that the witness construction consumes.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Establishes the stated mathematical result for loc lin minimax risk exact. -/
lemma locLinMinimaxRisk_exact
    (n d β : ℕ) (B p : ℝ)
    (hβ : 1 ≤ β) (hB : 0 < B) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n) :
    locLinMinimaxRisk (blockGraph n d) d β B p
        (le_of_lt hp0) (le_of_lt hp1) =
      B ^ 2 * blockEnergy β p d / blockCount n d := by
  classical
  let R0 := B ^ 2 * blockEnergy β p d / blockCount n d
  let w0 := canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv
  have hlower
      (w : LocLinWeights (blockGraph n d) d β p
        (le_of_lt hp0) (le_of_lt hp1)) :
      R0 ≤ locLinWorstRisk (blockGraph n d) d β B p
        (le_of_lt hp0) (le_of_lt hp1) w := by
    rw [locLinWorstRisk_exact_blockExtremal
      n d β B p hB (le_of_lt hp0) (le_of_lt hp1) hn hd hdiv w]
    have hsum :
        ∑ _b : Fin (blockCount n d),
            (d : ℝ) ^ 2 * blockEnergy β p d ≤
          ∑ b : Fin (blockCount n d),
            blockExtremal (blockGraph n d) d β p
              (le_of_lt hp0) (le_of_lt hp1) w
              (completeBlockUnits n d b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact completeBlock_blockExtremal_lower
        n d β p hp0 hp1 hn hd hdiv w b
    have hcoef : 0 ≤ B ^ 2 / (n : ℝ) ^ 2 := by positivity
    calc
      R0 =
          B ^ 2 / (n : ℝ) ^ 2 *
            ∑ _b : Fin (blockCount n d),
              (d : ℝ) ^ 2 * blockEnergy β p d := by
        symm
        exact completeBlock_benchmark_algebra
          n d B (blockEnergy β p d) hn hd hdiv
      _ ≤ B ^ 2 / (n : ℝ) ^ 2 *
          ∑ b : Fin (blockCount n d),
            blockExtremal (blockGraph n d) d β p
              (le_of_lt hp0) (le_of_lt hp1) w
              (completeBlockUnits n d b) :=
        mul_le_mul_of_nonneg_left hsum hcoef
  have hw0 :
      locLinWorstRisk (blockGraph n d) d β B p
          (le_of_lt hp0) (le_of_lt hp1) w0 = R0 := by
    rw [locLinWorstRisk_exact_blockExtremal
      n d β B p hB (le_of_lt hp0) (le_of_lt hp1) hn hd hdiv w0]
    have heq (b : Fin (blockCount n d)) :
        blockExtremal (blockGraph n d) d β p
            (le_of_lt hp0) (le_of_lt hp1) w0
            (completeBlockUnits n d b) =
          (d : ℝ) ^ 2 * blockEnergy β p d := by
      apply le_antisymm
      · exact canonical_completeBlock_blockExtremal_upper
          n d β p hp0 hp1 hn hd hdiv b
      · exact completeBlock_blockExtremal_lower
          n d β p hp0 hp1 hn hd hdiv w0 b
    rw [show
        (∑ b : Fin (blockCount n d),
          blockExtremal (blockGraph n d) d β p
            (le_of_lt hp0) (le_of_lt hp1) w0
            (completeBlockUnits n d b)) =
          ∑ _b : Fin (blockCount n d),
            (d : ℝ) ^ 2 * blockEnergy β p d by
      apply Finset.sum_congr rfl
      intro b hb
      exact heq b]
    exact completeBlock_benchmark_algebra
      n d B (blockEnergy β p d) hn hd hdiv
  unfold locLinMinimaxRisk
  apply le_antisymm
  · apply csInf_le
    · refine ⟨R0, ?_⟩
      intro r hr
      rcases hr with ⟨w, rfl⟩
      exact hlower w
    · exact ⟨w0, hw0⟩
  · apply le_csInf
    · exact ⟨locLinWorstRisk (blockGraph n d) d β B p
          (le_of_lt hp0) (le_of_lt hp1) w0, ⟨w0, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨w, rfl⟩
      exact hlower w

/-- Establishes the stated mathematical result for finite design abs e mul le sqrt. -/
lemma finiteDesign_abs_E_mul_le_sqrt
    {Ω : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (f g : Ω → ℝ) :
    |D.E (fun z => f z * g z)| ≤
      Real.sqrt (D.E (fun z => f z ^ 2)) *
        Real.sqrt (D.E (fun z => g z ^ 2)) := by
  unfold FiniteDesign.E
  exact Causalean.Mathlib.Analysis.abs_weighted_inner_le
    (Finset.univ : Finset Ω) D.p f g (fun i _ => D.p_nonneg i)

/-- Establishes the stated mathematical result for finite design e add sq le. -/
lemma finiteDesign_E_add_sq_le
    {Ω : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (f g : Ω → ℝ)
    (F G : ℝ)
    (hF : D.E (fun z => f z ^ 2) ≤ F)
    (hG : D.E (fun z => g z ^ 2) ≤ G)
    (hF0 : 0 ≤ F) (hG0 : 0 ≤ G) :
    D.E (fun z => (f z + g z) ^ 2) ≤
      F + 2 * Real.sqrt F * Real.sqrt G + G := by
  have hf0 : 0 ≤ D.E (fun z => f z ^ 2) :=
    D.E_nonneg (fun z => sq_nonneg _)
  have hg0 : 0 ≤ D.E (fun z => g z ^ 2) :=
    D.E_nonneg (fun z => sq_nonneg _)
  have hcross := finiteDesign_abs_E_mul_le_sqrt D f g
  have hsqrtF :
      Real.sqrt (D.E (fun z => f z ^ 2)) ≤ Real.sqrt F :=
    Real.sqrt_le_sqrt hF
  have hsqrtG :
      Real.sqrt (D.E (fun z => g z ^ 2)) ≤ Real.sqrt G :=
    Real.sqrt_le_sqrt hG
  have hprod :
      Real.sqrt (D.E (fun z => f z ^ 2)) *
          Real.sqrt (D.E (fun z => g z ^ 2)) ≤
        Real.sqrt F * Real.sqrt G := by
    exact mul_le_mul hsqrtF hsqrtG (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [show (fun z => (f z + g z) ^ 2) =
      (fun z => f z ^ 2 + 2 * (f z * g z) + g z ^ 2) by
    funext z
    ring]
  rw [D.E_add, D.E_add, D.E_const_mul]
  have habs :
      D.E (fun z => f z * g z) ≤
        Real.sqrt (D.E (fun z => f z ^ 2)) *
          Real.sqrt (D.E (fun z => g z ^ 2)) :=
    (le_abs_self _).trans hcross
  nlinarith

/-- Establishes the stated mathematical result for block candidate perturb energy le. -/
lemma blockCandidatePerturb_energy_le
    (n d β : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w w0 : LocLinWeights (blockGraph n d) d β p hp0 hp1)
    (b : Fin (blockCount n d))
    (choice : (Fin n → Bool) × (Fin n → Finset (Fin n)))
    (hchoice : ∀ i ∈ completeBlockUnits n d b,
      choice.2 i ⊆ completeBlockUnits n d b) :
    (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z =>
        (∑ i ∈ completeBlockUnits n d b,
          (if choice.1 i then (1 : ℝ) else -1) *
            ((w.weight i z - w0.weight i z) *
              ∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0)) ^ 2) ≤
      (d : ℝ) *
        ∑ i ∈ completeBlockUnits n d b,
          (bernoulliDesign (fun _ : Fin n => p) (fun _ => hp0)
            (fun _ => hp1)).E
            (fun z => (w.weight i z - w0.weight i z) ^ 2) := by
  classical
  let D := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => hp0) (fun _ => hp1)
  let x : (Fin n → Bool) → Fin n → ℝ := fun z i =>
    (if choice.1 i then (1 : ℝ) else -1) *
      ((w.weight i z - w0.weight i z) *
        ∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0)
  have hpoint (z : Fin n → Bool) :
      (∑ i ∈ completeBlockUnits n d b, x z i) ^ 2 ≤
        (d : ℝ) *
          ∑ i ∈ completeBlockUnits n d b,
            (w.weight i z - w0.weight i z) ^ 2 := by
    calc
      (∑ i ∈ completeBlockUnits n d b, x z i) ^ 2 ≤
          ((completeBlockUnits n d b).card : ℝ) *
            ∑ i ∈ completeBlockUnits n d b, (x z i) ^ 2 := by
        exact_mod_cast sq_sum_le_card_mul_sum_sq
          (s := completeBlockUnits n d b) (f := x z)
      _ = (d : ℝ) *
            ∑ i ∈ completeBlockUnits n d b, (x z i) ^ 2 := by
        rw [completeBlockUnits_card n d hd hdiv b]
      _ ≤ (d : ℝ) *
            ∑ i ∈ completeBlockUnits n d b,
              (w.weight i z - w0.weight i z) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro i hi
          dsimp [x]
          have hm :
              0 ≤ ∏ j ∈ choice.2 i,
                if z j then (1 : ℝ) else 0 := by
            apply Finset.prod_nonneg
            intro j hj
            split <;> positivity
          have hm1 :
              (∏ j ∈ choice.2 i,
                if z j then (1 : ℝ) else 0) ≤ 1 := by
            apply Finset.prod_le_one
            · intro j hj
              split <;> positivity
            · intro j hj
              split <;> simp_all
          have hmsq :
              (∏ j ∈ choice.2 i,
                if z j then (1 : ℝ) else 0) ^ 2 ≤ 1 := by
            nlinarith
          split <;> simp only [one_mul, neg_mul, neg_sq]
          · nlinarith [sq_nonneg (w.weight i z - w0.weight i z)]
          · nlinarith [sq_nonneg (w.weight i z - w0.weight i z)]
        · positivity
  have hn := D.E_nonneg (fun z => sub_nonneg.mpr (hpoint z))
  rw [FiniteDesign.E_sub, FiniteDesign.E_const_mul,
    FiniteDesign.E_sum] at hn
  simpa [D, x] using hn

/-- Establishes the stated mathematical result for block extremal le of weight distance. -/
lemma blockExtremal_le_of_weight_distance
    (n d β : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hdiv : d ∣ n)
    (w : LocLinWeights (blockGraph n d) d β p
      (le_of_lt hp0) (le_of_lt hp1))
    (b : Fin (blockCount n d)) :
    blockExtremal (blockGraph n d) d β p
        (le_of_lt hp0) (le_of_lt hp1) w
        (completeBlockUnits n d b) ≤
      (d : ℝ) ^ 2 * blockEnergy β p d +
        2 * Real.sqrt ((d : ℝ) ^ 2 * blockEnergy β p d) *
          Real.sqrt ((d : ℝ) *
            ∑ i ∈ completeBlockUnits n d b,
              (bernoulliDesign (fun _ : Fin n => p)
                (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
                (fun z =>
                  (w.weight i z -
                    (canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv).weight i z) ^ 2)) +
        (d : ℝ) *
          ∑ i ∈ completeBlockUnits n d b,
            (bernoulliDesign (fun _ : Fin n => p)
              (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)).E
              (fun z =>
                (w.weight i z -
                  (canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv).weight i z) ^ 2) := by
  classical
  let D := bernoulliDesign (fun _ : Fin n => p)
    (fun _ => le_of_lt hp0) (fun _ => le_of_lt hp1)
  let w0 := canonicalLocLinWeights n d β p hp0 hp1 hn hd hdiv
  let Eδ : ℝ :=
    ∑ i ∈ completeBlockUnits n d b,
      D.E (fun z => (w.weight i z - w0.weight i z) ^ 2)
  have hEδ0 : 0 ≤ Eδ := by
    dsimp [Eδ]
    apply Finset.sum_nonneg
    intro i hi
    exact D.E_nonneg (fun z => sq_nonneg _)
  unfold blockExtremal
  dsimp only
  apply Finset.sup'_le
  intro choice hchoiceMem
  have hchoice :
      ∀ i ∈ completeBlockUnits n d b,
        choice.2 i ⊆ completeBlockUnits n d b ∧
          (choice.2 i).card ≤ effBeta β d := by
    simpa using hchoiceMem
  let f : (Fin n → Bool) → ℝ := fun z =>
    ∑ i ∈ completeBlockUnits n d b,
      (if choice.1 i then (1 : ℝ) else -1) *
        locLinUnitError w0 i (choice.2 i) z
  let g : (Fin n → Bool) → ℝ := fun z =>
    ∑ i ∈ completeBlockUnits n d b,
      (if choice.1 i then (1 : ℝ) else -1) *
        ((w.weight i z - w0.weight i z) *
          ∏ j ∈ choice.2 i, if z j then (1 : ℝ) else 0)
  have hf :
      D.E (fun z => f z ^ 2) ≤
        (d : ℝ) ^ 2 * blockEnergy β p d := by
    calc
      D.E (fun z => f z ^ 2) ≤
          blockExtremal (blockGraph n d) d β p
            (le_of_lt hp0) (le_of_lt hp1) w0
            (completeBlockUnits n d b) := by
        unfold blockExtremal
        dsimp only
        convert Finset.le_sup'
          (f := fun choice =>
            D.E (fun z =>
              (∑ i ∈ completeBlockUnits n d b,
                (if choice.1 i then (1 : ℝ) else -1) *
                  locLinUnitError w0 i (choice.2 i) z) ^ 2))
          hchoiceMem using 1
      _ ≤ (d : ℝ) ^ 2 * blockEnergy β p d :=
        canonical_completeBlock_blockExtremal_upper
          n d β p hp0 hp1 hn hd hdiv b
  have hg :
      D.E (fun z => g z ^ 2) ≤ (d : ℝ) * Eδ := by
    exact blockCandidatePerturb_energy_le
      n d β p (le_of_lt hp0) (le_of_lt hp1) hd hdiv w w0 b choice
      (fun i hi => (hchoice i hi).1)
  have hA0 : 0 ≤ (d : ℝ) ^ 2 * blockEnergy β p d := by
    apply mul_nonneg (sq_nonneg _)
    unfold blockEnergy
    apply Finset.sum_nonneg
    intro r hr
    apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact pow_nonneg
        (mul_nonneg hp0.le (sub_nonneg.mpr hp1.le)) _
  have hDE0 : 0 ≤ (d : ℝ) * Eδ := mul_nonneg (by positivity) hEδ0
  have hadd := finiteDesign_E_add_sq_le D f g
    ((d : ℝ) ^ 2 * blockEnergy β p d) ((d : ℝ) * Eδ)
    hf hg hA0 hDE0
  convert hadd using 1
  · apply FiniteDesign.E_congr
    intro z
    congr 1
    dsimp [f, g, w0, locLinUnitError]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Establishes the stated mathematical result for e global centered mul raw eq zero. -/
lemma E_global_centered_mul_raw_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset V) (hTS : T ⊆ S) (hcard : T.card < S.card) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z =>
        (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) *
          ∏ j ∈ T, if z j then (1 : ℝ) else 0) = 0 := by
  let x : Bool → ℝ := fun b => (if b then 1 else 0) - p
  let y : Bool → ℝ := fun b => if b then 1 else 0
  rw [show (fun z : V → Bool =>
      (∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)) *
        ∏ j ∈ T, if z j then (1 : ℝ) else 0) =
      (fun z => ∏ j,
        (if j ∈ S then x (z j) else 1) *
          (if j ∈ T then y (z j) else 1)) by
    funext z
    rw [Finset.prod_mul_distrib]
    simp [x, y]]
  rw [E_global_coordinate_prod p hp0 hp1
    (fun j b =>
      (if j ∈ S then x b else 1) *
        (if j ∈ T then y b else 1))]
  have hex : ∃ j, j ∈ S ∧ j ∉ T := by
    by_contra h
    push_neg at h
    have hST : S ⊆ T := fun j hj => h j hj
    have := Finset.card_le_card hST
    omega
  obtain ⟨j, hjS, hjT⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hjS, hjT, x, y]
  ring

end CausalSmith.Experimentation.SnipeDegreeFrontier
