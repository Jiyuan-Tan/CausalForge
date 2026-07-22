/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variance of an edge-sum over a bounded-degree dependency graph

In the finite-design probability layer, this file proves an abstract linear-in-`N`
bound on the variance of a sum of bounded random variables `b i j` indexed by ordered
pairs that vanish off a symmetric, bounded-degree dependency graph and decorrelate
across non-adjacent edges.  The bound `Var ≤ 8·M²·m³·N` is the workhorse behind
design-based central-limit / consistency arguments under local dependence, with no
measure theory: everything is `Finset` algebra over the design weights.
-/

import Causalean.Experimentation.DesignBased.DesignCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Edge-sum variance bound for finite designs

This file proves bounded-expectation and bounded-covariance helpers for `FiniteDesign`
(`abs_E_le`, `abs_Cov_le_two_sq`, and `Cov_zero_left`) and the main dependency-graph edge-sum
variance inequality `var_edge_sum_le`. The final theorem controls the variance of a sum of bounded
edge-indexed statistics by `8 * M ^ 2 * (m ^ 3 * N)` when the edge variables vanish off a symmetric
bounded-degree graph and are uncorrelated across graph-separated edges.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)

/-! ### Pointwise expectation/covariance bounds -/

/-- The expectation of a random variable whose absolute value is bounded by `M`
pointwise is itself bounded by `M` in absolute value. -/
lemma abs_E_le {X : Ω → ℝ} {M : ℝ} (h : ∀ z, |X z| ≤ M) : |D.E X| ≤ M := by
  apply abs_le.mpr
  constructor
  · -- -M ≤ D.E X
    have hptw : ∀ z, 0 ≤ X z + M := by
      intro z; have := abs_le.mp (h z); linarith
    have hpos : 0 ≤ D.E (fun z => X z + M) := D.E_nonneg hptw
    have heq : D.E (fun z => X z + M) = D.E X + M := by
      rw [D.E_add]; simp [D.E_const]
    rw [heq] at hpos; linarith
  · -- D.E X ≤ M
    have hptw : ∀ z, 0 ≤ M - X z := by
      intro z; have := abs_le.mp (h z); linarith
    have hpos : 0 ≤ D.E (fun z => M - X z) := D.E_nonneg hptw
    have heq : D.E (fun z => M - X z) = M - D.E X := by
      rw [D.E_sub]; simp [D.E_const]
    rw [heq] at hpos; linarith

/-- The design covariance of two random variables each bounded by `M` in absolute
value pointwise is bounded by `2·M²` in absolute value. -/
lemma abs_Cov_le_two_sq {X Y : Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hX : ∀ z, |X z| ≤ M) (hY : ∀ z, |Y z| ≤ M) : |D.Cov X Y| ≤ 2 * M ^ 2 := by
  rw [D.Cov_eq]
  have hExy : |D.E (fun z => X z * Y z)| ≤ M ^ 2 := by
    apply D.abs_E_le (X := fun z => X z * Y z) (M := M ^ 2)
    intro z
    rw [abs_mul]
    have hmul := mul_le_mul (hX z) (hY z) (abs_nonneg _) hM
    rw [sq]
    exact hmul
  have hEX : |D.E X| ≤ M := D.abs_E_le hX
  have hEY : |D.E Y| ≤ M := D.abs_E_le hY
  have hprod : |D.E X * D.E Y| ≤ M ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hEX hEY (abs_nonneg _) hM
  calc |D.E (fun z => X z * Y z) - D.E X * D.E Y|
      ≤ |D.E (fun z => X z * Y z)| + |D.E X * D.E Y| := abs_sub _ _
    _ ≤ M ^ 2 + M ^ 2 := by linarith
    _ = 2 * M ^ 2 := by ring

/-- The covariance of the identically-zero random variable with anything is zero. -/
lemma Cov_zero_left (Y : Ω → ℝ) : D.Cov (fun _ => 0) Y = 0 := by
  rw [D.Cov_eq]
  have h1 : D.E (fun z => (0 : ℝ) * Y z) = 0 := by
    rw [D.E_congr (fun z => zero_mul (Y z)), D.E_const]
  have h2 : D.E (fun _ : Ω => (0 : ℝ)) = 0 := D.E_const 0
  rw [h1, h2]; ring

/-! ### The edge-sum variance bound -/

set_option linter.unusedDecidableInType false in
open Classical in
/-- **Variance of an edge-sum over a bounded-degree dependency graph.**
The variance of a sum of bounded random variables, each attached to an ordered pair of
units, is at most a constant times the number of units, provided each variable is
absolutely bounded by `M`, is zero whenever its pair is not an edge of the dependency
graph, the graph is symmetric with every degree at most `m`, and two edges' variables
are uncorrelated whenever no edge connects them.  Formally, `Var[∑_{i,j} b i j] ≤
8·M²·m³·N` where `N` is the number of units.  This is the design-based analogue of the
local-dependence variance bound that underlies central-limit theorems for
network/interference experiments. -/
theorem var_edge_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ι → Ω → ℝ) {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ i j z, |b i j z| ≤ M)
    (G : ι → ι → Prop) [DecidableRel G] (hsymm : ∀ i j, G i j → G j i)
    {m : ℕ} (hdeg : ∀ i, (Finset.univ.filter (fun j => G i j)).card ≤ m)
    (hvanish : ∀ i j, ¬ G i j → b i j = fun _ => 0)
    (hcov0 : ∀ i j k l, ¬ (G i k ∨ G i l ∨ G j k ∨ G j l) → D.Cov (b i j) (b k l) = 0) :
    D.Var (fun z => ∑ i, ∑ j, b i j z) ≤ 8 * M ^ 2 * ((m : ℝ) ^ 3 * (Fintype.card ι : ℝ)) := by
  classical
  -- local indicator
  set χ : Prop → ℝ := fun p => if p then (1 : ℝ) else 0 with hχdef
  have χ_nonneg : ∀ p, 0 ≤ χ p := by intro p; by_cases h : p <;> simp [hχdef, h]
  have χ_le_one : ∀ p, χ p ≤ 1 := by intro p; by_cases h : p <;> simp [hχdef, h]
  -- degree-sum bound: ∑ j χ(G i j) ≤ m
  have hdegsum : ∀ i : ι, (∑ j, χ (G i j)) ≤ (m : ℝ) := by
    intro i
    have : (∑ j, χ (G i j)) = ((Finset.univ.filter (fun j => G i j)).card : ℝ) := by
      convert Finset.sum_boole (fun j => G i j) Finset.univ using 3
    rw [this]
    exact_mod_cast hdeg i
  -- out-degree via symmetry: ∑ k χ(G k l) ≤ m
  have hdegsum' : ∀ l : ι, (∑ k, χ (G k l)) ≤ (m : ℝ) := by
    intro l
    have hcong : (∑ k, χ (G k l)) = (∑ k, χ (G l k)) := by
      apply Finset.sum_congr rfl
      intro k _
      have : G k l ↔ G l k := ⟨hsymm k l, hsymm l k⟩
      simp only [this]
    rw [hcong]
    exact hdegsum l
  -- (a) expand the variance as a quadruple sum of covariances
  have hexpand : D.Var (fun z => ∑ i, ∑ j, b i j z)
      = ∑ i, ∑ j, ∑ k, ∑ l, D.Cov (b i j) (b k l) := by
    have hrw : (fun z => ∑ i, ∑ j, b i j z)
        = (fun z => ∑ p ∈ (Finset.univ : Finset (ι × ι)), (1 : ℝ) * b p.1 p.2 z) := by
      funext z
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [one_mul]
    rw [hrw,
      D.Var_linear_comb (Finset.univ : Finset (ι × ι)) (fun _ => 1) (fun p z => b p.1 p.2 z)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [one_mul, one_mul]
  rw [hexpand]
  -- (b) termwise bound: Cov ≤ |Cov| ≤ (2M²)·bracket
  set bracket : ι → ι → ι → ι → ℝ :=
    fun i j k l => χ (G i j) * χ (G k l) * (χ (G i k) + χ (G i l) + χ (G j k) + χ (G j l))
    with hbracketdef
  have bracket_nonneg : ∀ i j k l, 0 ≤ bracket i j k l := by
    intro i j k l
    rw [hbracketdef]
    apply mul_nonneg (mul_nonneg (χ_nonneg _) (χ_nonneg _))
    have h1 := χ_nonneg (G i k); have h2 := χ_nonneg (G i l)
    have h3 := χ_nonneg (G j k); have h4 := χ_nonneg (G j l)
    linarith
  have htermwise : ∀ i j k l,
      D.Cov (b i j) (b k l) ≤ (2 * M ^ 2) * bracket i j k l := by
    intro i j k l
    -- Cov = 0 in the "otherwise" cases, and bracket ≥ 1 in the "all hold" case
    by_cases hij : G i j
    · by_cases hkl : G k l
      · by_cases hconn : G i k ∨ G i l ∨ G j k ∨ G j l
        · -- all hold: bracket ≥ 1, Cov ≤ |Cov| ≤ 2M²
          have hb1 : (1 : ℝ) ≤ bracket i j k l := by
            simp only [hbracketdef]
            have hχij : χ (G i j) = 1 := by simp [hχdef, hij]
            have hχkl : χ (G k l) = 1 := by simp [hχdef, hkl]
            rw [hχij, hχkl, one_mul, one_mul]
            have n1 := χ_nonneg (G i k); have n2 := χ_nonneg (G i l)
            have n3 := χ_nonneg (G j k); have n4 := χ_nonneg (G j l)
            rcases hconn with h | h | h | h
            · have : χ (G i k) = 1 := by simp [hχdef, h]
              linarith
            · have : χ (G i l) = 1 := by simp [hχdef, h]
              linarith
            · have : χ (G j k) = 1 := by simp [hχdef, h]
              linarith
            · have : χ (G j l) = 1 := by simp [hχdef, h]
              linarith
          have hcov : D.Cov (b i j) (b k l) ≤ 2 * M ^ 2 :=
            (le_abs_self _).trans (D.abs_Cov_le_two_sq hM (hbound i j) (hbound k l))
          have h2M2 : 0 ≤ 2 * M ^ 2 := by positivity
          calc D.Cov (b i j) (b k l) ≤ 2 * M ^ 2 := hcov
            _ = (2 * M ^ 2) * 1 := by ring
            _ ≤ (2 * M ^ 2) * bracket i j k l :=
                mul_le_mul_of_nonneg_left hb1 h2M2
        · -- ¬ connected: Cov = 0, bracket ≥ 0
          rw [hcov0 i j k l hconn]
          exact mul_nonneg (by positivity) (bracket_nonneg i j k l)
      · -- ¬ G k l: b k l = 0 so Cov = 0
        have : D.Cov (b i j) (b k l) = 0 := by
          rw [D.Cov_congr (X := b i j) (Y := b k l) (X' := b i j) (Y' := fun _ => 0)
            (fun z => rfl) (fun z => by rw [hvanish k l hkl])]
          rw [D.Cov_comm, D.Cov_zero_left]
        rw [this]
        exact mul_nonneg (by positivity) (bracket_nonneg i j k l)
    · -- ¬ G i j: b i j = 0 so Cov = 0
      have : D.Cov (b i j) (b k l) = 0 := by
        rw [D.Cov_congr (X := b i j) (Y := b k l) (X' := fun _ => 0) (Y' := b k l)
          (fun z => by rw [hvanish i j hij]) (fun z => rfl)]
        rw [D.Cov_zero_left]
      rw [this]
      exact mul_nonneg (by positivity) (bracket_nonneg i j k l)
  -- sum the termwise bound over the quadruple
  have hsumbound : (∑ i, ∑ j, ∑ k, ∑ l, D.Cov (b i j) (b k l))
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, (2 * M ^ 2) * bracket i j k l := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    apply Finset.sum_le_sum; intro l _
    exact htermwise i j k l
  refine hsumbound.trans ?_
  -- (c) pull out 2M² and split the bracket into four sums
  have hpull : (∑ i, ∑ j, ∑ k, ∑ l, (2 * M ^ 2) * bracket i j k l)
      = (2 * M ^ 2) * (∑ i, ∑ j, ∑ k, ∑ l, bracket i j k l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
  rw [hpull]
  -- split bracket into S1+S2+S3+S4
  set S : (ι → ι → ι → ι → ℝ) → ℝ := fun f => ∑ i, ∑ j, ∑ k, ∑ l, f i j k l with hSdef
  have hsplit : (∑ i, ∑ j, ∑ k, ∑ l, bracket i j k l)
      = S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i k))
        + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i l))
        + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j k))
        + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j l)) := by
    simp only [hSdef]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [hbracketdef]; ring
  rw [hsplit]
  -- Each of S1..S4 ≤ N·m³. We prove a generic factorization helper.
  -- Helper: ∑ over a slot of χ(edge) * (nonneg) ≤ m * sup, using degree bounds.
  -- We just prove the four bounds directly.
  have h2M2nn : (0 : ℝ) ≤ 2 * M ^ 2 := by positivity
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
  -- S1 = ∑i ∑j ∑k ∑l χ(Gij) χ(Gkl) χ(Gik)
  -- factor: ∑i (∑j χ(Gij)) * (∑k χ(Gik) * (∑l χ(Gkl)))
  have hS1 : S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i k))
      ≤ (Fintype.card ι : ℝ) * (m : ℝ) ^ 3 := by
    simp only [hSdef]
    have hcard : (Fintype.card ι : ℝ) * (m : ℝ) ^ 3
        = ∑ _i : ι, (m : ℝ) ^ 3 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    apply Finset.sum_le_sum; intro i _
    -- bound ∑j∑k∑l χ(Gij)χ(Gkl)χ(Gik) ≤ m^3
    -- = (∑j χ(Gij)) * (∑k χ(Gik) * (∑l χ(Gkl)))
    have hfact : (∑ j, ∑ k, ∑ l, χ (G i j) * χ (G k l) * χ (G i k))
        = (∑ j, χ (G i j)) * (∑ k, χ (G i k) * (∑ l, χ (G k l))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hfact]
    -- inner: ∑k χ(Gik) * (∑l χ(Gkl)) ≤ ∑k χ(Gik) * m ≤ m * m
    have hinner : (∑ k, χ (G i k) * (∑ l, χ (G k l))) ≤ (m : ℝ) ^ 2 := by
      have h1 : (∑ k, χ (G i k) * (∑ l, χ (G k l)))
          ≤ ∑ k, χ (G i k) * (m : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hdegsum k) (χ_nonneg _)
      have h2 : (∑ k, χ (G i k) * (m : ℝ)) = (∑ k, χ (G i k)) * (m : ℝ) := by
        rw [Finset.sum_mul]
      have h3 : (∑ k, χ (G i k)) * (m : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (hdegsum i) hmnn
      calc (∑ k, χ (G i k) * (∑ l, χ (G k l)))
          ≤ (∑ k, χ (G i k)) * (m : ℝ) := by rw [← h2]; exact h1
        _ ≤ (m : ℝ) * (m : ℝ) := h3
        _ = (m : ℝ) ^ 2 := by ring
    have hjsum : (∑ j, χ (G i j)) ≤ (m : ℝ) := hdegsum i
    have hinner_nn : (0 : ℝ) ≤ ∑ k, χ (G i k) * (∑ l, χ (G k l)) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (χ_nonneg _)
        (Finset.sum_nonneg (fun l _ => χ_nonneg _)))
    have hjsum_nn : (0 : ℝ) ≤ ∑ j, χ (G i j) :=
      Finset.sum_nonneg (fun j _ => χ_nonneg _)
    calc (∑ j, χ (G i j)) * (∑ k, χ (G i k) * (∑ l, χ (G k l)))
        ≤ (m : ℝ) * (m : ℝ) ^ 2 :=
          mul_le_mul hjsum hinner hinner_nn hmnn
      _ = (m : ℝ) ^ 3 := by ring
  -- S2 = ∑i∑j∑k∑l χ(Gij)χ(Gkl)χ(Gil)
  -- factor: ∑i (∑j χ(Gij)) * (∑l χ(Gil) * (∑k χ(Gkl)))  -- middle edge i–l
  have hS2 : S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i l))
      ≤ (Fintype.card ι : ℝ) * (m : ℝ) ^ 3 := by
    simp only [hSdef]
    have hcard : (Fintype.card ι : ℝ) * (m : ℝ) ^ 3
        = ∑ _i : ι, (m : ℝ) ^ 3 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    apply Finset.sum_le_sum; intro i _
    -- ∑j∑k∑l χ(Gij)χ(Gkl)χ(Gil) = (∑j χ(Gij)) * (∑l χ(Gil) * (∑k χ(Gkl)))
    have hfact : (∑ j, ∑ k, ∑ l, χ (G i j) * χ (G k l) * χ (G i l))
        = (∑ j, χ (G i j)) * (∑ l, χ (G i l) * (∑ k, χ (G k l))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hfact]
    have hinner : (∑ l, χ (G i l) * (∑ k, χ (G k l))) ≤ (m : ℝ) ^ 2 := by
      have h1 : (∑ l, χ (G i l) * (∑ k, χ (G k l)))
          ≤ ∑ l, χ (G i l) * (m : ℝ) := by
        apply Finset.sum_le_sum; intro l _
        exact mul_le_mul_of_nonneg_left (hdegsum' l) (χ_nonneg _)
      have h2 : (∑ l, χ (G i l) * (m : ℝ)) = (∑ l, χ (G i l)) * (m : ℝ) := by
        rw [Finset.sum_mul]
      have h3 : (∑ l, χ (G i l)) * (m : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (hdegsum i) hmnn
      calc (∑ l, χ (G i l) * (∑ k, χ (G k l)))
          ≤ (∑ l, χ (G i l)) * (m : ℝ) := by rw [← h2]; exact h1
        _ ≤ (m : ℝ) * (m : ℝ) := h3
        _ = (m : ℝ) ^ 2 := by ring
    have hjsum : (∑ j, χ (G i j)) ≤ (m : ℝ) := hdegsum i
    have hinner_nn : (0 : ℝ) ≤ ∑ l, χ (G i l) * (∑ k, χ (G k l)) :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (χ_nonneg _)
        (Finset.sum_nonneg (fun k _ => χ_nonneg _)))
    have hjsum_nn : (0 : ℝ) ≤ ∑ j, χ (G i j) :=
      Finset.sum_nonneg (fun j _ => χ_nonneg _)
    calc (∑ j, χ (G i j)) * (∑ l, χ (G i l) * (∑ k, χ (G k l)))
        ≤ (m : ℝ) * (m : ℝ) ^ 2 :=
          mul_le_mul hjsum hinner hinner_nn hmnn
      _ = (m : ℝ) ^ 3 := by ring
  -- S3 = ∑i∑j∑k∑l χ(Gij)χ(Gkl)χ(Gjk)  -- middle edge j–k
  -- factor over j first: ∑j (∑i χ(Gij)) * (∑k χ(Gjk) * (∑l χ(Gkl)))
  have hS3 : S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j k))
      ≤ (Fintype.card ι : ℝ) * (m : ℝ) ^ 3 := by
    simp only [hSdef]
    have hcard : (Fintype.card ι : ℝ) * (m : ℝ) ^ 3
        = ∑ _j : ι, (m : ℝ) ^ 3 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- reorganize: ∑i∑j∑k∑l = ∑j∑i∑k∑l
    rw [Finset.sum_comm]
    rw [hcard]
    apply Finset.sum_le_sum; intro j _
    -- inner sum over i,k,l : ∑i∑k∑l χ(Gij)χ(Gkl)χ(Gjk)
    -- = (∑i χ(Gij)) * (∑k χ(Gjk) * (∑l χ(Gkl)))
    have hfact : (∑ i, ∑ k, ∑ l, χ (G i j) * χ (G k l) * χ (G j k))
        = (∑ i, χ (G i j)) * (∑ k, χ (G j k) * (∑ l, χ (G k l))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hfact]
    -- ∑i χ(Gij) ≤ m (in-degree of j via symmetry)
    have hisum : (∑ i, χ (G i j)) ≤ (m : ℝ) := hdegsum' j
    have hinner : (∑ k, χ (G j k) * (∑ l, χ (G k l))) ≤ (m : ℝ) ^ 2 := by
      have h1 : (∑ k, χ (G j k) * (∑ l, χ (G k l)))
          ≤ ∑ k, χ (G j k) * (m : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hdegsum k) (χ_nonneg _)
      have h2 : (∑ k, χ (G j k) * (m : ℝ)) = (∑ k, χ (G j k)) * (m : ℝ) := by
        rw [Finset.sum_mul]
      have h3 : (∑ k, χ (G j k)) * (m : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (hdegsum j) hmnn
      calc (∑ k, χ (G j k) * (∑ l, χ (G k l)))
          ≤ (∑ k, χ (G j k)) * (m : ℝ) := by rw [← h2]; exact h1
        _ ≤ (m : ℝ) * (m : ℝ) := h3
        _ = (m : ℝ) ^ 2 := by ring
    have hinner_nn : (0 : ℝ) ≤ ∑ k, χ (G j k) * (∑ l, χ (G k l)) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (χ_nonneg _)
        (Finset.sum_nonneg (fun l _ => χ_nonneg _)))
    have hisum_nn : (0 : ℝ) ≤ ∑ i, χ (G i j) :=
      Finset.sum_nonneg (fun i _ => χ_nonneg _)
    calc (∑ i, χ (G i j)) * (∑ k, χ (G j k) * (∑ l, χ (G k l)))
        ≤ (m : ℝ) * (m : ℝ) ^ 2 :=
          mul_le_mul hisum hinner hinner_nn hmnn
      _ = (m : ℝ) ^ 3 := by ring
  -- S4 = ∑i∑j∑k∑l χ(Gij)χ(Gkl)χ(Gjl)  -- middle edge j–l
  -- factor over j first: ∑j (∑i χ(Gij)) * (∑l χ(Gjl) * (∑k χ(Gkl)))
  have hS4 : S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j l))
      ≤ (Fintype.card ι : ℝ) * (m : ℝ) ^ 3 := by
    simp only [hSdef]
    have hcard : (Fintype.card ι : ℝ) * (m : ℝ) ^ 3
        = ∑ _j : ι, (m : ℝ) ^ 3 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_comm]
    rw [hcard]
    apply Finset.sum_le_sum; intro j _
    -- ∑i∑k∑l χ(Gij)χ(Gkl)χ(Gjl) = (∑i χ(Gij)) * (∑l χ(Gjl) * (∑k χ(Gkl)))
    have hfact : (∑ i, ∑ k, ∑ l, χ (G i j) * χ (G k l) * χ (G j l))
        = (∑ i, χ (G i j)) * (∑ l, χ (G j l) * (∑ k, χ (G k l))) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hfact]
    have hisum : (∑ i, χ (G i j)) ≤ (m : ℝ) := hdegsum' j
    have hinner : (∑ l, χ (G j l) * (∑ k, χ (G k l))) ≤ (m : ℝ) ^ 2 := by
      have h1 : (∑ l, χ (G j l) * (∑ k, χ (G k l)))
          ≤ ∑ l, χ (G j l) * (m : ℝ) := by
        apply Finset.sum_le_sum; intro l _
        exact mul_le_mul_of_nonneg_left (hdegsum' l) (χ_nonneg _)
      have h2 : (∑ l, χ (G j l) * (m : ℝ)) = (∑ l, χ (G j l)) * (m : ℝ) := by
        rw [Finset.sum_mul]
      have h3 : (∑ l, χ (G j l)) * (m : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (hdegsum j) hmnn
      calc (∑ l, χ (G j l) * (∑ k, χ (G k l)))
          ≤ (∑ l, χ (G j l)) * (m : ℝ) := by rw [← h2]; exact h1
        _ ≤ (m : ℝ) * (m : ℝ) := h3
        _ = (m : ℝ) ^ 2 := by ring
    have hinner_nn : (0 : ℝ) ≤ ∑ l, χ (G j l) * (∑ k, χ (G k l)) :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (χ_nonneg _)
        (Finset.sum_nonneg (fun k _ => χ_nonneg _)))
    have hisum_nn : (0 : ℝ) ≤ ∑ i, χ (G i j) :=
      Finset.sum_nonneg (fun i _ => χ_nonneg _)
    calc (∑ i, χ (G i j)) * (∑ l, χ (G j l) * (∑ k, χ (G k l)))
        ≤ (m : ℝ) * (m : ℝ) ^ 2 :=
          mul_le_mul hisum hinner hinner_nn hmnn
      _ = (m : ℝ) ^ 3 := by ring
  -- combine: (2M²) * (S1+S2+S3+S4) ≤ (2M²)*(4 N m³) = 8 M² m³ N
  have hsum4 : S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i k))
        + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i l))
        + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j k))
        + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j l))
      ≤ 4 * ((Fintype.card ι : ℝ) * (m : ℝ) ^ 3) := by
    linarith [hS1, hS2, hS3, hS4]
  calc (2 * M ^ 2) *
        (S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i k))
          + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G i l))
          + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j k))
          + S (fun i j k l => χ (G i j) * χ (G k l) * χ (G j l)))
      ≤ (2 * M ^ 2) * (4 * ((Fintype.card ι : ℝ) * (m : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum4 h2M2nn
    _ = 8 * M ^ 2 * ((m : ℝ) ^ 3 * (Fintype.card ι : ℝ)) := by ring

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
