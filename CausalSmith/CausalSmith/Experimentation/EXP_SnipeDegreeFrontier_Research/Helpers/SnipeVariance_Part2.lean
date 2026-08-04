import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Estimator
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.BlockRepresenter
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.OverlapCount
import Causalean.Experimentation.DesignBased.ProductBlock
import Causalean.Experimentation.DesignBased.ProductVariance
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance_Part1

/-!
# Centred-monomial expansion of the SNIPE score

Expands a potential outcome in the centred monomial basis of the Bernoulli
design, records the orthogonality and energy identities of that expansion, and
shows the coefficients vanish outside the relevant block support.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A centered monomial on the global assignment cube. -/
noncomputable def globalCenteredMonomial
    (p : ℝ) (S : Finset V) (z : V → Bool) : ℝ :=
  ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)

/-- Every real function on a finite Boolean cube has a Bernoulli-centered
Fourier expansion. -/
lemma exists_globalCenteredMonomial_expansion
    (p : ℝ) (F : (V → Bool) → ℝ) :
    ∃ a : Finset V → ℝ, ∀ z,
      F z = ∑ S ∈ (Finset.univ : Finset V).powerset,
        a S * globalCenteredMonomial p S z := by
  classical
  let sgn : Bool → ℝ := fun b => if b then 1 else -1
  let base : Bool → ℝ := fun b => if b then p else 1 - p
  let a : Finset V → ℝ := fun S =>
    ∑ w : V → Bool,
      F w * (∏ j ∈ S, sgn (w j)) *
        ∏ j ∈ (Finset.univ : Finset V) \ S, base (w j)
  refine ⟨a, fun z => ?_⟩
  have hdelta (w : V → Bool) :
      (if z = w then (1 : ℝ) else 0) =
        ∑ S ∈ (Finset.univ : Finset V).powerset,
          ((∏ j ∈ S, sgn (w j)) *
              ∏ j ∈ (Finset.univ : Finset V) \ S, base (w j)) *
            globalCenteredMonomial p S z := by
    rw [show (if z = w then (1 : ℝ) else 0) =
        ∏ j : V, if z j = w j then (1 : ℝ) else 0 by
      by_cases hzw : z = w
      · subst w
        simp
      · rw [if_neg hzw]
        obtain ⟨j, hj⟩ : ∃ j, z j ≠ w j := by
          simpa [funext_iff] using hzw
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm]
    rw [show
        (∏ j : V, if z j = w j then (1 : ℝ) else 0) =
          ∏ j : V,
            (sgn (w j) * ((if z j then (1 : ℝ) else 0) - p) +
              base (w j)) by
      apply Finset.prod_congr rfl
      intro j hj
      cases hz : z j <;> cases hw : w j <;>
        simp [hz, hw, sgn, base] <;> ring]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro S hS
    rw [show
        (∏ i ∈ S,
              sgn (w i) * ((if z i then (1 : ℝ) else 0) - p)) =
          (∏ i ∈ S, sgn (w i)) *
            globalCenteredMonomial p S z by
      rw [Finset.prod_mul_distrib]
      rfl]
    ring
  calc
    F z = ∑ w : V → Bool, F w * (if z = w then (1 : ℝ) else 0) := by
      rw [Finset.sum_eq_single z]
      · simp
      · intro w hw hwz
        simp [Ne.symm hwz]
      · simp
    _ = ∑ w : V → Bool, F w *
        ∑ S ∈ (Finset.univ : Finset V).powerset,
          ((∏ j ∈ S, sgn (w j)) *
              ∏ j ∈ (Finset.univ : Finset V) \ S, base (w j)) *
            globalCenteredMonomial p S z := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hdelta w]
    _ = ∑ S ∈ (Finset.univ : Finset V).powerset,
        a S * globalCenteredMonomial p S z := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      dsimp [a]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      ring

/-- Orthogonality of global Bernoulli-centered monomials. -/
lemma E_globalCenteredMonomial_mul
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset V) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E
      (fun z =>
        globalCenteredMonomial p S z *
          globalCenteredMonomial p T z) =
      if S = T then (p * (1 - p)) ^ S.card else 0 := by
  let x : Bool → ℝ := fun b => (if b then 1 else 0) - p
  rw [show (fun z : V → Bool =>
      globalCenteredMonomial p S z *
        globalCenteredMonomial p T z) =
      (fun z => ∏ j,
        (if j ∈ S then x (z j) else 1) *
          (if j ∈ T then x (z j) else 1)) by
    funext z
    rw [Finset.prod_mul_distrib]
    simp [globalCenteredMonomial, x]]
  rw [E_global_coordinate_prod p hp0 hp1
    (fun j b =>
      (if j ∈ S then x b else 1) *
        (if j ∈ T then x b else 1))]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    have hfactor (j : V) :
        p * ((if j ∈ S then x true else 1) *
              (if j ∈ S then x true else 1)) +
            (1 - p) * ((if j ∈ S then x false else 1) *
              (if j ∈ S then x false else 1)) =
          if j ∈ S then p * (1 - p) else 1 := by
      by_cases hj : j ∈ S <;> simp [hj, x] <;> ring
    simp_rw [hfactor]
    rw [Finset.prod_ite_mem]
    simp
  · rw [if_neg hST]
    have hdiff :
        ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S) := by
      by_contra h
      apply hST
      ext j
      constructor
      · intro hjS
        by_contra hjT
        exact h ⟨j, Or.inl ⟨hjS, hjT⟩⟩
      · intro hjT
        by_contra hjS
        exact h ⟨j, Or.inr ⟨hjT, hjS⟩⟩
    obtain ⟨j, hj⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rcases hj with hj | hj
    · simp [hj.1, hj.2, x]
      ring
    · simp [hj.1, hj.2, x]
      ring

/-- Parseval's identity for a displayed global Bernoulli-Fourier
expansion. -/
lemma globalCenteredMonomial_expansion_energy
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : (V → Bool) → ℝ) (a : Finset V → ℝ)
    (ha : ∀ z, F z =
      ∑ S ∈ (Finset.univ : Finset V).powerset,
        a S * globalCenteredMonomial p S z) :
    (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E (fun z => F z ^ 2) =
      ∑ S ∈ (Finset.univ : Finset V).powerset,
        a S ^ 2 * (p * (1 - p)) ^ S.card := by
  let D := bernoulliDesign (fun _ : V => p) (fun _ => hp0)
    (fun _ => hp1)
  rw [show (fun z => F z ^ 2) =
      (fun z =>
        (∑ S ∈ (Finset.univ : Finset V).powerset,
            a S * globalCenteredMonomial p S z) *
          (∑ T ∈ (Finset.univ : Finset V).powerset,
            a T * globalCenteredMonomial p T z)) by
    funext z
    rw [ha z]
    ring]
  simp only [Finset.sum_mul, Finset.mul_sum, FiniteDesign.E_sum]
  have hterm (S T : Finset V) :
      D.E (fun z =>
        (a S * globalCenteredMonomial p S z) *
          (a T * globalCenteredMonomial p T z)) =
        a S * a T *
          (if S = T then (p * (1 - p)) ^ S.card else 0) := by
    rw [show (fun z =>
        (a S * globalCenteredMonomial p S z) *
          (a T * globalCenteredMonomial p T z)) =
        (fun z => (a S * a T) *
          (globalCenteredMonomial p S z *
            globalCenteredMonomial p T z)) by
      funext z
      ring]
    rw [FiniteDesign.E_const_mul,
      E_globalCenteredMonomial_mul p hp0 hp1 S T]
  dsimp [D] at hterm
  simp_rw [hterm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single S]
  · rw [if_pos rfl]
    ring
  · intro T hT hTS
    rw [if_neg hTS]
    ring
  · intro hS'
    exact (hS' hS).elim

/-- A displayed centered Fourier expansion has zero constant coefficient
when the expanded function is centered. -/
lemma globalCenteredMonomial_empty_coef_eq_zero
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : (V → Bool) → ℝ) (a : Finset V → ℝ)
    (ha : ∀ z, F z =
      ∑ S ∈ (Finset.univ : Finset V).powerset,
        a S * globalCenteredMonomial p S z)
    (hmean : (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
      (fun _ => hp1)).E F = 0) :
    a ∅ = 0 := by
  let D := bernoulliDesign (fun _ : V => p) (fun _ => hp0)
    (fun _ => hp1)
  rw [show F = fun z =>
      ∑ S ∈ (Finset.univ : Finset V).powerset,
        a S * globalCenteredMonomial p S z by
    funext z
    exact ha z, FiniteDesign.E_sum] at hmean
  have hterm (S : Finset V) :
      D.E (fun z => a S * globalCenteredMonomial p S z) =
        if S = ∅ then a S else 0 := by
    rw [FiniteDesign.E_const_mul]
    have h :=
      E_globalCenteredMonomial_mul (V := V) p hp0 hp1 S ∅
    have h' :
        (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
          (fun _ => hp1)).E (globalCenteredMonomial p S) =
            if S = ∅ then (p * (1 - p)) ^ S.card else 0 := by
      simpa [globalCenteredMonomial] using h
    change a S *
        (bernoulliDesign (fun _ : V => p) (fun _ => hp0)
          (fun _ => hp1)).E (globalCenteredMonomial p S) =
      if S = ∅ then a S else 0
    rw [h']
    by_cases hS : S = ∅ <;> simp [hS]
  dsimp [D] at hterm
  simp_rw [hterm] at hmean
  simpa using hmean

/-- Dependence on a designated finite coordinate block. -/
def DependsOnBlock
    (N : Finset V) (F : (V → Bool) → ℝ) : Prop :=
  ∀ z z', (∀ j ∈ N, z j = z' j) → F z = F z'

/-- A centered Fourier coefficient outside the coordinate block on which a
function depends vanishes. -/
lemma globalCenteredMonomial_coef_eq_zero_of_not_subset
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (N : Finset V) (F : (V → Bool) → ℝ)
    (hF : DependsOnBlock N F)
    (a : Finset V → ℝ)
    (ha : ∀ z, F z =
      ∑ S ∈ (Finset.univ : Finset V).powerset,
        a S * globalCenteredMonomial p S z)
    (S : Finset V) (hS : S ∈ (Finset.univ : Finset V).powerset)
    (hSN : ¬ S ⊆ N) :
    a S = 0 := by
  classical
  obtain ⟨j, hjS, hjN⟩ : ∃ j, j ∈ S ∧ j ∉ N := by
    simpa only [Finset.not_subset] using hSN
  let Dcoin : V → FiniteDesign Bool :=
    fun _ => coinDesign p (le_of_lt hp0) (le_of_lt hp1)
  let x : Bool → ℝ := fun b => (if b then 1 else 0) - p
  let R : (V → Bool) → ℝ := fun z =>
    F z * globalCenteredMonomial p (S.erase j) z
  have hfactor :
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
        (fun z => F z * globalCenteredMonomial p S z) = 0 := by
    unfold bernoulliDesign
    rw [show (fun z => F z * globalCenteredMonomial p S z) =
        (fun z => x (z j) * R z) by
      funext z
      dsimp [R, x, globalCenteredMonomial]
      rw [← Finset.mul_prod_erase S
        (fun k => (if z k then (1 : ℝ) else 0) - p) hjS]
      ring]
    rw [FiniteDesign.E_prod_block_mul Dcoin {j}
      (fun z => x (z j)) R]
    · have hx :
          (prodDesign Dcoin).E (fun z => x (z j)) = 0 := by
        change
          (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
            (fun _ => le_of_lt hp1)).E (fun z => x (z j)) = 0
        rw [show (fun z : V → Bool => x (z j)) =
            (fun z => ∏ k, if k = j then x (z k) else 1) by
          funext z
          rw [Finset.prod_eq_single j]
          · simp
          · intro k hk hkj
            simp [hkj]
          · simp]
        rw [E_global_coordinate_prod p (le_of_lt hp0) (le_of_lt hp1)
          (fun k b => if k = j then x b else 1)]
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [x]
        ring
      rw [hx, zero_mul]
    · intro z z' hzz
      exact congrArg x (hzz j (by simp))
    · intro z z' hzz
      dsimp [R]
      congr 1
      · apply hF z z'
        intro k hkN
        exact hzz k (by
          simp only [Finset.mem_singleton]
          intro hkj
          subst k
          exact hjN hkN)
      · unfold globalCenteredMonomial
        apply Finset.prod_congr rfl
        intro k hk
        rw [hzz k]
        simp only [Finset.mem_singleton]
        exact Finset.ne_of_mem_erase hk
  have hcoef :
      (bernoulliDesign (fun _ : V => p) (fun _ => le_of_lt hp0)
        (fun _ => le_of_lt hp1)).E
        (fun z => F z * globalCenteredMonomial p S z) =
        a S * (p * (1 - p)) ^ S.card := by
    rw [show (fun z => F z * globalCenteredMonomial p S z) =
        (fun z =>
          ∑ T ∈ (Finset.univ : Finset V).powerset,
            a T * (globalCenteredMonomial p T z *
              globalCenteredMonomial p S z)) by
      funext z
      rw [ha z, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro T hT
      ring]
    rw [FiniteDesign.E_sum]
    simp_rw [FiniteDesign.E_const_mul,
      E_globalCenteredMonomial_mul p (le_of_lt hp0) (le_of_lt hp1)]
    rw [Finset.sum_eq_single S]
    · simp
    · intro T hT hTS
      simp [hTS]
    · exact fun h => (h hS).elim
  rw [hfactor] at hcoef
  have hv : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  exact (mul_eq_zero.mp hcoef.symm).resolve_right (pow_ne_zero _ hv.ne')

end CausalSmith.Experimentation.SnipeDegreeFrontier
