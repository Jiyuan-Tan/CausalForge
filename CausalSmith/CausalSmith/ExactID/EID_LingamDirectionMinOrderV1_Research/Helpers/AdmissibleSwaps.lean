/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Source-swap reindexing helpers
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Basic.Swaps

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-- The admissible middle-block relabeling, as a permutation of all source indices. -/
-- @node: permMiddleEquiv
def permMiddleEquiv (m : ℕ) (π : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 2)) where
  toFun := permMiddle m π
  invFun := permMiddle m π⁻¹
  left_inv := by
    intro j
    apply Fin.ext
    simp only [permMiddle]
    split_ifs <;> simp_all <;> omega
  right_inv := by
    intro j
    apply Fin.ext
    simp only [permMiddle]
    split_ifs <;> simp_all <;> omega

-- @node: sum_permMiddle
/-- Relabeling the middle source indices while keeping the two endpoint indices fixed does not change a finite sum. -/
lemma sum_permMiddle {A : Type*} [AddCommMonoid A] (m : ℕ) (π : Equiv.Perm (Fin m))
    (f : Fin (m + 2) → A) :
    (∑ j, f (permMiddle m π j)) = ∑ j, f j := by
  exact Fintype.sum_equiv (permMiddleEquiv m π) _ _ (fun _ => rfl)

-- @node: forwardLoading_admissibleSourceSwap
/-- After an admissible source relabeling, each forward loading equals the original loading at the correspondingly relabeled source. -/
lemma forwardLoading_admissibleSourceSwap {R : Type*} [CommRing R] (m : ℕ)
    (π : Equiv.Perm (Fin m)) (θ : ParamSpace R m) (j : Fin (m + 2)) :
    forwardLoading m (admissibleSourceSwap m π θ).1
        (admissibleSourceSwap m π θ).2.1 j =
      forwardLoading m θ.1 θ.2.1 (permMiddle m π j) := by
  simp only [admissibleSourceSwap, forwardLoading, permMiddle]
  split_ifs <;> simp_all <;> try omega

-- @node: reverseLoading_admissibleSourceSwap
/-- After an admissible source relabeling, each reverse loading equals the original loading at the correspondingly relabeled source. -/
lemma reverseLoading_admissibleSourceSwap {R : Type*} [CommRing R] (m : ℕ)
    (π : Equiv.Perm (Fin m)) (η : ParamSpace R m) (j : Fin (m + 2)) :
    reverseLoading m (admissibleSourceSwap m π η).1
        (admissibleSourceSwap m π η).2.1 j =
      reverseLoading m η.1 η.2.1 (permMiddle m π j) := by
  simp only [admissibleSourceSwap, reverseLoading, permMiddle]
  split_ifs <;> simp_all <;> try omega

-- @node: forwardCumulantMap_admissibleSourceSwap
/-- The forward cumulant map is unchanged by any admissible relabeling of the middle sources. -/
lemma forwardCumulantMap_admissibleSourceSwap {R : Type*} [CommRing R] (m L : ℕ)
    (π : Equiv.Perm (Fin m)) (θ : ParamSpace R m) :
    forwardCumulantMap m L (admissibleSourceSwap m π θ) = forwardCumulantMap m L θ := by
  funext r a
  simp only [forwardCumulantMap]
  split_ifs
  · simp_rw [forwardLoading_admissibleSourceSwap]
    change (∑ j : Fin (m + 2),
        θ.2.2 (permMiddle m π j) r *
          (forwardLoading m θ.1 θ.2.1 (permMiddle m π j)).1 ^ (r - a) *
          (forwardLoading m θ.1 θ.2.1 (permMiddle m π j)).2 ^ a) = _
    exact sum_permMiddle (A := R) m π (fun j =>
      θ.2.2 j r * (forwardLoading m θ.1 θ.2.1 j).1 ^ (r - a) *
        (forwardLoading m θ.1 θ.2.1 j).2 ^ a)
  · rfl

-- @node: reverseCumulantMap_admissibleSourceSwap
/-- The reverse cumulant map is unchanged by any admissible relabeling of the middle sources. -/
lemma reverseCumulantMap_admissibleSourceSwap {R : Type*} [CommRing R] (m L : ℕ)
    (π : Equiv.Perm (Fin m)) (η : ParamSpace R m) :
    reverseCumulantMap m L (admissibleSourceSwap m π η) = reverseCumulantMap m L η := by
  funext r a
  simp only [reverseCumulantMap]
  split_ifs
  · simp_rw [reverseLoading_admissibleSourceSwap]
    change (∑ j : Fin (m + 2),
        η.2.2 (permMiddle m π j) r *
          (reverseLoading m η.1 η.2.1 (permMiddle m π j)).1 ^ (r - a) *
          (reverseLoading m η.1 η.2.1 (permMiddle m π j)).2 ^ a) = _
    exact sum_permMiddle (A := R) m π (fun j =>
      η.2.2 j r * (reverseLoading m η.1 η.2.1 j).1 ^ (r - a) *
        (reverseLoading m η.1 η.2.1 j).2 ^ a)
  · rfl

-- @node: permLeadingEquiv
/-- Extend a permutation of the middle slopes by fixing the leading direct-slope index. -/
def permLeadingEquiv (m : ℕ) (π : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) where
  toFun := Fin.cases 0 (fun i => Fin.succ (π i))
  invFun := Fin.cases 0 (fun i => Fin.succ (π⁻¹ i))
  left_inv := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · simp
  right_inv := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · simp

-- @node: finCons_comp_perm_injective
/-- If the direct slope together with all latent slopes are distinct, they remain distinct after permuting the latent slopes. -/
lemma finCons_comp_perm_injective {R : Type*} {m : ℕ} (x : R) (f : Fin m → R)
    (π : Equiv.Perm (Fin m)) (h : Function.Injective (Fin.cons x f)) :
    Function.Injective (Fin.cons x (fun i => f (π i))) := by
  have hcomp (i : Fin (m + 1)) :
      (Fin.cons x (fun j => f (π j)) : Fin (m + 1) → R) i =
        (Fin.cons x f : Fin (m + 1) → R) (permLeadingEquiv m π i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  intro i j hij
  apply (permLeadingEquiv m π).injective
  apply h
  rw [← hcomp i, ← hcomp j]
  exact hij

-- @node: realFeasibleRegion_admissibleSourceSwap
/-- The real feasible parameter region is closed under admissible relabeling of the middle sources. -/
lemma realFeasibleRegion_admissibleSourceSwap (m L : ℕ) (π : Equiv.Perm (Fin m))
    (θ : ParamSpace ℝ m) (hθ : θ ∈ realFeasibleRegion m L) :
    admissibleSourceSwap m π θ ∈ realFeasibleRegion m L := by
  rcases hθ with ⟨hedge, hinj, hout, hreal⟩
  refine ⟨hedge, finCons_comp_perm_injective θ.1 θ.2.1 π hinj, ?_, ?_⟩
  · intro j r hr
    exact hout (permMiddle m π j) r hr
  · intro j
    exact hreal (permMiddle m π j)

-- @node: forwardAxisModel_admissibleSourceSwap
/-- A forward axis model remains a forward axis model when middle sources and their parameters are relabeled together. -/
lemma forwardAxisModel_admissibleSourceSwap {Ω : Type*} [MeasurableSpace Ω] (m : ℕ)
    (π : Equiv.Perm (Fin m)) (θ : ParamSpace ℝ m) (S : Fin (m + 2) → Ω → ℝ)
    (X Y : Ω → ℝ) (h : ForwardAxisModel X Y S θ.1 θ.2.1) :
    ForwardAxisModel X Y (fun i => S (permMiddle m π i))
      (admissibleSourceSwap m π θ).1 (admissibleSourceSwap m π θ).2.1 := by
  constructor
  · intro ω
    rw [h.1 ω]
    simp only [forwardLoading_admissibleSourceSwap]
    exact (sum_permMiddle m π _).symm
  · intro ω
    rw [h.2 ω]
    simp only [forwardLoading_admissibleSourceSwap]
    exact (sum_permMiddle m π _).symm

-- @node: reverseAxisModel_admissibleSourceSwap
/-- A reverse axis model remains a reverse axis model when middle sources and their parameters are relabeled together. -/
lemma reverseAxisModel_admissibleSourceSwap {Ω : Type*} [MeasurableSpace Ω] (m : ℕ)
    (π : Equiv.Perm (Fin m)) (η : ParamSpace ℝ m) (S : Fin (m + 2) → Ω → ℝ)
    (X Y : Ω → ℝ) (h : ReverseAxisModel X Y S η.1 η.2.1) :
    ReverseAxisModel X Y (fun i => S (permMiddle m π i))
      (admissibleSourceSwap m π η).1 (admissibleSourceSwap m π η).2.1 := by
  constructor
  · intro ω
    rw [h.1 ω]
    simp only [reverseLoading_admissibleSourceSwap]
    exact (sum_permMiddle m π _).symm
  · intro ω
    rw [h.2 ω]
    simp only [reverseLoading_admissibleSourceSwap]
    exact (sum_permMiddle m π _).symm

-- @node: arrowTaggedOrbit_right_left_disjoint
/-- The admissible-swap orbits tagged as forward and reverse are disjoint, regardless of their parameter values. -/
lemma arrowTaggedOrbit_right_left_disjoint {R : Type*} (m : ℕ) (θ η : ParamSpace R m) :
    Disjoint (arrowTaggedOrbit m Arrow.right θ) (arrowTaggedOrbit m Arrow.left η) := by
  rw [Set.disjoint_left]
  intro p hpR hpL
  rcases hpR with ⟨π, rfl⟩
  rcases hpL with ⟨σ, hσ⟩
  have htag := congrArg Prod.fst hσ
  simp [admissibleSourceSwapTagged] at htag

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
