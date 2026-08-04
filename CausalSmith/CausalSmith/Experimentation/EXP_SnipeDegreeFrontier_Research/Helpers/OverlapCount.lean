import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Single-out-degree overlap count

The identity double-counts pairs consisting of an overlapping neighborhood
and an `r`-subset.  Its upper bound charges the graph's out-degree once.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of outcome neighborhoods containing a fixed subset. -/
noncomputable def containingNeighborhoods
    (G : V → V → Prop) (S : Finset V) : ℕ :=
  (Finset.univ.filter (fun l => S ⊆ nbhd G l)).card

/-- The exact overlap double-count and its degree-sharp upper bounds. -/
-- @node: lem:overlap-count
lemma overlap_count_le
    (G : V → V → Prop) (d r : ℕ) (i : V)
    (hdegree : BoundedDegree G d) (hr : 1 ≤ r) :
    (∑ l : V, Nat.choose ((nbhd G i ∩ nbhd G l).card) r) =
        ∑ S ∈ ((nbhd G i).powerset.filter (fun S => S.card = r)),
          containingNeighborhoods G S ∧
      (∑ S ∈ ((nbhd G i).powerset.filter (fun S => S.card = r)),
          containingNeighborhoods G S) ≤
        d * Nat.choose (nbhd G i).card r ∧
      d * Nat.choose (nbhd G i).card r ≤ d * Nat.choose d r := by
  classical
  let F := (nbhd G i).powerset.filter (fun S => S.card = r)
  have hchoose (l : V) :
      Nat.choose ((nbhd G i ∩ nbhd G l).card) r =
        ∑ S ∈ F, if S ⊆ nbhd G l then 1 else 0 := by
    rw [← Finset.card_powersetCard]
    rw [← Finset.card_filter]
    congr 1
    ext S
    simp only [F, Finset.mem_powersetCard, Finset.mem_filter,
      Finset.mem_powerset, Finset.subset_inter_iff]
    aesop
  have hcontain (S : Finset V) (hS : S ∈ F) :
      containingNeighborhoods G S ≤ d := by
    have hcard : S.card = r := (Finset.mem_filter.mp hS).2
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hne
    have hsub :
        Finset.univ.filter (fun l => S ⊆ nbhd G l) ⊆ outNbhd G j := by
      intro l hl
      have hjl : j ∈ nbhd G l := (Finset.mem_filter.mp hl).2 hj
      simpa [nbhd, outNbhd] using hjl
    calc
      containingNeighborhoods G S =
          (Finset.univ.filter (fun l => S ⊆ nbhd G l)).card := rfl
      _ ≤ (outNbhd G j).card := Finset.card_le_card hsub
      _ ≤ d := hdegree.2 j
  have hcardF : F.card = Nat.choose (nbhd G i).card r := by
    rw [← Finset.card_powersetCard]
    congr 1
    ext S
    simp [F, Finset.mem_powersetCard]
  constructor
  · calc
      (∑ l : V, Nat.choose ((nbhd G i ∩ nbhd G l).card) r) =
          ∑ l : V, ∑ S ∈ F, if S ⊆ nbhd G l then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro l hl
            exact hchoose l
      _ = ∑ S ∈ F, ∑ l : V, if S ⊆ nbhd G l then 1 else 0 :=
        Finset.sum_comm
      _ = ∑ S ∈ F, containingNeighborhoods G S := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [containingNeighborhoods, Finset.card_filter]
  constructor
  · calc
      (∑ S ∈ F, containingNeighborhoods G S) ≤ ∑ S ∈ F, d := by
        exact Finset.sum_le_sum fun S hS => hcontain S hS
      _ = d * Nat.choose (nbhd G i).card r := by
        simp [hcardF, Nat.mul_comm]
  · exact Nat.mul_le_mul_left d (Nat.choose_le_choose r (hdegree.1 i))

end CausalSmith.Experimentation.SnipeDegreeFrontier
