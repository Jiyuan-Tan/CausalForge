/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Basic closure geometry of the exceptional locus
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalCodimension
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalIncidence

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

/-- Proves the stated set-containment or membership property for subset zariski Closure. -/
lemma subset_zariskiClosure (A : Set (CumVec ℂ)) : A ⊆ zariskiClosure A := by
  intro t ht P hP
  exact hP t ht

/-- Proves the stated mathematical property of zariski Closure mono. -/
lemma zariskiClosure_mono {A B : Set (CumVec ℂ)} (h : A ⊆ B) :
    zariskiClosure A ⊆ zariskiClosure B := by
  intro t ht P hP
  exact ht P (fun s hs => hP s (h hs))

/-- Proves the stated mathematical property of zariski Closure idem. -/
@[simp] lemma zariskiClosure_idem (A : Set (CumVec ℂ)) :
    zariskiClosure (zariskiClosure A) = zariskiClosure A := by
  apply Set.Subset.antisymm
  · intro t ht P hP
    exact ht P fun s hs => hs P hP
  · exact subset_zariskiClosure _

/-- Proves the stated mathematical property of zariski Closure is Closed. -/
lemma zariskiClosure_isClosed (A : Set (CumVec ℂ)) :
    zariskiClosure (zariskiClosure A) = zariskiClosure A :=
  zariskiClosure_idem A

/-- Proves the stated set-containment or membership property for generic Full Fiber Compatibility subset forward range. -/
lemma genericFullFiberCompatibility_subset_forward_range (m : ℕ) :
    genericFullFiberCompatibility m ⊆
      Set.range (forwardCumulantMap m (2 * m + 2)) := by
  rintro t ⟨htband, hcompat⟩
  rcases hcompat with ⟨⟨θ, hθ, _⟩, _⟩ | ⟨_, ⟨θ, hθ⟩⟩
  · exact ⟨θ, map_eq_target_of_mem_fiberCorrespondence
      (forwardCumulantMap_mem_bandSupportedCumulants m (2 * m + 2)) htband hθ⟩
  · exact ⟨θ, map_eq_target_of_mem_fiberCorrespondence
      (forwardCumulantMap_mem_bandSupportedCumulants m (2 * m + 2)) htband hθ⟩

/-- Proves the stated set-containment or membership property for generic Full Fiber Compatibility subset reverse range. -/
lemma genericFullFiberCompatibility_subset_reverse_range (m : ℕ) :
    genericFullFiberCompatibility m ⊆
      Set.range (reverseCumulantMap m (2 * m + 2)) := by
  rintro t ⟨htband, hcompat⟩
  rcases hcompat with ⟨_, ⟨η, hη⟩⟩ | ⟨⟨η, hη, _⟩, _⟩
  · exact ⟨η, map_eq_target_of_mem_fiberCorrespondence
      (reverseCumulantMap_mem_bandSupportedCumulants m (2 * m + 2)) htband hη⟩
  · exact ⟨η, map_eq_target_of_mem_fiberCorrespondence
      (reverseCumulantMap_mem_bandSupportedCumulants m (2 * m + 2)) htband hη⟩

/-- Proves the stated set-containment or membership property for generic Compatibility Closure subset forward Variety. -/
lemma genericCompatibilityClosure_subset_forwardVariety (m : ℕ) :
    genericCompatibilityClosure m ⊆
      cumulantImageVariety (forwardCumulantMap m (2 * m + 2)) := by
  exact zariskiClosure_mono (genericFullFiberCompatibility_subset_forward_range m)

/-- Proves the stated set-containment or membership property for generic Compatibility Closure subset reverse Variety. -/
lemma genericCompatibilityClosure_subset_reverseVariety (m : ℕ) :
    genericCompatibilityClosure m ⊆
      cumulantImageVariety (reverseCumulantMap m (2 * m + 2)) := by
  exact zariskiClosure_mono (genericFullFiberCompatibility_subset_reverse_range m)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
