/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Admissible source swaps preserve causal direction
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.AdmissibleSwaps
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Selector

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-! ## In-scope crux: admissible swaps preserve the arrow -/

/-- **Admissible swaps preserve direction.**  For each `π ∈ G_m`:

* (map invariance) the forward and reverse cumulant maps are invariant under the
  admissible source swap `θ ↦ π · θ` — the Finset-sum reindexing crux;
* (real-feasibility preservation) the swap maps each real feasible region into
  itself (`θ ∈ F^b ⇒ π · θ ∈ F^b`);
* (full LvLiNGAM preservation, model tied to its weights) **for a real-feasible
  parameter** (`θ ∈ F^right_{m,L}`, resp. `η ∈ F^left_{m,L}`, within the valid order
  range `ValidOrder m L` — matching the paper's "if a forward structural model has
  real-feasible parameter `θ`" hypothesis), relabeling the latent
  sources by `π` (`S'_i = S_{π(i)}`, fixing `0` and `m + 1`) preserves independence,
  centering, non-Gaussianity, the finite moments, noncollinearity, the nonzero edge,
  the forward (resp. reverse) structural equation, and hence the observed pair
  `(X, Y)`, its observational law `P_M`, and the directed edge `D(M)`.  Each model's
  *actual* source cumulants are its parameter weights (`Cum(S_j) = θ.2.2 j` resp.
  `η.2.2 j`), and the swap transports this link to the relabeled model (its source
  cumulants are the swapped weights);
* (arrow-tag preservation and opposite-arrow orbit disjointness) the `G_m` action on
  `Arrow × ParamSpace` **preserves the arrow tag** `b` (the swap fixes indices `0` and
  `m + 1` and never converts a forward axis pattern into a reverse one), so the
  right-tagged and left-tagged `G_m`-orbits are **disjoint**; hence quotienting a
  same-arrow fiber by `G_m` identifies only source labels and never identifies
  opposite arrows. -/
-- @node: lem:admissible-swaps-preserve-direction
lemma admissibleSwaps_preserve_direction (m L : ℕ)
    (hm : ValidComplexity m) (hL : ValidOrder m L)
    (π : Equiv.Perm (Fin m))
    -- COMPLEX parameters carry the map/orbit invariance: the note states invariance and
    -- quotient behaviour for the **complex** `Θ`-fibers (`fiberCorrespondence`,
    -- `quotientFiber`, `admissibleOrbit` are all complex), so specializing those clauses
    -- to `ℝ` would understate the claim.
    (θc ηc : ParamSpace ℂ m)
    -- REAL parameters carry the feasible structural-model preservation: real feasibility
    -- (`realFeasibleRegion`) and the LvLiNGAM source witnesses are real objects.
    (θ η : ParamSpace ℝ m)
    (Pforward Preverse : Measure (ℝ × ℝ)) :
    -- (1) map invariance (both arrows), on the COMPLEX fibers:
    (forwardCumulantMap m L (admissibleSourceSwap m π θc) = forwardCumulantMap m L θc ∧
     reverseCumulantMap m L (admissibleSourceSwap m π ηc) = reverseCumulantMap m L ηc) ∧
    -- (2) real-feasibility preservation (both arrows):
    (θ ∈ realFeasibleRegion m L → admissibleSourceSwap m π θ ∈ realFeasibleRegion m L) ∧
    (η ∈ realFeasibleRegion m L → admissibleSourceSwap m π η ∈ realFeasibleRegion m L) ∧
    -- (3) full forward LvLiNGAM preservation under the source relabeling
    -- `S'_i = S_{π(i)}` (independence, centering, non-Gaussianity, moments,
    -- noncollinearity, nonzero edge, structural equation, pushforward law):
    (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Fin (m + 2) → Ω → ℝ)
        (X Y : Ω → ℝ),
        -- the paper conditions model preservation on the forward parameter being
        -- real-feasible (`θ ∈ F^right_{m,L}`) and on the declared valid order range:
        θ ∈ realFeasibleRegion m L → IsProbabilityMeasure μ →
        Pforward = μ.map (fun ω => (X ω, Y ω)) →
        IndependentSources μ S → (∀ j, ∫ ω, S j ω ∂μ = 0) → SourceNonGaussian μ S →
        FiniteCumulants μ S (2 * m + 2) → ForwardAxisModel X Y S θ.1 θ.2.1 →
        ForwardNonCollinear θ.1 θ.2.1 → ForwardNonzeroEdge θ.1 →
        -- the model's actual source cumulants ARE its parameter weights `θ.2.2`:
        (∀ j, ∀ r, 2 ≤ r → r ≤ L → sourceCumulant μ (S j) r = θ.2.2 j r) →
          IndependentSources μ (fun i => S (permMiddle m π i)) ∧
          (∀ j, ∫ ω, S (permMiddle m π j) ω ∂μ = 0) ∧
          SourceNonGaussian μ (fun i => S (permMiddle m π i)) ∧
          FiniteCumulants μ (fun i => S (permMiddle m π i)) (2 * m + 2) ∧
          ForwardAxisModel X Y (fun i => S (permMiddle m π i))
            (admissibleSourceSwap m π θ).1 (admissibleSourceSwap m π θ).2.1 ∧
          ForwardNonCollinear (admissibleSourceSwap m π θ).1 (admissibleSourceSwap m π θ).2.1 ∧
          ForwardNonzeroEdge (admissibleSourceSwap m π θ).1 ∧
          -- the relabeled model's source cumulants are the SWAPPED weights, so the
          -- model–parameter link is transported by the swap:
          (∀ j, ∀ r, 2 ≤ r → r ≤ L →
              sourceCumulant μ (S (permMiddle m π j)) r = (admissibleSourceSwap m π θ).2.2 j r) ∧
          -- the relabeled witnesses therefore realize the same observational law
          -- inside the forward LvLiNGAM class, which is the formal direction verdict:
          ForwardLvLiNGAM Pforward m) ∧
    -- reverse mirror:
    (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Fin (m + 2) → Ω → ℝ)
        (X Y : Ω → ℝ),
        -- reverse mirror, conditioned on the reverse parameter being real-feasible
        -- (`η ∈ F^left_{m,L}`) and on the declared valid order range:
        η ∈ realFeasibleRegion m L → IsProbabilityMeasure μ →
        Preverse = μ.map (fun ω => (X ω, Y ω)) →
        IndependentSources μ S → (∀ j, ∫ ω, S j ω ∂μ = 0) → SourceNonGaussian μ S →
        FiniteCumulants μ S (2 * m + 2) → ReverseAxisModel X Y S η.1 η.2.1 →
        ReverseNonCollinear η.1 η.2.1 → ReverseNonzeroEdge η.1 →
        -- the model's actual source cumulants ARE its parameter weights `η.2.2`:
        (∀ j, ∀ r, 2 ≤ r → r ≤ L → sourceCumulant μ (S j) r = η.2.2 j r) →
          IndependentSources μ (fun i => S (permMiddle m π i)) ∧
          (∀ j, ∫ ω, S (permMiddle m π j) ω ∂μ = 0) ∧
          SourceNonGaussian μ (fun i => S (permMiddle m π i)) ∧
          FiniteCumulants μ (fun i => S (permMiddle m π i)) (2 * m + 2) ∧
          ReverseAxisModel X Y (fun i => S (permMiddle m π i))
            (admissibleSourceSwap m π η).1 (admissibleSourceSwap m π η).2.1 ∧
          ReverseNonCollinear (admissibleSourceSwap m π η).1 (admissibleSourceSwap m π η).2.1 ∧
          ReverseNonzeroEdge (admissibleSourceSwap m π η).1 ∧
          -- the relabeled model's source cumulants are the SWAPPED weights:
          (∀ j, ∀ r, 2 ≤ r → r ≤ L →
              sourceCumulant μ (S (permMiddle m π j)) r = (admissibleSourceSwap m π η).2.2 j r) ∧
          -- reverse mirror: the same observational law remains represented in the
          -- reverse LvLiNGAM class, hence its structural arrow stays `Y → X`:
          ReverseLvLiNGAM Preverse m) ∧
    -- (4) explicit structural-model direction verdicts.  These clauses state the
    -- paper's `D(M) = X → Y` / `D(M) = Y → X` conclusion on the actual model
    -- carrier, rather than leaving direction implicit in class membership.  The
    -- relabeled model has the same observational law and the swapped feasible
    -- parameter, while its `edge` field records the unchanged causal direction.
    (∀ M : StructuralModel m L,
        M.edge = Direction.forward → M.param = θ →
        ∃ M' : StructuralModel m L,
          M'.law = M.law ∧ M'.edge = Direction.forward ∧
          M'.param = admissibleSourceSwap m π θ) ∧
    (∀ M : StructuralModel m L,
        M.edge = Direction.reverse → M.param = η →
        ∃ M' : StructuralModel m L,
          M'.law = M.law ∧ M'.edge = Direction.reverse ∧
          M'.param = admissibleSourceSwap m π η) ∧
    -- (5) arrow-tagged quotient/orbit distinctness.  The admissible `G_m` swap
    -- relabels the source WEIGHT family, so each relabeled source's cumulants are
    -- exactly the original weights `θ.2.2` (resp. `η.2.2`) at the permuted index —
    -- linking the actual sources' cumulants to `θ.2.2`/`η.2.2`.  The boundary loading
    -- directions (indices `0`, `m+1`) are fixed by the swap.  And for EVERY pair of
    -- admissible swaps on the two arrows (`Arrow.right` for `θ`, `Arrow.left` for `η`)
    -- the forward fixed vertical axis differs from the reverse fixed horizontal axis:
    -- no admissible swap converts a forward axis pattern into a reverse one, so the
    -- two arrow-tagged `G_m`-orbits are never identified:
    ((∀ j : Fin (m + 2),
        (admissibleSourceSwapArrow m Arrow.right π θc).2.2 j
          = fun r => θc.2.2 (permMiddle m π j) r) ∧
     (∀ j : Fin (m + 2),
        (admissibleSourceSwapArrow m Arrow.left π ηc).2.2 j
          = fun r => ηc.2.2 (permMiddle m π j) r) ∧
     (∀ j : Fin (m + 2), j.val = 0 ∨ j.val = m + 1 →
        forwardLoading m (admissibleSourceSwap m π θc).1 (admissibleSourceSwap m π θc).2.1 j
          = forwardLoading m θc.1 θc.2.1 j) ∧
     -- arrow-tag preservation: the `G_m` action on `Arrow × ParamSpace` fixes the tag
     -- `b`, so every image of a right-tagged (resp. left-tagged) parameter stays
     -- right-tagged (resp. left-tagged):
     (∀ π' : Equiv.Perm (Fin m),
        (admissibleSourceSwapTagged m π' (Arrow.right, θc)).1 = Arrow.right ∧
        (admissibleSourceSwapTagged m π' (Arrow.left, ηc)).1 = Arrow.left) ∧
     -- hence the right-tagged and left-tagged `G_m`-orbits are DISJOINT: no admissible
     -- swap converts a forward-tagged parameter into a reverse-tagged one, so
     -- quotienting a same-arrow fiber by `G_m` never identifies opposite arrows:
     Disjoint (arrowTaggedOrbit m Arrow.right θc) (arrowTaggedOrbit m Arrow.left ηc)) ∧
    -- (6) same-arrow map invariance under every relabeling `σ`, on the COMPLEX fibers:
    (∀ σ : Equiv.Perm (Fin m),
        forwardCumulantMap m L (admissibleSourceSwap m σ θc) = forwardCumulantMap m L θc ∧
        reverseCumulantMap m L (admissibleSourceSwap m σ ηc) = reverseCumulantMap m L ηc) := by
  refine ⟨⟨forwardCumulantMap_admissibleSourceSwap m L π θc,
      reverseCumulantMap_admissibleSourceSwap m L π ηc⟩,
    realFeasibleRegion_admissibleSourceSwap m L π θ,
    realFeasibleRegion_admissibleSourceSwap m L π η, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω inst μ S X Y _hθ hprob hP hind hcenter hng hfinite haxis hnc hedge hcum
    have hind' : IndependentSources μ (fun i => S (permMiddle m π i)) :=
      hind.precomp (permMiddleEquiv m π).injective
    have hcenter' : ∀ j, ∫ ω, S (permMiddle m π j) ω ∂μ = 0 :=
      fun j => hcenter (permMiddle m π j)
    have hng' : SourceNonGaussian μ (fun i => S (permMiddle m π i)) :=
      fun j => hng (permMiddle m π j)
    have hfinite' : FiniteCumulants μ (fun i => S (permMiddle m π i)) (2 * m + 2) :=
      fun j => hfinite (permMiddle m π j)
    have haxis' := forwardAxisModel_admissibleSourceSwap m π θ S X Y haxis
    have hnc' : ForwardNonCollinear (admissibleSourceSwap m π θ).1
        (admissibleSourceSwap m π θ).2.1 :=
      finCons_comp_perm_injective θ.1 θ.2.1 π hnc
    have hcum' : ∀ j r, 2 ≤ r → r ≤ L →
        sourceCumulant μ (S (permMiddle m π j)) r =
          (admissibleSourceSwap m π θ).2.2 j r := by
      intro j r hr2 hrL
      exact hcum (permMiddle m π j) r hr2 hrL
    refine ⟨hind', hcenter', hng', hfinite', haxis', hnc', hedge, hcum', ?_⟩
    exact ⟨Ω, inst, μ, (fun i => S (permMiddle m π i)), X, Y,
      (admissibleSourceSwap m π θ).1, (admissibleSourceSwap m π θ).2.1,
      hprob, hind', hfinite', hng', hcenter', haxis', hnc', hedge, hP⟩
  · intro Ω inst μ S X Y _hη hprob hP hind hcenter hng hfinite haxis hnc hedge hcum
    have hind' : IndependentSources μ (fun i => S (permMiddle m π i)) :=
      hind.precomp (permMiddleEquiv m π).injective
    have hcenter' : ∀ j, ∫ ω, S (permMiddle m π j) ω ∂μ = 0 :=
      fun j => hcenter (permMiddle m π j)
    have hng' : SourceNonGaussian μ (fun i => S (permMiddle m π i)) :=
      fun j => hng (permMiddle m π j)
    have hfinite' : FiniteCumulants μ (fun i => S (permMiddle m π i)) (2 * m + 2) :=
      fun j => hfinite (permMiddle m π j)
    have haxis' := reverseAxisModel_admissibleSourceSwap m π η S X Y haxis
    have hnc' : ReverseNonCollinear (admissibleSourceSwap m π η).1
        (admissibleSourceSwap m π η).2.1 :=
      finCons_comp_perm_injective η.1 η.2.1 π hnc
    have hcum' : ∀ j r, 2 ≤ r → r ≤ L →
        sourceCumulant μ (S (permMiddle m π j)) r =
          (admissibleSourceSwap m π η).2.2 j r := by
      intro j r hr2 hrL
      exact hcum (permMiddle m π j) r hr2 hrL
    refine ⟨hind', hcenter', hng', hfinite', haxis', hnc', hedge, hcum', ?_⟩
    exact ⟨Ω, inst, μ, (fun i => S (permMiddle m π i)), X, Y,
      (admissibleSourceSwap m π η).1, (admissibleSourceSwap m π η).2.1,
      hprob, hind', hfinite', hng', hcenter', haxis', hnc', hedge, hP⟩
  · intro M hedge hparam
    subst θ
    obtain ⟨hrep, hmap⟩ := M.realizes.1 hedge
    rcases hrep with
      ⟨Ω, inst, μ, S, X, Y, hprob, hind, hfinite, hng, hcenter, haxis, hnc,
        hnonzero, hcum, hP⟩
    letI : MeasurableSpace Ω := inst
    have hind' : IndependentSources μ (fun i => S (permMiddle m π i)) :=
      hind.precomp (permMiddleEquiv m π).injective
    have hfinite' : FiniteCumulants μ (fun i => S (permMiddle m π i)) (2 * m + 2) :=
      fun j => hfinite (permMiddle m π j)
    have hng' : SourceNonGaussian μ (fun i => S (permMiddle m π i)) :=
      fun j => hng (permMiddle m π j)
    have hcenter' : ∀ j, ∫ ω, S (permMiddle m π j) ω ∂μ = 0 :=
      fun j => hcenter (permMiddle m π j)
    have haxis' := forwardAxisModel_admissibleSourceSwap m π M.param S X Y haxis
    have hnc' : ForwardNonCollinear (admissibleSourceSwap m π M.param).1
        (admissibleSourceSwap m π M.param).2.1 :=
      finCons_comp_perm_injective M.param.1 M.param.2.1 π hnc
    have hcum' : ∀ j r, 2 ≤ r → r ≤ L →
        sourceCumulant μ (S (permMiddle m π j)) r =
          (admissibleSourceSwap m π M.param).2.2 j r := by
      intro j r hr2 hrL
      exact hcum (permMiddle m π j) r hr2 hrL
    refine ⟨{
      law := M.law
      edge := Direction.forward
      param := admissibleSourceSwap m π M.param
      feasible := realFeasibleRegion_admissibleSourceSwap m L π M.param M.feasible
      realizes := ?_
    }, rfl, rfl, rfl⟩
    constructor
    · intro _
      constructor
      · exact ⟨Ω, inst, μ, (fun i => S (permMiddle m π i)), X, Y,
          hprob, hind', hfinite', hng', hcenter', haxis', hnc', hnonzero, hcum', hP⟩
      · exact (forwardCumulantMap_admissibleSourceSwap m L π M.param).trans hmap
    · intro hcontra
      simp at hcontra
  · intro M hedge hparam
    subst η
    obtain ⟨hrep, hmap⟩ := M.realizes.2 hedge
    rcases hrep with
      ⟨Ω, inst, μ, S, X, Y, hprob, hind, hfinite, hng, hcenter, haxis, hnc,
        hnonzero, hcum, hP⟩
    letI : MeasurableSpace Ω := inst
    have hind' : IndependentSources μ (fun i => S (permMiddle m π i)) :=
      hind.precomp (permMiddleEquiv m π).injective
    have hfinite' : FiniteCumulants μ (fun i => S (permMiddle m π i)) (2 * m + 2) :=
      fun j => hfinite (permMiddle m π j)
    have hng' : SourceNonGaussian μ (fun i => S (permMiddle m π i)) :=
      fun j => hng (permMiddle m π j)
    have hcenter' : ∀ j, ∫ ω, S (permMiddle m π j) ω ∂μ = 0 :=
      fun j => hcenter (permMiddle m π j)
    have haxis' := reverseAxisModel_admissibleSourceSwap m π M.param S X Y haxis
    have hnc' : ReverseNonCollinear (admissibleSourceSwap m π M.param).1
        (admissibleSourceSwap m π M.param).2.1 :=
      finCons_comp_perm_injective M.param.1 M.param.2.1 π hnc
    have hcum' : ∀ j r, 2 ≤ r → r ≤ L →
        sourceCumulant μ (S (permMiddle m π j)) r =
          (admissibleSourceSwap m π M.param).2.2 j r := by
      intro j r hr2 hrL
      exact hcum (permMiddle m π j) r hr2 hrL
    refine ⟨{
      law := M.law
      edge := Direction.reverse
      param := admissibleSourceSwap m π M.param
      feasible := realFeasibleRegion_admissibleSourceSwap m L π M.param M.feasible
      realizes := ?_
    }, rfl, rfl, rfl⟩
    constructor
    · intro hcontra
      simp at hcontra
    · intro _
      constructor
      · exact ⟨Ω, inst, μ, (fun i => S (permMiddle m π i)), X, Y,
          hprob, hind', hfinite', hng', hcenter', haxis', hnc', hnonzero, hcum', hP⟩
      · exact (reverseCumulantMap_admissibleSourceSwap m L π M.param).trans hmap
  · refine ⟨?_, ?_, ?_, ?_, arrowTaggedOrbit_right_left_disjoint m θc ηc⟩
    · intro j
      funext r
      rfl
    · intro j
      funext r
      rfl
    · intro j hj
      rw [forwardLoading_admissibleSourceSwap]
      congr 1
      apply Fin.ext
      simp only [permMiddle]
      split_ifs <;> simp_all
    · intro σ
      constructor <;> rfl
  · intro σ
    exact ⟨forwardCumulantMap_admissibleSourceSwap m L σ θc,
      reverseCumulantMap_admissibleSourceSwap m L σ ηc⟩

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
