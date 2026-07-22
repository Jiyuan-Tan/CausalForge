/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 — W-marginal pushforward and hPinned-conditional rectangle identity

`fillZrW`-image bookkeeping plus the W-marginal pushforward identity
(`obsKernel_fixSet_W_marginal_pushforward_eq`) and the rectangle integral
identity (`obsKernel_fixSet_W_rect_integral_eq`), both stated under the
explicit `hPinned` hypothesis that the do-target's random copies coincide
M2-a.s. with the do-values.

This file holds the "hPinned-conditional" rectangle infrastructure.
The hPinned-free rectangle identity is in `Rule2Kernel/RectIdentity.lean`,
which assembles the analytic upgrade via d-sep collapse and the cross-SCM
bridge along the filled assignment.
-/

import Causalean.SCM.Do.Rule2Kernel.InterSingleton

/-! # Marginal Identities for Rule 2

This file proves the filled-assignment measure identities used in the
conditional version of Rule 2. The helper lemmas describe the image of a
measurable `W`-event under `fillZrW`, prove that `fillZrW` is injective and a
measurable embedding, and use that embedding in
`obsKernel_fixSet_W_marginal_pushforward_eq`. The theorem
`obsKernel_fixSet_W_rect_integral_eq` then gives the rectangle integral identity
under the explicit hypothesis that the intervened random treatment copies equal
their assigned fixed intervention values almost surely. These conditional
identities are later upgraded to the full kernel statement of Rule 2. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § fillZrW level-set bookkeeping for W-marginal identities
-- ============================================================

/-- The image of a `W`-event under the filled-assignment map
    `fillZrW Z hZ_obs hZ_fixed W s` is exactly the set of assignments on
    `Z.image .random ∪ W` whose `W`-projection lies in the event and whose
    `Z.image .random` projection equals the fixed intervention value
    `zFixedAsRandom (valuesProjection (fixSet_image_fixed_subset ...) s)`. -/
lemma fillZrW_image_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (A : Set (ValuesOn W (swigΩ Ω))) :
    (M'.fillZrW Z hZ_obs hZ_fixed W s') '' A =
      (fun c : ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) =>
          valuesProjection
            (Finset.subset_union_right (s₁ := Z.image SWIGNode.random)) c)⁻¹' A ∩
      (fun c => valuesProjection
            (Finset.subset_union_left (s₂ := W)) c)⁻¹'
        ({zFixedAsRandom
            (valuesProjection
              (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')} :
          Set (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))) := by
  classical
  let F := M'.fillZrW Z hZ_obs hZ_fixed W s'
  let ζ_s : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) :=
    zFixedAsRandom
      (valuesProjection (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')
  ext c
  constructor
  · rintro ⟨w, hwA, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_preimage]
      have : valuesProjection (Finset.subset_union_right : W ⊆ _) (F w) = w := by
        funext ⟨v, hv⟩
        simp only [valuesProjection, F, fillZrW]
        by_cases hvA : v ∈ Z.image SWIGNode.random
        · exfalso
          exact Finset.disjoint_left.mp hDisj_ZrW hvA hv
        · rw [valuesUnionMk_apply_right _ _ _ hvA hv]
      rw [this]
      exact hwA
    · simp only [Set.mem_preimage, Set.mem_singleton_iff]
      funext ⟨v, hv⟩
      simp only [valuesProjection, fillZrW]
      rw [valuesUnionMk_apply_left _ _ _ hv]
  · rintro ⟨hW_mem, hZr_mem⟩
    simp only [Set.mem_preimage] at hW_mem
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hZr_mem
    refine ⟨valuesProjection (Finset.subset_union_right : W ⊆ _) c, hW_mem, ?_⟩
    funext ⟨v, hv⟩
    simp only [fillZrW]
    rcases Finset.mem_union.mp hv with hZrV | hWV
    · rw [valuesUnionMk_apply_left _ _ _ hZrV]
      have := congrFun hZr_mem ⟨v, hZrV⟩
      simp only [valuesProjection] at this
      exact this.symm
    · by_cases hZrV' : v ∈ Z.image SWIGNode.random
      · rw [valuesUnionMk_apply_left _ _ _ hZrV']
        have := congrFun hZr_mem ⟨v, hZrV'⟩
        simp only [valuesProjection] at this
        exact this.symm
      · rw [valuesUnionMk_apply_right _ _ _ hZrV' hWV]
        simp only [valuesProjection]

/-- `fillZrW Z _ _ W s'` is injective when `Z.image .random` and `W` are
    disjoint. -/
lemma fillZrW_injective
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    Function.Injective (M'.fillZrW Z hZ_obs hZ_fixed W s') := by
  classical
  intro w₁ w₂ h
  funext ⟨v, hv⟩
  -- Project both sides of `h` to the W-coordinate v.
  have h_in : v ∈ Z.image SWIGNode.random ∪ W := Finset.subset_union_right hv
  have hvNotZr : v ∉ Z.image SWIGNode.random := fun hvZr =>
    Finset.disjoint_left.mp hDisj_ZrW hvZr hv
  have hcoord := congrFun h ⟨v, h_in⟩
  simp only [fillZrW] at hcoord
  rw [valuesUnionMk_apply_right _ _ h_in hvNotZr hv,
      valuesUnionMk_apply_right _ _ h_in hvNotZr hv] at hcoord
  exact hcoord

/-- A measurable `W`-event has a measurable image under `fillZrW`.

    Together with `measurable_fillZrW` and `fillZrW_injective`, this is the
    measurable-set image component used to package `fillZrW` as a
    `MeasurableEmbedding`. -/
lemma measurableSet_fillZrW_image
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    {A : Set (ValuesOn W (swigΩ Ω))} (hA : MeasurableSet A) :
    MeasurableSet ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A) := by
  classical
  let ζ_s : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) :=
    zFixedAsRandom
      (valuesProjection (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')
  by_cases hW : Nonempty (ValuesOn W (swigΩ Ω))
  · obtain ⟨w₀⟩ := hW
    -- The Zr-singleton `{ζ_s}` is measurable (pulled back from the
    -- measurable singleton in `ValuesOn (Zr ∪ W)`).
    have hSingZr :
        MeasurableSet ({ζ_s} : Set (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))) := by
      have hmeas : Measurable
          (fun ζ : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) =>
            valuesUnionMk ζ w₀) := by
        refine measurable_pi_iff.mpr ?_
        rintro ⟨v, hv⟩
        by_cases hvZ : v ∈ Z.image SWIGNode.random
        · have h_eq : (fun ζ : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) =>
              valuesUnionMk ζ w₀ ⟨v, hv⟩) = (fun ζ => ζ ⟨v, hvZ⟩) :=
            funext fun _ => valuesUnionMk_apply_left _ _ hv hvZ
          rw [h_eq]
          exact measurable_pi_apply _
        · have hvW : v ∈ W := (Finset.mem_union.mp hv).resolve_left hvZ
          have h_eq : (fun ζ : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) =>
              valuesUnionMk ζ w₀ ⟨v, hv⟩) = (fun _ => w₀ ⟨v, hvW⟩) :=
            funext fun _ => valuesUnionMk_apply_right _ _ hv hvZ
          rw [h_eq]
          exact measurable_const
      have h_pre :
          ({ζ_s} : Set (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))) =
            (fun ζ => valuesUnionMk ζ w₀)⁻¹'
              ({valuesUnionMk ζ_s w₀} :
                Set (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))) := by
        ext ζ
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        refine ⟨fun h => by rw [h], fun h => ?_⟩
        funext ⟨v, hv⟩
        have hv_union : v ∈ Z.image SWIGNode.random ∪ W :=
          Finset.subset_union_left hv
        have h_coord := congrFun h ⟨v, hv_union⟩
        rw [valuesUnionMk_apply_left _ _ hv_union hv,
            valuesUnionMk_apply_left _ _ hv_union hv] at h_coord
        exact h_coord
      rw [h_pre]
      exact hmeas (measurableSet_singleton _)
    rw [fillZrW_image_eq M' Z hZ_obs hZ_fixed W hDisj_ZrW s' A]
    refine MeasurableSet.inter ?_ ?_
    · exact (measurable_valuesProjection _) hA
    · exact (measurable_valuesProjection _) hSingZr
  · -- `ValuesOn W` empty: A = ∅, so F '' A = ∅.
    have hA_empty : A = ∅ := by
      ext w
      exact ⟨fun _ => (hW ⟨w⟩).elim, fun h => h.elim⟩
    rw [hA_empty, Set.image_empty]
    exact MeasurableSet.empty

/-- `fillZrW Z _ _ W s'` is a `MeasurableEmbedding` when `Z.image .random`
    and `W` are disjoint. -/
lemma measurableEmbedding_fillZrW
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    MeasurableEmbedding (M'.fillZrW Z hZ_obs hZ_fixed W s') :=
  { injective := fillZrW_injective M' Z hZ_obs hZ_fixed W hDisj_ZrW s'
    measurable := measurable_fillZrW M' Z hZ_obs hZ_fixed W s'
    measurableSet_image' := fun _ hA =>
      measurableSet_fillZrW_image M' Z hZ_obs hZ_fixed W hDisj_ZrW s' hA }

/-- **W-marginal pushforward identity.**

    When the post-intervention random treatment copies are pinned almost surely
    to their assigned do-values, the do-model marginal law on W equals the
    base-model law on the treatment-random-copy-and-W coordinates evaluated on
    the `fillZrW` image.  Concretely, for any measurable `A ⊆ ValuesOn W`,
    ```
    ((M2.obsKernel s').map π_W) A
      = ((M1.obsKernel sM1).map π_C) (F '' A).
    ```

    **Proof.** RHS measures `M1(π_C⁻¹(F''A))`. The cross-SCM cylinder
    agreement theorem with `S := univ` turns this into `M2(π_C⁻¹(F''A))`.
    Decompose `π_C⁻¹(F''A) = π_W⁻¹ A ∩ π_Zr⁻¹ {ζ_s}` via
    `fillZrW_image_eq`. The intersection with `π_Zr⁻¹ {ζ_s}` is a no-op
    under M2 thanks to the pinning assumption, so the M2-measure coincides
    with `M2(π_W⁻¹A) = LHS`. -/
lemma obsKernel_fixSet_W_marginal_pushforward_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N)) (hW : W ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (hPinned : ∀ᵐ ω ∂((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s'),
      ∀ D (hD : D ∈ Z),
        ω ⟨SWIGNode.random D, hZ_obs D hD⟩
          = s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M' Z hZ_obs hZ_fixed hD⟩)
    {A : Set (ValuesOn W (swigΩ Ω))} (hA : MeasurableSet A) :
    ((MeasureTheory.Measure.map
        (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
        ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s'))) A
      = ((MeasureTheory.Measure.map
          (valuesProjection hZrW)
          (M'.obsKernel
            (M'.fixSetProj Z hZ_obs hZ_fixed s'))))
          ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A) := by
  classical
  -- Abbreviations.
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let sM1 : M'.FixedValues := M'.fixSetProj Z hZ_obs hZ_fixed s'
  let F := M'.fillZrW Z hZ_obs hZ_fixed W s'
  have hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW
  have hW_M2 : W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW
  have hπW_M2 : Measurable
      (valuesProjection hW_M2 : M2.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπC_M1 : Measurable
      (valuesProjection hZrW : M'.ObservedValues → _) :=
    measurable_valuesProjection _
  have hImg_meas : MeasurableSet (F '' A) :=
    measurableSet_fillZrW_image M' Z hZ_obs hZ_fixed W hDisj_ZrW s' hA
  -- Rewrite the maps as obsKernel applied to preimages.
  rw [MeasureTheory.Measure.map_apply hπW_M2 hA,
      MeasureTheory.Measure.map_apply hπC_M1 hImg_meas]
  -- Now: M2.obsKernel s' (π_W⁻¹ A) = M1.obsKernel sM1 (π_C⁻¹ (F''A)).
  -- Step 1: by (★), M2(π_W⁻¹A) = M2(π_W⁻¹A ∩ π_Zr⁻¹ {ζ_s}).
  -- We instead show that π_W⁻¹A = π_C⁻¹(F''A) ∪ N for a null set N under M2,
  -- and π_C⁻¹(F''A) ⊆ π_W⁻¹A.  Then the measures are equal.
  -- Concrete plan: show that on the event {ω : π_Zr ω = ζ_s} (M2-a.e.),
  --   π_W ω ∈ A  ↔  π_C ω ∈ F''A,
  -- so the two preimages agree M2-a.e.
  set ζ_s : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) :=
    zFixedAsRandom
      (valuesProjection (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')
    with hζ_def
  have hZr_subset : Z.image SWIGNode.random ⊆ M2.observed := by
    intro v hv
    exact hZrW_M2 (Finset.subset_union_left hv)
  have hImgExpand : F '' A =
      (fun c : ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) =>
          valuesProjection
            (Finset.subset_union_right (s₁ := Z.image SWIGNode.random)) c)⁻¹' A ∩
      (fun c => valuesProjection
            (Finset.subset_union_left (s₂ := W)) c)⁻¹' ({ζ_s} :
              Set (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))) :=
    fillZrW_image_eq M' Z hZ_obs hZ_fixed W hDisj_ZrW s' A
  -- Step A: apply Helper 1 with S := π_W⁻¹A to get
  --   M2(π_W⁻¹A ∩ π_C⁻¹(F''A)) = M1(π_W⁻¹A ∩ π_C⁻¹(F''A))
  -- (where π_W⁻¹A on the M2 side uses hW_M2; same on M1 side with hW).
  -- But we want bare π_C⁻¹(F''A), so use S = univ.
  have hHelper1 :
      M2.obsKernel s'
          (Set.univ ∩ (valuesProjection hZrW_M2)⁻¹' (F '' A))
        = M'.obsKernel sM1
            (Set.univ ∩ (valuesProjection hZrW)⁻¹' (F '' A)) :=
    obsKernel_inter_Wset_Zrand_levelset_eq M' Z hZ_obs hZ_fixed W
      hZrW hDisj_ZrW s' MeasurableSet.univ hA
  rw [Set.univ_inter, Set.univ_inter] at hHelper1
  -- Now rewrite RHS = M1(π_C⁻¹(F''A)) using hHelper1 (reversed).
  rw [← hHelper1]
  -- Goal: M2.obsKernel s' (π_W⁻¹ A) = M2.obsKernel s' (π_C⁻¹ (F '' A))
  -- where π_W uses hW_M2 and π_C uses hZrW_M2.
  -- Use the (★) hypothesis to show these sets agree M2-a.e.
  refine MeasureTheory.measure_congr ?_
  refine Filter.Eventually.mono hPinned ?_
  intro ω hω
  -- hω : ∀ D ∈ Z, ω ⟨.random D, hZ_obs D _⟩ = s' ⟨.fixed D, _⟩
  -- Show: π_W⁻¹A ω ↔ π_C⁻¹(F''A) ω
  apply propext
  constructor
  · intro hπW_mem
    -- We have π_W ω ∈ A.  Show π_C ω ∈ F''A by exhibiting `w = π_W ω`.
    change ω ∈ valuesProjection hZrW_M2 ⁻¹' (F '' A)
    refine ⟨valuesProjection hW_M2 ω, hπW_mem, ?_⟩
    funext ⟨v, hv⟩
    simp only [F, fillZrW]
    rcases Finset.mem_union.mp hv with hZrV | hWV
    · rw [valuesUnionMk_apply_left _ _ _ hZrV]
      obtain ⟨D, hDZ, hDeq⟩ := Finset.mem_image.mp hZrV
      cases hDeq
      simp only [zFixedAsRandom, valuesProjection]
      -- Goal: s' ⟨.fixed D, _⟩ = ω ⟨.random D, _⟩  (from valuesUnionMk_apply_left)
      exact (hω D hDZ).symm
    · by_cases hZrV' : v ∈ Z.image SWIGNode.random
      · rw [valuesUnionMk_apply_left _ _ _ hZrV']
        obtain ⟨D, hDZ, hDeq⟩ := Finset.mem_image.mp hZrV'
        cases hDeq
        simp only [zFixedAsRandom, valuesProjection]
        exact (hω D hDZ).symm
      · rw [valuesUnionMk_apply_right _ _ _ hZrV' hWV]
        simp only [valuesProjection]
  · intro hMem
    -- π_C ω = F w₀ for some w₀ ∈ A.  Show π_W ω ∈ A.
    obtain ⟨w₀, hw₀A, hF_eq⟩ := hMem
    -- The W-coordinate of F w₀ equals w₀ (since W is disjoint from Z.image .random).
    suffices h : valuesProjection hW_M2 ω = w₀ by
      change ω ∈ valuesProjection hW_M2 ⁻¹' A
      rw [Set.mem_preimage, h]; exact hw₀A
    funext ⟨v, hvW⟩
    have hv_in : v ∈ Z.image SWIGNode.random ∪ W :=
      Finset.subset_union_right hvW
    have hvNotZr : v ∉ Z.image SWIGNode.random := fun hvZr =>
      Finset.disjoint_left.mp hDisj_ZrW hvZr hvW
    have hcoord := congrFun hF_eq ⟨v, hv_in⟩
    simp only [valuesProjection, F, fillZrW] at hcoord ⊢
    rw [valuesUnionMk_apply_right _ _ hv_in hvNotZr hvW] at hcoord
    exact hcoord.symm

/-- Cross-SCM rectangle bridge for the W-marginal.

    Under d-separation, joint overlap, and the additional assumption that the
    post-intervention random treatment copies are pinned almost surely to their
    assigned do-values, integrating the base-model conditional kernel along
    `fillZrW W s` against the do-model W-marginal reconstructs the do-model
    rectangle measure:
    ```
    ∫⁻ w in A, M1.obsCondKernel Y (Zr∪W) (sM1, fillZrW W s w) B
                 d((M2.obsKernel s).map π_W)
      = M2.obsKernel s (π_W⁻¹ A ∩ π_Y⁻¹ B).
    ```

    **Hypotheses.**

    This legacy hPinned-conditional rectangle identity assumes d-separation
    (to make the observation conditional well-defined), joint absolute
    continuity of the cross-SCM `Z.rand ∪ W`-marginals (so that the level-set
    evaluation of the M1 conditional kernel is pinned down up to a null set
    under M2's W-marginal), and almost-sure pinning of the do-target's random
    copies:
    * `hdSep` — `Y` is d-separated from the natural `Z.rand` given
      `W ∪ M2.fixed` in the post-intervention SWIG DAG.  Equivalent (by
      `globalMarkov_with_fixed`) to `Y ⊥⊥ Z.rand | W` under
      `M2.obsKernel s`.
    * `hOverlap` (= `Rule2JointOverlap`) —
      `(M2.obsKernel s).map π_C ≪ (M1.obsKernel sM1).map π_C`.
    * `hPinned` — under `M2.obsKernel s`, every random treatment copy in `Z`
      equals the corresponding fixed do-value almost surely.

    **Proof outline.** Reduce to the conditional-kernel a.e. equality
    `M2.obsCondKernel(Y|W)(s, w) =a.e. M1.obsCondKernel(Y|C)(sM1, F w)`
    (under `(M2.obsKernel s).map π_W`) via the following chain:
    1. **M2 disintegration** along `π_W`: the RHS already equals
       `∫_A M2.obsCondKernel(Y|W)(s, w) B d(M_W^M2)`.
    2. **M2 d-sep collapse** (uses `hdSep`):
       `M2.obsCondKernel(Y|C)(s, c) =a.e. M2.obsCondKernel(Y|W)(s, π_W^C c)`
       under `(M2.obsKernel s).map π_C`.
    3. **Generalized cross-SCM bridge**
       (`obsKernel_inter_Wset_Zrand_levelset_eq`) integrated:
       `M2.obsKernel s (π_Y⁻¹B ∩ π_C⁻¹(F''A))
         = M1.obsKernel sM1 (π_Y⁻¹B ∩ π_C⁻¹(F''A))`.
    4. **M1 disintegration** (`obsKernel_disintegrate_rect`) on the RHS of (3).
    5. **Rule2JointOverlap** to lift the (3)–(4) integral identity to an
       a.e. cross-SCM conditional kernel equality on the `F''W`-image
       under `M_C^M1` (or equivalently `M_C^M2`).
    6. **Change of variables** along `F = fillZrW(s, ·)` (measurable
       injection) to bring the integral back to `M_W^M2`. -/
theorem obsKernel_fixSet_W_rect_integral_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed) (hW : W ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (hdSep : (M'.fixSet Z hZ_obs hZ_fixed).dag.dSep
              Y (Z.image SWIGNode.random)
              (W ∪ (M'.fixSet Z hZ_obs hZ_fixed).fixed))
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.obsKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure
        ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (hOverlap : Causalean.SCM.ID.Rule2JointOverlap
                  M' Z hZ_obs hZ_fixed W hZrW s)
    (hPinned : ∀ᵐ ω ∂((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s),
      ∀ D (hD : D ∈ Z),
        ω ⟨SWIGNode.random D, hZ_obs D hD⟩
          = s ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M' Z hZ_obs hZ_fixed hD⟩)
    {A : Set (ValuesOn W (swigΩ Ω))}
    {B : Set (ValuesOn Y (swigΩ Ω))}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ w in A,
        (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
          (M'.fixSetProj Z hZ_obs hZ_fixed s,
           M'.fillZrW Z hZ_obs hZ_fixed W s w)) B
        ∂(MeasureTheory.Measure.map
            (valuesProjection
              ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
            ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s))
      = ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)
          ((valuesProjection
              ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))⁻¹' A
           ∩ (valuesProjection
              ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY))⁻¹' B) := by
  -- ============================================================
  -- Proof strategy (using the (★) hypothesis `hPinned`):
  --
  -- Let M1 = M', M2 = M'.fixSet Z hZ_obs hZ_fixed,
  -- sM1 = M'.fixSetProj Z hZ_obs hZ_fixed s,
  -- F = fillZrW Z hZ_obs hZ_fixed W s.
  -- Let ν_W := (M2.obsKernel s).map π_W, μ_C := (M1.obsKernel sM1).map π_C.
  -- Let ĥ(c) := M1.obsCondKernel Y (Z.image .random ∪ W) (sM1, c) B.
  --
  -- LHS = ∫⁻ w in A, ĥ(F w) d ν_W
  --     = ∫⁻ c in F''A, ĥ(c) d (ν_W.map F)            [change of vars, F MeasEmb]
  --     = ∫⁻ c in F''A, ĥ(c) d (μ_C.restrict (range F))[ν_W = μ_C.comap F via helper]
  --     = ∫⁻ c in F''A, ĥ(c) d μ_C                    [F''A ⊆ range F]
  --     = M1.obsKernel sM1 (π_C⁻¹(F''A) ∩ π_Y⁻¹ B)    [Helper 2 / M1 disintegration]
  --     = M2.obsKernel s (π_C⁻¹(F''A) ∩ π_Y⁻¹ B)      [Helper 1, S := π_Y⁻¹B]
  --     = M2.obsKernel s (π_W⁻¹A ∩ π_Y⁻¹ B)           [by (★) and hImg]
  --     = RHS.
  -- ============================================================
  classical
  let M1 := M'
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let sM1 : M1.FixedValues := M'.fixSetProj Z hZ_obs hZ_fixed s
  let F := M'.fillZrW Z hZ_obs hZ_fixed W s
  have hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW
  have hW_M2 : W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW
  have hY_M2 : Y ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY
  -- F is a MeasurableEmbedding.
  have hME : MeasurableEmbedding F :=
    measurableEmbedding_fillZrW M' Z hZ_obs hZ_fixed W hDisj_ZrW s
  have hF_meas : Measurable F :=
    M'.measurable_fillZrW Z hZ_obs hZ_fixed W s
  have hπW_M2 : Measurable
      (valuesProjection hW_M2 : M2.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπC_M1 : Measurable
      (valuesProjection hZrW : M1.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπC_M2 : Measurable
      (valuesProjection hZrW_M2 : M2.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπY_M2 : Measurable
      (valuesProjection hY_M2 : M2.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπY_M1 : Measurable
      (valuesProjection hY : M1.ObservedValues → _) :=
    measurable_valuesProjection _
  -- Abbreviations for measures and integrand.
  set ν_W : MeasureTheory.Measure (ValuesOn W (swigΩ Ω)) :=
    (M2.obsKernel s).map (valuesProjection hW_M2) with hν_W_def
  set μ_C : MeasureTheory.Measure
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω)) :=
    (M1.obsKernel sM1).map (valuesProjection hZrW) with hμ_C_def
  let ĥ : ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) → ENNReal :=
    fun c => (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
              (sM1, c)) B
  -- Image of A is measurable in `ValuesOn (Z.image .random ∪ W)`.
  have hImg_meas : MeasurableSet (F '' A) := hME.measurableSet_image' hA
  -- The pushforward identity from the helper.
  have hPushApply : ∀ ⦃S : Set (ValuesOn W (swigΩ Ω))⦄, MeasurableSet S →
      ν_W S = μ_C (F '' S) := by
    intro S hS
    simp only [hν_W_def, hμ_C_def]
    exact obsKernel_fixSet_W_marginal_pushforward_eq M' Z hZ_obs hZ_fixed W hW
      hZrW hDisj_ZrW s hPinned hS
  -- ν_W = μ_C.comap F as measures on `ValuesOn W`.
  have hcomap_eq : ν_W = μ_C.comap F := by
    refine MeasureTheory.Measure.ext ?_
    intro S hS
    rw [hME.comap_apply, hPushApply hS]
  -- ν_W.map F = μ_C.restrict (range F).
  have hmap_F : ν_W.map F = μ_C.restrict (Set.range F) := by
    rw [hcomap_eq, hME.map_comap]
  -- ----------------------------------------------------------------
  -- Step 1: rewrite LHS using `MeasurableEmbedding.lintegral_map`.
  -- LHS = ∫⁻ c in F''A, ĥ(c) d (ν_W.map F).
  -- ----------------------------------------------------------------
  -- The current LHS displays the measure as
  -- `Measure.map (valuesProjection ((fixSet_observed ...).symm ▸ hW)) (M2.obsKernel s)`
  -- which is definitionally equal to `ν_W`.  Likewise the integrand is `ĥ ∘ F`.
  have hLHS_step1 :
      ∫⁻ w in A,
          (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
            (sM1, F w)) B ∂ν_W
        = ∫⁻ c in F '' A, ĥ c ∂(ν_W.map F) := by
    -- ∫⁻ c in F''A, ĥ c d (ν_W.map F)
    --   = ∫⁻ c, indicator(F''A) c · ĥ c d (ν_W.map F)
    --   = ∫⁻ w, indicator(F''A) (F w) · ĥ (F w) d ν_W   [lintegral_map]
    --   = ∫⁻ w, indicator(A) w · ĥ (F w) d ν_W           [F injective]
    --   = ∫⁻ w in A, ĥ (F w) d ν_W
    rw [← MeasureTheory.lintegral_indicator hImg_meas,
        hME.lintegral_map (fun c => (F '' A).indicator ĥ c),
        ← MeasureTheory.lintegral_indicator hA]
    refine MeasureTheory.lintegral_congr ?_
    intro w
    by_cases hw : w ∈ A
    · have hFw : F w ∈ F '' A := ⟨w, hw, rfl⟩
      simp [Set.indicator_of_mem hw, Set.indicator_of_mem hFw, ĥ]
    · have hFw : F w ∉ F '' A := by
        rintro ⟨w', hw', heq⟩
        exact hw (hME.injective heq ▸ hw')
      simp [Set.indicator_of_notMem hw, Set.indicator_of_notMem hFw]
  -- ----------------------------------------------------------------
  -- Step 2: ∫⁻ c in F''A, ĥ d (ν_W.map F) = ∫⁻ c in F''A, ĥ d μ_C
  -- using ν_W.map F = μ_C.restrict (range F) and F''A ⊆ range F.
  -- ----------------------------------------------------------------
  have hRangeF : F '' A ⊆ Set.range F :=
    Set.image_subset_range _ _
  have hLHS_step2 :
      ∫⁻ c in F '' A, ĥ c ∂(ν_W.map F)
        = ∫⁻ c in F '' A, ĥ c ∂μ_C := by
    rw [hmap_F]
    -- (μ_C.restrict (range F)).restrict (F''A) = μ_C.restrict ((F''A) ∩ range F)
    -- = μ_C.restrict (F''A)  since F''A ⊆ range F.
    rw [MeasureTheory.Measure.restrict_restrict_of_subset hRangeF]
  -- ----------------------------------------------------------------
  -- Step 3: ∫⁻ c in F''A, ĥ d μ_C = M1.obsKernel sM1 (π_C⁻¹ (F''A) ∩ π_Y⁻¹ B)
  -- via Helper 2 (M1 disintegration along π_C, CC := Z.image .random ∪ W).
  -- ----------------------------------------------------------------
  have hLHS_step3 :
      ∫⁻ c in F '' A, ĥ c ∂μ_C
        = M1.obsKernel sM1
            ((valuesProjection hZrW)⁻¹' (F '' A)
              ∩ (valuesProjection hY)⁻¹' B) := by
    rw [hμ_C_def]
    exact (obsKernel_disintegrate_rect M1 Y (Z.image SWIGNode.random ∪ W)
            hY hZrW sM1 hImg_meas hB).symm
  -- ----------------------------------------------------------------
  -- Step 4: swap M1 to M2 using Helper 1 (S := π_Y⁻¹ B).
  -- ----------------------------------------------------------------
  have hHelper1 :
      M2.obsKernel s
          ((valuesProjection hY_M2)⁻¹' B
            ∩ (valuesProjection hZrW_M2)⁻¹' (F '' A))
        = M1.obsKernel sM1
            ((valuesProjection hY)⁻¹' B
              ∩ (valuesProjection hZrW)⁻¹' (F '' A)) :=
    obsKernel_inter_Wset_Zrand_levelset_eq M' Z hZ_obs hZ_fixed W
      hZrW hDisj_ZrW s (hπY_M1 hB) hA
  -- Both intersections appear in either order: align via Set.inter_comm.
  have hLHS_step4 :
      M1.obsKernel sM1
          ((valuesProjection hZrW)⁻¹' (F '' A)
            ∩ (valuesProjection hY)⁻¹' B)
        = M2.obsKernel s
            ((valuesProjection hZrW_M2)⁻¹' (F '' A)
              ∩ (valuesProjection hY_M2)⁻¹' B) := by
    rw [Set.inter_comm ((valuesProjection hZrW)⁻¹' (F '' A))
                       ((valuesProjection hY)⁻¹' B),
        Set.inter_comm ((valuesProjection hZrW_M2)⁻¹' (F '' A))
                       ((valuesProjection hY_M2)⁻¹' B)]
    exact hHelper1.symm
  -- ----------------------------------------------------------------
  -- Step 5: M2(π_C⁻¹(F''A) ∩ π_Y⁻¹B) = M2(π_W⁻¹A ∩ π_Y⁻¹B) by (★).
  -- ----------------------------------------------------------------
  have hLHS_step5 :
      M2.obsKernel s
          ((valuesProjection hZrW_M2)⁻¹' (F '' A)
            ∩ (valuesProjection hY_M2)⁻¹' B)
        = M2.obsKernel s
            ((valuesProjection hW_M2)⁻¹' A
              ∩ (valuesProjection hY_M2)⁻¹' B) := by
    refine MeasureTheory.measure_congr ?_
    refine Filter.Eventually.mono hPinned ?_
    intro ω hω
    -- Show: ω ∈ π_C⁻¹(F''A) ∩ π_Y⁻¹B ↔ ω ∈ π_W⁻¹A ∩ π_Y⁻¹B
    apply propext
    constructor
    · rintro ⟨hπCmem, hπYmem⟩
      refine ⟨?_, hπYmem⟩
      -- ω ∈ π_C⁻¹(F''A) gives w₀ ∈ A with F w₀ = π_C ω.
      -- W-coord of F w₀ is w₀; project to extract.
      obtain ⟨w₀, hw₀A, hF_eq⟩ := hπCmem
      change ω ∈ valuesProjection hW_M2 ⁻¹' A
      suffices h : valuesProjection hW_M2 ω = w₀ by
        rw [Set.mem_preimage, h]; exact hw₀A
      funext ⟨v, hvW⟩
      have hv_in : v ∈ Z.image SWIGNode.random ∪ W :=
        Finset.subset_union_right hvW
      have hvNotZr : v ∉ Z.image SWIGNode.random := fun hvZr =>
        Finset.disjoint_left.mp hDisj_ZrW hvZr hvW
      have hcoord := congrFun hF_eq ⟨v, hv_in⟩
      simp only [valuesProjection, F, fillZrW] at hcoord ⊢
      rw [valuesUnionMk_apply_right _ _ hv_in hvNotZr hvW] at hcoord
      exact hcoord.symm
    · rintro ⟨hπWmem, hπYmem⟩
      refine ⟨?_, hπYmem⟩
      -- ω ∈ π_W⁻¹A.  Use (★) to construct w₀ = π_W ω showing π_C ω = F w₀.
      change ω ∈ valuesProjection hZrW_M2 ⁻¹' (F '' A)
      refine ⟨valuesProjection hW_M2 ω, hπWmem, ?_⟩
      funext ⟨v, hv⟩
      simp only [F, fillZrW]
      rcases Finset.mem_union.mp hv with hZrV | hWV
      · rw [valuesUnionMk_apply_left _ _ _ hZrV]
        obtain ⟨D, hDZ, hDeq⟩ := Finset.mem_image.mp hZrV
        cases hDeq
        simp only [zFixedAsRandom, valuesProjection]
        exact (hω D hDZ).symm
      · by_cases hZrV' : v ∈ Z.image SWIGNode.random
        · rw [valuesUnionMk_apply_left _ _ _ hZrV']
          obtain ⟨D, hDZ, hDeq⟩ := Finset.mem_image.mp hZrV'
          cases hDeq
          simp only [zFixedAsRandom, valuesProjection]
          exact (hω D hDZ).symm
        · rw [valuesUnionMk_apply_right _ _ _ hZrV' hWV]
          simp only [valuesProjection]
  -- ----------------------------------------------------------------
  -- Assemble the chain.
  -- ----------------------------------------------------------------
  change ∫⁻ w in A,
        (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
          (sM1, F w)) B ∂ν_W
      = M2.obsKernel s
          ((valuesProjection hW_M2)⁻¹' A
            ∩ (valuesProjection hY_M2)⁻¹' B)
  rw [hLHS_step1, hLHS_step2, hLHS_step3, hLHS_step4, hLHS_step5]

end SCM

end Causalean
