/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.EvalOverrideC

/-! # The latent cutset `C_W` for the continuous-backdoor witness kernel

This file isolates the block of latent roots that drive a target set `Y`
without being mediated by an overridden block `C`.  A latent node belongs to
the cutset when it reaches some node of `Y` along a directed path whose interior
nodes all avoid `C`.  The keystone result is a structural factorization: the
override evaluation `evalMap_overrideC` with override block `C` depends on the
latent assignment only through its values on the cutset, so two latent vectors
that agree on the cutset produce the same override evaluation on `Y`.

## Main definitions

* `DAG.isAncestorAvoiding` — there is a directed path from `u` to `v` whose
  strictly interior nodes all avoid a forbidden set `C`.
* `SCM.cutsetLatent` — the latent roots reaching `Y` along a `C`-avoiding path
  (the block `C_W`).

## Main results

* `SCM.evalMap_overrideC_agree_cutset` — the structural cutset factorization:
  agreement of two latent vectors on the cutset forces the override evaluations
  on `Y` to coincide.
* `SCM.exists_evalMap_overrideC_factors_cutset` — packages the agreement lemma
  as a measurable factorization through the cutset projection.
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace DAG

variable (G : DAG V)

/-- Avoiding ancestry means there is a directed path whose strictly interior nodes avoid a forbidden set.

    `isAncestorAvoiding G C u v` holds when there is a directed path from `u`
    to `v` whose strictly interior nodes all avoid the forbidden set `C`.
    The two endpoints `u` and `v` are unconstrained; only the nodes strictly
    between them must avoid `C`.  Built by extending at the target end. -/
inductive isAncestorAvoiding (C : Finset V) : V → V → Prop
  | edge {u v : V} : G.edge u v → isAncestorAvoiding C u v
  | trans {u w v : V} :
      isAncestorAvoiding C u w → w ∉ C → G.edge w v → isAncestorAvoiding C u v

/-- Every avoiding ancestry relation is also ordinary directed ancestry.

    An avoiding path is in particular a directed path: it forgets the
    interior-avoidance and yields an ordinary ancestor. -/
theorem isAncestorAvoiding.toIsAncestor {C : Finset V} {u v : V}
    (h : G.isAncestorAvoiding C u v) : G.isAncestor u v := by
  induction h with
  | edge he => exact isAncestor.edge he
  | trans _ _ he ih => exact isAncestor.trans ih he

/-- An avoiding path can be extended backward by one edge when the new interior node avoids the forbidden set.

    Prepend an edge at the source end: if `u → w` is an edge, `w ∉ C`, and there
    is a `C`-avoiding path from `w` to `v`, then there is a `C`-avoiding path
    from `u` to `v`.  The new interior node is `w`, which avoids `C`. -/
theorem isAncestorAvoiding.cons {C : Finset V} {u w v : V}
    (he : G.edge u w) (hw : w ∉ C) (h : G.isAncestorAvoiding C w v) :
    G.isAncestorAvoiding C u v := by
  induction h with
  | edge he' => exact (isAncestorAvoiding.edge he).trans hw he'
  | trans _ hmid he' ih => exact ih.trans hmid he'

/-- Avoiding ancestry can be materialized as a concrete directed path with all strictly interior nodes avoiding the forbidden set.

    **Path extraction from a `C`-avoiding ancestry.**

    A `C`-avoiding path from `u` to `v` materialises as a concrete forward-directed
    path list `q` whose strictly interior nodes all avoid `C`.  Each interior node
    additionally has an incoming edge inside `q` (it is never the head), so it is
    never a graph root — a fact used downstream to exclude fixed nodes. -/
theorem isAncestorAvoiding.exists_path {C : Finset V} {u v : V}
    (h : G.isAncestorAvoiding C u v) :
    ∃ q : List V, q.length ≥ 2 ∧ q.head? = some u ∧ q.getLast? = some v ∧
      (∀ (i : ℕ) (hi : i + 1 < q.length),
        G.edge (q.get ⟨i, by omega⟩) (q.get ⟨i + 1, hi⟩)) ∧
      (∀ (i : ℕ) (hi : i + 2 < q.length), q.get ⟨i + 1, by omega⟩ ∉ C) := by
  induction h with
  | edge he =>
    rename_i u v
    refine ⟨[u, v], by simp, rfl, rfl, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by simp at hi; omega
      subst this; exact he
    · intro i hi; simp at hi
  | trans hav hwC he ih =>
    rename_i u w v
    obtain ⟨q, hlen, hhead, hlast, hedge, hint⟩ := ih
    have hqne : q ≠ [] := by intro hq; rw [hq] at hlen; simp at hlen
    have hlen_q : (q ++ [v]).length = q.length + 1 := by
      rw [List.length_append, List.length_singleton]
    refine ⟨q ++ [v], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlen_q]; omega
    · rw [List.head?_append_of_ne_nil _ hqne]; exact hhead
    · rw [List.getLast?_append]; simp
    · -- Directed edges: the new last edge `w → v` joins at the old last node `w`.
      intro i hi
      rw [hlen_q] at hi
      by_cases hlast_i : i + 1 = q.length
      · -- Seam edge: q[i] = q.getLast = w, and q ++ [v] at i+1 = v.
        have hi_lt : i < q.length := by omega
        have hwq : q.get ⟨i, hi_lt⟩ = w := by
          have hgl := List.getLast?_eq_some_getLast hqne
          rw [hlast] at hgl
          have hw_eq : q.getLast hqne = w := Option.some_inj.mp hgl.symm
          have hidx : (⟨i, hi_lt⟩ : Fin q.length) = ⟨q.length - 1, by omega⟩ := by
            simp only [Fin.mk.injEq]; omega
          rw [hidx, List.get_eq_getElem, ← hw_eq, List.getLast_eq_getElem]
        have hgi : (q ++ [v]).get ⟨i, by omega⟩ = q.get ⟨i, hi_lt⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left (h := hi_lt)]
        have hgi1 : (q ++ [v]).get ⟨i + 1, by omega⟩ = v := by
          rw [List.get_eq_getElem, List.getElem_append_right (by simp; omega)]
          simp [hlast_i]
        rw [hgi, hgi1, hwq]; exact he
      · -- Edge fully inside `q`.
        have hi_lt : i + 1 < q.length := by omega
        have hi_lt0 : i < q.length := by omega
        have hgi : (q ++ [v]).get ⟨i, by omega⟩ = q.get ⟨i, hi_lt0⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left (h := hi_lt0)]
        have hgi1 : (q ++ [v]).get ⟨i + 1, by omega⟩ = q.get ⟨i + 1, hi_lt⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left (h := hi_lt)]
        rw [hgi, hgi1]; exact hedge i hi_lt
    · -- Interior avoidance: interior nodes of `q ++ [v]` are either interior of `q`,
      -- or the seam node `w` (the old last of `q`), which avoids `C` by `hwC`.
      intro i hi
      rw [hlen_q] at hi
      by_cases hlast_i : i + 1 = q.length - 1
      · -- The seam node q[i+1] = q.getLast = w.
        have hi1_lt : i + 1 < q.length := by omega
        have hwq : q.get ⟨i + 1, hi1_lt⟩ = w := by
          have hgl := List.getLast?_eq_some_getLast hqne
          rw [hlast] at hgl
          have hw_eq : q.getLast hqne = w := Option.some_inj.mp hgl.symm
          have hidx : (⟨i + 1, hi1_lt⟩ : Fin q.length) = ⟨q.length - 1, by omega⟩ := by
            simp only [Fin.mk.injEq]; omega
          rw [hidx, List.get_eq_getElem, ← hw_eq, List.getLast_eq_getElem]
        have hgi1 : (q ++ [v]).get ⟨i + 1, by omega⟩ = q.get ⟨i + 1, hi1_lt⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left (h := hi1_lt)]
        rw [hgi1, hwq]; exact hwC
      · -- Interior node of `q`: i + 2 < q.length.
        have hi2_lt : i + 2 < q.length := by omega
        have hi1_lt : i + 1 < q.length := by omega
        have hgi1 : (q ++ [v]).get ⟨i + 1, by omega⟩ = q.get ⟨i + 1, hi1_lt⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left (h := hi1_lt)]
        rw [hgi1]; exact hint i hi2_lt

end DAG

namespace SCM

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

/-- The latent cutset contains the unobserved roots that can drive a target set along paths avoiding an override block.

    **The latent cutset `C_W`.**

    The latent roots that reach some node of `Y` along a directed path whose
    interior avoids the override block `C`.  A latent node `u` belongs to the
    cutset when either `u ∈ Y` (degenerate, but kept for uniformity) or there is
    a `C`-avoiding directed path from `u` to a node `y ∈ Y`. -/
noncomputable def cutsetLatent (M : Causalean.SCM N Ω)
    (Y C : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  letI : DecidablePred
      (fun u : SWIGNode N =>
        ∃ y ∈ Y, u = y ∨ M.dag.isAncestorAvoiding C u y) :=
    Classical.decPred _
  M.unobserved.filter (fun u => ∃ y ∈ Y, u = y ∨ M.dag.isAncestorAvoiding C u y)

/-- Membership in the latent cutset means being unobserved and reaching the target set along an avoiding path. -/
theorem mem_cutsetLatent (M : Causalean.SCM N Ω)
    {Y C : Finset (SWIGNode N)} {u : SWIGNode N} :
    u ∈ M.cutsetLatent Y C ↔
      u ∈ M.unobserved ∧
        ∃ y ∈ Y, u = y ∨ M.dag.isAncestorAvoiding C u y := by
  letI : DecidablePred
      (fun u : SWIGNode N =>
        ∃ y ∈ Y, u = y ∨ M.dag.isAncestorAvoiding C u y) :=
    Classical.decPred _
  change u ∈ M.unobserved.filter _ ↔ _
  exact Finset.mem_filter

/-- The latent cutset is contained in the model's unobserved node set. -/
theorem cutsetLatent_subset (M : Causalean.SCM N Ω)
    (Y C : Finset (SWIGNode N)) :
    M.cutsetLatent Y C ⊆ M.unobserved := by
  intro u hu
  exact (M.mem_cutsetLatent.mp hu).1

-- ============================================================
-- § 2. Structural cutset factorization for `evalMap_overrideC`
-- ============================================================

/-- **Cutset agreement at the topological-index level.**

    Two latent assignments `ℓ₁`, `ℓ₂` that agree on every latent node reaching a
    target set `T` along a `C`-avoiding directed path produce the same override
    evaluation at every topological index whose observed node reaches `T` along a
    `C`-avoiding path (or lies in `T`).

    Proof by strong recursion on the topological index, mirroring
    `evalObservedAuxOverride_agree_anc`.  At each node the override either reads
    from `c` (when the node is in `C`, no latent dependence) or applies the
    structural function to parent values; each latent parent is in the cutset by
    extending the avoiding path through the non-`C` current node, and each
    observed non-`C` parent recurses with the avoiding witness extended. -/
private lemma evalObservedAuxOverride_agree_cutset (M : Causalean.SCM N Ω)
    (T : Finset (SWIGNode N))
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M)
    (c : ValuesOn C (swigΩ Ω))
    (ℓ₁ ℓ₂ : LatentValues M)
    (hAgree : ∀ (u : SWIGNode N) (hu : u ∈ M.unobserved),
      (∃ t ∈ T, u = t ∨ M.dag.isAncestorAvoiding C u t) →
        ℓ₁ ⟨u, hu⟩ = ℓ₂ ⟨u, hu⟩) :
    ∀ (n : ℕ) (hn : n < M.observed.card)
      (_ : ∃ t ∈ T, (M.observedAt ⟨n, hn⟩).val = t ∨
        M.dag.isAncestorAvoiding C (M.observedAt ⟨n, hn⟩).val t),
      evalObservedAuxOverride M hC s c ℓ₁ n hn =
        evalObservedAuxOverride M hC s c ℓ₂ n hn := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn hReach
    rw [evalObservedAuxOverride_eq M hC s c ℓ₁ n hn,
        evalObservedAuxOverride_eq M hC s c ℓ₂ n hn]
    by_cases hSelf : (M.observedAt ⟨n, hn⟩).val ∈ C
    · rw [dif_pos hSelf, dif_pos hSelf]
    · rw [dif_neg hSelf, dif_neg hSelf]
      congr 1
      funext w
      have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
        M.dag.mem_parents.mp w.property
      -- Extend the avoiding witness from `observedAt n` through `w`.
      have hReachW : ∃ t ∈ T, w.val = t ∨ M.dag.isAncestorAvoiding C w.val t := by
        rcases hReach with ⟨t, ht, hOr⟩
        refine ⟨t, ht, ?_⟩
        rcases hOr with hEq | hAv
        · exact Or.inr (hEq ▸ DAG.isAncestorAvoiding.edge hedge)
        · exact Or.inr (DAG.isAncestorAvoiding.cons M.dag hedge hSelf hAv)
      by_cases huo : w.val ∈ M.unobserved
      · rw [parentMapOverride_unobserved M hC s c ℓ₁ hn _ w huo,
            parentMapOverride_unobserved M hC s c ℓ₂ hn _ w huo]
        exact hAgree w.val huo hReachW
      · by_cases hfix : w.val ∈ M.fixed
        · rw [parentMapOverride_fixed M hC s c ℓ₁ hn _ w huo hfix,
              parentMapOverride_fixed M hC s c ℓ₂ hn _ w huo hfix]
        · have hobs : w.val ∈ M.observed := by
            rcases Finset.mem_union.mp
                (M.dag_edges_classified _ _ hedge).1 with h1' | h2'
            · rcases Finset.mem_union.mp h1' with hfx | hob
              · exact absurd hfx hfix
              · exact hob
            · exact absurd h2' huo
          by_cases hcW : w.val ∈ C
          · rw [parentMapOverride_C M hC s c ℓ₁ hn _ w huo hfix hcW,
                parentMapOverride_C M hC s c ℓ₂ hn _ w huo hfix hcW]
          · rw [parentMapOverride_observed M hC s c ℓ₁ hn _ w huo hfix hobs hcW,
                parentMapOverride_observed M hC s c ℓ₂ hn _ w huo hfix hobs hcW]
            have hj : (M.observedIndex ⟨w.val, hobs⟩).val < n :=
              M.observed_parent_index_lt hn hedge hobs
            congr 1
            apply ih _ hj
            rcases hReachW with ⟨t, ht, hwt⟩
            refine ⟨t, ht, ?_⟩
            have h_at : (M.observedAt
                ⟨(M.observedIndex ⟨w.val, hobs⟩).val,
                  (M.observedIndex ⟨w.val, hobs⟩).isLt⟩).val = w.val :=
              M.observedAt_observedIndex ⟨w.val, hobs⟩
            rw [h_at]
            exact hwt

/-- The overridden evaluation on the target set depends on latent values only through the latent cutset.

    **Structural cutset factorization (the keystone).**

    The override evaluation `evalMap_overrideC` with override block `C` depends
    on the latent assignment only through its values on the cutset `cutsetLatent
    Y C`.  Concretely, if two latent vectors `ℓ₁`, `ℓ₂` agree on `cutsetLatent
    Y C`, then their override evaluations agree on `Y`.

    No d-separation hypothesis is needed: latents outside the cutset reach `Y`
    only through the overridden block `C`, where the recursion short-circuits to
    the override value `c` and never reads the latent assignment. -/
theorem evalMap_overrideC_agree_cutset (M : Causalean.SCM N Ω)
    {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed)
    (s : FixedValues M)
    (c : ValuesOn C (swigΩ Ω))
    (ℓ₁ ℓ₂ : LatentValues M)
    (hAgree : valuesProjection (M.cutsetLatent_subset Y C) ℓ₁ =
              valuesProjection (M.cutsetLatent_subset Y C) ℓ₂) :
    M.evalMap_overrideC hY hC s c ℓ₁ = M.evalMap_overrideC hY hC s c ℓ₂ := by
  -- Turn the cutset-projection agreement into pointwise latent agreement on the
  -- avoiding-reachable latents.
  have hAgree' : ∀ (u : SWIGNode N) (hu : u ∈ M.unobserved),
      (∃ y ∈ Y, u = y ∨ M.dag.isAncestorAvoiding C u y) →
        ℓ₁ ⟨u, hu⟩ = ℓ₂ ⟨u, hu⟩ := by
    intro u hu hReach
    have huMem : u ∈ M.cutsetLatent Y C := M.mem_cutsetLatent.mpr ⟨hu, hReach⟩
    have := congrFun hAgree ⟨u, huMem⟩
    simpa [valuesProjection] using this
  funext v
  rw [evalMap_overrideC_eq M hY hC s c ℓ₁ v,
      evalMap_overrideC_eq M hY hC s c ℓ₂ v]
  congr 1
  apply evalObservedAuxOverride_agree_cutset M Y hC s c ℓ₁ ℓ₂ hAgree'
  refine ⟨v.val, v.property, Or.inl ?_⟩
  exact M.observedAt_observedIndex ⟨v.val, hY v.property⟩

/-- The overridden target evaluation factors through a single measurable function of the latent cutset projection.

    **Genuine cutset factorization of the override evaluation.**

    Packaging the keystone agreement as an honest factorization: there is a single
    measurable map `h` from the cutset projection to the observed values on `Y`
    such that the override evaluation `evalMap_overrideC` on `Y` equals `h` applied
    to the cutset projection of the latent assignment.  In words, the override
    evaluation on `Y` is a measurable function of the latent values restricted to
    the cutset `cutsetLatent Y C` (together with the fixed and override inputs,
    held fixed here). -/
theorem exists_evalMap_overrideC_factors_cutset (M : Causalean.SCM N Ω)
    [∀ n, Nonempty (Ω n)]
    {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) :
    ∃ h : ValuesOn (M.cutsetLatent Y C) (swigΩ Ω) → ValuesOn Y (swigΩ Ω),
      Measurable h ∧
      ∀ ℓ : LatentValues M,
        M.evalMap_overrideC hY hC s c ℓ =
          h (valuesProjection (M.cutsetLatent_subset Y C) ℓ) := by
  classical
  have hNEΩ : ∀ w : SWIGNode N, Nonempty (swigΩ Ω w) := by
    intro w; cases w <;> exact inferInstance
  -- Extend a cutset projection to a full latent vector (default off the cutset).
  let ℓ₀ : LatentValues M := fun u => (hNEΩ u.val).some
  let extend : ValuesOn (M.cutsetLatent Y C) (swigΩ Ω) → LatentValues M :=
    fun cwProj u =>
      if h : u.val ∈ M.cutsetLatent Y C then cwProj ⟨u.val, h⟩ else ℓ₀ u
  have hext_meas : Measurable extend := by
    refine measurable_pi_lambda _ (fun u => ?_)
    by_cases h : u.val ∈ M.cutsetLatent Y C
    · have : (fun cwProj : ValuesOn (M.cutsetLatent Y C) (swigΩ Ω) => extend cwProj u)
          = fun cwProj => cwProj ⟨u.val, h⟩ := by funext cwProj; simp [extend, h]
      rw [this]; exact measurable_pi_apply _
    · have : (fun cwProj : ValuesOn (M.cutsetLatent Y C) (swigΩ Ω) => extend cwProj u)
          = fun _ => ℓ₀ u := by funext cwProj; simp [extend, h]
      rw [this]; exact measurable_const
  refine ⟨fun cwProj => M.evalMap_overrideC hY hC s c (extend cwProj), ?_, ?_⟩
  · -- Measurability: override map (jointly measurable) precomposed with `extend`.
    have hcomp : (fun cwProj => M.evalMap_overrideC hY hC s c (extend cwProj)) =
        (fun ℓ : LatentValues M => M.evalMap_overrideC hY hC s c ℓ) ∘ extend := by
      funext cwProj; rfl
    rw [hcomp]
    have hcurry : (fun ℓ : LatentValues M => M.evalMap_overrideC hY hC s c ℓ) =
        (fun p : (M.FixedValues × ValuesOn C (swigΩ Ω)) × M.LatentValues =>
          M.evalMap_overrideC hY hC p.1.1 p.1.2 p.2) ∘ (fun ℓ => ((s, c), ℓ)) := by
      funext ℓ; rfl
    rw [hcurry, Function.comp_assoc]
    exact (measurable_evalMap_overrideC M hY hC).comp
      ((measurable_const.prodMk measurable_id).comp hext_meas)
  · -- Agreement: `extend (proj ℓ)` agrees with `ℓ` on the cutset, so apply (A).
    intro ℓ
    change M.evalMap_overrideC hY hC s c ℓ =
      M.evalMap_overrideC hY hC s c (extend (valuesProjection (M.cutsetLatent_subset Y C) ℓ))
    refine evalMap_overrideC_agree_cutset M hY hC s c ℓ _ ?_
    funext u
    simp only [valuesProjection, extend, dif_pos u.property]

end SCM

end Causalean
