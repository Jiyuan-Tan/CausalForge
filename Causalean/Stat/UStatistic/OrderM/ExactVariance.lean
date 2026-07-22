/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Exact variance of a completely-degenerate fixed-order U-statistic

For a symmetric, square-integrable, **completely degenerate** order-`m` kernel `g`
(`OrderDegenKernel`: integrating out any single coordinate gives `0`), the
fixed-order U-statistic has an *exact* second moment — not just the `O(1/n)` rate
bound of `OrderM.RemainderSecondMoment`.

## The Hoeffding second-moment computation

Write `Sₙ = Σ_{t ∈ injectiveTuples m n} g(Z_t)`.  For two ordered injective
`m`-tuples `t, q`:

* If `image t ≠ image q`, some index `a ∈ image t ∖ image q` occurs only in
  `g(Z_t)`; integrating that coordinate out (complete degeneracy) kills the cross
  expectation: `E[g(Z_t) g(Z_q)] = 0`.
* If `image t = image q`, then `q = t ∘ σ` for a permutation `σ`, so
  `g(Z_q) = g(Z_t)` by symmetry and `E[g(Z_t) g(Z_q)] = ζ_m = zetaOrder P g`.
  There are exactly `m!` such `q` for each `t` (the reorderings).

Hence `E[Sₙ²] = m! · n^{(m)} · ζ_m` with `n^{(m)} = injectiveTupleCount m n`, so

  `Var[Uₙ] = m! · ζ_m / n^{(m)}`,   `E[(√n Uₙ)²] = n · m! · ζ_m / n^{(m)}`.

At `m = 2`, the variance formula specializes to `2ζ / (n(n−1))` and the
rescaled second moment specializes to `2ζ / (n−1)`, matching the order-2
`integral_offDiag_sum_sq` / `integral_rescaled_sq` interface.  This is the
order-`m` generalization of the exact degenerate variance consumed by the
higher-order influence-function estimators.
-/

import Causalean.Stat.UStatistic.OrderM.Variance

/-!
# Exact variance for completely degenerate fixed-order U-statistics

This module proves the exact second-moment calculation for a completely
degenerate fixed-order kernel.  The cross-term lemmas
`IIDSample.crossterm_eq_zeta_of_image_eq` and
`IIDSample.crossterm_eq_zero_of_image_ne` classify pairs of injective tuples by
whether their images agree; `card_injectiveTuples_image_eq` counts the
same-image reorderings.

The headline variance identities are
`IIDSample.integral_injectiveTuples_sum_sq_degen` for the raw injective-tuple
sum and `IIDSample.integral_rescaled_order_sq_degen` for the `√n`-rescaled
degenerate U-statistic.  These sharpen the general rate bound to an exact
formula in the completely degenerate case.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {m : ℕ} [NeZero m] {g : (Fin m → X) → ℝ} (S : IIDSample Ω X μ P)

/-! ## Cross expectations by image comparison -/

private noncomputable def permOfImageEq {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    (himg : Finset.univ.image t = Finset.univ.image q) : Equiv.Perm (Fin m) := by
  classical
  let f : Fin m → Fin m := fun j =>
    Classical.choose ((Finset.mem_image.mp (by
      have hqmem : q j ∈ Finset.univ.image q :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      simp [himg])) : ∃ i, i ∈ Finset.univ ∧ t i = q j)
  let r : Fin m → Fin m := fun i =>
    Classical.choose ((Finset.mem_image.mp (by
      have htmem : t i ∈ Finset.univ.image t :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      simp [← himg])) : ∃ j, j ∈ Finset.univ ∧ q j = t i)
  have hf : ∀ j, t (f j) = q j := by
    intro j
    exact (Classical.choose_spec ((Finset.mem_image.mp (by
      have hqmem : q j ∈ Finset.univ.image q :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      simp [himg])) : ∃ i, i ∈ Finset.univ ∧ t i = q j)).2
  have hr : ∀ i, q (r i) = t i := by
    intro i
    exact (Classical.choose_spec ((Finset.mem_image.mp (by
      have htmem : t i ∈ Finset.univ.image t :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      simp [← himg])) : ∃ j, j ∈ Finset.univ ∧ q j = t i)).2
  exact
    { toFun := f
      invFun := r
      left_inv := by
        intro j
        apply hq
        rw [hr (f j), hf j]
      right_inv := by
        intro i
        apply ht
        rw [hf (r i), hr i] }

omit [NeZero m] in
private theorem permOfImageEq_apply {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    (himg : Finset.univ.image t = Finset.univ.image q) (j : Fin m) :
    t (permOfImageEq (m := m) ht hq himg j) = q j := by
  classical
  simp only [permOfImageEq]
  exact (Classical.choose_spec ((Finset.mem_image.mp (by
    have hqmem : q j ∈ Finset.univ.image q :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    simp [himg])) : ∃ i, i ∈ Finset.univ ∧ t i = q j)).2

omit [IsProbabilityMeasure P] in
/-- **Equal-image cross term.**  If two ordered injective `m`-tuples have the same
image, then `q` is a reordering of `t`, so by symmetry `g(Z_q) = g(Z_t)` and the
cross expectation is `ζ_m = zetaOrder P g`. -/
theorem crossterm_eq_zeta_of_image_eq (hg : OrderDegenKernel P g)
    {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    (himg : Finset.univ.image t = Finset.univ.image q) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ
      = zetaOrder P g := by
  classical
  let σ : Equiv.Perm (Fin m) := permOfImageEq (m := m) ht hq himg
  have hq_rewrite : ∀ ω,
      (fun j => S.Z (q j : ℕ) ω) = (fun j => S.Z (t j : ℕ) ω) ∘ σ := by
    intro ω
    funext j
    rw [Function.comp_apply]
    have hσ := permOfImageEq_apply (m := m) ht hq himg j
    rw [← hσ]
  have hcongr :
      (fun ω => g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω))
        =
      (fun ω => (g (fun j => S.Z (t j : ℕ) ω)) ^ 2) := by
    funext ω
    rw [hq_rewrite ω, hg.symm σ]
    ring
  rw [hcongr]
  exact S.orderTerm_diag hg ht

/-- **Distinct-image cross term.**  If two ordered injective `m`-tuples have
different images, complete degeneracy kills the cross expectation: some index of
`t` is absent from `q`, and integrating that coordinate out gives `0`. -/
theorem crossterm_eq_zero_of_image_ne (hg : OrderDegenKernel P g)
    {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    (himg : Finset.univ.image t ≠ Finset.univ.image q) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ = 0 := by
  classical
  let A : Finset (Fin n) := Finset.univ.image t
  let B : Finset (Fin n) := Finset.univ.image q
  have hAcard : A.card = m := by
    simpa [A] using (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin m))) ht)
  have hBcard : B.card = m := by
    simpa [B] using (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin m))) hq)
  have hnot_subset : ¬ A ⊆ B := by
    intro hsub
    apply himg
    have hcard_le : B.card ≤ A.card := by
      rw [hAcard, hBcard]
    simpa [A, B] using (Finset.eq_of_subset_of_card_le hsub hcard_le)
  rcases Finset.not_subset.mp hnot_subset with ⟨a, haA, haB⟩
  rcases Finset.mem_image.mp haA with ⟨p, _hp, htp⟩
  subst a
  let R : Finset (Fin n) := (A ∪ B).erase (t p)
  let XR : Ω → (R → X) := fun ω i => S.Z (i.1 : ℕ) ω
  let πR : Measure (R → X) := Measure.pi fun _ : R => P
  let tailOf : (R → X) → ({k : Fin m // k ≠ p} → X) := fun xr k =>
    xr ⟨t k.1, by
      have hmemA : t k.1 ∈ A :=
        Finset.mem_image.mpr ⟨k.1, Finset.mem_univ k.1, rfl⟩
      have hne : t k.1 ≠ t p := fun h => k.2 (ht h)
      simp [R, hmemA, hne]⟩
  let Ψ : (R → X) → ℝ := fun xr =>
    g (fun j => xr ⟨q j, by
      have hmemB : q j ∈ B :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
      have hne : q j ≠ t p := by
        intro h
        exact haB (by simpa [B, h] using hmemB)
      simp [R, hmemB, hne]⟩)
  let F : X × (R → X) → ℝ := fun z =>
    g (insertCoord p z.1 (tailOf z.2)) * Ψ z.2
  have hXRmeas : Measurable XR := by
    exact measurable_pi_lambda _ (fun i : R => S.meas (i.1 : ℕ))
  have hX0meas : Measurable (fun ω : Ω => S.Z (t p : ℕ) ω) := S.meas (t p : ℕ)
  have hPairMeas : Measurable (fun ω : Ω => (S.Z (t p : ℕ) ω, XR ω)) :=
    hX0meas.prodMk hXRmeas
  have hXRmap : μ.map XR = πR := by
    have hr : Function.Injective (fun i : R => i.1) := by
      intro i j hij
      exact Subtype.ext hij
    simpa [XR, πR, R] using
      (S.map_fintype_tuple_eq (ι := R) (r := fun i : R => i.1) hr)
  have hdisj : Disjoint ({t p} : Finset (Fin n)) R := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hx0, hxR⟩
      have hxeq : x = t p := by simpa using hx0
      subst x
      simp [R] at hxR
    · intro hx
      simp at hx
  have hindFin : iIndepFun (fun i : Fin n => S.Z (i : ℕ)) μ :=
    S.indep.precomp (fun _ _ h => Fin.ext h)
  have hindBlocks :
      IndepFun
        (fun ω : Ω => fun i : ({t p} : Finset (Fin n)) => S.Z (i.1 : ℕ) ω)
        XR μ := by
    simpa [XR] using
      (ProbabilityTheory.iIndepFun.indepFun_finset
        ({t p} : Finset (Fin n)) R hdisj hindFin
        (fun i : Fin n => S.meas (i : ℕ)))
  have hEval :
      Measurable
        (fun x : ({t p} : Finset (Fin n)) → X =>
          x ⟨t p, by simp⟩) :=
    measurable_pi_apply _
  have hind : IndepFun (fun ω : Ω => S.Z (t p : ℕ) ω) XR μ := by
    have hcomp := hindBlocks.comp hEval measurable_id
    simpa [Function.comp_def] using hcomp
  have hΦ : Measurable (fun z : X × (R → X) => g (insertCoord p z.1 (tailOf z.2))) := by
    exact hg.meas.comp (measurable_pi_lambda _ (fun j : Fin m => by
      by_cases hj : j = p
      · subst j
        simpa [insertCoord] using measurable_fst
      · simpa [tailOf, insertCoord, hj] using
          (measurable_pi_apply
            (⟨t j, by
              have hmemA : t j ∈ A :=
                Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
              have hne : t j ≠ t p := fun h => hj (ht h)
              simp [R, hmemA, hne]⟩ : R)).comp measurable_snd))
  have hΨ : Measurable Ψ := by
    exact hg.meas.comp (measurable_pi_lambda _ (fun j : Fin m =>
      measurable_pi_apply _))
  have hFmeas : Measurable F := hΦ.mul (hΨ.comp measurable_snd)
  have ht_rewrite : ∀ ω, g (fun j => S.Z (t j : ℕ) ω)
      = g (insertCoord p (S.Z (t p : ℕ) ω) (tailOf (XR ω))) := by
    intro ω
    congr 1
    funext j
    by_cases hj : j = p
    · subst j
      simp [insertCoord]
    · simp [tailOf, XR, insertCoord, hj]
  have hq_rewrite : ∀ ω, g (fun j => S.Z (q j : ℕ) ω) = Ψ (XR ω) := by
    intro ω
    rfl
  have hcomp_int : Integrable (fun ω => F (S.Z (t p : ℕ) ω, XR ω)) μ := by
    have horig := S.integrable_orderTerm_mul hg ht hq
    refine horig.congr ?_
    filter_upwards with ω
    simp [F, ht_rewrite ω, hq_rewrite ω]
  have hmap_pair :
      μ.map (fun ω : Ω => (S.Z (t p : ℕ) ω, XR ω)) = P.prod (μ.map XR) := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map
      hX0meas.aemeasurable hXRmeas.aemeasurable).mp hind
    simpa [S.map_eq (t p : ℕ)] using h
  have hFint_map : Integrable F (P.prod (μ.map XR)) := by
    have hmap_int : Integrable F (μ.map fun ω : Ω => (S.Z (t p : ℕ) ω, XR ω)) :=
      (integrable_map_measure hFmeas.aestronglyMeasurable
        hPairMeas.aemeasurable).mpr hcomp_int
    simpa [hmap_pair] using hmap_int
  have hinner : ∀ xr : R → X, (∫ x : X, F (x, xr) ∂P) = 0 := by
    intro xr
    change (∫ x : X, g (insertCoord p x (tailOf xr)) * Ψ xr ∂P) = 0
    rw [integral_mul_const, hg.deg p (tailOf xr), zero_mul]
  calc
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ
        = ∫ ω, F (S.Z (t p : ℕ) ω, XR ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simp [F, ht_rewrite ω, hq_rewrite ω]
    _ = ∫ z, F z ∂(μ.map fun ω : Ω => (S.Z (t p : ℕ) ω, XR ω)) := by
          rw [integral_map hPairMeas.aemeasurable hFmeas.aestronglyMeasurable]
    _ = ∫ z, F z ∂(P.prod (μ.map XR)) := by
          rw [hmap_pair]
    _ = ∫ xr, ∫ x, F (x, xr) ∂P ∂(μ.map XR) := by
          rw [integral_prod_symm F hFint_map]
    _ = 0 := by
          rw [show (fun xr : R → X => ∫ x, F (x, xr) ∂P) = fun _ => 0 by
            funext xr
            exact hinner xr]
          simp

/-! ## Counting reorderings -/

omit [NeZero m] in
/-- For an ordered injective `m`-tuple `t`, the ordered injective tuples with the
same image are exactly its `m!` reorderings. -/
theorem card_injectiveTuples_image_eq {n : ℕ} {t : Fin m → Fin n}
    (ht : Function.Injective t) :
    ((injectiveTuples m n).filter
        (fun q => Finset.univ.image q = Finset.univ.image t)).card = m.factorial := by
  classical
  have hcard_perm : (Finset.univ : Finset (Equiv.Perm (Fin m))).card = m.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← hcard_perm]
  symm
  refine Finset.card_bij (fun σ _ => t ∘ σ) ?hmem ?hinj ?hsurj
  · intro σ _hσ
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp [injectiveTuples, ht.comp σ.injective]
    · ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨j, _hj, hjx⟩
        exact Finset.mem_image.mpr ⟨σ j, Finset.mem_univ _, hjx⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨j, _hj, hjx⟩
        exact Finset.mem_image.mpr ⟨σ.symm j, Finset.mem_univ _, by simp [Function.comp, hjx]⟩
  · intro σ₁ _ σ₂ _ hσ
    ext j
    exact congrArg Fin.val (ht (congrFun hσ j))
  · intro q hq
    rw [Finset.mem_filter] at hq
    have hqinj : Function.Injective q := by
      simpa [injectiveTuples] using hq.1
    let σ : Equiv.Perm (Fin m) :=
      permOfImageEq (m := m) ht hqinj hq.2.symm
    refine ⟨σ, Finset.mem_univ σ, ?_⟩
    funext j
    exact permOfImageEq_apply (m := m) ht hqinj hq.2.symm j

/-! ## Exact second moment and variance -/

/-- **Exact second moment of the injective-tuple sum.**
`E[(Σ_{t} g(Z_t))²] = m! · n^{(m)} · ζ_m`. -/
theorem integral_injectiveTuples_sum_sq_degen (hg : OrderDegenKernel P g) (n : ℕ) :
    ∫ ω, (∑ t ∈ injectiveTuples m n, g (fun j => S.Z (t j : ℕ) ω)) ^ 2 ∂μ
      = (m.factorial : ℝ) * injectiveTupleCount m n * zetaOrder P g := by
  classical
  let T : Finset (Fin m → Fin n) := injectiveTuples m n
  let F : (Fin m → Fin n) → (Fin m → Fin n) → ℝ := fun t q =>
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) *
      g (fun j => S.Z (q j : ℕ) ω) ∂μ
  have hinj_of_mem_T : ∀ t ∈ T, Function.Injective t := by
    intro t ht
    have ht' : t ∈ injectiveTuples m n := by simpa [T] using ht
    exact (Finset.mem_filter.mp ht').2
  have hexpand :
      (fun ω => (∑ t ∈ T, g (fun j => S.Z (t j : ℕ) ω)) ^ 2)
        = (fun ω => ∑ t ∈ T, ∑ q ∈ T,
            g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω)) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
  rw [show (∫ ω, (∑ t ∈ injectiveTuples m n,
      g (fun j => S.Z (t j : ℕ) ω)) ^ 2 ∂μ)
      = ∫ ω, (∑ t ∈ T, g (fun j => S.Z (t j : ℕ) ω)) ^ 2 ∂μ by rfl]
  rw [hexpand]
  rw [integral_finset_sum _ (fun t ht => by
    apply integrable_finset_sum
    intro q hq
    exact S.integrable_orderTerm_mul hg (hinj_of_mem_T t ht) (hinj_of_mem_T q hq))]
  have hpush : ∀ t ∈ T,
      ∫ ω, ∑ q ∈ T,
        g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ
        = ∑ q ∈ T, F t q := by
    intro t ht
    exact integral_finset_sum _ (fun q hq =>
      S.integrable_orderTerm_mul hg (hinj_of_mem_T t ht) (hinj_of_mem_T q hq))
  rw [Finset.sum_congr rfl hpush]
  have hinner : ∀ t ∈ T, ∑ q ∈ T, F t q = (m.factorial : ℝ) * zetaOrder P g := by
    intro t ht
    let SAME : Finset (Fin m → Fin n) :=
      T.filter (fun q => Finset.univ.image q = Finset.univ.image t)
    have hsub : SAME ⊆ T := Finset.filter_subset _ _
    have hzero : ∀ q ∈ T, q ∉ SAME → F t q = 0 := by
      intro q hq hqnot
      have htinj := hinj_of_mem_T t ht
      have hqinj := hinj_of_mem_T q hq
      have hne : Finset.univ.image t ≠ Finset.univ.image q := by
        intro h
        exact hqnot (Finset.mem_filter.mpr ⟨hq, h.symm⟩)
      simpa [F] using S.crossterm_eq_zero_of_image_ne hg htinj hqinj hne
    rw [← Finset.sum_subset hsub hzero]
    have hsame : ∀ q ∈ SAME, F t q = zetaOrder P g := by
      intro q hq
      have htinj := hinj_of_mem_T t ht
      have hqT : q ∈ T := (Finset.mem_filter.mp hq).1
      have hqinj := hinj_of_mem_T q hqT
      have himg : Finset.univ.image t = Finset.univ.image q :=
        (Finset.mem_filter.mp hq).2.symm
      simpa [F] using S.crossterm_eq_zeta_of_image_eq hg htinj hqinj himg
    rw [Finset.sum_congr rfl hsame]
    rw [Finset.sum_const, nsmul_eq_mul]
    have htinj := hinj_of_mem_T t ht
    have hcard : SAME.card = m.factorial := by
      simpa [SAME, T] using card_injectiveTuples_image_eq (m := m) (n := n) htinj
    rw [hcard]
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [T, injectiveTupleCount]
  ring

/-- **Exact variance of the rescaled degenerate fixed-order U-statistic.**
`E[(√n · Uₙ)²] = n · m! · ζ_m / n^{(m)}`.  For `m = 2` this is `2ζ / (n−1)`. -/
theorem integral_rescaled_order_sq_degen (hg : OrderDegenKernel P g)
    {n : ℕ} (hmn : m ≤ n) :
    ∫ ω, (Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) ^ 2 ∂μ
      = (n : ℝ) * (m.factorial : ℝ) * zetaOrder P g / injectiveTupleCount m n := by
  classical
  let K : Ω → ℝ := fun ω => ∑ t ∈ injectiveTuples m n,
    g (fun j => S.Z (t j : ℕ) ω)
  have hcount_ne : injectiveTupleCount m n ≠ 0 := injectiveTupleCount_ne_zero hmn
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hpoint :
      (fun ω => (Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) ^ 2)
        =
      (fun ω => ((n : ℝ) * (injectiveTupleCount m n)⁻¹ ^ 2) * (K ω) ^ 2) := by
    funext ω
    simp only [uStatisticOrder, K]
    rw [mul_pow, Real.sq_sqrt hnnonneg]
    ring
  rw [hpoint, integral_const_mul]
  rw [show (∫ ω, (K ω) ^ 2 ∂μ)
      = ∫ ω, (∑ t ∈ injectiveTuples m n,
          g (fun j => S.Z (t j : ℕ) ω)) ^ 2 ∂μ by rfl]
  rw [S.integral_injectiveTuples_sum_sq_degen hg n]
  field_simp [hcount_ne]

end IIDSample

end Causalean.Stat
