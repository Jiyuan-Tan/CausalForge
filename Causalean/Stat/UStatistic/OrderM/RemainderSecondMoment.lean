/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Higher-order second-moment bound for the fixed-order U-statistic remainder

This file proves the keystone estimate behind the negligibility of the order-`m`
Hájek remainder: for a first-order degenerate kernel `g` there is a constant `C`
with `E[(√n · Uₙ)²] ≤ C / n` for all `n ≥ m`.

## Strategy

Write `Sₙ = Σ_{t ∈ injectiveTuples m n} g(Z_t)` so `√n·Uₙ = √n·(n^{(m)})⁻¹·Sₙ`.
Expand `E[Sₙ²] = Σ_{t,q} E[g(Z_t) g(Z_q)]`.

* **Cross-term vanishing** (`crossterm_eq_zero_of_shared_le_one`): if the ordered
  injective tuples `t, q` share `≤ 1` sample index then `E[g(Z_t) g(Z_q)] = 0`.
  Zero shared ⇒ the two blocks are independent (distinct indices) and each factor
  has mean `uMeanOrder g P = 0`.  Exactly one shared index `a` ⇒ condition on
  `Z_a`: the two factors become conditionally independent, and each conditional
  mean is a first Hoeffding projection of `g`, hence `0` by `firstDeg`.  Use the
  product-law transport `IIDSample.map_fintype_tuple_eq` on the joined index set
  and Fubini to reduce to the coordinate integral.
* **Cauchy–Schwarz**: each surviving term satisfies
  `|E[g(Z_t) g(Z_q)]| ≤ ζ_m = zetaOrder P g` (both terms are in `L²` with second
  moment `ζ_m`, cf. `orderTerm_diag`).
* **Counting**: the pairs `(t, q)` sharing `≥ 2` indices number `≤ C(m)·n^{2m-2}`
  (choose `t`: `≤ nᵐ`; pick which `2` of `q`'s slots are shared and give them
  values from `image t`: `≤ C(m,2)·m²`; fill the other `m−2` slots freely:
  `≤ n^{m-2}`).  Bound the surviving part of `E[Sₙ²]` by `C(m)·n^{2m-2}·ζ_m`.
* **Normalization**: with `n^{(m)} = injectiveTupleCount m n ≍ nᵐ`,
  `E[(√n Uₙ)²] = n·(n^{(m)})⁻²·E[Sₙ²] ≤ C·ζ_m / n`.

The counting is the fiddly part; phrase it as an injection of the surviving
pair-set into an explicit product `Finset` of size `C(m)·n^{2m-2}` and bound the
sum with `Finset.sum_le_card_nsmul` / a Cauchy–Schwarz per-term bound.
-/

import Causalean.Stat.UStatistic.OrderM.FirstDegenKernel

/-!
Proves the second-moment bound for first-order degenerate fixed-order
U-statistic remainders.

The central public estimate is `IIDSample.integral_rescaled_order_sq_le`: for a
kernel satisfying `OrderFirstDegenKernel`, there is a finite constant `C`
depending only on the order and `ζ_m = E[g²]` such that
`E[(√n * Uₙ)²] ≤ C / n` whenever `n ≥ m`.  The proof first shows
`crossterm_eq_zero_of_shared_le_one`, bounding the only nonzero terms by
Cauchy-Schwarz, then counts the tuple pairs sharing at least two sample indices
and normalizes by the falling factorial denominator.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {m : ℕ} [NeZero m] {g : (Fin m → X) → ℝ} (S : IIDSample Ω X μ P)

omit [IsProbabilityMeasure P] in
private theorem orderFirstTerm_diag (hg : OrderFirstDegenKernel P g)
    {n : ℕ} {t : Fin m → Fin n} (ht : Function.Injective t) :
    ∫ ω, (g (fun j => S.Z (t j : ℕ) ω)) ^ 2 ∂μ = zetaOrder P g := by
  rw [zetaOrder]
  rw [← S.map_tuple_eq ht]
  rw [integral_map
    (measurable_pi_lambda _ (fun j : Fin m => S.meas (t j : ℕ))).aemeasurable
    (hg.meas.pow_const 2).aestronglyMeasurable]

/-- **Disjoint case.**  If the two tuples' images are disjoint, the blocks are
independent, so the cross expectation factors as `E[g(Z_t)]·E[g(Z_q)] = 0·0`.
Use `iIndepFun.indepFun_finset` (disjoint index Finsets) + `.comp` +
`IndepFun.integral_fun_mul_eq_mul_integral`; each factor's mean is
`uMeanOrder g P = hg.integral_eq_zero` (via `S.integral_orderKernelTerm_eq`). -/
private theorem crossterm_zero_of_disjoint (hg : OrderFirstDegenKernel P g)
    {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    (hdisj : Disjoint (Finset.univ.image t) (Finset.univ.image q)) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ = 0 := by
  classical
  let A : Finset (Fin n) := Finset.univ.image t
  let B : Finset (Fin n) := Finset.univ.image q
  let Xt : Ω → (A → X) := fun ω i => S.Z (i.1 : ℕ) ω
  let Xq : Ω → (B → X) := fun ω i => S.Z (i.1 : ℕ) ω
  let φ : (A → X) → ℝ := fun x =>
    g (fun j => x ⟨t j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
  let ψ : (B → X) → ℝ := fun x =>
    g (fun j => x ⟨q j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
  have hindFin : iIndepFun (fun i : Fin n => S.Z (i : ℕ)) μ :=
    S.indep.precomp (fun _ _ h => Fin.ext h)
  have hindBlocks : IndepFun Xt Xq μ := by
    simpa [A, B, Xt, Xq] using
      (ProbabilityTheory.iIndepFun.indepFun_finset A B hdisj hindFin
        (fun i : Fin n => S.meas (i : ℕ)))
  have hφ : Measurable φ := by
    exact hg.meas.comp (measurable_pi_lambda _ (fun j : Fin m => measurable_pi_apply _))
  have hψ : Measurable ψ := by
    exact hg.meas.comp (measurable_pi_lambda _ (fun j : Fin m => measurable_pi_apply _))
  have hind : IndepFun (φ ∘ Xt) (ψ ∘ Xq) μ := hindBlocks.comp hφ hψ
  have hφsm : AEStronglyMeasurable (φ ∘ Xt) μ :=
    (hφ.comp (measurable_pi_lambda _ (fun i : A => S.meas (i.1 : ℕ)))).aestronglyMeasurable
  have hψsm : AEStronglyMeasurable (ψ ∘ Xq) μ :=
    (hψ.comp (measurable_pi_lambda _ (fun i : B => S.meas (i.1 : ℕ)))).aestronglyMeasurable
  have hfactor :
      ∫ ω, (φ ∘ Xt) ω * (ψ ∘ Xq) ω ∂μ =
        (∫ ω, (φ ∘ Xt) ω ∂μ) * (∫ ω, (ψ ∘ Xq) ω ∂μ) :=
    hind.integral_fun_mul_eq_mul_integral hφsm hψsm
  have hmean_t : ∫ ω, (φ ∘ Xt) ω ∂μ = 0 := by
    simpa [φ, Xt, uMeanOrder] using
      (S.integral_orderKernelTerm_eq_zero_of_uMean_zero hg.meas ht hg.integral_eq_zero)
  have hmean_q : ∫ ω, (ψ ∘ Xq) ω ∂μ = 0 := by
    simpa [ψ, Xq, uMeanOrder] using
      (S.integral_orderKernelTerm_eq_zero_of_uMean_zero hg.meas hq hg.integral_eq_zero)
  change ∫ ω, (φ ∘ Xt) ω * (ψ ∘ Xq) ω ∂μ = 0
  rw [hfactor, hmean_t, hmean_q, zero_mul]

/-- **One-shared case.**  If the two tuples' images meet in a single index `a`,
integrate out the `m − 1` coordinates of the first tuple other than the slot
carrying `a`; that inner integral is the first Hoeffding projection
`hg.firstDeg (t⁻¹ a) x_a = 0`.  Map to the product law over the `2m − 1` distinct
indices (`map_fintype_tuple_eq`) and Fubini-split, mirroring `Variance.lean`'s
`term_shared` / `map_triple_eq'`. -/
private theorem crossterm_zero_of_shared_one (hg : OrderFirstDegenKernel P g)
    {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    {a : Fin n} (hshare : Finset.univ.image t ∩ Finset.univ.image q = {a}) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ = 0 := by
  classical
  have ha_inter : a ∈ Finset.univ.image t ∩ Finset.univ.image q := by
    rw [hshare]
    simp
  have ha_t : a ∈ Finset.univ.image t := (Finset.mem_inter.mp ha_inter).1
  have ha_q : a ∈ Finset.univ.image q := (Finset.mem_inter.mp ha_inter).2
  rcases Finset.mem_image.mp ha_t with ⟨p, _hp, htp⟩
  let Tail : Type := {k : Fin m // k ≠ p}
  let B : Finset (Fin n) := Finset.univ.image q
  let XA : Ω → (Tail → X) := fun ω k => S.Z (t k.1 : ℕ) ω
  let Xq : Ω → (B → X) := fun ω i => S.Z (i.1 : ℕ) ω
  let πTail : Measure (Tail → X) := Measure.pi fun _ : Tail => P
  let Φ : (Tail → X) → (B → X) → ℝ := fun tail xq =>
    g (insertCoord p (xq ⟨a, ha_q⟩) tail)
  let Ψ : (B → X) → ℝ := fun xq =>
    g (fun j => xq ⟨q j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
  let F : (Tail → X) × (B → X) → ℝ := fun z => Φ z.1 z.2 * Ψ z.2
  have hXAmeas : Measurable XA := by
    exact measurable_pi_lambda _ (fun k : Tail => S.meas (t k.1 : ℕ))
  have hXqmeas : Measurable Xq := by
    exact measurable_pi_lambda _ (fun i : B => S.meas (i.1 : ℕ))
  have hPairMeas : Measurable (fun ω => (XA ω, Xq ω)) := hXAmeas.prodMk hXqmeas
  have hXAmap : μ.map XA = πTail := by
    have hr : Function.Injective (fun k : Tail => t k.1) := by
      intro k l hkl
      exact Subtype.ext (ht hkl)
    simpa [XA, πTail, Tail] using
      (S.map_fintype_tuple_eq (ι := Tail) (r := fun k : Tail => t k.1) hr)
  have hdisj : Disjoint (Finset.univ.image (fun k : Tail => t k.1)) B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxA, hxB⟩
      rcases Finset.mem_image.mp hxA with ⟨k, _hk, hkx⟩
      have hx_inter : x ∈ Finset.univ.image t ∩ Finset.univ.image q := by
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr ⟨k.1, Finset.mem_univ k.1, hkx⟩, by simpa [B] using hxB⟩
      have hxa : x = a := by
        have : x ∈ ({a} : Finset (Fin n)) := by
          simpa [hshare] using hx_inter
        simpa using this
      have hkp : k.1 = p := ht (by
        calc
          t k.1 = x := hkx
          _ = a := hxa
          _ = t p := htp.symm)
      exact (k.2 hkp).elim
    · intro hx
      simp at hx
  have hindFin : iIndepFun (fun i : Fin n => S.Z (i : ℕ)) μ :=
    S.indep.precomp (fun _ _ h => Fin.ext h)
  have hindBlocks :
      IndepFun
        (fun ω : Ω =>
          fun i : (Finset.univ.image (fun k : Tail => t k.1)) => S.Z (i.1 : ℕ) ω)
        Xq μ := by
    simpa [B, Xq] using
      (ProbabilityTheory.iIndepFun.indepFun_finset
        (Finset.univ.image (fun k : Tail => t k.1)) B hdisj hindFin
        (fun i : Fin n => S.meas (i : ℕ)))
  have htoTail :
      Measurable
        (fun w : (Finset.univ.image (fun k : Tail => t k.1)) → X =>
          fun k : Tail => w ⟨t k.1,
            Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩) := by
    exact measurable_pi_lambda _ (fun k : Tail => measurable_pi_apply _)
  have hind : IndepFun XA Xq μ := by
    have hcomp := hindBlocks.comp htoTail measurable_id
    simpa [XA, Function.comp_def] using hcomp
  have hΦpair : Measurable (fun z : (Tail → X) × (B → X) =>
      Φ z.1 z.2) := by
    exact hg.meas.comp (measurable_pi_lambda _ (fun j : Fin m => by
      by_cases hj : j = p
      · subst j
        simpa [Φ, insertCoord]
          using (measurable_pi_apply (⟨a, ha_q⟩ : B)).comp
            measurable_snd
      · simpa [Φ, insertCoord, hj]
          using (measurable_pi_apply (⟨j, hj⟩ : Tail)).comp
            measurable_fst))
  have hΨ : Measurable Ψ := by
    exact hg.meas.comp (measurable_pi_lambda _ (fun j : Fin m => measurable_pi_apply _))
  have hΨpair : Measurable (fun z : (Tail → X) × (B → X) => Ψ z.2) :=
    hΨ.comp measurable_snd
  have hFmeas : Measurable F := hΦpair.mul hΨpair
  have ht_rewrite : ∀ ω, g (fun j => S.Z (t j : ℕ) ω) = Φ (XA ω) (Xq ω) := by
    intro ω
    congr 1
    funext j
    by_cases hj : j = p
    · subst j
      simp [Xq, insertCoord, htp]
    · simp [XA, insertCoord, hj]
  have hq_rewrite : ∀ ω, g (fun j => S.Z (q j : ℕ) ω) = Ψ (Xq ω) := by
    intro ω
    rfl
  have hcomp_int : Integrable (fun ω => F (XA ω, Xq ω)) μ := by
    have horig := S.integrable_sqKernelTerm_mul hg.meas hg.sq ht hq
    refine horig.congr ?_
    filter_upwards with ω
    simp [F, ht_rewrite ω, hq_rewrite ω]
  have hmap_pair :
      μ.map (fun ω => (XA ω, Xq ω)) = πTail.prod (μ.map Xq) := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map
      hXAmeas.aemeasurable hXqmeas.aemeasurable).mp hind
    simpa [hXAmap] using h
  have hFint_map : Integrable F (πTail.prod (μ.map Xq)) := by
    have hmap_int : Integrable F (μ.map fun ω => (XA ω, Xq ω)) :=
      (integrable_map_measure hFmeas.aestronglyMeasurable
        hPairMeas.aemeasurable).mpr hcomp_int
    simpa [hmap_pair] using hmap_int
  have hinner : ∀ xq : B → X, (∫ tail : Tail → X, F (tail, xq) ∂πTail) = 0 := by
    intro xq
    change
      (∫ tail : Tail → X,
          g (insertCoord p (xq ⟨a, ha_q⟩) tail) * Ψ xq ∂πTail) = 0
    rw [integral_mul_const, hg.firstDeg p (xq ⟨a, ha_q⟩)]
    simp
  calc
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ
        = ∫ ω, F (XA ω, Xq ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simp [F, ht_rewrite ω, hq_rewrite ω]
    _ = ∫ z, F z ∂(μ.map fun ω => (XA ω, Xq ω)) := by
          rw [integral_map hPairMeas.aemeasurable hFmeas.aestronglyMeasurable]
    _ = ∫ z, F z ∂(πTail.prod (μ.map Xq)) := by
          rw [hmap_pair]
    _ = ∫ xq, ∫ tail, F (tail, xq) ∂πTail ∂(μ.map Xq) := by
          rw [integral_prod_symm F hFint_map]
    _ = 0 := by
          rw [show (fun xq : B → X => ∫ tail : Tail → X, F (tail, xq) ∂πTail) =
              fun _ => 0 by
            funext xq
            exact hinner xq]
          simp

/-- Cross-term vanishing, assembled from the disjoint (`card = 0`) and one-shared
(`card = 1`) cases. -/
private theorem crossterm_eq_zero_of_shared_le_one_product_disintegration
    (hg : OrderFirstDegenKernel P g)
    {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    (hshare : (Finset.univ.image t ∩ Finset.univ.image q).card ≤ 1) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hshare with h0 | h1
  · have hempty : Finset.univ.image t ∩ Finset.univ.image q = ∅ :=
      Finset.card_eq_zero.mp h0
    exact S.crossterm_zero_of_disjoint hg ht hq
      (Finset.disjoint_iff_inter_eq_empty.mpr hempty)
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    exact S.crossterm_zero_of_shared_one hg ht hq ha

/-- **Cross-term vanishing.**  If two ordered injective `m`-tuples share at most
one sample index, the expected product of the corresponding kernel terms is zero.
Zero shared indices ⇒ independence + mean zero; one shared index ⇒ condition on
it and use first-order degeneracy of each factor. -/
theorem crossterm_eq_zero_of_shared_le_one (hg : OrderFirstDegenKernel P g)
    {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q)
    (hshare : (Finset.univ.image t ∩ Finset.univ.image q).card ≤ 1) :
    ∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ = 0 := by
  exact S.crossterm_eq_zero_of_shared_le_one_product_disintegration hg ht hq hshare

omit [IsProbabilityMeasure P] in
/-- **Per-term Cauchy–Schwarz bound.**  Each cross expectation is bounded by
`ζ_m = zetaOrder P g`, since both factors are `L²` with second moment
`orderFirstTerm_diag = zetaOrder P g`. -/
private theorem crossterm_abs_le_zeta (hg : OrderFirstDegenKernel P g)
    {n : ℕ} {t q : Fin m → Fin n}
    (ht : Function.Injective t) (hq : Function.Injective q) :
    |∫ ω, g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ|
      ≤ zetaOrder P g := by
  let ft : Ω → ℝ := fun ω => g (fun j => S.Z (t j : ℕ) ω)
  let fq : Ω → ℝ := fun ω => g (fun j => S.Z (q j : ℕ) ω)
  have hft0 : MemLp ft 2 μ := S.memLp_sqKernelTerm hg.meas hg.sq ht
  have hfq0 : MemLp fq 2 μ := S.memLp_sqKernelTerm hg.meas hg.sq hq
  have hft : MemLp ft (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hft0
  have hfq : MemLp fq (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hfq0
  have hcs := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := ft) (g := fq) (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr (by norm_num)) hft hfq
  have habs :
      |∫ ω, ft ω * fq ω ∂μ| ≤ ∫ ω, ‖ft ω‖ * ‖fq ω‖ ∂μ := by
    calc
      |∫ ω, ft ω * fq ω ∂μ| ≤ ∫ ω, |ft ω * fq ω| ∂μ :=
        abs_integral_le_integral_abs
      _ = ∫ ω, ‖ft ω‖ * ‖fq ω‖ ∂μ := by
        simp [Real.norm_eq_abs, abs_mul]
  have ht2 : ∫ ω, ‖ft ω‖ ^ (2 : ℝ) ∂μ = zetaOrder P g := by
    simpa [ft, sq_abs] using S.orderFirstTerm_diag hg ht
  have hq2 : ∫ ω, ‖fq ω‖ ^ (2 : ℝ) ∂μ = zetaOrder P g := by
    simpa [fq, sq_abs] using S.orderFirstTerm_diag hg hq
  have hznonneg : 0 ≤ zetaOrder P g := zetaOrder_nonneg
  rw [ht2, hq2] at hcs
  have hroot :
      (zetaOrder P g) ^ (1 / (2 : ℝ)) * (zetaOrder P g) ^ (1 / (2 : ℝ))
        = zetaOrder P g := by
    rw [← Real.rpow_add' hznonneg
      (by norm_num : (1 / (2 : ℝ) + 1 / (2 : ℝ)) ≠ 0)]
    rw [show (1 / (2 : ℝ) + 1 / (2 : ℝ)) = (1 : ℝ) by norm_num]
    exact Real.rpow_one (zetaOrder P g)
  rw [hroot] at hcs
  exact le_trans habs hcs

private abbrev shareCountEncoding (m n : ℕ) :=
  Σ _t : Fin m → Fin n,
    Σ s : {s : Finset (Fin m) // s ∈ Finset.univ.powersetCard 2},
      (({j : Fin m // j ∈ s.1} → Fin m) × ({j : Fin m // j ∉ s.1} → Fin n))

private noncomputable def shareCountDecodeQ {m n : ℕ}
    (e : shareCountEncoding m n) : Fin m → Fin n :=
  fun j =>
    if hj : j ∈ e.2.1.1 then e.1 (e.2.2.1 ⟨j, hj⟩) else e.2.2.2 ⟨j, hj⟩

private theorem shareCountEncoding_card_le (m n : ℕ) :
    Fintype.card (shareCountEncoding m n)
      ≤ n ^ m * m.choose 2 * m ^ 2 * n ^ (m - 2) := by
  classical
  simp only [shareCountEncoding]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  have hsummand : ∀ x : {s : Finset (Fin m) // s ∈ Finset.univ.powersetCard 2},
      m ^ Fintype.card {j : Fin m // j ∈ x.1} *
          n ^ Fintype.card {j : Fin m // j ∉ x.1}
        = m ^ 2 * n ^ (m - 2) := by
    intro x
    have hxcard : x.1.card = 2 := (Finset.mem_powersetCard.mp x.2).2
    have hsub : x.1 ⊆ (Finset.univ : Finset (Fin m)) :=
      (Finset.mem_powersetCard.mp x.2).1
    have hcardIn : Fintype.card {j : Fin m // j ∈ x.1} = 2 := by
      rw [Fintype.card_subtype]
      simpa using hxcard
    have hcardOut : Fintype.card {j : Fin m // j ∉ x.1} = m - 2 := by
      rw [Fintype.card_subtype]
      change (Finset.univ.filter fun j : Fin m => j ∉ x.1).card = m - 2
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (p := fun j : Fin m => j ∈ x.1)
      have hin :
          (Finset.univ.filter fun j : Fin m => j ∈ x.1).card = x.1.card := by
        congr 1
        ext j
        simp
      have huniv : (Finset.univ : Finset (Fin m)).card = m := by simp
      omega
    rw [hcardIn, hcardOut]
  rw [Finset.sum_congr rfl (fun x _ => hsummand x)]
  simp only [Finset.univ_eq_attach, Finset.sum_const, Finset.card_attach,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Fintype.card_pi, Finset.prod_const, ge_iff_le]
  exact le_of_eq (by ring)

omit [NeZero m] in
private theorem sharedPositions_card_eq {n : ℕ} {t q : Fin m → Fin n}
    (hq : Function.Injective q) :
    (Finset.univ.filter (fun j : Fin m => q j ∈ Finset.univ.image t)).card =
      (Finset.univ.image t ∩ Finset.univ.image q).card := by
  have himage :
      (Finset.univ.filter (fun j : Fin m => q j ∈ Finset.univ.image t)).image q =
        Finset.univ.image t ∩ Finset.univ.image q := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter] at hj
      exact Finset.mem_inter.mpr
        ⟨hj.2, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨hat, haq⟩
      rcases Finset.mem_image.mp haq with ⟨j, _hj, rfl⟩
      exact Finset.mem_image.mpr ⟨j, by simpa using hat, rfl⟩
  rw [← himage]
  exact (Finset.card_image_of_injOn
    (s := Finset.univ.filter (fun j : Fin m => q j ∈ Finset.univ.image t))
    (f := q) (fun a _ b _ h => hq h)).symm

/-- **Count of surviving tuple pairs.**  The ordered injective tuple pairs sharing
`≥ 2` indices number `≤ (m choose 2)·m²·n^{2m-2}` — choose `t` (`≤ nᵐ`), the two
shared slots of `q` (`≤ m.choose 2`), their values from `image t` (`≤ m²`), and
the free remaining `m-2` slots (`≤ n^{m-2}`).  Prove by an injection of the pair
set into an explicit product `Finset`. -/
private theorem card_share_ge_two_le {n : ℕ} :
    ((injectiveTuples m n ×ˢ injectiveTuples m n).filter
        (fun tq => 2 ≤ (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card
      ≤ m.choose 2 * m ^ 2 * n ^ (2 * m - 2) := by
  classical
  let share : Finset ((Fin m → Fin n) × (Fin m → Fin n)) :=
    (injectiveTuples m n ×ˢ injectiveTuples m n).filter
      (fun tq => 2 ≤ (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)
  let D := {tq : (Fin m → Fin n) × (Fin m → Fin n) // tq ∈ share}
  let encode : D → shareCountEncoding m n := fun d =>
    let t := d.1.1
    let q := d.1.2
    have hmem : d.1 ∈ share := d.2
    have hpair : d.1 ∈ injectiveTuples m n ×ˢ injectiveTuples m n :=
      (Finset.mem_filter.mp hmem).1
    have hq : Function.Injective q :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hpair).2).2
    let sp : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => q j ∈ Finset.univ.image t)
    have hspcard : 2 ≤ sp.card := by
      have hshare : 2 ≤ (Finset.univ.image t ∩ Finset.univ.image q).card :=
        (Finset.mem_filter.mp hmem).2
      rwa [sharedPositions_card_eq (m := m) (t := t) (q := q) hq]
    let s : Finset (Fin m) :=
      Classical.choose (Finset.powersetCard_nonempty.mpr hspcard)
    have hs_sp : s ∈ sp.powersetCard 2 :=
      Classical.choose_spec (Finset.powersetCard_nonempty.mpr hspcard)
    have hs_univ : s ∈ (Finset.univ : Finset (Fin m)).powersetCard 2 := by
      exact Finset.mem_powersetCard.mpr
        ⟨fun j _ => Finset.mem_univ j, (Finset.mem_powersetCard.mp hs_sp).2⟩
    let k : {j : Fin m // j ∈ s} → Fin m := fun j =>
      Classical.choose (Finset.mem_image.mp
        ((Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hs_sp).1 j.2)).2))
    let r : {j : Fin m // j ∉ s} → Fin n := fun j => q j.1
    ⟨t, ⟨⟨s, hs_univ⟩, (k, r)⟩⟩
  have hdecode : ∀ d : D, shareCountDecodeQ (encode d) = d.1.2 := by
    intro d
    funext j
    dsimp [encode, shareCountDecodeQ]
    split_ifs with hj
    · exact (Classical.choose_spec (Finset.mem_image.mp
        ((Finset.mem_filter.mp
          ((Classical.choose_spec
            (Finset.powersetCard_nonempty.mpr
              (by
                have hmem : d.1 ∈ share := d.2
                have hpair : d.1 ∈ injectiveTuples m n ×ˢ injectiveTuples m n :=
                  (Finset.mem_filter.mp hmem).1
                have hq : Function.Injective d.1.2 :=
                  (Finset.mem_filter.mp (Finset.mem_product.mp hpair).2).2
                have hshare : 2 ≤ (Finset.univ.image d.1.1 ∩ Finset.univ.image d.1.2).card :=
                  (Finset.mem_filter.mp hmem).2
                rwa [sharedPositions_card_eq (m := m) (t := d.1.1) (q := d.1.2) hq]))
            |> Finset.mem_powersetCard.mp).1 hj)).2))).2
    · rfl
  have hinj : Function.Injective encode := by
    intro d₁ d₂ h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Sigma.fst h
    · have hq := congrFun (congrArg shareCountDecodeQ h) 
      funext j
      rw [hdecode d₁, hdecode d₂] at hq
      exact hq j
  have hcardD : share.card = Fintype.card D := by
    simp [D]
  rw [show ((injectiveTuples m n ×ˢ injectiveTuples m n).filter
        (fun tq => 2 ≤ (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card =
      share.card by rfl, hcardD]
  exact le_trans (Fintype.card_le_of_injective encode hinj)
    (le_trans (shareCountEncoding_card_le m n) (by
      have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      by_cases h2 : 2 ≤ m
      · have hexp : m + (m - 2) = 2 * m - 2 := by omega
        calc
          n ^ m * m.choose 2 * m ^ 2 * n ^ (m - 2)
              = m.choose 2 * m ^ 2 * (n ^ m * n ^ (m - 2)) := by ring
          _ ≤ m.choose 2 * m ^ 2 * n ^ (2 * m - 2) := by
            rw [← Nat.pow_add, hexp]
      · have hm1 : m = 1 := by omega
        subst m
        simp))

/-- **Falling-factorial lower bound.**  For `n ≥ m`,
`n^m / m^m ≤ n.descFactorial m` (each of the `m` factors `n - i ≥ n - (m-1)`, and
`∏ (1 - i/n)` is minimized at `n = m`). -/
private theorem descFactorial_ge {n : ℕ} (hmn : m ≤ n) :
    (n : ℝ) ^ m / (m : ℝ) ^ m ≤ (n.descFactorial m : ℝ) := by
  have hmposNat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
  rw [Nat.descFactorial_eq_prod_range]
  norm_num [Nat.cast_prod]
  have hfactor : ∀ i ∈ Finset.range m, (n : ℝ) / (m : ℝ) ≤ (n - i : ℕ) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hin : i ≤ n := le_trans (Nat.le_of_lt him) hmn
    rw [Nat.cast_sub hin]
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hiR : (i : ℝ) + 1 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt him)
    have hmul : (n : ℝ) ≤ ((n : ℝ) - (i : ℝ)) * (m : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmnR)
        (sub_nonneg.mpr (by linarith : (1 : ℝ) ≤ (m : ℝ)))]
    exact (div_le_iff₀ hmpos).mpr hmul
  have hprod := Finset.prod_le_prod (s := Finset.range m)
    (f := fun _i : ℕ => (n : ℝ) / (m : ℝ))
    (g := fun i : ℕ => (n - i : ℕ))
    (fun _i _hi => div_nonneg (Nat.cast_nonneg _) (le_of_lt hmpos)) hfactor
  simpa [Finset.prod_const, div_pow] using hprod

private theorem integral_injectiveTuples_sum_sq_le_shared_count
    (hg : OrderFirstDegenKernel P g) {n : ℕ} :
    ∫ ω, (∑ t ∈ injectiveTuples m n, g (fun j => S.Z (t j : ℕ) ω)) ^ 2 ∂μ
      ≤ (((injectiveTuples m n ×ˢ injectiveTuples m n).filter
          (fun tq => 2 ≤ (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card : ℝ)
        * zetaOrder P g := by
  classical
  let T : Finset (Fin m → Fin n) := injectiveTuples m n
  let SHARE : Finset ((Fin m → Fin n) × (Fin m → Fin n)) :=
    (T ×ˢ T).filter
      (fun tq => 2 ≤ (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)
  let F : ((Fin m → Fin n) × (Fin m → Fin n)) → ℝ := fun tq =>
    ∫ ω, g (fun j => S.Z (tq.1 j : ℕ) ω) *
      g (fun j => S.Z (tq.2 j : ℕ) ω) ∂μ
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
    exact S.integrable_sqKernelTerm_mul hg.meas hg.sq
      (hinj_of_mem_T t ht) (hinj_of_mem_T q hq))]
  have hpush : ∀ t ∈ T,
      ∫ ω, ∑ q ∈ T,
        g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ
        = ∑ q ∈ T, ∫ ω,
          g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ := by
    intro t ht
    exact integral_finset_sum _ (fun q hq =>
      S.integrable_sqKernelTerm_mul hg.meas hg.sq
        (hinj_of_mem_T t ht) (hinj_of_mem_T q hq))
  rw [Finset.sum_congr rfl hpush]
  rw [show (∑ t ∈ T, ∑ q ∈ T, ∫ ω,
      g (fun j => S.Z (t j : ℕ) ω) * g (fun j => S.Z (q j : ℕ) ω) ∂μ)
      = ∑ tq ∈ T ×ˢ T, F tq by
    rw [Finset.sum_product]]
  have hsub : SHARE ⊆ T ×ˢ T := Finset.filter_subset _ _
  have hzero : ∀ x ∈ T ×ˢ T, x ∉ SHARE → F x = 0 := by
    intro x hx hxnot
    have ht : Function.Injective x.1 := hinj_of_mem_T x.1 (Finset.mem_product.mp hx).1
    have hq : Function.Injective x.2 := hinj_of_mem_T x.2 (Finset.mem_product.mp hx).2
    have hcard : (Finset.univ.image x.1 ∩ Finset.univ.image x.2).card ≤ 1 := by
      have : ¬ 2 ≤ (Finset.univ.image x.1 ∩ Finset.univ.image x.2).card := by
        intro h2
        exact hxnot (Finset.mem_filter.mpr ⟨hx, h2⟩)
      omega
    simpa [F] using S.crossterm_eq_zero_of_shared_le_one hg ht hq hcard
  rw [← Finset.sum_subset hsub hzero]
  have hterm_le : ∀ x ∈ SHARE, F x ≤ zetaOrder P g := by
    intro x hx
    have hxT : x ∈ T ×ˢ T := (Finset.mem_filter.mp hx).1
    have ht : Function.Injective x.1 := hinj_of_mem_T x.1 (Finset.mem_product.mp hxT).1
    have hq : Function.Injective x.2 := hinj_of_mem_T x.2 (Finset.mem_product.mp hxT).2
    exact le_trans (le_abs_self (F x)) (by
      simpa [F] using S.crossterm_abs_le_zeta hg ht hq)
  have hsum := Finset.sum_le_card_nsmul SHARE F (zetaOrder P g) hterm_le
  simpa [SHARE, T, nsmul_eq_mul] using hsum

private theorem rescaled_order_normalization_le {n : ℕ} (hmn : m ≤ n) {ζ : ℝ}
    (hζ : 0 ≤ ζ) :
    (n : ℝ) * (injectiveTupleCount m n)⁻¹ ^ 2 *
        ((m.choose 2 : ℝ) * (m : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2) * ζ)
      ≤ ((m.choose 2 : ℝ) * (m : ℝ) ^ (2 * m + 2) * ζ) / (n : ℝ) := by
  have hmposNat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hnposNat : 0 < n := lt_of_lt_of_le hmposNat hmn
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hDpos : 0 < (n.descFactorial m : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hmn
  have hDlower : (n : ℝ) ^ m / (m : ℝ) ^ m ≤ (n.descFactorial m : ℝ) :=
    descFactorial_ge (m := m) hmn
  have hlower_pos : 0 < (n : ℝ) ^ m / (m : ℝ) ^ m := by positivity
  have hinv :
      ((n.descFactorial m : ℝ)⁻¹) ≤ ((m : ℝ) ^ m / (n : ℝ) ^ m) := by
    have h := inv_anti₀ hlower_pos hDlower
    have hrewrite :
        ((n : ℝ) ^ m / (m : ℝ) ^ m)⁻¹ = (m : ℝ) ^ m / (n : ℝ) ^ m := by
      field_simp [pow_ne_zero _ hmpos.ne', pow_ne_zero _ hnpos.ne']
    simpa [hrewrite] using h
  have hinv_sq :
      ((n.descFactorial m : ℝ)⁻¹) ^ 2
        ≤ ((m : ℝ) ^ m / (n : ℝ) ^ m) ^ 2 := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr hDpos.le) hinv 2
  rw [injectiveTupleCount_eq_descFactorial]
  calc
    (n : ℝ) * ((n.descFactorial m : ℝ)⁻¹) ^ 2 *
        ((m.choose 2 : ℝ) * (m : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2) * ζ)
        ≤ (n : ℝ) * ((m : ℝ) ^ m / (n : ℝ) ^ m) ^ 2 *
          ((m.choose 2 : ℝ) * (m : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2) * ζ) := by
          gcongr
    _ = ((m.choose 2 : ℝ) * (m : ℝ) ^ (2 * m + 2) * ζ) / (n : ℝ) := by
      have hpow_n : (n : ℝ) ^ 2 * (n : ℝ) ^ (m * 2 - 2) = (n : ℝ) ^ (m * 2) := by
        rw [← pow_add]
        congr 1
        omega
      have hpow_n' : (n : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2) = (n : ℝ) ^ (2 * m) := by
        rw [← pow_add]
        congr 1
        omega
      have hpow_m :
          ((m : ℝ) ^ m) ^ 2 * (m : ℝ) ^ 2 = (m : ℝ) ^ (2 * m + 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      have hpow_n_rhs : ((n : ℝ) ^ m) ^ 2 = (n : ℝ) ^ (2 * m) := by
        rw [← pow_mul]
        congr 1
        omega
      field_simp [pow_ne_zero _ hnpos.ne', pow_ne_zero _ hmpos.ne']
      calc
        (n : ℝ) ^ 2 * ((m : ℝ) ^ m) ^ 2 * (m.choose 2 : ℝ) *
              (m : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2) * ζ
            = (m.choose 2 : ℝ) * ζ * (((m : ℝ) ^ m) ^ 2 * (m : ℝ) ^ 2) *
                ((n : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2)) := by ring
        _ = (m.choose 2 : ℝ) * ζ * (m : ℝ) ^ (2 * m + 2) * (n : ℝ) ^ (2 * m) := by
          rw [hpow_m, hpow_n']
        _ = ((n : ℝ) ^ m) ^ 2 * (m.choose 2 : ℝ) * ζ * (m : ℝ) ^ (2 * m + 2) := by
          rw [hpow_n_rhs]
          ring

private theorem integral_rescaled_order_sq_le_counting_normalization
    (hg : OrderFirstDegenKernel P g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, m ≤ n →
      ∫ ω, (Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) ^ 2 ∂μ ≤ C / (n : ℝ) := by
  classical
  let C : ℝ := (m.choose 2 : ℝ) * (m : ℝ) ^ (2 * m + 2) * zetaOrder P g
  have hzeta : 0 ≤ zetaOrder P g := zetaOrder_nonneg
  refine ⟨C, ?_, ?_⟩
  · positivity
  · intro n hmn
    have hmposNat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hnposNat : 0 < n := lt_of_lt_of_le hmposNat hmn
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnnonneg
    let K : Ω → ℝ := fun ω =>
      ∑ t ∈ injectiveTuples m n, g (fun j => S.Z (t j : ℕ) ω)
    have hpoint :
        (fun ω => (Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) ^ 2)
          = fun ω => ((n : ℝ) * (injectiveTupleCount m n)⁻¹ ^ 2) * (K ω) ^ 2 := by
      funext ω
      simp only [K, uStatisticOrder]
      rw [mul_pow, hsqrt, mul_pow]
      ring
    have hscale_nonneg : 0 ≤ (n : ℝ) * (injectiveTupleCount m n)⁻¹ ^ 2 := by
      positivity
    have hsum_le :
        ∫ ω, (K ω) ^ 2 ∂μ
          ≤ (((injectiveTuples m n ×ˢ injectiveTuples m n).filter
              (fun tq => 2 ≤
                (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card : ℝ)
            * zetaOrder P g := by
      simpa [K] using S.integral_injectiveTuples_sum_sq_le_shared_count hg (n := n)
    have hcard_le :
        (((injectiveTuples m n ×ˢ injectiveTuples m n).filter
            (fun tq => 2 ≤
              (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card : ℝ)
          * zetaOrder P g
        ≤ ((m.choose 2 : ℝ) * (m : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2))
          * zetaOrder P g := by
      have hcardNat := card_share_ge_two_le (m := m) (n := n)
      have hcardCast :
          (((injectiveTuples m n ×ˢ injectiveTuples m n).filter
              (fun tq => 2 ≤
                (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card : ℝ)
            ≤ ((m.choose 2 * m ^ 2 * n ^ (2 * m - 2) : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      calc
        (((injectiveTuples m n ×ˢ injectiveTuples m n).filter
            (fun tq => 2 ≤
              (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card : ℝ)
          * zetaOrder P g
            ≤ ((m.choose 2 * m ^ 2 * n ^ (2 * m - 2) : ℕ) : ℝ)
              * zetaOrder P g := by
                exact mul_le_mul_of_nonneg_right hcardCast hzeta
        _ = ((m.choose 2 : ℝ) * (m : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2))
              * zetaOrder P g := by
                norm_num [Nat.cast_mul, Nat.cast_pow]
    calc
      ∫ ω, (Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) ^ 2 ∂μ
          = (n : ℝ) * (injectiveTupleCount m n)⁻¹ ^ 2 * ∫ ω, (K ω) ^ 2 ∂μ := by
            rw [hpoint, integral_const_mul]
      _ ≤ (n : ℝ) * (injectiveTupleCount m n)⁻¹ ^ 2 *
            ((((injectiveTuples m n ×ˢ injectiveTuples m n).filter
              (fun tq => 2 ≤
                (Finset.univ.image tq.1 ∩ Finset.univ.image tq.2).card)).card : ℝ)
              * zetaOrder P g) := by
            exact mul_le_mul_of_nonneg_left hsum_le hscale_nonneg
      _ ≤ (n : ℝ) * (injectiveTupleCount m n)⁻¹ ^ 2 *
            (((m.choose 2 : ℝ) * (m : ℝ) ^ 2 * (n : ℝ) ^ (2 * m - 2))
              * zetaOrder P g) := by
            exact mul_le_mul_of_nonneg_left hcard_le hscale_nonneg
      _ ≤ C / (n : ℝ) := by
            simpa [C, mul_assoc] using
              rescaled_order_normalization_le (m := m) (n := n) hmn hzeta

/-- **`L²` bound on the rescaled higher-order remainder.**  For a first-order
degenerate order-`m` kernel there is a constant `C` (depending only on `m` and
`ζ_m = E[g²]`) with `E[(√n · Uₙ)²] ≤ C / n` for all `n ≥ m`.  This is the
keystone estimate; it packages cross-term vanishing, the Cauchy–Schwarz bound
`|E[g_t g_q]| ≤ ζ_m`, the `O(n^{2m-2})` count of surviving tuple pairs, and the
`n · (n^{(m)})⁻²` normalization. -/
theorem integral_rescaled_order_sq_le (hg : OrderFirstDegenKernel P g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, m ≤ n →
      ∫ ω, (Real.sqrt (n : ℝ) * uStatisticOrder S g n ω) ^ 2 ∂μ ≤ C / (n : ℝ) := by
  exact S.integral_rescaled_order_sq_le_counting_normalization hg

end IIDSample

end Causalean.Stat
