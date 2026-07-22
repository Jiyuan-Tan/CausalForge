/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.KeyIdentity
import Causalean.Discovery.LinearDisentanglement.PartialOrderRQ
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Linear causal disentanglement: the rowspan inclusion lemma (Lemma 1)

The technical heart linking the *observable* precision differences to the *latent*
graph structure (their Lemma 1).  By `key_identity`, `rowspan(Θₖ − Θ₀)` is spanned by
the two vectors `Hᵀ Bₖᵀ e_{iₖ}`, `Hᵀ B₀ᵀ e_{iₖ}`, both lying in `⟨hᵢ : i ∈ Pa(iₖ)⟩`.
Full row rank of `H` makes this containment *characterize* the parent set:

* (a) `rowspan(Θₖ − Θ₀) ⊆ ⟨hᵢ : i ∈ 𝓘⟩` iff `Pa(iₖ) ⊆ 𝓘`;
* (b) `rowspan(Θₖ − Θ₀) ⊆ ⟨qᵢ : i ∈ An(iₖ)⟩`;
* (c) if the intervention changes the precision matrix, `𝓘` is ancestor-closed, and
  `Pa(iₖ) ⊄ 𝓘`, then `rowspan(Θₖ − Θ₀) ⊄ ⟨qᵢ : i ∈ 𝓘⟩`.

The file also defines the three spans used in those statements: `rowSpan` for rows
of an observable precision-difference matrix, `hSpan` for selected rows of the
mixing pseudoinverse `H`, and `qSpan` for selected rows of a partial-order RQ
factor `Q`.
-/

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-- The row span of a `p × p` matrix: the subspace of `Fin p → ℝ` spanned by its rows. -/
noncomputable def rowSpan (M : Matrix (Fin p) (Fin p) ℝ) : Submodule ℝ (Fin p → ℝ) :=
  Submodule.span ℝ (Set.range (fun i => M i))

/-- The span of the rows of `H` indexed by a set `𝓘 ⊆ [d]`. -/
noncomputable def hSpan (S : Solution d p K) (I : Set (Fin d)) : Submodule ℝ (Fin p → ℝ) :=
  Submodule.span ℝ ((fun i => (S.H i : Fin p → ℝ)) '' I)

/-- The span of the rows of `Q` (from a partial order RQ decomposition) indexed by `𝓘`. -/
noncomputable def qSpan (Q : Matrix (Fin d) (Fin p) ℝ) (I : Set (Fin d)) :
    Submodule ℝ (Fin p → ℝ) :=
  Submodule.span ℝ ((fun i => (Q i : Fin p → ℝ)) '' I)

/-- `qSpan` is monotone in the index set. -/
private theorem qSpan_mono (Q : Matrix (Fin d) (Fin p) ℝ) {I J : Set (Fin d)} (h : I ⊆ J) :
    qSpan Q I ≤ qSpan Q J :=
  Submodule.span_mono (Set.image_mono h)

/-- The vector `Hᵀ (Mᵀ e_i)` is the linear combination `∑ⱼ Mᵢⱼ hⱼ` of the rows of `H`,
where `Mᵢⱼ` is the `(i,j)` entry of `M` and `hⱼ` the `j`-th row of `H`.  This is the
algebraic heart of Lemma 1: it rewrites the two spanning vectors of `key_identity` as
explicit combinations of the rows of `H`. -/
private theorem H_mulVec_row (S : Solution d p K) (M : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) :
    S.H.transpose *ᵥ (M.transpose *ᵥ stdVec d i) = ∑ j, (M i j) • (S.H j) := by
  rw [stdVec, Matrix.mulVec_single_one, Matrix.mulVec_transpose, Matrix.vecMul_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.col_apply, Matrix.transpose_apply]

/-- The rows of an outer-product difference `u uᵀ − v vᵀ` lie in `span{u, v}`; hence its
row span is contained in `span{u, v}`.  (Each row `a` equals `uₐ • u − vₐ • v`.) -/
private theorem rowSpan_vecMulVec_sub_le {q : ℕ} (u v : Fin q → ℝ) :
    rowSpan (Matrix.vecMulVec u u - Matrix.vecMulVec v v)
      ≤ Submodule.span ℝ {u, v} := by
  rw [rowSpan, Submodule.span_le]
  rintro x ⟨a, rfl⟩
  have hrow : (Matrix.vecMulVec u u - Matrix.vecMulVec v v) a = u a • u - v a • v := by
    funext b
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  change (Matrix.vecMulVec u u - Matrix.vecMulVec v v) a ∈ Submodule.span ℝ {u, v}
  rw [hrow]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- A combination `∑ⱼ cⱼ hⱼ` of the rows of `H` lies in `⟨hᵢ : i ∈ 𝓘⟩` whenever the
support of `c` is contained in `𝓘`. -/
private theorem sum_smul_H_mem_hSpan (S : Solution d p K) (c : Fin d → ℝ)
    (I : Set (Fin d)) (hc : ∀ j, c j ≠ 0 → j ∈ I) :
    (∑ j, c j • S.H j) ∈ hSpan S I := by
  apply Submodule.sum_mem
  intro j _
  by_cases hj : c j = 0
  · simp [hj]
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hc j hj, rfl⟩)

/-- A linear combination `∑ⱼ cⱼ hⱼ` of the (linearly independent) rows of `H` equals
the zero vector only if every coefficient vanishes. -/
private theorem coeff_eq_zero_of_sum_eq_zero (S : Solution d p K) (c : Fin d → ℝ)
    (hzero : (∑ j, c j • S.H j) = 0) (j : Fin d) : c j = 0 :=
  linearIndependent_iff'.1 S.hH Finset.univ c hzero j (Finset.mem_univ j)

/-- If a combination `∑ⱼ cⱼ hⱼ` of the rows of `H` lies in `⟨hᵢ : i ∈ 𝓘⟩` then every
coefficient on an index *outside* `𝓘` vanishes.  This is the converse-flavoured
counterpart to `sum_smul_H_mem_hSpan`, and the only place linear independence of the
rows of `H` (`S.hH`) is used to *read off* coordinates. -/
private theorem coeff_eq_zero_of_sum_mem_hSpan (S : Solution d p K) (c : Fin d → ℝ)
    (I : Set (Fin d)) (hmem : (∑ j, c j • S.H j) ∈ hSpan S I) {j : Fin d} (hj : j ∉ I) :
    c j = 0 := by
  rw [hSpan, Finsupp.mem_span_image_iff_linearCombination] at hmem
  obtain ⟨l, hlsupp, hl⟩ := hmem
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
  -- Extend the sum over `l.support` to a sum over all of `Fin d` (zero off support).
  have hlfull : (∑ i, l i • S.H i) = ∑ j, c j • S.H j := by
    rw [← hl, eq_comm, Finset.sum_subset (Finset.subset_univ _)]
    intro i _ hi
    rw [Finsupp.notMem_support_iff.1 hi, zero_smul]
  -- Hence `∑ i, (l i - c i) • h i = 0`, so `l j = c j` for all `j` by independence.
  have hcomb : (∑ i, (l i - c i) • S.H i) = 0 := by
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, hlfull, sub_self]
  have hlj : l j - c j = 0 := coeff_eq_zero_of_sum_eq_zero S (fun i => l i - c i) hcomb j
  have hlj0 : l j = 0 := Finsupp.notMem_support_iff.1 (fun h => hj (hlsupp h))
  linarith [hlj, hlj0]

/-- The support of the `iₖ`-th row of `B₀` is contained in `Pa(iₖ)`: an off-diagonal
nonzero entry is an edge into `iₖ` (a parent), and the diagonal index is `iₖ` itself. -/
private theorem B0_row_support_subset_Pa (S : Solution d p K) (k : Fin K) :
    ∀ j, S.B0 (S.target k) j ≠ 0 → j ∈ S.Pa (S.target k) := by
  intro j hj
  by_cases hji : j = S.target k
  · exact hji ▸ Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ((S.hB0supp (S.target k) j (Ne.symm hji)).1 hj)

/-- The support of the `iₖ`-th row of `Bₖ` is `{iₖ}` (a perfect intervention zeroes out
all incoming edges of the target), hence contained in `Pa(iₖ)`. -/
private theorem Bint_row_support_subset_Pa (S : Solution d p K) (k : Fin K) :
    ∀ j, S.Bint k (S.target k) j ≠ 0 → j ∈ S.Pa (S.target k) := by
  intro j hj
  by_cases hji : j = S.target k
  · exact hji ▸ Set.mem_insert _ _
  · exfalso; apply hj
    rw [S.hInt k]
    simp [Matrix.add_apply, Matrix.vecMulVec_apply, stdVec, Pi.single_eq_of_ne hji]

/-- Off-diagonal entries of the target row of `Bₖ` vanish: a perfect intervention
removes every incoming edge of `iₖ`, so `(Bₖ)_{iₖ,j} = 0` for `j ≠ iₖ`. -/
private theorem Bint_target_offdiag (S : Solution d p K) (k : Fin K) {j : Fin d}
    (hj : j ≠ S.target k) : S.Bint k (S.target k) j = 0 := by
  rw [S.hInt k]
  simp [Matrix.add_apply, Matrix.vecMulVec_apply, stdVec, Pi.single_eq_of_ne hj]

/-- The diagonal entry of the target row of `Bₖ` is the intervention scaling `λₖ`:
`(Bₖ)_{iₖ,iₖ} = λₖ`. -/
private theorem Bint_target_diag (S : Solution d p K) (k : Fin K) :
    S.Bint k (S.target k) (S.target k) = S.lam k := by
  rw [S.hInt k]
  simp [Matrix.add_apply, Matrix.vecMulVec_apply, stdVec]

/-- The core containment from `key_identity`: `rowspan(Θₖ − Θ₀) ⊆ ⟨hᵢ : i ∈ Pa(iₖ)⟩`.
Both spanning vectors of the rank-≤2 difference are combinations of rows of `H` whose
support sits in the parent set of the target. -/
private theorem rowSpan_le_hSpan_Pa (S : Solution d p K) (k : Fin K) :
    rowSpan (S.Theta k - S.Theta0) ≤ hSpan S (S.Pa (S.target k)) := by
  rw [key_identity, H_mulVec_row, H_mulVec_row]
  refine le_trans (rowSpan_vecMulVec_sub_le _ _) ?_
  rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨sum_smul_H_mem_hSpan S _ _ (Bint_row_support_subset_Pa S k),
    sum_smul_H_mem_hSpan S _ _ (B0_row_support_subset_Pa S k)⟩

/-- **The coordinate relation behind Lemma 1(a)→.**  Write `u = ∑ᵢ (Bₖ)_{iₖ,i} hᵢ` and
`v = ∑ᵢ (B₀)_{iₖ,i} hᵢ` for the two `key_identity` vectors.  If `rowspan(Θₖ−Θ₀) ⊆
⟨hᵢ : i∈𝓘⟩` and `j ∉ 𝓘`, then for every row index `a`,
`uₐ · (Bₖ)_{iₖ,j} = vₐ · (B₀)_{iₖ,j}`.  Reason: row `a` of `Θₖ−Θ₀` is `uₐ•u − vₐ•v =
∑ᵢ (uₐ(Bₖ)_{iₖ,i} − vₐ(B₀)_{iₖ,i}) hᵢ ∈ ⟨hᵢ:i∈𝓘⟩`, so its `hⱼ`-coefficient vanishes by
linear independence of the rows of `H`. -/
private theorem coord_eq_of_rowSpan_le (S : Solution d p K) (k : Fin K) (I : Set (Fin d))
    (hsub : rowSpan (S.Theta k - S.Theta0) ≤ hSpan S I) {j : Fin d} (hjI : j ∉ I)
    (a : Fin p) :
    (∑ i, S.Bint k (S.target k) i • S.H i) a * S.Bint k (S.target k) j
      = (∑ i, S.B0 (S.target k) i • S.H i) a * S.B0 (S.target k) j := by
  set u : Fin p → ℝ := ∑ i, S.Bint k (S.target k) i • S.H i with hu
  set v : Fin p → ℝ := ∑ i, S.B0 (S.target k) i • S.H i with hv
  -- `Θₖ − Θ₀ = u u ᵀ − v v ᵀ`.
  have hid : S.Theta k - S.Theta0 = Matrix.vecMulVec u u - Matrix.vecMulVec v v := by
    rw [key_identity, hu, hv, H_mulVec_row, H_mulVec_row]
  -- Row `a` of the difference, as a combination of the rows of `H`.
  have hrowcomb :
      (Matrix.vecMulVec u u - Matrix.vecMulVec v v) a
        = ∑ i, (u a * S.Bint k (S.target k) i - v a * S.B0 (S.target k) i) • S.H i := by
    have hrow : (Matrix.vecMulVec u u - Matrix.vecMulVec v v) a = u a • u - v a • v := by
      funext b
      simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [hrow, hu, hv, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul, smul_smul, sub_smul]
  -- That row lies in `hSpan S I`.
  have hmemI : (∑ i, (u a * S.Bint k (S.target k) i - v a * S.B0 (S.target k) i) • S.H i)
      ∈ hSpan S I := by
    rw [← hrowcomb, ← hid]
    apply hsub
    exact Submodule.subset_span ⟨a, rfl⟩
  -- Coefficient at `j ∉ 𝓘` vanishes.
  have hzero := coeff_eq_zero_of_sum_mem_hSpan S
    (fun i => u a * S.Bint k (S.target k) i - v a * S.B0 (S.target k) i) I hmemI hjI
  linarith [hzero]

/-- **Lemma 1(a).**  Under the non-degeneracy hypothesis `Θₖ ≠ Θ₀` (the paper's
genericity / Assumption (b) — the intervention actually changes the precision matrix),
`rowspan(Θₖ − Θ₀) ⊆ ⟨hᵢ : i ∈ 𝓘⟩` iff `Pa(iₖ) ⊆ 𝓘`.

The `←` direction is unconditional; `hk` is used only in the `→` direction (and there
only in the case where the witnessed parent is the target itself, to rule out the
degenerate `λₖ = (B₀)_{iₖ,iₖ}` configuration that would make `Θₖ = Θ₀`). -/
theorem rowspan_inclusion_a (S : Solution d p K) (k : Fin K) (I : Set (Fin d))
    (hk : S.Theta k ≠ S.Theta0) :
    rowSpan (S.Theta k - S.Theta0) ≤ hSpan S I ↔ S.Pa (S.target k) ⊆ I := by
  constructor
  · -- Forward direction.  Take `j ∈ Pa(iₖ)`; suppose `j ∉ I` for contradiction.
    intro hsub j hj
    by_contra hjI
    -- The two `key_identity` vectors `u = ∑ᵢ (Bₖ)_{iₖ,i} hᵢ`, `v = ∑ᵢ (B₀)_{iₖ,i} hᵢ`.
    set u : Fin p → ℝ := ∑ i, S.Bint k (S.target k) i • S.H i with hu
    set v : Fin p → ℝ := ∑ i, S.B0 (S.target k) i • S.H i with hv
    -- `v ≠ 0`: its `h_{iₖ}` coefficient is `(B₀)_{iₖ,iₖ} > 0`.
    have hv_ne : v ≠ 0 := by
      intro h0
      exact absurd (coeff_eq_zero_of_sum_eq_zero S _ h0 (S.target k))
        (ne_of_gt (S.hB0pos (S.target k)))
    -- `Θₖ − Θ₀ = u uᵀ − v vᵀ`.
    have hid : S.Theta k - S.Theta0 = Matrix.vecMulVec u u - Matrix.vecMulVec v v := by
      rw [key_identity, hu, hv, H_mulVec_row, H_mulVec_row]
    -- The coordinate relation (★): `∀ a, uₐ (Bₖ)_{iₖ,j} = vₐ (B₀)_{iₖ,j}`.
    have huv := coord_eq_of_rowSpan_le S k I hsub hjI
    rw [← hu, ← hv] at huv
    by_cases hji : j = S.target k
    · -- Case `j = iₖ`: here non-degeneracy `hk` is needed.
      subst hji
      -- `(Bₖ)_{j,j} = λₖ`, `(B₀)_{j,j} = β > 0`; (★) becomes `λₖ uₐ = β vₐ`.
      have hbk : S.Bint k (S.target k) (S.target k) = S.lam k := Bint_target_diag S k
      set β : ℝ := S.B0 (S.target k) (S.target k) with hβ
      have hβpos : 0 < β := S.hB0pos (S.target k)
      set s : ℝ := β / S.lam k with hs
      -- `u = s • v` from (★) and `λₖ > 0`.
      have hus : u = s • v := by
        funext a
        have ha := huv a
        rw [hbk] at ha
        rw [Pi.smul_apply, smul_eq_mul, hs, div_mul_eq_mul_div, eq_div_iff (ne_of_gt (S.hlam k))]
        linarith [ha]
      -- Hence `Θₖ − Θ₀ = (s² − 1) • (v vᵀ)`.
      have hdiff : S.Theta k - S.Theta0 = (s ^ 2 - 1) • Matrix.vecMulVec v v := by
        rw [hid, hus]
        ext a b
        simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply,
          smul_eq_mul]
        ring
      -- Pick `a` with `vₐ ≠ 0`; then row `a` of the difference recovers `v ∈ hSpan S I`.
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hv_ne
      rw [Pi.zero_apply] at ha
      -- `s² ≠ 1`, else `Θₖ = Θ₀`, contradicting `hk`.
      have hs2 : s ^ 2 - 1 ≠ 0 := by
        intro h
        exact hk (sub_eq_zero.mp (by rw [hdiff, h, zero_smul]))
      have hcoef : (s ^ 2 - 1) * v a ≠ 0 := mul_ne_zero hs2 ha
      -- Row `a` of `Θₖ − Θ₀` equals `((s²−1) vₐ) • v`, and lies in `hSpan S I`.
      have hrow_mem : ((s ^ 2 - 1) * v a) • v ∈ hSpan S I := by
        have : ((s ^ 2 - 1) * v a) • v = (S.Theta k - S.Theta0) a := by
          funext b
          rw [hdiff]
          simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [this]
        exact hsub (Submodule.subset_span ⟨a, rfl⟩)
      -- Scale to land `v ∈ hSpan S I`.
      have hv_mem : v ∈ hSpan S I := by
        have := Submodule.smul_mem (hSpan S I) ((s ^ 2 - 1) * v a)⁻¹ hrow_mem
        rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at this
      -- But `v = ∑ᵢ (B₀)_{iₖ,i} hᵢ` with `(B₀)_{j,j} = β ≠ 0` and `j ∉ I`. Contradiction.
      exact absurd (coeff_eq_zero_of_sum_mem_hSpan S _ I hv_mem hjI) (ne_of_gt hβpos)
    · -- Case `j ≠ iₖ` (a proper parent): `(Bₖ)_{iₖ,j} = 0`, `(B₀)_{iₖ,j} ≠ 0`. No `hk` needed.
      have hbk0 : S.Bint k (S.target k) j = 0 := Bint_target_offdiag S k hji
      -- `j ∈ pa(iₖ)`, i.e. an edge `j → iₖ`, so `(B₀)_{iₖ,j} ≠ 0`.
      have hedge : S.Edge j (S.target k) := by
        rcases hj with h | h
        · exact absurd h hji
        · exact h
      have hb0_ne : S.B0 (S.target k) j ≠ 0 := (S.hB0supp (S.target k) j (Ne.symm hji)).2 hedge
      -- (★) with `(Bₖ)_{iₖ,j} = 0` gives `vₐ (B₀)_{iₖ,j} = 0`, so `vₐ = 0` for all `a`.
      have hv0 : v = 0 := by
        funext a
        have ha := huv a
        rw [hbk0, mul_zero] at ha
        exact (mul_eq_zero.mp ha.symm).resolve_right hb0_ne
      exact hv_ne hv0
  · -- Backward direction (unconditional): `Pa(iₖ) ⊆ I ⟹ rowSpan(Θₖ − Θ₀) ≤ ⟨hᵢ : i∈I⟩`.
    intro hPa
    refine le_trans (rowSpan_le_hSpan_Pa S k) ?_
    exact Submodule.span_mono (Set.image_mono hPa)

/-- `i ⪯ j` (support relation of `R`) is the same as `j ∈ An(i)`. -/
private theorem preceq_iff_mem_An (S : Solution d p K) (i j : Fin d) :
    S.preceq i j ↔ j ∈ S.An i := by
  unfold Solution.preceq Solution.An Solution.anc Solution.prec
  simp only [Set.mem_insert_iff, Set.mem_setOf_eq, eq_comm]

/-- Each row `hᵢ` of `H` lies in `⟨qⱼ : j ∈ An(i)⟩`.  From `H = R Q` (so `hᵢ = ∑ⱼ Rᵢⱼ qⱼ`)
together with the support condition `Rᵢⱼ = 0` unless `i ⪯ j`, i.e. `j ∈ An(i)`. -/
private theorem H_row_mem_qSpan_An (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ} (hRQ : IsPORQ S R Q)
    (i : Fin d) :
    S.H i ∈ qSpan Q (S.An i) := by
  have hrow : S.H i = ∑ j, R i j • Q j := by
    rw [hRQ.factor]
    funext a
    rw [Matrix.mul_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => rfl)
  rw [hrow]
  apply Submodule.sum_mem
  intro j _
  by_cases hj : R i j = 0
  · simp [hj]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_, rfl⟩)
    rw [← preceq_iff_mem_An]
    exact not_not.1 (fun h => hj (hRQ.supp i j h))

/-- For `i ∈ Pa(iₖ)` we have `An(i) ⊆ An(iₖ)`: parents are ancestors and ancestorship is
transitive. -/
private theorem An_subset_An_of_mem_Pa (S : Solution d p K) (k : Fin K) {i : Fin d}
    (hi : i ∈ S.Pa (S.target k)) : S.An i ⊆ S.An (S.target k) := by
  -- First: `i ∈ An(iₖ)`.
  have hi_anc : i ∈ S.An (S.target k) := by
    rcases hi with hi | hi
    · exact hi ▸ Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Relation.TransGen.single hi)
  intro x hx
  rcases hx with hx | hx
  · exact hx ▸ hi_anc
  · -- `x ∈ anc(i)` and `i ∈ An(iₖ)`; conclude `x ∈ An(iₖ)` by transitivity.
    rcases hi_anc with hi' | hi'
    · exact hi' ▸ Set.mem_insert_of_mem _ hx
    · exact Set.mem_insert_of_mem _ (Relation.TransGen.trans hx hi')

/-- **Lemma 1(b).**  `rowspan(Θₖ − Θ₀) ⊆ ⟨qᵢ : i ∈ An(iₖ)⟩`. -/
theorem rowspan_inclusion_b (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ} (hRQ : IsPORQ S R Q)
    (k : Fin K) :
    rowSpan (S.Theta k - S.Theta0) ≤ qSpan Q (S.An (S.target k)) := by
  refine le_trans (rowSpan_le_hSpan_Pa S k) ?_
  rw [hSpan, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  exact qSpan_mono Q (An_subset_An_of_mem_Pa S k hi) (H_row_mem_qSpan_An S hRQ i)

/-- A linear combination `∑ₐ cₐ • (M a)` of the rows of `M` lies in `rowSpan M`. -/
private theorem sum_smul_row_mem_rowSpan {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (c : Fin q → ℝ) : (∑ a, c a • M a) ∈ rowSpan M := by
  apply Submodule.sum_mem
  intro a _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- **The Gram extraction lemma.**  For real vectors `u, v` with `v ≠ 0`, if the rank-≤2
outer-product difference `M = u uᵀ − v vᵀ` is nonzero, then `v ∈ rowSpan M`.  Two linear
combinations of the rows of `M` are `w₀ = (u·u)u − (u·v)v` and `w₁ = (u·v)u − (v·v)v`; the
Gram combination `(u·v)•w₀ − (u·u)•w₁ = G • v` with Gram determinant
`G = (u·u)(v·v) − (u·v)²`.  If `G ≠ 0`, `v` is a multiple of `G•v ∈ rowSpan`.  If `G = 0`
the vectors are dependent (`u = s•v`); then `M = (s²−1) v vᵀ ≠ 0`, and
`w₁ = (v·v)(s²−1)•v` is a nonzero multiple of `v` in `rowSpan`. -/
private theorem vec_mem_rowSpan_vecMulVec_sub {q : ℕ} {u v : Fin q → ℝ} (hv : v ≠ 0)
    (hM : Matrix.vecMulVec u u - Matrix.vecMulVec v v ≠ 0) :
    v ∈ rowSpan (Matrix.vecMulVec u u - Matrix.vecMulVec v v) := by
  set M : Matrix (Fin q) (Fin q) ℝ := Matrix.vecMulVec u u - Matrix.vecMulVec v v with hMdef
  -- The `a`-th row of `M`.
  have hrow : ∀ a, M a = u a • u - v a • v := by
    intro a; funext b
    simp only [hMdef, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
  -- `w₀ = (u·u)u − (u·v)v` and `w₁ = (u·v)u − (v·v)v`, both in `rowSpan`.
  set w0 : Fin q → ℝ := ∑ a, u a • M a with hw0
  set w1 : Fin q → ℝ := ∑ a, v a • M a with hw1
  have hw0_mem : w0 ∈ rowSpan M := sum_smul_row_mem_rowSpan M u
  have hw1_mem : w1 ∈ rowSpan M := sum_smul_row_mem_rowSpan M v
  have hw0_eq : w0 = (u ⬝ᵥ u) • u - (u ⬝ᵥ v) • v := by
    rw [hw0]
    simp_rw [hrow, smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [dotProduct, dotProduct]
  have hw1_eq : w1 = (u ⬝ᵥ v) • u - (v ⬝ᵥ v) • v := by
    rw [hw1]
    simp_rw [hrow, smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [show (∑ a, v a * u a) = u ⬝ᵥ v by
      rw [dotProduct]; exact Finset.sum_congr rfl (fun a _ => mul_comm _ _),
      show (∑ a, v a * v a) = v ⬝ᵥ v from rfl]
  -- Gram combination: `(u·v)•w₀ − (u·u)•w₁ = G • v`, hence `G • v ∈ rowSpan`.
  set G : ℝ := (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) * (u ⬝ᵥ v) with hGdef
  have hcombo : (u ⬝ᵥ v) • w0 - (u ⬝ᵥ u) • w1 = G • v := by
    rw [hw0_eq, hw1_eq, hGdef]; module
  have hGv_mem : G • v ∈ rowSpan M := by
    rw [← hcombo]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hw0_mem) (Submodule.smul_mem _ _ hw1_mem)
  have hvv_pos : 0 < v ⬝ᵥ v := dotProduct_self_pos hv
  by_cases hG : G = 0
  · -- Degenerate (Gram-singular) case: `u` and `v` are linearly dependent.
    set s : ℝ := (u ⬝ᵥ v) / (v ⬝ᵥ v) with hs
    -- `(u − s•v) ⬝ᵥ (u − s•v) = G / (v·v) = 0`, so `u = s • v`.
    have hres0 : (u - s • v) ⬝ᵥ (u - s • v) = 0 := by
      have hvvne : (v ⬝ᵥ v) ≠ 0 := ne_of_gt hvv_pos
      simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
        smul_eq_mul, hs]
      rw [dotProduct_comm v u]
      field_simp
      rw [hGdef] at hG
      ring_nf
      ring_nf at hG
      linarith [hG]
    have husv : u = s • v := by
      by_contra hne
      have hdiff : u - s • v ≠ 0 := fun h => hne (by rwa [sub_eq_zero] at h)
      exact absurd hres0 (ne_of_gt (dotProduct_self_pos hdiff))
    -- `M = (s²−1) • (v vᵀ)`, so `s² − 1 ≠ 0` (else `M = 0`).
    have hM_eq : M = (s ^ 2 - 1) • Matrix.vecMulVec v v := by
      rw [hMdef, husv]
      ext a b
      simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    have hs2 : s ^ 2 - 1 ≠ 0 := by
      intro h
      exact hM (by rw [hM_eq, h, zero_smul])
    -- `w₁ = (v·v)(s²−1) • v`, a nonzero multiple of `v` in `rowSpan`.
    have hw1_v : w1 = ((v ⬝ᵥ v) * (s ^ 2 - 1)) • v := by
      rw [hw1_eq, husv, smul_dotProduct, smul_eq_mul]; module
    have hcoef : (v ⬝ᵥ v) * (s ^ 2 - 1) ≠ 0 := mul_ne_zero (ne_of_gt hvv_pos) hs2
    have : ((v ⬝ᵥ v) * (s ^ 2 - 1))⁻¹ • w1 ∈ rowSpan M := Submodule.smul_mem _ _ hw1_mem
    rwa [hw1_v, smul_smul, inv_mul_cancel₀ hcoef, one_smul] at this
  · -- Generic case: `G ≠ 0`, so `v = G⁻¹ • (G • v) ∈ rowSpan`.
    have : G⁻¹ • (G • v) ∈ rowSpan M := Submodule.smul_mem _ _ hGv_mem
    rwa [smul_smul, inv_mul_cancel₀ hG, one_smul] at this

/-- `An` is ancestrally closed: if `x ∈ An(i)` then `An(x) ⊆ An(i)` (an ancestor of an
ancestor of `i` is an ancestor of `i`). -/
private theorem An_subset_An_of_mem_An (S : Solution d p K) {i x : Fin d}
    (hx : x ∈ S.An i) : S.An x ⊆ S.An i := by
  intro y hy
  rcases hx with hx | hx
  · exact hx ▸ hy
  · rcases hy with hy | hy
    · exact hy ▸ Set.mem_insert_of_mem _ hx
    · exact Set.mem_insert_of_mem _ (Relation.TransGen.trans hy hx)

/-- For each `x ∈ An(i)`, the row `hₓ` lies in `qSpan Q (An i)` (it lies in `qSpan Q (An x)`
by `H_row_mem_qSpan_An`, and `An x ⊆ An i`).  Hence `hSpan S (An i) ≤ qSpan Q (An i)`. -/
private theorem hSpan_An_le_qSpan_An (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ} (hRQ : IsPORQ S R Q)
    (i : Fin d) : hSpan S (S.An i) ≤ qSpan Q (S.An i) := by
  rw [hSpan, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact qSpan_mono Q (An_subset_An_of_mem_An S hx) (H_row_mem_qSpan_An S hRQ x)

/-- **Inverse PORQ support** (dimension form).  `hSpan S (An i) = qSpan Q (An i)`: the two
spans coincide.  We already have `hSpan ≤ qSpan`; equality follows by a dimension count.
The `|An i|` rows `hₓ` (`x ∈ An i`) are linearly independent (restriction of `S.hH`), so the
left span has dimension `|An i|`; the right span is generated by `|An i|` vectors, so it has
dimension `≤ |An i|`; a subspace containing one of equal-or-greater dimension is equal. -/
private theorem hSpan_An_eq_qSpan_An (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ} (hRQ : IsPORQ S R Q)
    (i : Fin d) : hSpan S (S.An i) = qSpan Q (S.An i) := by
  letI : Fintype ↥(S.An i) := (Set.toFinite _).fintype
  have hle := hSpan_An_le_qSpan_An S hRQ i
  -- Linear independence of the restricted `H`-rows over `↥(An i)`.
  have hindep : LinearIndependent ℝ (fun x : ↥(S.An i) => (S.H x.1 : Fin p → ℝ)) :=
    S.hH.comp (fun x : ↥(S.An i) => x.1) Subtype.val_injective
  -- `finrank (hSpan) = |An i|`.
  have hH_eq : hSpan S (S.An i)
      = Submodule.span ℝ (Set.range (fun x : ↥(S.An i) => (S.H x.1 : Fin p → ℝ))) := by
    rw [hSpan, Set.image_eq_range]
  have hfin_h : Module.finrank ℝ (hSpan S (S.An i)) = Fintype.card ↥(S.An i) := by
    rw [hH_eq]; exact finrank_span_eq_card hindep
  -- `finrank (qSpan) ≤ |An i|`.
  have hQ_eq : qSpan Q (S.An i)
      = Submodule.span ℝ (Set.range (fun x : ↥(S.An i) => (Q x.1 : Fin p → ℝ))) := by
    rw [qSpan, Set.image_eq_range]
  have hfin_q : Module.finrank ℝ (qSpan Q (S.An i)) ≤ Fintype.card ↥(S.An i) := by
    rw [hQ_eq]; exact finrank_range_le_card _
  -- Equal finrank ⟹ equal subspaces.
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hfin_h]; exact hfin_q)

/-- A vector orthogonal (under `⬝ᵥ`) to every generator `qₗ`, `l ∈ T`, is orthogonal to
all of `qSpan Q T`.  (`x ↦ y ⬝ᵥ x` is linear and vanishes on the generators.) -/
private theorem dotProduct_eq_zero_of_mem_qSpan (Q : Matrix (Fin d) (Fin p) ℝ)
    (T : Set (Fin d)) (y : Fin p → ℝ) (hy : ∀ l ∈ T, y ⬝ᵥ Q l = 0)
    {w : Fin p → ℝ} (hw : w ∈ qSpan Q T) : y ⬝ᵥ w = 0 := by
  rw [qSpan] at hw
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨l, hl, rfl⟩ := hx; exact hy l hl
  | zero => simp
  | add a b _ _ ha hb => rw [dotProduct_add, ha, hb, add_zero]
  | smul c a _ ha => rw [dotProduct_smul, ha, smul_zero]

/-- **The PORQ orthogonality sublemma** (the key geometric input of Lemma 1(c)).  If `j`
is a strict ancestor of `i` (`j ∈ an(i)`) then the `i`-th row of `Q` is orthogonal to the
`j`-th row of `H`: `qᵢ ⬝ᵥ hⱼ = 0`.  Reason: `hⱼ ∈ ⟨qₗ : l ∈ An(j)⟩` (`H_row_mem_qSpan_An`),
and every `l ∈ An(j)` is a strict ancestor of `i` (an ancestor of an ancestor), so
`qᵢ ⬝ᵥ qₗ = 0` by `IsPORQ.orth`. -/
private theorem Q_row_dotProduct_H_row_eq_zero (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ} (hRQ : IsPORQ S R Q)
    {i j : Fin d} (hij : j ∈ S.anc i) : (Q i) ⬝ᵥ (S.H j) = 0 := by
  -- `j ∈ an(i)` means `prec i j`.
  have hprecij : S.prec i j := hij
  refine dotProduct_eq_zero_of_mem_qSpan Q (S.An j) (Q i) ?_ (H_row_mem_qSpan_An S hRQ j)
  intro l hl
  -- `l ∈ An(j)`, so `prec i l` (l is an ancestor of j, j ancestor of i).
  have hprecil : S.prec i l := by
    rcases hl with hl | hl
    · exact hl ▸ hprecij
    · exact Relation.TransGen.trans hl hprecij
  -- Orthogonality along the strict order.
  exact hRQ.orth i l hprecil

/-- **Lemma 1(c).**  Under the non-degeneracy hypothesis `Θₖ ≠ Θ₀` (the paper's
genericity / Assumption (b)), if `Pa(iₖ) ⊄ 𝓘` then `rowspan(Θₖ − Θ₀) ⊄ ⟨qᵢ : i ∈ 𝓘⟩`.

The hypothesis `hk` makes the statement correct: for a degenerate source intervention
with `λₖ = (B₀)_{iₖ,iₖ}` one has `Θₖ = Θ₀`, hence `rowSpan = ⊥ ≤ qSpan Q I` for every
`I` (e.g. `I = ∅` with `Pa(iₖ) = {iₖ} ⊄ ∅`), which would falsify the conclusion; `hk`
rules exactly this out.

Proof strategy.  Assume for contradiction `rowspan(Θₖ−Θ₀) ≤ ⟨qᵢ : i∈I⟩` and pick
`j ∈ Pa(iₖ)` with `j ∉ I`.
*  The spanning vector `v = Hᵀ B₀ᵀ e_{iₖ} = ∑ᵢ (B₀)_{iₖ,i} hᵢ` lies in
   `rowspan(Θₖ−Θ₀)` (`vec_mem_rowSpan_vecMulVec_sub`, the Gram-extraction lemma,
   where `hk` ⟹ the rank-≤2 difference is nonzero), hence `v ∈ ⟨qᵢ : i∈I⟩`.
*  By the **inverse PORQ support** lemma `hSpan_An_eq_qSpan_An` (proved by a *dimension
   count* — `|An i|` independent `H`-rows vs. `|An i|` generating `Q`-rows — rather than
   by inverting `R`, so `R⁻¹` is not needed), `⟨qᵢ : i∈I⟩` sits inside
   `⟨hₓ : x ∈ ⋃_{i∈I} An(i)⟩`, so `v ∈ ⟨hₓ : x ∈ ⋃_{i∈I} An(i)⟩`.

The `hⱼ`-coefficient of `v` is `(B₀)_{iₖ,j} ≠ 0` (positive diagonal if `j = iₖ`, nonzero
edge entry if `j` is a proper parent).  We split on whether `j ∈ ⋃_{i∈I} An(i)`:

The lemma requires `I` to be **ancestor-closed** (`hIclosed`), which is exactly the paper's
usage condition: Lemma 1(c) is invoked in `prop:orthogonal-correctness` only for
`I = I_{t-1}`, the already-processed nodes, which is ancestor-closed by construction.
Without it the statement is FALSE — the "diamond" `𝒢` (edges 2→1, 2→0, 1→0, target 0) with
the non-closed `I = {0,1}` admits a valid `IsPORQ` model where `rowSpan(Θₖ−Θ₀) ⊆ qSpan Q {0,1}`
yet `Pa(0) = {0,1,2} ⊄ {0,1}` (the `IsPORQ` axioms pin `R` only as the Gram–Schmidt factor of
`H`, with no `B₀` coupling, so the shared ancestor `2 ∈ An(0) ∩ An(1)` is dropped).  We split
on whether `j ∈ ⋃_{i∈I} An(i)`:

*  **Non-descendant case (`I_d = ∅`).**  If `j ∉ ⋃_{i∈I} An(i)` then the `hⱼ`-coordinate of
   `v ∈ ⟨hₓ : x ∈ ⋃_{i∈I} An(i)⟩` vanishes by linear independence of the rows of `H`
   (`coeff_eq_zero_of_sum_mem_hSpan`), contradicting `(B₀)_{iₖ,j} ≠ 0`.

*  **Descendant case (`I_d ≠ ∅`) is vacuous.**  If `j ∈ ⋃_{i∈I} An(i)` then `j ∈ An(i₀)` for
   some `i₀ ∈ I`; ancestor-closedness gives `An(i₀) ⊆ I`, so `j ∈ I` — contradicting `j ∉ I`. -/
theorem rowspan_inclusion_c (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ} (hRQ : IsPORQ S R Q)
    (k : Fin K) (I : Set (Fin d)) (hk : S.Theta k ≠ S.Theta0)
    (hIclosed : ∀ i ∈ I, S.An i ⊆ I)
    (hPa : ¬ S.Pa (S.target k) ⊆ I) :
    ¬ rowSpan (S.Theta k - S.Theta0) ≤ qSpan Q I := by
  intro hsub
  obtain ⟨j, hjPa, hjI⟩ := Set.not_subset.mp hPa
  -- The two `key_identity` vectors `u = ∑ᵢ (Bₖ)_{iₖ,i} hᵢ`, `v = ∑ᵢ (B₀)_{iₖ,i} hᵢ`.
  set u : Fin p → ℝ := ∑ i, S.Bint k (S.target k) i • S.H i with hu
  set v : Fin p → ℝ := ∑ i, S.B0 (S.target k) i • S.H i with hv
  -- `v ≠ 0`: its `h_{iₖ}` coefficient is `(B₀)_{iₖ,iₖ} > 0`.
  have hv_ne : v ≠ 0 := fun h0 =>
    absurd (coeff_eq_zero_of_sum_eq_zero S _ h0 (S.target k))
      (ne_of_gt (S.hB0pos (S.target k)))
  -- `Θₖ − Θ₀ = u uᵀ − v vᵀ`, and `hk` ⟹ this is nonzero.
  have hid : S.Theta k - S.Theta0 = Matrix.vecMulVec u u - Matrix.vecMulVec v v := by
    rw [key_identity, hu, hv, H_mulVec_row, H_mulVec_row]
  have hM : Matrix.vecMulVec u u - Matrix.vecMulVec v v ≠ 0 := by
    rw [← hid]; exact fun h => hk (sub_eq_zero.mp h)
  -- `v ∈ rowspan(Θₖ−Θ₀)` (Gram extraction), hence `v ∈ ⟨qᵢ : i∈I⟩`.
  have hv_rowspan : v ∈ rowSpan (S.Theta k - S.Theta0) := by
    rw [hid]; exact vec_mem_rowSpan_vecMulVec_sub hv_ne hM
  have hv_qspan : v ∈ qSpan Q I := hsub hv_rowspan
  -- Inverse-PORQ deployment: `⟨qᵢ : i∈I⟩ ⊆ ⟨hₓ : x ∈ ⋃_{i∈I} An(i)⟩`, so `v` lands there.
  have key : qSpan Q I ≤ hSpan S (⋃ i ∈ I, S.An i) := by
    rw [qSpan, Submodule.span_le]
    rintro _ ⟨i, hiI, rfl⟩
    have hqi : (Q i : Fin p → ℝ) ∈ qSpan Q (S.An i) :=
      Submodule.subset_span ⟨i, Set.mem_insert _ _, rfl⟩
    rw [← hSpan_An_eq_qSpan_An S hRQ i] at hqi
    exact Submodule.span_mono (Set.image_mono (fun x hx => Set.mem_biUnion hiI hx)) hqi
  have hv_hspan : v ∈ hSpan S (⋃ i ∈ I, S.An i) := key hv_qspan
  -- The `hⱼ`-coefficient of `v` is `(B₀)_{iₖ,j} ≠ 0`: `j ∈ Pa(iₖ)` is either the target
  -- itself (positive diagonal) or a proper parent (nonzero edge entry).
  have hb0j : S.B0 (S.target k) j ≠ 0 := by
    by_cases hji : j = S.target k
    · rw [hji]; exact ne_of_gt (S.hB0pos (S.target k))
    · have hedge : S.Edge j (S.target k) := by
        rcases hjPa with h | h
        · exact absurd h hji
        · exact h
      exact (S.hB0supp (S.target k) j (Ne.symm hji)).2 hedge
  -- Split on whether `j` is an ancestor of some `i ∈ I` (i.e. `I_d ≠ ∅`).
  by_cases hjU : j ∈ ⋃ i ∈ I, S.An i
  · -- **Descendant case (`I_d ≠ ∅`) is vacuous under `hIclosed`.**  If `j ∈ ⋃_{i∈I} An(i)`,
    -- then `j ∈ An(i₀)` for some `i₀ ∈ I`; since `I` is ancestor-closed (`hIclosed`),
    -- `An(i₀) ⊆ I`, so `j ∈ I` — contradicting `j ∉ I`.
    --
    -- This hypothesis is exactly the paper's usage condition: Lemma 1(c) is invoked in
    -- `prop:orthogonal-correctness` only for `I = I_{t-1}`, the already-processed nodes,
    -- which is ancestor-closed by construction.  Without it the statement is FALSE — the
    -- "diamond" `𝒢` (edges 2→1, 2→0, 1→0, target 0) with the non-closed `I = {0,1}`
    -- admits a valid `IsPORQ` model where `rowSpan(Θₖ−Θ₀) ⊆ qSpan Q {0,1}` yet
    -- `Pa(0) = {0,1,2} ⊄ {0,1}`, because the `IsPORQ` axioms pin `R` only as the
    -- Gram–Schmidt factor of `H` (no `B₀` coupling) and `2 ∈ An(0) ∩ An(1)` is dropped.
    obtain ⟨i₀, hi₀I, hji₀⟩ : ∃ i ∈ I, j ∈ S.anc i := by
      simp only [Set.mem_iUnion] at hjU
      obtain ⟨i₀, hi₀I, hji₀⟩ := hjU
      refine ⟨i₀, hi₀I, ?_⟩
      rcases hji₀ with hji₀ | hji₀
      · exact absurd (hji₀ ▸ hi₀I) hjI
      · exact hji₀
    exact hjI (hIclosed i₀ hi₀I (Set.mem_insert_of_mem _ hji₀))
  · -- **Non-descendant case (`I_d = ∅`).**  `j ∉ ⋃_{i∈I} An(i)`, so the `hⱼ`-coordinate of
    -- `v ∈ hSpan S (⋃_{i∈I} An i)` vanishes by linear independence of the rows of `H`
    -- (`coeff_eq_zero_of_sum_mem_hSpan`), contradicting `(B₀)_{iₖ,j} ≠ 0`.
    have hvmem : (∑ i, S.B0 (S.target k) i • S.H i) ∈ hSpan S (⋃ i ∈ I, S.An i) := by
      rw [← hv]; exact hv_hspan
    exact hb0j (coeff_eq_zero_of_sum_mem_hSpan S _ _ hvmem hjU)

end Causalean.Discovery.LinearDisentanglement
