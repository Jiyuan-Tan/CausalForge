/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Model
import Mathlib.Logic.Relation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear causal disentanglement: graph order and the partial-order RQ decomposition

We package the graph-theoretic notions used throughout (parents, ancestors, and the
partial order `≺_𝒢` with `i ≺ j ↔ j ∈ an(i)`), and the **partial order RQ
decomposition** of the paper (Definition 1, Appendix B): a generalization of the
reduced RQ decomposition where the upper-triangular support of `R` is replaced by
the partial order, and orthogonality of the rows of `Q` is required only along the
order.  `porq_exists` / `porq_unique` are its existence and uniqueness (their
Proposition in Appendix B), proved there by the Gram–Schmidt-style construction in
Algorithm "Partial Order RQ Decomposition".
-/

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

namespace Solution

/-- Parents of `i`: nodes `j` with an edge `j → i`. -/
def pa (S : Solution d p K) (i : Fin d) : Set (Fin d) := {j | S.Edge j i}

/-- `Pa(i) = pa(i) ∪ {i}`. -/
def Pa (S : Solution d p K) (i : Fin d) : Set (Fin d) := insert i (S.pa i)

/-- Ancestors of `i`: nodes `j` with a directed path `j ⇝ i` (transitive closure of
the edge relation). -/
def anc (S : Solution d p K) (i : Fin d) : Set (Fin d) := {j | Relation.TransGen S.Edge j i}

/-- `An(i) = an(i) ∪ {i}`. -/
def An (S : Solution d p K) (i : Fin d) : Set (Fin d) := insert i (S.anc i)

/-- The partial order `≺_𝒢`: `i ≺ j` iff `j` is an ancestor of `i`. -/
def prec (S : Solution d p K) (i j : Fin d) : Prop := Relation.TransGen S.Edge j i

/-- The reflexive closure `⪯_𝒢` of `≺_𝒢`. -/
def preceq (S : Solution d p K) (i j : Fin d) : Prop := i = j ∨ S.prec i j

/-- The strict partial order embeds into the `Fin d` linear order: if `i ≺ j`
(`j` is a strict ancestor of `i`) then `i < j`.  This is the acyclicity of `𝒢`
lifted through the transitive closure, and the engine behind every "process the
nodes in a topological order" argument below. -/
theorem prec_lt (S : Solution d p K) {i j : Fin d} (hij : S.prec i j) : i < j := by
  induction hij with
  | single hab => exact S.hAcyc _ _ hab
  | tail _ hbc ih => exact lt_trans (S.hAcyc _ _ hbc) ih

/-- `≺` is irreflexive: a node is never its own strict ancestor. -/
theorem not_prec_self (S : Solution d p K) (i : Fin d) : ¬ S.prec i i :=
  fun h => lt_irrefl i (S.prec_lt h)

end Solution

/-! ### Bridge between `dotProduct` and the `EuclideanSpace` inner product

The partial-order RQ decomposition is a Gram–Schmidt construction, but Mathlib's
Gram–Schmidt / orthogonal-projection machinery lives on `EuclideanSpace ℝ (Fin p)`
(the `PiLp 2` inner product), whereas `IsPORQ` is phrased with the bare
`dotProduct` (`⬝ᵥ`) on `Fin p → ℝ`.  These lemmas transfer between the two. -/

/-- The `EuclideanSpace ℝ (Fin p)` inner product of `toLp x` and `toLp y` is exactly
the `dotProduct` `x ⬝ᵥ y`.  This is the bridge used to import all of Mathlib's
inner-product-space machinery into the `dotProduct` world. -/
theorem inner_toLp_eq_dotProduct (x y : Fin p → ℝ) :
    (inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin p)) (WithLp.toLp 2 y) : ℝ)
      = dotProduct x y := by
  rw [PiLp.inner_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, real_inner_eq_re_inner, mul_comm]
  simp

/-- The self `dotProduct` of a nonzero real vector is strictly positive
(positive-definiteness of `⬝ᵥ`).  Equivalently, `x ⬝ᵥ x = 0 ↔ x = 0`; this is what
makes "normalize the projection residual" well defined in the construction. -/
theorem dotProduct_self_pos {x : Fin p → ℝ} (hx : x ≠ 0) : 0 < dotProduct x x := by
  rcases Function.ne_iff.mp hx with ⟨i, hi⟩
  have hnn : 0 ≤ dotProduct x x := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  rcases lt_or_eq_of_le hnn with h | h
  · exact h
  · exfalso
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (x j))).mp h.symm i (Finset.mem_univ i)
    exact hi (by simpa using (mul_self_eq_zero).mp hzero)

/-- **Right cancellation by a full-row-rank `Q`.**  If the rows of `Q` are linearly
independent and `R Q = R' Q`, then `R = R'`.  This pins the `R` factor once `Q` is
fixed, and is the algebraic half of the uniqueness proof. -/
theorem eq_of_mul_eq_mul_row_indep {R R' : Matrix (Fin d) (Fin d) ℝ}
    {Q : Matrix (Fin d) (Fin p) ℝ} (hQ : LinearIndependent ℝ Q.row)
    (hRQ : R * Q = R' * Q) : R = R' := by
  have hinj : Function.Injective (fun v => Matrix.vecMul v Q) :=
    Matrix.vecMul_injective_iff.mpr hQ
  ext i j
  have hrow : Matrix.vecMul (R i) Q = Matrix.vecMul (R' i) Q := by
    rw [← Matrix.mul_apply_eq_vecMul, ← Matrix.mul_apply_eq_vecMul, hRQ]
  exact congrFun (hinj hrow) j

/-- **A full-row-rank product forces a full-row-rank right factor.**  If the rows of
`R Q` are linearly independent (`d` of them), then so are the rows of `Q`.  The rows
of `R Q` lie in the span of the rows of `Q`, which has at most `d` of them, so a
dimension count forces the `d` rows of `Q` to be independent.  Applied to `H = R Q`
with `H` of full row rank, this shows the rows `qᵢ` of any PORQ factor are
independent — the hypothesis `eq_of_mul_eq_mul_row_indep` needs. -/
theorem row_indep_of_mul_row_indep (R : Matrix (Fin d) (Fin d) ℝ)
    (Q : Matrix (Fin d) (Fin p) ℝ) (hH : LinearIndependent ℝ (R * Q).row) :
    LinearIndependent ℝ Q.row := by
  have hHcard := (linearIndependent_iff_card_le_finrank_span (b := (R * Q).row)).mp hH
  rw [linearIndependent_iff_card_le_finrank_span]
  refine le_trans hHcard ?_
  have hsub : Submodule.span ℝ (Set.range (R * Q).row)
      ≤ Submodule.span ℝ (Set.range Q.row) := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Matrix.row_def, Matrix.mul_apply_eq_vecMul,
      Matrix.vecMul_eq_sum]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact Submodule.finrank_mono hsub

/-- **Definition 1 (partial order RQ decomposition).**  `H = R Q` with `R` having
non-negative diagonal and support along `⪯` (`Rᵢⱼ = 0` unless `i ⪯ j`), and the rows
`qᵢ` of `Q` of unit Euclidean norm and pairwise orthogonal along the strict order
(`qᵢ ⟂ qⱼ` whenever `i ≺ j`). -/
structure IsPORQ (S : Solution d p K)
    (R : Matrix (Fin d) (Fin d) ℝ) (Q : Matrix (Fin d) (Fin p) ℝ) : Prop where
  /-- `H` factors as `R Q`. -/
  factor : S.H = R * Q
  /-- `R` has non-negative diagonal. -/
  diag_nonneg : ∀ i, 0 ≤ R i i
  /-- `R` is supported on the partial order: `Rᵢⱼ = 0` unless `i ⪯ j`. -/
  supp : ∀ i j, ¬ S.preceq i j → R i j = 0
  /-- Each row of `Q` has unit norm. -/
  unit : ∀ i, (Q i) ⬝ᵥ (Q i) = 1
  /-- Rows of `Q` are orthogonal along the strict order. -/
  orth : ∀ i j, S.prec i j → (Q i) ⬝ᵥ (Q j) = 0

/-- **The diagonal of any PORQ factor is strictly positive.**

Because `R` is supported on `⪯` and `i ≺ j ⟹ i < j` (`Solution.prec_lt`), the support
condition `Rᵢⱼ = 0` unless `i ⪯ j` forces `Rᵢⱼ = 0` whenever `j < i`, i.e. `R` is upper
triangular in the `Fin d` order, so `det R = ∏ᵢ Rᵢᵢ`.  Full row rank of `H = R Q`
(`S.hH`) makes the right factor `R` of full rank too (a `v` with `v R = 0` gives
`v H = 0`), hence `det R ≠ 0`, so every diagonal entry is nonzero; combined with
`diag_nonneg` this gives `0 < Rᵢᵢ`.  This is what makes "`Rᵢᵢ ≥ 0` fixes the sign of
`qᵢ`" effective in the uniqueness argument. -/
theorem porq_diag_pos (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ}
    (h : IsPORQ S R Q) (i : Fin d) : 0 < R i i := by
  -- `H = R Q` has full row rank.
  have hHrow : LinearIndependent ℝ (R * Q).row := by
    have hind := S.hH
    rw [h.factor] at hind
    rwa [Matrix.row_def]
  -- `R` itself has full row rank: `v R = 0 ⟹ v (R Q) = 0 ⟹ v = 0`.
  have hRrow : LinearIndependent ℝ R.row := by
    rw [← Matrix.vecMul_injective_iff]
    have hinjH : Function.Injective (fun v => Matrix.vecMul v (R * Q)) :=
      Matrix.vecMul_injective_iff.mpr hHrow
    intro v w hvw
    apply hinjH
    simp only at hvw ⊢
    rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hvw]
  -- Hence `R` is a unit, so `det R ≠ 0`.
  have hdet : R.det ≠ 0 := by
    have hunit : IsUnit R := Matrix.linearIndependent_rows_iff_isUnit.mp hRrow
    exact (Matrix.isUnit_iff_isUnit_det R).mp hunit |>.ne_zero
  -- `R` is upper triangular, so `det R = ∏ Rᵢᵢ`.
  have hupper : R.BlockTriangular id := by
    intro a b hba
    apply h.supp
    rintro (rfl | hprec)
    · exact lt_irrefl _ hba
    · exact lt_irrefl _ (lt_trans hba (S.prec_lt hprec))
  rw [Matrix.det_of_upperTriangular hupper] at hdet
  -- Each diagonal entry is nonzero, hence (with `diag_nonneg`) positive.
  have hne : R i i ≠ 0 := by
    intro hzero
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  exact lt_of_le_of_ne (h.diag_nonneg i) (Ne.symm hne)

/-- **Row-split of a PORQ factorization.**  Splitting off the diagonal term, the `i`-th
row of `H` is `Rᵢᵢ • qᵢ` plus a combination of the *other* rows `qₖ` (`k ≠ i`); by
`supp` only the strict ancestors `i ≺ k` contribute, so this is exactly the triangular
equation `hᵢ = Rᵢᵢ qᵢ + ∑_{i ≺ k} Rᵢₖ qₖ`.  It is the membership half of the
orthogonal-decomposition uniqueness argument. -/
theorem porq_row_split (S : Solution d p K)
    {R : Matrix (Fin d) (Fin d) ℝ} {Q : Matrix (Fin d) (Fin p) ℝ}
    (h : IsPORQ S R Q) (i : Fin d) :
    S.H i = R i i • Q i + ∑ k ∈ Finset.univ.erase i, R i k • Q k := by
  have hrow : S.H i = ∑ k, R i k • Q k := by
    rw [h.factor, Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum]
  rw [hrow, ← Finset.add_sum_erase Finset.univ (fun k => R i k • Q k) (Finset.mem_univ i)]

open Classical in
/-- The partial-order Gram–Schmidt residuals, working in `EuclideanSpace ℝ (Fin p)`:
`porqResidual i = (toLp (hᵢ)) − proj_{Wᵢ} (toLp hᵢ)` where `Wᵢ = span {porqResidual k : i ≺ k}`
is the span of the already-built strict-ancestor residuals.  The recursion terminates
because every recursive call is to a strict ancestor `k` with `i < k`
(`Solution.prec_lt`), so the measure `d − i` strictly decreases. -/
noncomputable def porqResidual (S : Solution d p K) (i : Fin d) :
    EuclideanSpace ℝ (Fin p) :=
  letI W : Submodule ℝ (EuclideanSpace ℝ (Fin p)) :=
    Submodule.span ℝ (Set.range (fun k : {k // S.prec i k} => porqResidual S k.1))
  (WithLp.toLp 2 (S.H i) : EuclideanSpace ℝ (Fin p)) - W.starProjection (WithLp.toLp 2 (S.H i))
termination_by d - i.1
decreasing_by
  have hik : i.1 < k.1.1 := S.prec_lt k.2
  omega

open Classical in
/-- The span `Wᵢ = span {porqResidual k : i ≺ k}` of the already-built strict-ancestor
residuals, the subspace the `i`-th residual is orthogonalized against. -/
noncomputable def porqAncSpan (S : Solution d p K) (i : Fin d) :
    Submodule ℝ (EuclideanSpace ℝ (Fin p)) :=
  Submodule.span ℝ (Set.range (fun k : {k // S.prec i k} => porqResidual S k.1))

open Classical in
/-- Unfolding equation for `porqResidual`: it is `toLp hᵢ` minus its orthogonal
projection onto the ancestor span `porqAncSpan i`. -/
theorem porqResidual_eq (S : Solution d p K) (i : Fin d) :
    porqResidual S i = (WithLp.toLp 2 (S.H i) : EuclideanSpace ℝ (Fin p))
      - (porqAncSpan S i).starProjection (WithLp.toLp 2 (S.H i)) := by
  rw [porqResidual, porqAncSpan]

/-- Each strict-ancestor residual lies in the ancestor span `porqAncSpan i`. -/
theorem porqResidual_mem_ancSpan (S : Solution d p K) {i k : Fin d} (hk : S.prec i k) :
    porqResidual S k ∈ porqAncSpan S i := by
  classical
  rw [porqAncSpan]
  exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

/-- The `i`-th residual is orthogonal to its ancestor span: `porqResidual i ∈ (Wᵢ)ᗮ`. -/
theorem porqResidual_mem_orthogonal (S : Solution d p K) (i : Fin d) :
    porqResidual S i ∈ (porqAncSpan S i)ᗮ := by
  rw [porqResidual_eq]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- **Orthogonality along the order.**  The `i`-th residual is orthogonal to every
strict-ancestor residual `porqResidual k` (`i ≺ k`), since the latter lies in `Wᵢ` and
the former in `(Wᵢ)ᗮ`. -/
theorem porqResidual_orthogonal (S : Solution d p K) {i k : Fin d} (hk : S.prec i k) :
    (inner ℝ (porqResidual S i) (porqResidual S k) : ℝ) = 0 := by
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal (porqResidual_mem_ancSpan S hk)
    (porqResidual_mem_orthogonal S i)


/-- The images of the rows of `H` under `toLp` are linearly independent (full row rank
of `H` transported through the linear isomorphism `toLp`). -/
theorem toLp_H_linearIndependent (S : Solution d p K) :
    LinearIndependent ℝ (fun j : Fin d =>
      (WithLp.toLp 2 (S.H j) : EuclideanSpace ℝ (Fin p))) := by
  have hker : ((WithLp.linearEquiv 2 ℝ (Fin p → ℝ)).symm.toLinearMap).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin p → ℝ)).symm.injective
  have := S.hH.map' (WithLp.linearEquiv 2 ℝ (Fin p → ℝ)).symm.toLinearMap hker
  simpa [Function.comp] using this

open Classical in
/-- The `i`-th residual lies in the span of `{toLp hₘ : i ⪯ m}` (the row itself and its
strict ancestors).  Proved by strong induction on the reversed `Fin d` order: the
diagonal term is `toLp hᵢ`, and the projection lives in `Wᵢ`, whose generators
`porqResidual k` (`i ≺ k`) lie, by induction, in `span {toLp hₘ : k ⪯ m} ⊆ span {toLp hₘ : i ⪯ m}`
(by transitivity of `⪯`). -/
theorem porqResidual_mem_HspanLE (S : Solution d p K) (i : Fin d) :
    porqResidual S i ∈ Submodule.span ℝ
      {x | ∃ m, S.preceq i m ∧ x = (WithLp.toLp 2 (S.H m) : EuclideanSpace ℝ (Fin p))} := by
  induction i using WellFoundedGT.induction with
  | _ i hIH =>
    rw [porqResidual_eq]
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨i, Or.inl rfl, rfl⟩
    · -- The projection lies in `Wᵢ`, which is contained in the target span.
      have hproj : (porqAncSpan S i).starProjection (WithLp.toLp 2 (S.H i))
          ∈ porqAncSpan S i := Submodule.starProjection_apply_mem _ _
      have hsub : porqAncSpan S i ≤ Submodule.span ℝ
          {x | ∃ m, S.preceq i m ∧ x = (WithLp.toLp 2 (S.H m) : EuclideanSpace ℝ (Fin p))} := by
        rw [porqAncSpan, Submodule.span_le]
        rintro x ⟨⟨k, hik⟩, rfl⟩
        -- `porqResidual k ∈ span {toLp hₘ : k ⪯ m} ⊆ span {toLp hₘ : i ⪯ m}`.
        have hk := hIH k (S.prec_lt hik)
        refine Submodule.span_mono ?_ hk
        rintro y ⟨m, hkm, rfl⟩
        refine ⟨m, ?_, rfl⟩
        rcases hkm with rfl | hkm
        · exact Or.inr hik
        · exact Or.inr (Relation.TransGen.trans hkm hik)
      exact hsub hproj

/-- **Non-vanishing of the residual.**  `porqResidual i ≠ 0`: if it were zero then
`toLp hᵢ` would lie in `Wᵢ ⊆ span {toLp hₘ : i ≺ m}`, contradicting the linear
independence of `{toLp hⱼ}` (a member is never in the span of the strictly-others). -/
theorem porqResidual_ne_zero (S : Solution d p K) (i : Fin d) :
    porqResidual S i ≠ 0 := by
  intro hzero
  -- From `porqResidual i = 0`, `toLp hᵢ` equals its projection, hence lies in `Wᵢ`.
  have hmem : (WithLp.toLp 2 (S.H i) : EuclideanSpace ℝ (Fin p)) ∈ porqAncSpan S i := by
    have := porqResidual_eq S i
    rw [hzero] at this
    have heq : (WithLp.toLp 2 (S.H i) : EuclideanSpace ℝ (Fin p))
        = (porqAncSpan S i).starProjection (WithLp.toLp 2 (S.H i)) :=
      eq_of_sub_eq_zero this.symm
    rw [heq]
    exact Submodule.starProjection_apply_mem _ _
  -- `Wᵢ ⊆ span {toLp hₘ : i ≺ m}`, so `toLp hᵢ ∈ span {toLp hₘ : m ≠ i}`.
  have hsub : porqAncSpan S i ≤ Submodule.span ℝ
      ((fun j : Fin d => (WithLp.toLp 2 (S.H j) : EuclideanSpace ℝ (Fin p))) '' {j | j ≠ i}) := by
    rw [porqAncSpan, Submodule.span_le]
    rintro x ⟨⟨k, hik⟩, rfl⟩
    have hk := porqResidual_mem_HspanLE S k
    refine Submodule.span_mono ?_ hk
    rintro y ⟨m, hkm, rfl⟩
    refine ⟨m, ?_, rfl⟩
    -- `k ⪯ m` and `i ≺ k` give `i ≺ m`, so `m ≠ i`.
    have him : S.prec i m := by
      rcases hkm with rfl | hkm
      · exact hik
      · exact Relation.TransGen.trans hkm hik
    exact fun hmi => S.not_prec_self i (hmi ▸ him)
  have hmem' : (WithLp.toLp 2 (S.H i) : EuclideanSpace ℝ (Fin p))
      ∈ Submodule.span ℝ
        ((fun j : Fin d => (WithLp.toLp 2 (S.H j) : EuclideanSpace ℝ (Fin p))) '' {j | j ≠ i}) :=
    hsub hmem
  -- Contradiction with linear independence of `{toLp hⱼ}`.
  exact (toLp_H_linearIndependent S).notMem_span_image (by simp) hmem'

open Classical in
/-- **Row coefficients of the existence factorization.**  Writing
`qₘ = ‖rₘ‖⁻¹ • rₘ` for the normalized residuals, the row `toLp hᵢ` decomposes as
`‖rᵢ‖ • qᵢ + ∑_{i ≺ k} (coefficient) • qₖ`: the diagonal coefficient is the residual
norm `‖rᵢ‖ ≥ 0`, the off-diagonal coefficients are supported on the strict ancestors
`i ≺ k`, and there are none off `⪯`.  This packages `factor`, `diag_nonneg` and `supp`
into one existence statement (the `i`-th row of `R`). -/
theorem porq_rowCoeffs (S : Solution d p K) (i : Fin d) :
    ∃ c : Fin d → ℝ, (∀ j, ¬ S.preceq i j → c j = 0) ∧ c i = ‖porqResidual S i‖ ∧
      (WithLp.toLp 2 (S.H i) : EuclideanSpace ℝ (Fin p))
        = ∑ m, c m • ((‖porqResidual S m‖)⁻¹ • porqResidual S m) := by
  classical
  set q : Fin d → EuclideanSpace ℝ (Fin p) :=
    fun m => (‖porqResidual S m‖)⁻¹ • porqResidual S m with hq
  have hrne : ∀ m, porqResidual S m ≠ 0 := porqResidual_ne_zero S
  have hnne : ∀ m, ‖porqResidual S m‖ ≠ 0 := fun m => norm_ne_zero_iff.mpr (hrne m)
  -- `rₘ = ‖rₘ‖ • qₘ`.
  have hrq : ∀ m, porqResidual S m = ‖porqResidual S m‖ • q m := by
    intro m
    rw [hq]
    simp only
    rw [smul_smul, mul_inv_cancel₀ (hnne m), one_smul]
  -- The projection lies in `Wᵢ = span (range rₖ)`; extract subtype coefficients.
  have hproj : (porqAncSpan S i).starProjection (WithLp.toLp 2 (S.H i)) ∈ porqAncSpan S i :=
    Submodule.starProjection_apply_mem _ _
  rw [porqAncSpan, Submodule.mem_span_range_iff_exists_fun] at hproj
  obtain ⟨c0, hc0⟩ := hproj
  rw [← porqAncSpan] at hc0
  -- Assemble the `Fin d`-indexed coefficient vector.
  refine ⟨fun m => if m = i then ‖porqResidual S i‖
      else if h : S.prec i m then c0 ⟨m, h⟩ * ‖porqResidual S m‖ else 0, ?_, ?_, ?_⟩
  · -- support on `⪯`
    intro j hj
    have hji : j ≠ i := fun h => hj (Or.inl h.symm)
    have hnp : ¬ S.prec i j := fun h => hj (Or.inr h)
    simp only [hji, if_false, hnp, dite_false]
  · -- diagonal
    simp
  · -- factor
    -- `toLp hᵢ = rᵢ + proj`.
    have hsplit : (WithLp.toLp 2 (S.H i) : EuclideanSpace ℝ (Fin p))
        = porqResidual S i + (porqAncSpan S i).starProjection (WithLp.toLp 2 (S.H i)) := by
      rw [porqResidual_eq]; abel
    rw [hsplit, ← hc0]
    -- Split the universe sum off the diagonal `m = i`.
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    beta_reduce
    -- Diagonal: `‖rᵢ‖ • qᵢ = rᵢ`.
    rw [if_pos rfl, smul_smul, mul_inv_cancel₀ (hnne i), one_smul]
    congr 1
    -- Off-diagonal: the erased sum equals `∑ k, c0 k • r_k` (subtype reindexing).
    -- The common summand `f m = if prec i m then c0⟨m,_⟩ • r_m else 0`.
    set f : Fin d → EuclideanSpace ℝ (Fin p) :=
      fun m => if h : S.prec i m then c0 ⟨m, h⟩ • porqResidual S m else 0 with hf
    -- Step 1: each erased term equals `f m`.
    have hterm : ∀ m ∈ Finset.univ.erase i,
        (if m = i then ‖porqResidual S i‖
          else if h : S.prec i m then c0 ⟨m, h⟩ * ‖porqResidual S m‖ else 0)
            • ((‖porqResidual S m‖)⁻¹ • porqResidual S m) = f m := by
      intro m hm
      have hmi : m ≠ i := Finset.ne_of_mem_erase hm
      simp only [hf, if_neg hmi]
      by_cases hpm : S.prec i m
      · rw [dif_pos hpm, dif_pos hpm, smul_smul, mul_assoc,
          mul_inv_cancel₀ (hnne m), mul_one]
      · rw [dif_neg hpm, dif_neg hpm, zero_smul]
    rw [Finset.sum_congr rfl hterm]
    -- Step 2: drop the terms off the ancestor filter (f vanishes there).
    have hvanish : ∀ m ∈ Finset.univ.erase i, f m ≠ 0 → S.prec i m := by
      intro m _ hfm
      by_contra hpm
      exact hfm (by simp only [hf, dif_neg hpm])
    rw [← Finset.sum_filter_of_ne hvanish]
    -- Step 3: reindex the filter sum to the subtype sum.
    have hmem_iff : ∀ m, m ∈ (Finset.univ.erase i).filter (fun m => S.prec i m) ↔ S.prec i m := by
      intro m
      rw [Finset.mem_filter]
      refine ⟨fun hm => hm.2, fun hm => ⟨?_, hm⟩⟩
      exact Finset.mem_erase.mpr ⟨fun h => S.not_prec_self i (h ▸ hm), Finset.mem_univ m⟩
    rw [Finset.sum_subtype _ hmem_iff f]
    -- `f ↑k = c0 k • r_k`.
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf, dif_pos k.2]

/-- **Existence of the partial order RQ decomposition** (Appendix B Proposition).

Proved by the paper's Algorithm "Partial Order RQ Decomposition": process the rows
in a topological order of `𝒢` — here *decreasing* `Fin d` order, since
`Solution.prec_lt` shows a strict ancestor `j` of `i` satisfies `j > i`, so all
ancestors are handled before `i`.  For each `i`, with `Wᵢ = span {qⱼ : i ≺ j}` the
span of the already-built ancestor rows, set `qᵢ = ‖rᵢ‖⁻¹ • rᵢ` where
`rᵢ = proj_{Wᵢ⊥} hᵢ`; full row rank of `H` (`S.hH`) makes `rᵢ ≠ 0`, so the
normalization is valid (`Solution.dotProduct_self_pos`), giving `unit`, and the
projection gives `orth`.  The `i`-th row of `R` solves the triangular system
`∑_{j ⪰ i} Rᵢⱼ qⱼ = hᵢ`, with `Rᵢᵢ = ‖rᵢ‖ > 0` (`diag_nonneg`) and `Rᵢⱼ = 0` off
`⪯` (`supp`); `factor` then holds by construction. -/
theorem porq_exists (S : Solution d p K) :
    ∃ (R : Matrix (Fin d) (Fin d) ℝ) (Q : Matrix (Fin d) (Fin p) ℝ), IsPORQ S R Q := by
  classical
  -- The unit-norm residual directions `qᵢ = ‖rᵢ‖⁻¹ • rᵢ` (in `EuclideanSpace`).
  set q : Fin d → EuclideanSpace ℝ (Fin p) :=
    fun i => (‖porqResidual S i‖)⁻¹ • porqResidual S i with hq
  have hrne : ∀ i, porqResidual S i ≠ 0 := porqResidual_ne_zero S
  have hnne : ∀ i, ‖porqResidual S i‖ ≠ 0 := fun i => norm_ne_zero_iff.mpr (hrne i)
  -- The matrix `Q` of these directions, in `dotProduct` coordinates.
  set Qmat : Matrix (Fin d) (Fin p) ℝ := Matrix.of fun i j => WithLp.ofLp (q i) j with hQmat
  -- Bridge: `dotProduct` of two `Q` rows is the `EuclideanSpace` inner product of `qᵢ, qⱼ`.
  have hbridge : ∀ i j, (Qmat i) ⬝ᵥ (Qmat j) = (inner ℝ (q i) (q j) : ℝ) := by
    intro i j
    have hb := inner_toLp_eq_dotProduct (WithLp.ofLp (q i)) (WithLp.ofLp (q j))
    rw [WithLp.toLp_ofLp, WithLp.toLp_ofLp] at hb
    change (WithLp.ofLp (q i)) ⬝ᵥ (WithLp.ofLp (q j)) = _
    rw [hb]
  -- The row coefficients of `R`, packaged by `porq_rowCoeffs`.
  choose Rrow hRsupp hRdiag hRfactor using fun i => porq_rowCoeffs S i
  refine ⟨Matrix.of fun i j => Rrow i j, Qmat, ?_, ?_, ?_, ?_, ?_⟩
  · -- factor: `H = R Q`.
    ext i j
    have hHi : (WithLp.ofLp (WithLp.toLp 2 (S.H i)) : Fin p → ℝ)
        = WithLp.ofLp (∑ m, Rrow i m • q m) := by rw [hRfactor i]
    rw [WithLp.ofLp_toLp] at hHi
    rw [hHi]
    rw [Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum]
    -- `ofLp (∑ Rrow i m • q m) j = ∑ m, Rrow i m • (Qmat m) j`.
    simp only [hQmat, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      WithLp.ofLp_sum, WithLp.ofLp_smul]
  · -- diag_nonneg: `R i i = ‖rᵢ‖ ≥ 0`.
    intro i
    rw [Matrix.of_apply, hRdiag i]
    exact norm_nonneg _
  · -- supp.
    intro i j hij
    rw [Matrix.of_apply]
    exact hRsupp i j hij
  · -- unit: `‖qᵢ‖ = 1` in `dotProduct`.
    intro i
    rw [hbridge, hq]
    simp only [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
      RCLike.conj_to_real]
    rw [pow_two]
    field_simp
    exact div_self (hnne i)
  · -- orth: `qᵢ ⟂ qⱼ` for `i ≺ j`.
    intro i j hij
    rw [hbridge, hq]
    simp only [inner_smul_left, inner_smul_right]
    rw [porqResidual_orthogonal S hij]
    ring

/-- **Uniqueness of the partial order RQ decomposition** (Appendix B Proposition). -/
theorem porq_unique (S : Solution d p K)
    {R R' : Matrix (Fin d) (Fin d) ℝ} {Q Q' : Matrix (Fin d) (Fin p) ℝ}
    (h : IsPORQ S R Q) (h' : IsPORQ S R' Q') : R = R' ∧ Q = Q' := by
  -- `H = R Q` has full row rank, so `Q` has linearly independent rows.
  have hHQ : LinearIndependent ℝ (R * Q).row := by
    have hind := S.hH
    rw [h.factor] at hind
    rwa [Matrix.row_def]
  have hQrow : LinearIndependent ℝ Q.row := row_indep_of_mul_row_indep R Q hHQ
  -- The `Q` factor is determined by the analytic uniqueness of the Gram–Schmidt
  -- vectors along the partial order (the genuinely hard half).
  have hQeq : Q = Q' := by
    -- Both diagonals are strictly positive (the sign-fixing fact).
    have hRpos := porq_diag_pos S h
    have hR'pos := porq_diag_pos S h'
    -- Prove `Q i = Q' i` for every `i`, by strong induction on the reversed `Fin d`
    -- order: a strict ancestor `k` of `i` (`i ≺ k`) has `k > i`, so the rows `qₖ`
    -- it is orthogonal to are already known to coincide with `q'ₖ`.
    have key : ∀ i, Q i = Q' i := by
      intro i
      induction i using WellFoundedGT.induction with
      | _ i hIH =>
        -- `aᵢ := Rᵢᵢ • qᵢ` and `bᵢ := R'ᵢᵢ • q'ᵢ` are the residuals; both equal
        -- `hᵢ` minus a combination of ancestor rows, hence `aᵢ - bᵢ` lies in the
        -- ancestor span, while orthogonality makes `aᵢ - bᵢ` perpendicular to it.
        set a := R i i • Q i with ha
        set b := R' i i • Q' i with hb
        -- The residual is orthogonal to every strict ancestor row.
        have horth : ∀ k, S.prec i k → (a - b) ⬝ᵥ Q k = 0 := by
          intro k hk
          have hqk : Q k = Q' k := hIH k (S.prec_lt hk)
          rw [sub_dotProduct, ha, hb]
          have h1 : (R i i • Q i) ⬝ᵥ Q k = 0 := by
            rw [smul_dotProduct, h.orth i k hk, smul_zero]
          have h2 : (R' i i • Q' i) ⬝ᵥ Q k = 0 := by
            rw [hqk, smul_dotProduct, h'.orth i k hk, smul_zero]
          rw [h1, h2, sub_zero]
        -- Membership: `a - b = Y - X`, a combination of ancestor rows, where
        -- `hᵢ = a + X = b + Y` (row-split).
        have hmem : a - b = (∑ k ∈ Finset.univ.erase i, R' i k • Q' k)
            - ∑ k ∈ Finset.univ.erase i, R i k • Q k := by
          have hX := porq_row_split S h i
          have hY := porq_row_split S h' i
          rw [← ha] at hX
          rw [← hb] at hY
          -- a + X = H i = b + Y  ⟹  a - b = Y - X
          have heq : a + (∑ k ∈ Finset.univ.erase i, R i k • Q k)
              = b + ∑ k ∈ Finset.univ.erase i, R' i k • Q' k := by
            rw [← hX, ← hY]
          rw [sub_eq_sub_iff_add_eq_add, heq, add_comm]
        -- `a - b` is in the ancestor span (`hmem`) and ⟂ it (`horth`), so it is null.
        have hself : (a - b) ⬝ᵥ (a - b) = 0 := by
          nth_rewrite 2 [hmem]
          rw [dotProduct_sub, dotProduct_sum, dotProduct_sum]
          have hYz : ∀ k ∈ Finset.univ.erase i, (a - b) ⬝ᵥ (R' i k • Q' k) = 0 := by
            intro k hk
            rw [dotProduct_smul]
            by_cases hRk : R' i k = 0
            · rw [hRk, zero_smul]
            · have hprec : S.prec i k := by
                rcases Classical.em (S.preceq i k) with hpe | hpe
                · rcases hpe with rfl | hp
                  · exact absurd rfl (Finset.ne_of_mem_erase hk)
                  · exact hp
                · exact absurd (h'.supp i k hpe) hRk
              rw [← hIH k (S.prec_lt hprec), horth k hprec, smul_zero]
          have hXz : ∀ k ∈ Finset.univ.erase i, (a - b) ⬝ᵥ (R i k • Q k) = 0 := by
            intro k hk
            rw [dotProduct_smul]
            by_cases hRk : R i k = 0
            · rw [hRk, zero_smul]
            · have hprec : S.prec i k := by
                rcases Classical.em (S.preceq i k) with hpe | hpe
                · rcases hpe with rfl | hp
                  · exact absurd rfl (Finset.ne_of_mem_erase hk)
                  · exact hp
                · exact absurd (h.supp i k hpe) hRk
              rw [horth k hprec, smul_zero]
          rw [Finset.sum_eq_zero hYz, Finset.sum_eq_zero hXz, sub_zero]
        -- Positive-definiteness forces `a = b`.
        have hab : a = b := by
          by_contra hne
          have : (0 : ℝ) < (a - b) ⬝ᵥ (a - b) :=
            dotProduct_self_pos (sub_ne_zero.mpr hne)
          rw [hself] at this
          exact lt_irrefl _ this
        -- `a = b` means `Rᵢᵢ • qᵢ = R'ᵢᵢ • q'ᵢ`; squaring (unit norm) pins `Rᵢᵢ = R'ᵢᵢ`.
        rw [ha, hb] at hab
        have hsq : R i i * R i i = R' i i * R' i i := by
          have := congrArg (fun v => v ⬝ᵥ v) hab
          simp only [smul_dotProduct, dotProduct_smul, h.unit i, h'.unit i,
            smul_eq_mul, mul_one] at this
          linarith
        have hRR : R i i = R' i i := by
          have h1 : (0 : ℝ) ≤ R i i := le_of_lt (hRpos i)
          have h2 : (0 : ℝ) ≤ R' i i := le_of_lt (hR'pos i)
          nlinarith [hsq, hRpos i, hR'pos i]
        -- Cancel the (nonzero) scalar.
        rw [hRR] at hab
        exact smul_right_injective (Fin p → ℝ) (ne_of_gt (hR'pos i)) hab
    funext i
    exact key i
  -- Once `Q = Q'`, right-cancellation by the full-row-rank `Q` pins `R`.
  refine ⟨?_, hQeq⟩
  apply eq_of_mul_eq_mul_row_indep hQrow
  rw [← h.factor, hQeq, ← h'.factor]

end Causalean.Discovery.LinearDisentanglement
