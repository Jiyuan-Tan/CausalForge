import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.BumpHolderScaling

/-!
# Hölder assembly for separated packing bumps

This module records the support fact that turns the pointwise derivative
scaling estimates into bounds independent of the number of packing cells.
It is the first step in the Hölder-ball certificate for the angular family.
-/

open Set
open scoped Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- At a positive integer smoothness order, the standard Euclidean Hölder
ball is exactly a bounded-derivative ball whose top required derivative is
Lipschitz.  This removes the ceiling and real-power bookkeeping from the
angular packing's eventual Hölder certificate. -/
-- @node: euclideanHolderBallStd_nat_iff
lemma euclideanHolderBallStd_nat_iff (f : Score → ℝ) (q : ℕ) (L : ℝ)
    (S : Set Score) (hq : 1 ≤ q) :
    EuclideanHolderBallStd f (q : ℝ) L S ↔
      ContDiffOn ℝ (q - 1) f S ∧
      (∀ j : ℕ, j ≤ q - 1 → ∀ x ∈ S,
        ‖iteratedFDeriv ℝ j f x‖ ≤ L) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖iteratedFDeriv ℝ (q - 1) f x -
            iteratedFDeriv ℝ (q - 1) f y‖ ≤ L * ‖x - y‖) := by
  unfold EuclideanHolderBallStd
  rw [Nat.ceil_natCast]
  have hexp : (q : ℝ) - ((q - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub hq]
    norm_num
  rw [hexp]
  simp

/-- The first Fréchet derivative of the affine baseline has operator norm at
most the absolute slope. -/
-- @node: packingAffineBaseline_iteratedFDeriv_one_norm_le
lemma packingAffineBaseline_iteratedFDeriv_one_norm_le (b : ℝ) (x : Score) :
    ‖iteratedFDeriv ℝ 1 (packingAffineBaseline b) x‖ ≤ |b| := by
  unfold packingAffineBaseline
  rw [show (fun x : Score => 1 / 2 + b * x 0) =
      (fun _ => 1 / 2) + (fun x => b * x 0) by rfl]
  rw [iteratedFDeriv_add_apply (by fun_prop) (by fun_prop)]
  simp only [iteratedFDeriv_const_of_ne one_ne_zero, Pi.zero_apply, zero_add]
  rw [norm_iteratedFDeriv_one]
  rw [show fderiv ℝ (fun x : Score => b * x 0) x =
      b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) by
    convert ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 0).const_mul b).fderiv]
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg b) (by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    simpa using PiLp.norm_apply_le z 0)

/-- Every derivative of the affine baseline of order at least two vanishes. -/
-- @node: packingAffineBaseline_iteratedFDeriv_eq_zero
lemma packingAffineBaseline_iteratedFDeriv_eq_zero (b : ℝ) (j : ℕ)
    (hj : 2 ≤ j) (x : Score) :
    iteratedFDeriv ℝ j (packingAffineBaseline b) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 2 + k = (k + 1) + 1 by omega]
  rw [iteratedFDeriv_succ_eq_comp_right]
  have hf : fderiv ℝ (packingAffineBaseline b) =
      fun _ => b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) := by
    funext y
    unfold packingAffineBaseline
    rw [show (fun x : Score => 1 / 2 + b * x 0) =
      (fun _ => 1 / 2) + (fun x => b * x 0) by rfl]
    rw [fderiv_add (by fun_prop) (by fun_prop), fderiv_const_apply]
    simp only [zero_add]
    convert ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).const_mul b).fderiv
  rw [hf, iteratedFDeriv_const_of_ne (by omega)]
  exact LinearIsometryEquiv.map_zero _

/-- Every positive-order derivative of the affine baseline is independent of
the evaluation point. -/
-- @node: packingAffineBaseline_iteratedFDeriv_sub_eq_zero
lemma packingAffineBaseline_iteratedFDeriv_sub_eq_zero (b : ℝ) (j : ℕ)
    (hj : 1 ≤ j) (x y : Score) :
    iteratedFDeriv ℝ j (packingAffineBaseline b) x -
      iteratedFDeriv ℝ j (packingAffineBaseline b) y = 0 := by
  rcases eq_or_lt_of_le hj with rfl | hj'
  · have hx : fderiv ℝ (packingAffineBaseline b) x =
        b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) := by
      unfold packingAffineBaseline
      rw [show (fun z : Score => 1 / 2 + b * z 0) =
        (fun _ => 1 / 2) + (fun z => b * z 0) by rfl]
      rw [fderiv_add (by fun_prop) (by fun_prop), fderiv_const_apply]
      simp only [zero_add]
      convert ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 0).const_mul b).fderiv
    have hy : fderiv ℝ (packingAffineBaseline b) y =
        b • (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) := by
      unfold packingAffineBaseline
      rw [show (fun z : Score => 1 / 2 + b * z 0) =
        (fun _ => 1 / 2) + (fun z => b * z 0) by rfl]
      rw [fderiv_add (by fun_prop) (by fun_prop), fderiv_const_apply]
      simp only [zero_add]
      convert ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 y 0).const_mul b).fderiv
    rw [show iteratedFDeriv ℝ 1 (packingAffineBaseline b) x -
        iteratedFDeriv ℝ 1 (packingAffineBaseline b) y = 0 by
      apply sub_eq_zero.mpr
      apply ContinuousMultilinearMap.ext
      intro m
      simp only [iteratedFDeriv_one_apply, hx, hy]]
  · rw [packingAffineBaseline_iteratedFDeriv_eq_zero b j (by omega) x,
      packingAffineBaseline_iteratedFDeriv_eq_zero b j (by omega) y, sub_zero]

/-- A finite sum of selected localized packing bumps is smooth to every
finite order.  This is the smoothness half of the eventual Hölder-ball
certificate; separation is only needed for its uniform derivative bounds. -/
-- @node: packingBumpSum_contDiff
lemma packingBumpSum_contDiff {M : ℕ} (delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Score => ∑ i, if omega i then
        localizedPackingBump delta w (centers i) y else 0) := by
  apply ContDiff.sum
  intro i _
  split
  · exact localizedPackingBump_contDiff delta w (centers i)
  · exact contDiff_const

/-- Every iterated derivative of a positive-bandwidth localized bump is
supported in the corresponding closed ball. -/
-- @node: localizedPackingBump_support_iteratedFDeriv_subset
lemma localizedPackingBump_support_iteratedFDeriv_subset (j : ℕ)
    (delta : ℝ) {w : ℝ} (hw : 0 < w) (center : Score) :
    Function.support (iteratedFDeriv ℝ j (localizedPackingBump delta w center)) ⊆
      Metric.closedBall center w := by
  refine (support_iteratedFDeriv_subset j).trans ?_
  apply closure_minimal
  · intro x hx
    by_contra hball
    have hfar : w ≤ dist x center := by
      exact (by simpa [Metric.mem_closedBall, not_le] using hball : w < dist x center).le
    exact hx (localizedPackingBump_eq_zero_of_bandwidth_le_dist hw hfar)
  · exact Metric.isClosed_closedBall

/-- At a point, derivatives of two distinct separated packing bumps cannot
both be nonzero. -/
-- @node: localizedPackingBump_iteratedFDeriv_pairwise_exclusive
lemma localizedPackingBump_iteratedFDeriv_pairwise_exclusive {M : ℕ}
    (j : ℕ) (delta : ℝ) {w : ℝ} (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {i k : Fin M} (hik : i ≠ k) (x : Score) :
    iteratedFDeriv ℝ j (localizedPackingBump delta w (centers i)) x = 0 ∨
      iteratedFDeriv ℝ j (localizedPackingBump delta w (centers k)) x = 0 := by
  by_contra h
  push_neg at h
  have hi : x ∈ Metric.closedBall (centers i) w :=
    localizedPackingBump_support_iteratedFDeriv_subset j delta hw (centers i) h.1
  have hk : x ∈ Metric.closedBall (centers k) w :=
    localizedPackingBump_support_iteratedFDeriv_subset j delta hw (centers k) h.2
  have htri : dist (centers i) (centers k) ≤
      dist (centers i) x + dist x (centers k) := dist_triangle _ _ _
  rw [Metric.mem_closedBall] at hi
  rw [Metric.mem_closedBall] at hk
  rw [dist_comm (centers i) x] at htri
  linarith [hsep i k hik]

/-- A separated family of localized bumps has at most one nonzero iterated
derivative at each point. -/
-- @node: localizedPackingBump_iteratedFDeriv_unique_active
lemma localizedPackingBump_iteratedFDeriv_unique_active {M : ℕ}
    (j : ℕ) (delta : ℝ) {w : ℝ} (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (x : Score) :
    ∀ i k : Fin M,
      iteratedFDeriv ℝ j (localizedPackingBump delta w (centers i)) x ≠ 0 →
      iteratedFDeriv ℝ j (localizedPackingBump delta w (centers k)) x ≠ 0 →
      i = k := by
  intro i k hi hk
  by_contra hik
  rcases localizedPackingBump_iteratedFDeriv_pairwise_exclusive
      j delta hw hsep hik x with hzero | hzero
  · exact hi hzero
  · exact hk hzero

/-- An explicit normalized-bump derivative bound transfers to a separated
bump sum without acquiring a factor depending on the grid size. -/
-- @node: packingBumpSum_iteratedFDeriv_bound_with
lemma packingBumpSum_iteratedFDeriv_bound_with {M : ℕ}
    (j : ℕ) (delta : ℝ) {w C : ℝ} (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (hC0 : 0 ≤ C)
    (hC : ∀ z : Score, ‖iteratedFDeriv ℝ j packingBump z‖ ≤ C)
    (x : Score) :
      ‖iteratedFDeriv ℝ j
          (fun y : Score => ∑ i, if omega i then
            localizedPackingBump delta w (centers i) y else 0) x‖ ≤
        |delta| * (w⁻¹) ^ j * C := by
  let f : Fin M → Score → ℝ := fun i y =>
    if omega i then localizedPackingBump delta w (centers i) y else 0
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin M)), ContDiff ℝ j (f i) := by
    intro i _
    dsimp [f]
    split
    · exact (localizedPackingBump_contDiff delta w (centers i)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    · exact contDiff_const
  rw [show (fun y : Score => ∑ i, if omega i then
      localizedPackingBump delta w (centers i) y else 0) =
      (fun y : Score => ∑ i, f i y) by rfl]
  rw [iteratedFDeriv_sum hf]
  simp only [Finset.sum_apply]
  by_cases hex : ∃ i : Fin M, iteratedFDeriv ℝ j (f i) x ≠ 0
  · obtain ⟨i, hi⟩ := hex
    have hbit : omega i = true := by
      by_contra hbit
      have hfalse : omega i = false := Bool.eq_false_of_not_eq_true hbit
      simp [f, hfalse] at hi
    have hi' : iteratedFDeriv ℝ j
        (localizedPackingBump delta w (centers i)) x ≠ 0 := by
      simpa [f, hbit] using hi
    rw [Finset.sum_eq_single i]
    · dsimp [f] at hi ⊢
      simp only [hbit, if_true]
      rw [localizedPackingBump_iteratedFDeriv, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hw]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hC (w⁻¹ • (x - centers i)))
          (mul_nonneg (abs_nonneg delta) (pow_nonneg (inv_nonneg.mpr hw.le) j))
    · intro k _ hki
      by_cases hbit : omega k = true
      · dsimp [f]
        simp only [hbit, if_true]
        rcases localizedPackingBump_iteratedFDeriv_pairwise_exclusive
            j delta hw hsep (Ne.symm hki) x with hz | hz
        · exact (hi' hz).elim
        · exact hz
      · have hfalse : omega k = false := Bool.eq_false_of_not_eq_true hbit
        simp [f, hfalse]
    · simp
  · have hzero : ∀ i : Fin M, iteratedFDeriv ℝ j (f i) x = 0 := by
      intro i
      exact not_ne_iff.mp (not_exists.mp hex i)
    rw [Finset.sum_eq_zero fun i _ => hzero i]
    rw [norm_zero]
    exact mul_nonneg
      (mul_nonneg (abs_nonneg delta) (pow_nonneg (inv_nonneg.mpr hw.le) j)) hC0

/-- The norm of any derivative of a separated bump sum is bounded by the
single-bump scaling bound, with no factor depending on the grid size. -/
-- @node: packingBumpSum_iteratedFDeriv_bound
lemma packingBumpSum_iteratedFDeriv_bound {M : ℕ}
    (j : ℕ) (delta : ℝ) {w : ℝ} (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (x : Score) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖iteratedFDeriv ℝ j
          (fun y : Score => ∑ i, if omega i then
            localizedPackingBump delta w (centers i) y else 0) x‖ ≤
        |delta| * (w⁻¹) ^ j * C := by
  rcases packingBump_iteratedFDeriv_bound j with ⟨C, hC0, hC⟩
  exact ⟨C, hC0,
    packingBumpSum_iteratedFDeriv_bound_with j delta hw hsep omega hC0 hC x⟩

/-- The top derivative of a separated bump sum is globally Lipschitz, with
the one-bump scaling constant and no dependence on the number of cells. -/
-- @node: packingBumpSum_iteratedFDeriv_lipschitz
lemma packingBumpSum_iteratedFDeriv_lipschitz {M : ℕ}
    (j : ℕ) (delta : ℝ) {w : ℝ} (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (x y : Score) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖iteratedFDeriv ℝ j
          (fun z : Score => ∑ i, if omega i then
            localizedPackingBump delta w (centers i) z else 0) x -
        iteratedFDeriv ℝ j
          (fun z : Score => ∑ i, if omega i then
            localizedPackingBump delta w (centers i) z else 0) y‖ ≤
        |delta| * (w⁻¹) ^ (j + 1) * C * ‖x - y‖ := by
  let f : Score → ℝ := fun z => ∑ i, if omega i then
    localizedPackingBump delta w (centers i) z else 0
  rcases packingBump_iteratedFDeriv_bound (j + 1) with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  have hf := packingBumpSum_contDiff delta w centers omega
  have hd : ∀ z ∈ (Set.univ : Set Score),
      DifferentiableAt ℝ (iteratedFDeriv ℝ j f) z := by
    intro z _
    have hj : ((j : ℕ∞) : WithTop ℕ∞) <
        ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j)
    exact (ContDiff.differentiable_iteratedFDeriv hj hf) z
  have hb : ∀ z ∈ (Set.univ : Set Score),
      ‖fderiv ℝ (iteratedFDeriv ℝ j f) z‖ ≤
        |delta| * (w⁻¹) ^ (j + 1) * C := by
    intro z _
    rw [norm_fderiv_iteratedFDeriv]
    exact packingBumpSum_iteratedFDeriv_bound_with (j + 1) delta hw hsep
      omega hC0 hC z
  simpa [f, norm_sub_rev, mul_assoc] using
    (convex_univ.norm_image_sub_le_of_norm_fderiv_le hd hb
      (Set.mem_univ y) (Set.mem_univ x))

/-- A supplied normalized-bump derivative bound gives the corresponding
Lipschitz estimate for a separated bump sum.  This explicit-constant variant
lets the final Hölder assembly use one finite family of constants. -/
-- @node: packingBumpSum_iteratedFDeriv_lipschitz_with
lemma packingBumpSum_iteratedFDeriv_lipschitz_with {M : ℕ}
    (j : ℕ) (delta : ℝ) {w C : ℝ} (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (hC0 : 0 ≤ C)
    (hC : ∀ z : Score, ‖iteratedFDeriv ℝ (j + 1) packingBump z‖ ≤ C)
    (x y : Score) :
      ‖iteratedFDeriv ℝ j
          (fun z : Score ↦ ∑ i, if omega i then
            localizedPackingBump delta w (centers i) z else 0) x -
        iteratedFDeriv ℝ j
          (fun z : Score ↦ ∑ i, if omega i then
            localizedPackingBump delta w (centers i) z else 0) y‖ ≤
        |delta| * (w⁻¹) ^ (j + 1) * C * ‖x - y‖ := by
  let f : Score → ℝ := fun z ↦ ∑ i, if omega i then
    localizedPackingBump delta w (centers i) z else 0
  have hf := packingBumpSum_contDiff delta w centers omega
  have hd : ∀ z ∈ (Set.univ : Set Score),
      DifferentiableAt ℝ (iteratedFDeriv ℝ j f) z := by
    intro z _
    have hj : ((j : ℕ∞) : WithTop ℕ∞) <
        ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j)
    exact (ContDiff.differentiable_iteratedFDeriv hj hf) z
  have hb : ∀ z ∈ (Set.univ : Set Score),
      ‖fderiv ℝ (iteratedFDeriv ℝ j f) z‖ ≤
        |delta| * (w⁻¹) ^ (j + 1) * C := by
    intro z _
    rw [norm_fderiv_iteratedFDeriv]
    exact packingBumpSum_iteratedFDeriv_bound_with (j + 1) delta hw hsep
      omega hC0 hC z
  simpa [f, norm_sub_rev, mul_assoc] using
    (convex_univ.norm_image_sub_le_of_norm_fderiv_le hd hb
      (Set.mem_univ y) (Set.mem_univ x))

/-- At every point of the supporting square, clipping is inactive throughout
a neighborhood.  This is stronger than pointwise equality on the square and
therefore transfers ambient Fréchet derivatives at boundary points. -/
-- @node: clippedPackingRegression_eventuallyEq_packingRegression_at_square
lemma clippedPackingRegression_eventuallyEq_packingRegression_at_square
    {M : ℕ} {b delta w : ℝ}
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2)) :
    clippedPackingRegression b delta w centers omega =ᶠ[𝓝 x]
      packingRegression b delta w centers omega := by
  let p := packingRegression b delta w centers omega
  have hpx := packingRegression_mem_Icc hb hdelta0 hdelta hw hsep omega hx
  have hpx' : p x ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [p]
    constructor <;> linarith [hpx.1, hpx.2]
  have hpcont : Continuous p := by
    exact (packingRegression_contDiff b delta w centers omega).continuous
  have hevent : ∀ᶠ y in 𝓝 x, p y ∈ Set.Ioo (0 : ℝ) 1 :=
    hpcont.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hpx')
  filter_upwards [hevent] with y hy
  exact clippedPackingRegression_eq_of_mem_Icc ⟨hy.1.le, hy.2.le⟩

/-- On the supporting square, the clipped packing regression is smooth to
every finite order.  This packages the neighborhood-level inactivity of the
clip into the first conjunct of the eventual Hölder-ball certificate. -/
-- @node: clippedPackingRegression_contDiffOn_square
lemma clippedPackingRegression_contDiffOn_square {M : ℕ} (j : ℕ)
    {b delta w : ℝ}
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) :
    ContDiffOn ℝ j (clippedPackingRegression b delta w centers omega)
      (scoreCube (1 / 2)) := by
  intro x hx
  have hp : ContDiffAt ℝ j (packingRegression b delta w centers omega) x :=
    (packingRegression_contDiff b delta w centers omega).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have heq := clippedPackingRegression_eventuallyEq_packingRegression_at_square
    hb hdelta0 hdelta hw hsep omega hx
  exact (hp.congr_of_eventuallyEq heq).contDiffWithinAt

/-- On the supporting square, every ambient iterated derivative of the
clipped kernel regression equals that of the smooth packing regression. -/
-- @node: clippedPackingRegression_iteratedFDeriv_eq_on_square
lemma clippedPackingRegression_iteratedFDeriv_eq_on_square
    {M : ℕ} (j : ℕ) {b delta w : ℝ}
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2)) :
    iteratedFDeriv ℝ j (clippedPackingRegression b delta w centers omega) x =
      iteratedFDeriv ℝ j (packingRegression b delta w centers omega) x := by
  exact ((clippedPackingRegression_eventuallyEq_packingRegression_at_square
    hb hdelta0 hdelta hw hsep omega hx).iteratedFDeriv ℝ j).eq_of_nhds

/-- Unit derivative and top-derivative Lipschitz bounds for the separated bump
sum assemble with the small affine baseline to put the clipped regression in
every envelope-`L` integer Hölder ball with `L ≥ 4`.  The two bump bounds are
exactly the conclusions supplied by the scaling lemmas above once their
paper-scale scalar factors have been bounded. -/
-- @node: clippedPackingRegression_mem_holder_of_bump_bounds
lemma clippedPackingRegression_mem_holder_of_bump_bounds
    {M q : ℕ} {L b delta w : ℝ} (hq : 1 ≤ q) (hL : 4 ≤ L)
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool)
    (hderiv : ∀ j : ℕ, j ≤ q - 1 → 1 ≤ j → ∀ x : Score,
      ‖iteratedFDeriv ℝ j
        (fun y : Score ↦ ∑ i, if omega i then
          localizedPackingBump delta w (centers i) y else 0) x‖ ≤ 1)
    (hlip : ∀ x y : Score,
      ‖iteratedFDeriv ℝ (q - 1)
          (fun z : Score ↦ ∑ i, if omega i then
            localizedPackingBump delta w (centers i) z else 0) x -
        iteratedFDeriv ℝ (q - 1)
          (fun z : Score ↦ ∑ i, if omega i then
            localizedPackingBump delta w (centers i) z else 0) y‖ ≤ ‖x - y‖) :
    EuclideanHolderBallStd
      (clippedPackingRegression b delta w centers omega)
      (q : ℝ) L (scoreCube (1 / 2)) := by
  rw [euclideanHolderBallStd_nat_iff _ q L _ hq]
  let bumps : Score → ℝ := fun y ↦ ∑ i, if omega i then
    localizedPackingBump delta w (centers i) y else 0
  have hbumps : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) bumps :=
    packingBumpSum_contDiff delta w centers omega
  have hreg_deriv (j : ℕ) (x : Score) :
      iteratedFDeriv ℝ j (packingRegression b delta w centers omega) x =
        iteratedFDeriv ℝ j (packingAffineBaseline b) x +
          iteratedFDeriv ℝ j bumps x := by
    change iteratedFDeriv ℝ j (packingAffineBaseline b + bumps) x = _
    rw [iteratedFDeriv_add_apply
      ((packingAffineBaseline_contDiff b).of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      (hbumps.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  constructor
  · exact clippedPackingRegression_contDiffOn_square (q - 1) hb hdelta0
      hdelta hw hsep omega
  constructor
  · intro j hj x hx
    rw [clippedPackingRegression_iteratedFDeriv_eq_on_square j hb hdelta0
      hdelta hw hsep omega hx]
    by_cases hj0 : j = 0
    · subst j
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
      have hp := packingRegression_mem_Icc hb hdelta0 hdelta hw hsep omega hx
      constructor <;> linarith [hp.1, hp.2]
    · rw [hreg_deriv]
      calc
        ‖iteratedFDeriv ℝ j (packingAffineBaseline b) x +
            iteratedFDeriv ℝ j bumps x‖ ≤
            ‖iteratedFDeriv ℝ j (packingAffineBaseline b) x‖ +
              ‖iteratedFDeriv ℝ j bumps x‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 := by
          gcongr
          · rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hj0) with rfl | hj'
            · exact (packingAffineBaseline_iteratedFDeriv_one_norm_le b x).trans hb
            · rw [packingAffineBaseline_iteratedFDeriv_eq_zero b j (by omega) x,
                norm_zero]
              norm_num
          · exact hderiv j hj (Nat.one_le_iff_ne_zero.mpr hj0) x
        _ ≤ L := by linarith
  · intro x hx y hy
    rw [clippedPackingRegression_iteratedFDeriv_eq_on_square (q - 1) hb
      hdelta0 hdelta hw hsep omega hx,
      clippedPackingRegression_iteratedFDeriv_eq_on_square (q - 1) hb
        hdelta0 hdelta hw hsep omega hy, hreg_deriv, hreg_deriv]
    have hbase :
        ‖iteratedFDeriv ℝ (q - 1) (packingAffineBaseline b) x -
            iteratedFDeriv ℝ (q - 1) (packingAffineBaseline b) y‖ ≤
          (1 / 4 : ℝ) * ‖x - y‖ := by
      by_cases hq1 : q = 1
      · subst q
        rw [show (1 : ℕ) - 1 = 0 by omega]
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map]
        unfold packingAffineBaseline
        rw [show (1 / 2 + b * x 0) - (1 / 2 + b * y 0) =
            b * ((x - y) 0) by rw [PiLp.sub_apply]; ring,
          Real.norm_eq_abs, abs_mul]
        calc
          |b| * |(x - y) 0| ≤ |b| * ‖x - y‖ := by
            gcongr
            simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) 0
          _ ≤ (1 / 4 : ℝ) * ‖x - y‖ := by gcongr
      · rw [packingAffineBaseline_iteratedFDeriv_sub_eq_zero b (q - 1)
            (by omega) x y, norm_zero]
        positivity
    calc
      ‖(iteratedFDeriv ℝ (q - 1) (packingAffineBaseline b) x +
            iteratedFDeriv ℝ (q - 1) bumps x) -
          (iteratedFDeriv ℝ (q - 1) (packingAffineBaseline b) y +
            iteratedFDeriv ℝ (q - 1) bumps y)‖ =
          ‖(iteratedFDeriv ℝ (q - 1) (packingAffineBaseline b) x -
              iteratedFDeriv ℝ (q - 1) (packingAffineBaseline b) y) +
            (iteratedFDeriv ℝ (q - 1) bumps x -
              iteratedFDeriv ℝ (q - 1) bumps y)‖ := by congr 1 <;> abel
      _ ≤ (1 / 4 : ℝ) * ‖x - y‖ + ‖x - y‖ :=
        (norm_add_le _ _).trans (add_le_add hbase (hlip x y))
      _ ≤ L * ‖x - y‖ := by
        have hnorm : 0 ≤ ‖x - y‖ := norm_nonneg _
        nlinarith

/-- Uniform normalized-bump derivative constants whose paper-scale factors
are at most one imply the complete clipped-regression Hölder certificate. -/
-- @node: clippedPackingRegression_mem_holder_of_scaling_bounds
lemma clippedPackingRegression_mem_holder_of_scaling_bounds
    {M q : ℕ} {L b delta w : ℝ} (hq : 1 ≤ q) (hL : 4 ≤ L)
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (C : ℕ → ℝ)
    (hC0 : ∀ j, 0 ≤ C j)
    (hC : ∀ j z, ‖iteratedFDeriv ℝ j packingBump z‖ ≤ C j)
    (hscale : ∀ j, j ≤ q → |delta| * (w⁻¹) ^ j * C j ≤ 1) :
    EuclideanHolderBallStd
      (clippedPackingRegression b delta w centers omega)
      (q : ℝ) L (scoreCube (1 / 2)) := by
  apply clippedPackingRegression_mem_holder_of_bump_bounds hq hL hb hdelta0
    hdelta hw hsep omega
  · intro j hj _ x
    exact (packingBumpSum_iteratedFDeriv_bound_with j delta hw hsep omega
      (hC0 j) (hC j) x).trans (hscale j (by omega))
  · intro x y
    have htop := packingBumpSum_iteratedFDeriv_lipschitz_with (q - 1) delta hw
      hsep omega (hC0 q) (by
        intro z
        rw [Nat.sub_add_cancel hq]
        exact hC q z) x y
    calc
      _ ≤ |delta| * (w⁻¹) ^ q * C q * ‖x - y‖ := by
        simpa [Nat.sub_add_cancel hq] using htop
      _ ≤ ‖x - y‖ := by
        have hn : 0 ≤ ‖x - y‖ := norm_nonneg _
        nlinarith [hscale q le_rfl]

end CausalSmith.Stat.BddUniformLogPenalty
