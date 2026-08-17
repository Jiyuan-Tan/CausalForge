import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularGrid
import Causalean.Mathlib.InformationTheory.CommonStatisticBernoulli
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth radial bumps for the angular packing

This file isolates the compactly supported Euclidean bump used in the packing
regressions.  It records its range, support, smoothness, and the corresponding
facts after translation and rescaling.
-/

open Set
open scoped Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- A fixed smooth Euclidean bump, equal to one on the ball of radius `1/2`
and supported in the open unit ball. -/
-- @node: packingContDiffBump
noncomputable def packingContDiffBump : ContDiffBump (0 : Score) :=
  ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩

/-- The normalized radial bump used by the packing construction. -/
-- @node: packingBump
noncomputable def packingBump (z : Score) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace Score).toFun 2 ((2 : ℝ) • z)

/-- The normalized bump equals one at its center. -/
-- @node: packingBump_zero
lemma packingBump_zero : packingBump 0 = 1 := by
  unfold packingBump
  apply ContDiffBumpBase.eq_one
  · norm_num
  · simp

/-- The normalized bump takes values in `[0,1]`. -/
-- @node: packingBump_mem_Icc
lemma packingBump_mem_Icc (z : Score) : packingBump z ∈ Icc (0 : ℝ) 1 := by
  exact ContDiffBumpBase.mem_Icc _ _ _

/-- The normalized bump vanishes outside the open unit ball. -/
-- @node: packingBump_eq_zero_of_one_le_norm
lemma packingBump_eq_zero_of_one_le_norm {z : Score} (hz : 1 ≤ ‖z‖) :
    packingBump z = 0 := by
  unfold packingBump
  rw [← not_ne_iff, ← Function.mem_support]
  rw [ContDiffBumpBase.support _ _ (by norm_num)]
  simp only [Metric.mem_ball, dist_zero_right]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- The normalized radial bump is smooth to every finite order. -/
-- @node: packingBump_contDiff
lemma packingBump_contDiff :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) packingBump := by
  have hs := (ContDiffBumpBase.ofInnerProductSpace Score).smooth
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Score => ((2 : ℝ), (2 : ℝ) • z)) := by fun_prop
  rw [← contDiffOn_univ]
  have hc := hs.comp (s := Set.univ) hg.contDiffOn (fun z _ => by simp)
  exact hc

/-- The normalized packing bump depends only on Euclidean radius. -/
-- @node: packingBump_eq_of_norm_eq
lemma packingBump_eq_of_norm_eq {x y : Score} (hxy : ‖x‖ = ‖y‖) :
    packingBump x = packingBump y := by
  unfold packingBump ContDiffBumpBase.ofInnerProductSpace
  change Real.smoothTransition ((2 - ‖(2 : ℝ) • x‖) / (2 - 1)) =
    Real.smoothTransition ((2 - ‖(2 : ℝ) • y‖) / (2 - 1))
  rw [norm_smul, norm_smul, hxy]

/-- Every iterated Fréchet derivative of the normalized packing bump is
uniformly bounded. -/
-- @node: packingBump_iteratedFDeriv_bound
lemma packingBump_iteratedFDeriv_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Score,
      ‖iteratedFDeriv ℝ j packingBump z‖ ≤ C := by
  have hcont : Continuous (iteratedFDeriv ℝ j packingBump) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
      packingBump_contDiff
  have hsupp : HasCompactSupport (iteratedFDeriv ℝ j packingBump) := by
    have hbump : HasCompactSupport packingBump := by
      change IsCompact (closure (Function.support
        ((ContDiffBumpBase.ofInnerProductSpace Score).toFun 2 ∘
          fun z : Score => (2 : ℝ) • z)))
      rw [Function.support_comp_eq_preimage,
        ContDiffBumpBase.support _ _ (by norm_num)]
      have heq : (fun z : Score => (2 : ℝ) • z) ⁻¹' Metric.ball 0 2 =
          Metric.ball 0 1 := by
        ext z
        simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
        rw [norm_smul]
        norm_num
      rw [heq, closure_ball _ one_ne_zero]
      exact isCompact_closedBall 0 1
    exact hbump.iteratedFDeriv j
  rcases hcont.bounded_above_of_compact_support hsupp with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  exact (hC z).trans (le_max_left _ _)

/-- The last derivative required by an arbitrary positive Hölder order has
a global Hölder modulus. -/
-- @node: packingBump_iteratedFDeriv_holder
lemma packingBump_iteratedFDeriv_holder (s : ℝ) (hs : 0 < s) :
    let k := ⌈s⌉₊ - 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Score,
      ‖iteratedFDeriv ℝ k packingBump u -
          iteratedFDeriv ℝ k packingBump v‖ ≤
        C * ‖u - v‖ ^ (s - (k : ℝ)) := by
  classical
  let k := ⌈s⌉₊ - 1
  have hceil : k + 1 = ⌈s⌉₊ := by
    dsimp [k]
    have : 0 < ⌈s⌉₊ := Nat.ceil_pos.mpr hs
    omega
  have hk_lt : (k : ℝ) < s := by
    rw [← Nat.lt_ceil]
    omega
  have hs_le : s ≤ (k : ℝ) + 1 := by
    calc
      s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
      _ = (k : ℝ) + 1 := by rw [← hceil]; norm_num
  have hq0 : 0 ≤ s - (k : ℝ) := by linarith
  have hq1 : s - (k : ℝ) ≤ 1 := by linarith
  rcases packingBump_iteratedFDeriv_bound k with ⟨B0, hB0, h0⟩
  rcases packingBump_iteratedFDeriv_bound (k + 1) with ⟨B1, hB1, h1⟩
  let C := max B1 (2 * B0)
  refine ⟨C, hB1.trans (le_max_left _ _), ?_⟩
  intro u v
  have hlip : ‖iteratedFDeriv ℝ k packingBump u -
        iteratedFDeriv ℝ k packingBump v‖ ≤ B1 * ‖u - v‖ := by
    have hd : ∀ z ∈ (Set.univ : Set Score),
        DifferentiableAt ℝ (iteratedFDeriv ℝ k packingBump) z := by
      intro z _
      have hk0 : (k : ℕ∞) < (⊤ : ℕ∞) := WithTop.coe_lt_top k
      have hk : ((k : ℕ∞) : WithTop ℕ∞) <
          ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_lt_coe.mpr hk0
      exact (ContDiff.differentiable_iteratedFDeriv hk packingBump_contDiff) z
    have hb : ∀ z ∈ (Set.univ : Set Score),
        ‖fderiv ℝ (iteratedFDeriv ℝ k packingBump) z‖ ≤ B1 := by
      intro z _
      rw [norm_fderiv_iteratedFDeriv]
      exact h1 z
    simpa [norm_sub_rev] using
      (convex_univ.norm_image_sub_le_of_norm_fderiv_le hd hb
        (Set.mem_univ v) (Set.mem_univ u))
  by_cases huv : ‖u - v‖ ≤ 1
  · calc
      ‖iteratedFDeriv ℝ k packingBump u - iteratedFDeriv ℝ k packingBump v‖
          ≤ B1 * ‖u - v‖ := hlip
      _ ≤ B1 * ‖u - v‖ ^ (s - (k : ℝ)) := by
        gcongr
        exact Real.self_le_rpow_of_le_one (norm_nonneg _) huv hq1
      _ ≤ C * ‖u - v‖ ^ (s - (k : ℝ)) := by
        gcongr
        exact le_max_left _ _
  · have huv1 : 1 ≤ ‖u - v‖ := le_of_not_ge huv
    calc
      ‖iteratedFDeriv ℝ k packingBump u - iteratedFDeriv ℝ k packingBump v‖
          ≤ 2 * B0 := by
        calc
          _ ≤ ‖iteratedFDeriv ℝ k packingBump u‖ +
                ‖iteratedFDeriv ℝ k packingBump v‖ := norm_sub_le _ _
          _ ≤ B0 + B0 := add_le_add (h0 u) (h0 v)
          _ = 2 * B0 := by ring
      _ ≤ C := le_max_right _ _
      _ ≤ C * ‖u - v‖ ^ (s - (k : ℝ)) := by
        have hp := Real.one_le_rpow huv1 hq0
        nlinarith [hB1.trans (le_max_left B1 (2 * B0))]

/-- A translated bump of amplitude `delta` and bandwidth `w`. -/
-- @node: localizedPackingBump
noncomputable def localizedPackingBump (delta w : ℝ) (center x : Score) : ℝ :=
  delta * packingBump (w⁻¹ • (x - center))

/-- A localized packing bump is the normalized radial profile evaluated at
its distance from the center. -/
-- @node: localizedPackingBump_eq_delta_mul_radial
lemma localizedPackingBump_eq_delta_mul_radial
    {delta w : ℝ} (center x : Score) :
    localizedPackingBump delta w center x =
      delta * packingBump (w⁻¹ • scorePoint (dist x center) 0) := by
  unfold localizedPackingBump
  congr 1
  apply packingBump_eq_of_norm_eq
  rw [norm_smul, norm_smul]
  congr 1
  rw [dist_eq_norm]
  simp [scorePoint, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs]

/-- A localized bump takes its prescribed amplitude at its center. -/
-- @node: localizedPackingBump_center
lemma localizedPackingBump_center (delta w : ℝ) (center : Score) :
    localizedPackingBump delta w center center = delta := by
  simp [localizedPackingBump, packingBump_zero]

/-- A nonnegative localized bump is bounded by its amplitude. -/
-- @node: localizedPackingBump_mem_Icc
lemma localizedPackingBump_mem_Icc {delta w : ℝ} (hdelta : 0 ≤ delta)
    (center x : Score) : localizedPackingBump delta w center x ∈ Icc 0 delta := by
  have hb := packingBump_mem_Icc (w⁻¹ • (x - center))
  exact ⟨mul_nonneg hdelta hb.1, (mul_le_mul_of_nonneg_left hb.2 hdelta).trans_eq
    (mul_one delta)⟩

/-- A positive-bandwidth localized bump vanishes at distance at least `w`
from its center. -/
-- @node: localizedPackingBump_eq_zero_of_bandwidth_le_dist
lemma localizedPackingBump_eq_zero_of_bandwidth_le_dist {delta w : ℝ}
    {center x : Score} (hw : 0 < w) (hx : w ≤ dist x center) :
    localizedPackingBump delta w center x = 0 := by
  have hnorm : 1 ≤ ‖w⁻¹ • (x - center)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw]
    rw [inv_mul_eq_div, one_le_div hw]
    simpa [dist_eq_norm] using hx
  rw [localizedPackingBump, packingBump_eq_zero_of_one_le_norm hnorm, mul_zero]

/-- Translation and nonzero rescaling preserve smoothness of the radial bump. -/
-- @node: localizedPackingBump_contDiff
lemma localizedPackingBump_contDiff (delta w : ℝ) (center : Score) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (localizedPackingBump delta w center) := by
  unfold localizedPackingBump
  have hi : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Score => w⁻¹ • (x - center)) :=
    ContDiff.const_smul w⁻¹ (contDiff_id.sub contDiff_const)
  have hb := packingBump_contDiff.comp hi
  simpa [Function.comp_def] using ContDiff.const_smul delta hb

/-- The small affine baseline used in every member of the hard family. -/
-- @node: packingAffineBaseline
noncomputable def packingAffineBaseline (b : ℝ) (x : Score) : ℝ :=
  1 / 2 + b * x 0

/-- A slope of absolute value at most `1/2` keeps the affine baseline in
`[1/4,3/4]` throughout the unit square. -/
-- @node: packingAffineBaseline_mem_Icc
lemma packingAffineBaseline_mem_Icc {b : ℝ} (hb : |b| ≤ 1 / 2)
    {x : Score} (hx : x ∈ scoreCube (1 / 2)) :
    packingAffineBaseline b x ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hprod : |b * x 0| ≤ 1 / 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg b, abs_nonneg (x 0), hx 0]
  rw [abs_le] at hprod
  constructor <;> unfold packingAffineBaseline <;> linarith

/-- The affine baseline is smooth to every finite order. -/
-- @node: packingAffineBaseline_contDiff
lemma packingAffineBaseline_contDiff (b : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (packingAffineBaseline b) := by
  unfold packingAffineBaseline
  fun_prop

/-- The regression profile obtained by adding the active disjoint radial bumps
to the common affine baseline. -/
-- @node: packingRegression
noncomputable def packingRegression {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (x : Score) : ℝ :=
  packingAffineBaseline b x +
    ∑ j, if omega j then localizedPackingBump delta w (centers j) x else 0

/-- Every finite packing regression is smooth to every finite order. -/
-- @node: packingRegression_contDiff
lemma packingRegression_contDiff {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (packingRegression b delta w centers omega) := by
  unfold packingRegression
  apply (packingAffineBaseline_contDiff b).add
  apply ContDiff.sum
  intro j _
  split
  · exact localizedPackingBump_contDiff delta w (centers j)
  · exact contDiff_const

/-- Every finite packing regression is Borel measurable. -/
-- @node: packingRegression_measurable
lemma packingRegression_measurable {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    Measurable (packingRegression b delta w centers omega) :=
  (packingRegression_contDiff b delta w centers omega).continuous.measurable

/-- Inside one closed packing ball, the regression depends on the bit vector
only through that ball's coordinate. -/
-- @node: packingRegression_eq_on_cell
lemma packingRegression_eq_on_cell {M : ℕ} {b delta w : ℝ} (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {omega omega' : Fin M → Bool} {j : Fin M} (hbit : omega j = omega' j)
    {x : Score} (hx : x ∈ Metric.closedBall (centers j) w) :
    packingRegression b delta w centers omega x =
      packingRegression b delta w centers omega' x := by
  unfold packingRegression
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    rw [hbit]
  · have hfar : w ≤ dist x (centers i) := by
      have htri : dist (centers i) (centers j) ≤
          dist (centers i) x + dist x (centers j) := dist_triangle _ _ _
      have hs := hsep i j hij
      rw [Metric.mem_closedBall] at hx
      rw [dist_comm (centers i) x] at htri
      linarith
    rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw hfar]
    simp

/-- Away from every closed packing ball, all radial bumps vanish and the
regression equals the common affine baseline. -/
-- @node: packingRegression_eq_off_cells
lemma packingRegression_eq_off_cells {M : ℕ} {b delta w : ℝ} (hw : 0 < w)
    {centers : Fin M → Score} (omega : Fin M → Bool)
    {x : Score} (hx : ∀ j, x ∉ Metric.closedBall (centers j) w) :
    packingRegression b delta w centers omega x = packingAffineBaseline b x := by
  unfold packingRegression
  rw [Finset.sum_eq_zero]
  · simp
  · intro j _
    have hfar : w ≤ dist x (centers j) := by
      have hlt : w < dist x (centers j) := by
        simpa [Metric.mem_closedBall, not_le] using hx j
      exact hlt.le
    rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw hfar]
    simp

/-- At a separated grid center all other radial bumps vanish, so the regression
value depends only on that center's bit. -/
-- @node: packingRegression_center
lemma packingRegression_center {M : ℕ} {b delta w : ℝ}
    {centers : Fin M → Score} (omega : Fin M → Bool) (j : Fin M)
    (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k)) :
    packingRegression b delta w centers omega (centers j) =
      packingAffineBaseline b (centers j) + if omega j then delta else 0 := by
  unfold packingRegression
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [localizedPackingBump_center]
  · intro i _ hij
    have hfar : w ≤ dist (centers j) (centers i) := by
      have hs := hsep j i (Ne.symm hij)
      linarith
    rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw hfar]
    split <;> simp
  · simp

/-- The two possible regression values at a packing center are separated by
exactly the bump amplitude. -/
-- @node: packingRegression_center_separation
lemma packingRegression_center_separation {M : ℕ} (b delta : ℝ)
    (centers : Fin M → Score) (j : Fin M) :
    |(packingAffineBaseline b (centers j) + delta) -
        packingAffineBaseline b (centers j)| = |delta| := by
  ring_nf

/-- The two declared regression values at a packing center, indexed by its
Boolean coordinate. -/
-- @node: packingCenterValue
noncomputable def packingCenterValue {M : ℕ} (b delta : ℝ)
    (centers : Fin M → Score) (j : Fin M) (bit : Bool) : ℝ :=
  packingAffineBaseline b (centers j) + if bit then delta else 0

/-- A separated packing regression takes exactly its declared Boolean value
at every grid center. -/
-- @node: packingRegression_eq_packingCenterValue
lemma packingRegression_eq_packingCenterValue {M : ℕ} {b delta w : ℝ}
    {centers : Fin M → Score} (omega : Fin M → Bool) (j : Fin M)
    (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k)) :
    packingRegression b delta w centers omega (centers j) =
      packingCenterValue b delta centers j (omega j) := by
  rw [packingRegression_center omega j hw hsep]
  rfl

/-- For a nonnegative bump amplitude, the two declared center values are
separated by exactly that amplitude. -/
-- @node: packingCenterValue_true_false
lemma packingCenterValue_true_false {M : ℕ} {b delta : ℝ}
    (hdelta : 0 ≤ delta) (centers : Fin M → Score) (j : Fin M) :
    |packingCenterValue b delta centers j true -
        packingCenterValue b delta centers j false| = delta := by
  simpa [packingCenterValue, abs_of_nonneg hdelta] using
    packingRegression_center_separation b delta centers j

/-- At the selected packing amplitude, the two center values have the exact
fixed-constant frontier-rate separation used by `AngularPackingAt`. -/
-- @node: packingCenterValue_frontierRate_separation
lemma packingCenterValue_frontierRate_separation {M n : ℕ} (hn : 2 ≤ n)
    (b : ℝ) (centers : Fin M → Score) (j : Fin M) :
    |packingCenterValue b (angularPackingDelta n) centers j true -
        packingCenterValue b (angularPackingDelta n) centers j false| =
      (1 / 1024 : ℝ) * frontierRate n := by
  rw [packingCenterValue_true_false
    (show 0 ≤ angularPackingDelta n by
      unfold angularPackingDelta
      exact div_nonneg (frontierRate_pos hn).le (by norm_num))]
  unfold angularPackingDelta
  ring

/-- At any point, a three-bandwidth-separated family of localized bumps has
total active amplitude between zero and the amplitude of one bump. -/
-- @node: packingRegression_bump_sum_mem_Icc
lemma packingRegression_bump_sum_mem_Icc {M : ℕ} {delta w : ℝ}
    (hdelta : 0 ≤ delta) (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (x : Score) :
    (∑ j, if omega j then localizedPackingBump delta w (centers j) x else 0)
      ∈ Icc 0 delta := by
  have hnonneg : ∀ j : Fin M,
      0 ≤ if omega j then localizedPackingBump delta w (centers j) x else 0 := by
    intro j
    split
    · exact (localizedPackingBump_mem_Icc hdelta (centers j) x).1
    · exact le_rfl
  constructor
  · exact Finset.sum_nonneg fun j _ => hnonneg j
  · by_cases hex : ∃ j, omega j = true ∧
        localizedPackingBump delta w (centers j) x ≠ 0
    · obtain ⟨j, hjbit, hjne⟩ := hex
      rw [Finset.sum_eq_single j]
      · simp [hjbit]
        exact (localizedPackingBump_mem_Icc hdelta (centers j) x).2
      · intro i _ hij
        have hzero : localizedPackingBump delta w (centers i) x = 0 := by
          by_contra hine
          have hxi : dist x (centers i) < w := by
            apply lt_of_not_ge
            intro hfar
            exact hine (localizedPackingBump_eq_zero_of_bandwidth_le_dist hw hfar)
          have hxj : dist x (centers j) < w := by
            apply lt_of_not_ge
            intro hfar
            exact hjne (localizedPackingBump_eq_zero_of_bandwidth_le_dist hw hfar)
          have htri : dist (centers i) (centers j) ≤
              dist (centers i) x + dist x (centers j) := dist_triangle _ _ _
          have hs := hsep i j hij
          rw [dist_comm (centers i) x] at htri
          linarith
        simp [hzero]
      · simp
    · have hzero : ∀ j : Fin M,
          (if omega j then localizedPackingBump delta w (centers j) x else 0) = 0 := by
        intro j
        by_cases hj : omega j = true
        · simp only [hj, if_true]
          by_contra hjne
          exact hex ⟨j, hj, hjne⟩
        · have hjfalse : omega j = false := Bool.eq_false_of_not_eq_true hj
          simp [hjfalse]
      rw [Finset.sum_eq_zero fun j _ => hzero j]
      exact hdelta

/-- With the paper's small affine slope and bump amplitude, every packing
regression stays in `[1/4,3/4]` on the unit square. -/
-- @node: packingRegression_mem_Icc
lemma packingRegression_mem_Icc {M : ℕ} {b delta w : ℝ}
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2)) :
    packingRegression b delta w centers omega x ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hx0 := hx (0 : Fin 2)
  have hprod : |b * x 0| ≤ 1 / 8 := by
    rw [abs_mul]
    nlinarith [abs_nonneg b, abs_nonneg (x 0)]
  have hbase : packingAffineBaseline b x ∈ Icc (3 / 8 : ℝ) (5 / 8 : ℝ) := by
    rw [abs_le] at hprod
    constructor <;> unfold packingAffineBaseline <;> linarith
  have hsum := packingRegression_bump_sum_mem_Icc hdelta0 hw hsep omega x
  unfold packingRegression
  constructor
  · calc
      (1 / 4 : ℝ) ≤ 3 / 8 := by norm_num
      _ ≤ packingAffineBaseline b x := hbase.1
      _ ≤ packingAffineBaseline b x +
          ∑ j, if omega j then localizedPackingBump delta w (centers j) x else 0 :=
        le_add_of_nonneg_right hsum.1
  · calc
      packingAffineBaseline b x +
          (∑ j, if omega j then localizedPackingBump delta w (centers j) x else 0) ≤
          5 / 8 + delta := add_le_add hbase.2 hsum.2
      _ ≤ (3 / 4 : ℝ) := by linarith

/-- The globally bounded version of the packing regression used to define a
Markov outcome kernel.  It agrees with the paper regression everywhere on the
supporting square, where the latter already lies in the middle half of the
unit interval. -/
-- @node: clippedPackingRegression
noncomputable def clippedPackingRegression {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (x : Score) : ℝ :=
  max 0 (min 1 (packingRegression b delta w centers omega x))

/-- The clipped packing regression takes values in the unit interval on the
whole ambient score space. -/
-- @node: clippedPackingRegression_mem_Icc
lemma clippedPackingRegression_mem_Icc {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (x : Score) :
    clippedPackingRegression b delta w centers omega x ∈ Icc (0 : ℝ) 1 := by
  unfold clippedPackingRegression
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- Clipping does not alter a packing regression value that is already in the
unit interval. -/
-- @node: clippedPackingRegression_eq_of_mem_Icc
lemma clippedPackingRegression_eq_of_mem_Icc {M : ℕ} {b delta w : ℝ}
    {centers : Fin M → Score} {omega : Fin M → Bool} {x : Score}
    (hx : packingRegression b delta w centers omega x ∈ Icc (0 : ℝ) 1) :
    clippedPackingRegression b delta w centers omega x =
      packingRegression b delta w centers omega x := by
  unfold clippedPackingRegression
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- On the supporting square, the globally clipped kernel regression agrees
with the paper's smooth packing regression. -/
-- @node: clippedPackingRegression_eq_on_square
lemma clippedPackingRegression_eq_on_square {M : ℕ} {b delta w : ℝ}
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2)) :
    clippedPackingRegression b delta w centers omega x =
      packingRegression b delta w centers omega x := by
  apply clippedPackingRegression_eq_of_mem_Icc
  have hp := packingRegression_mem_Icc hb hdelta0 hdelta hw hsep omega hx
  constructor <;> linarith [hp.1, hp.2]

/-- Within one square-truncated packing cell, the globally clipped regression
depends on a packing vertex only through that cell's Boolean coordinate. -/
-- @node: clippedPackingRegression_eq_on_cell
lemma clippedPackingRegression_eq_on_cell {M : ℕ} {b delta w : ℝ}
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {omega omega' : Fin M → Bool} {j : Fin M} (hbit : omega j = omega' j)
    {x : Score}
    (hx : x ∈ Metric.closedBall (centers j) w ∩ scoreCube (1 / 2 : ℝ)) :
    clippedPackingRegression b delta w centers omega x =
      clippedPackingRegression b delta w centers omega' x := by
  rw [clippedPackingRegression_eq_on_square hb hdelta0 hdelta hw hsep omega hx.2,
    clippedPackingRegression_eq_on_square hb hdelta0 hdelta hw hsep omega' hx.2]
  exact packingRegression_eq_on_cell hw hsep hbit hx.1

/-- The globally clipped packing regression is Borel measurable. -/
-- @node: clippedPackingRegression_measurable
lemma clippedPackingRegression_measurable {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    Measurable (clippedPackingRegression b delta w centers omega) := by
  unfold clippedPackingRegression
  exact measurable_const.max
    (measurable_const.min (packingRegression_measurable b delta w centers omega))

/-- The globally clipped packing regression is continuous. -/
-- @node: clippedPackingRegression_continuous
lemma clippedPackingRegression_continuous {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    Continuous (clippedPackingRegression b delta w centers omega) := by
  unfold clippedPackingRegression
  exact continuous_const.max
    (continuous_const.min (packingRegression_contDiff b delta w centers omega).continuous)

/-- The conditional variance profile generated by a Bernoulli regression and
independent unit Gaussian noise. -/
-- @node: packingConditionalVariance
noncomputable def packingConditionalVariance {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (x : Score) : ℝ :=
  let p := packingRegression b delta w centers omega x
  1 + p * (1 - p)

/-- Within a packing cell, the conditional variance depends only on the same
single bit as the regression. -/
-- @node: packingConditionalVariance_eq_on_cell
lemma packingConditionalVariance_eq_on_cell {M : ℕ} {b delta w : ℝ}
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {omega omega' : Fin M → Bool} {j : Fin M} (hbit : omega j = omega' j)
    {x : Score} (hx : x ∈ Metric.closedBall (centers j) w) :
    packingConditionalVariance b delta w centers omega x =
      packingConditionalVariance b delta w centers omega' x := by
  unfold packingConditionalVariance
  rw [packingRegression_eq_on_cell hw hsep hbit hx]

/-- The conditional variance profile is continuous (indeed smooth). -/
-- @node: packingConditionalVariance_continuous
lemma packingConditionalVariance_continuous {M : ℕ} (b delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    Continuous (packingConditionalVariance b delta w centers omega) := by
  have hp := (packingRegression_contDiff b delta w centers omega).continuous
  unfold packingConditionalVariance
  fun_prop

/-- Under the bump envelope hypotheses, the entire conditional variance
profile lies in `[1,5/4]` on the packing square. -/
-- @node: packingConditionalVariance_mem_Icc
lemma packingConditionalVariance_mem_Icc {M : ℕ} {b delta w : ℝ}
    (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 8)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2)) :
    packingConditionalVariance b delta w centers omega x ∈
      Icc (1 : ℝ) (5 / 4 : ℝ) := by
  exact Causalean.Mathlib.InformationTheory.one_add_mul_one_sub_mem_Icc
    (packingRegression_mem_Icc hb hdelta0 hdelta hw hsep omega hx)

/-- For every paper envelope `L ≥ 4`, the preceding variance interval is
contained in `[L⁻¹,L]`. -/
-- @node: packingConditionalVariance_envelope
lemma packingConditionalVariance_envelope {M : ℕ} {L b delta w : ℝ}
    (hL : 4 ≤ L) (hb : |b| ≤ 1 / 4) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / 8) (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {x : Score} (hx : x ∈ scoreCube (1 / 2)) :
    L⁻¹ ≤ packingConditionalVariance b delta w centers omega x ∧
      packingConditionalVariance b delta w centers omega x ≤ L := by
  have hvar := packingConditionalVariance_mem_Icc hb hdelta0 hdelta hw hsep omega hx
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  constructor
  · exact ((inv_le_one₀ hL0).2 (by linarith)).trans hvar.1
  · exact hvar.2.trans (by linarith)

end CausalSmith.Stat.BddUniformLogPenalty
