module

public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Data.Set.Pairwise.Chain
public import Mathlib.Order.Zorn
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Finite nets in finite-dimensional normed spaces

This file provides dimension-explicit finite nets for bounded subsets of a
finite-dimensional real normed space.  The general statement
`exists_internal_net_card_le` covers an arbitrary subset of the closed unit ball
at an arbitrary scale `v`, with net points drawn from the set itself and
cardinality at most `(1 + 2 / v) ^ finrank ℝ E`; `exists_unit_ball_net_card_le`
and `exists_half_net_card_le_five_pow_finrank` are the unit-ball and
unit-sphere-at-scale-`1/2` specializations.
-/

@[expose] public section

open Metric Module Set MeasureTheory
open scoped ENNReal NNReal Function

noncomputable section

namespace Causalean

/-- Every subset of the closed unit ball of a finite-dimensional real normed space admits an
internal net at any prescribed accuracy `v`: finitely many points, all taken from the set
itself, such that every point of the set is within distance `v` of one of them, and the number
of net points is at most `(1 + 2 / v)` raised to the dimension of the space.

The net is obtained by taking a maximal `v`-separated subset; the cardinality bound comes from
comparing the total volume of the disjoint balls of radius `v / 2` around the net points with
the volume of the ball of radius `1 + v / 2` containing them. -/
lemma exists_internal_net_card_le (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : Set E) (hA : ∀ x ∈ A, ‖x‖ ≤ 1) {v : ℝ} (hv : 0 < v) :
    ∃ N : Finset E,
      (∀ y ∈ N, y ∈ A) ∧
      (∀ x ∈ A, ∃ y ∈ N, ‖x - y‖ ≤ v) ∧
      (N.card : ℝ) ≤ (1 + 2 / v) ^ finrank ℝ E := by
  classical
  let ε : ℝ≥0 := ⟨v, hv.le⟩
  have hε : (ε : ℝ≥0∞) = ENNReal.ofReal v := by
    exact ENNReal.coe_nnreal_eq ε
  have hAball : A ⊆ closedBall (0 : E) 1 := fun x hx ↦ by
    simpa [mem_closedBall, dist_zero_right] using hA x hx
  obtain ⟨M, hM⟩ :
      ∃ M : Set E, Maximal (fun N ↦ N ⊆ A ∧ Metric.IsSeparated ε N) M := by
    apply zorn_subset
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun s hs ↦ subset_sUnion_of_mem hs⟩
    constructor
    · exact sUnion_subset fun s hs ↦ (hc hs).1
    · rw [Metric.IsSeparated, hchain.pairwise_sUnion]
      exact fun s hs ↦ (hc hs).2
  have hMsub : M ⊆ A := hM.prop.1
  have hMsep : Metric.IsSeparated ε M := hM.prop.2
  have hMcover : Metric.IsCover ε A M := Metric.IsCover.of_maximal_isSeparated hM
  obtain ⟨t, _htB, htfinite, htcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : E) 1) (half_pos hv)
  have hsmall : ∀ c : E, (M ∩ ball c (v / 2)).Subsingleton := by
    intro c x hx y hy
    by_contra hxy
    have hsep := hMsep hx.1 hy.1 hxy
    have hdist : dist x y < v := by
      calc
        dist x y ≤ dist x c + dist y c := dist_triangle_right x y c
        _ < v / 2 + v / 2 := add_lt_add (mem_ball.mp hx.2) (mem_ball.mp hy.2)
        _ = v := by ring
    have hdist' : edist x y < (ε : ℝ≥0∞) := by
      rw [edist_dist, hε, ENNReal.ofReal_lt_ofReal_iff hv]
      exact hdist
    exact (not_lt_of_ge hsep.le) hdist'
  have hMfinite : M.Finite := by
    have hUfinite : (⋃ c ∈ t, M ∩ ball c (v / 2)).Finite :=
      htfinite.biUnion fun c _ ↦ (hsmall c).finite
    apply hUfinite.subset
    intro x hx
    obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (htcover (hAball (hMsub hx)))
    exact mem_iUnion₂.mpr ⟨c, hct, hx, hxc⟩
  let N : Finset E := hMfinite.toFinset
  have hNsub : ∀ y ∈ N, y ∈ A := fun y hy ↦ hMsub (by simpa [N] using hy)
  have hNmem : ∀ y ∈ N, ‖y‖ ≤ 1 := fun y hy ↦ hA y (hNsub y hy)
  have hNcover : ∀ x ∈ A, ∃ y ∈ N, ‖x - y‖ ≤ v := by
    intro x hx
    obtain ⟨y, hyM, hxy⟩ := hMcover hx
    refine ⟨y, by simpa [N] using hyM, ?_⟩
    change edist x y ≤ (ε : ℝ≥0∞) at hxy
    rw [edist_dist, hε, ENNReal.ofReal_le_ofReal_iff hv.le] at hxy
    simpa [dist_eq_norm] using hxy
  refine ⟨N, hNsub, hNcover, ?_⟩
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := v / 2
  let ρ : ℝ := 1 + v / 2
  have hδ : 0 < δ := div_pos hv (by norm_num)
  have hρ : 0 < ρ := by positivity
  set U := ⋃ c ∈ N, ball (c : E) δ with hU
  have hdisj : Set.Pairwise (N : Set E) (Disjoint on fun c ↦ ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    have hsep := hMsep (by simpa [N] using hc) (by simpa [N] using hd) hcd
    have hdist : v < dist c d := by
      change (ε : ℝ≥0∞) < edist c d at hsep
      rw [edist_dist, hε, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hv.le] at hsep
      exact hsep
    simpa [δ] using hdist.le
  have hUsub : U ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx ↦ ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (hNmem x hx)
      _ = ρ := by simp [δ, ρ, add_comm]
  have hvol :
      (N.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (N.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ U := by
        rw [hU, measure_biUnion_finset hdisj fun c _ ↦ measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hUsub
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hρ]
  have hcancel :
      (N.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvol
  have hreal : (N.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have h := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by simp) (by simp))
      (by simp : ENNReal.ofReal (ρ ^ finrank ℝ E) ≠ ∞)).2 hcancel
    simpa [ENNReal.toReal_ofReal (pow_nonneg hδ.le _),
      ENNReal.toReal_ofReal (pow_nonneg hρ.le _)] using h
  have hδpow : 0 < δ ^ finrank ℝ E := pow_pos hδ _
  calc
    (N.card : ℝ) ≤ ρ ^ finrank ℝ E / δ ^ finrank ℝ E := (le_div_iff₀ hδpow).2 hreal
    _ = (1 + 2 / v) ^ finrank ℝ E := by
      rw [← div_pow]
      congr 1
      field_simp [δ, ρ, hv.ne']
      ring

/-- The closed unit ball of a finite-dimensional real normed space has, at every accuracy `v`,
a finite net of at most `(1 + 2 / v)` raised to the dimension of the space many points. -/
lemma exists_unit_ball_net_card_le (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : ℝ} (hv : 0 < v) :
    ∃ N : Finset E,
      (∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ N, ‖x - y‖ ≤ v) ∧
      (N.card : ℝ) ≤ (1 + 2 / v) ^ finrank ℝ E := by
  obtain ⟨N, _hNsub, hNcover, hNcard⟩ :=
    exists_internal_net_card_le E {x : E | ‖x‖ ≤ 1} (by simp) hv
  exact ⟨N, by simpa using hNcover, hNcard⟩

/-- For [a finite-dimensional real normed space `E`](hyp:E), [there exists a finite
set of unit vectors, of size at most `5` raised to the dimension of `E`, that
forms a half-net of the unit sphere: every unit vector lies within distance
`1/2` of some point in the set](goal). -/
lemma exists_half_net_card_le_five_pow_finrank (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ = 1) ∧
      (∀ x, ‖x‖ = 1 → ∃ v ∈ N, ‖x - v‖ ≤ (1 : ℝ) / 2) ∧
      N.card ≤ 5 ^ finrank ℝ E := by
  obtain ⟨N, hNsub, hNcover, hNcard⟩ :=
    exists_internal_net_card_le E {x : E | ‖x‖ = 1} (fun x hx ↦ le_of_eq hx)
      (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨N, hNsub, hNcover, ?_⟩
  have h5 : (1 : ℝ) + 2 / (1 / 2) = 5 := by
    rw [show (2 : ℝ) / (1 / 2) = 4 by norm_num]
    norm_num
  rw [h5] at hNcard
  exact_mod_cast hNcard

end Causalean
