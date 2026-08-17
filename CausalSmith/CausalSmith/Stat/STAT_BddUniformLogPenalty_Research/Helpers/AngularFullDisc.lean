import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularMeasure

/-!
# Full-disc angular cancellation

The causal hard-square construction places its angular cells on an interior
assignment boundary.  Its score cells are therefore complete disks rather
than the support-boundary half-disks used by the original angular packing.
This module supplies the corresponding zero-mass cancellation.
-/

open MeasureTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- A radial angular correction integrates to zero on every complete disk.
Point reflection through the disk center preserves Lebesgue measure and the
disk while negating the direction cosine. -/
-- @node: packingAngularTerm_integral_closedBall
lemma packingAngularTerm_integral_closedBall {b cA delta w : ℝ}
    (center : Score) :
    (∫ x : Score in Metric.closedBall center w,
      packingAngularTerm b cA delta w center x) = 0 := by
  let T : Score → Score := fun x => (2 : ℝ) • center - x
  have hT : MeasurePreserving T (volume : Measure Score) volume := by
    exact (measurePreserving_add_left volume ((2 : ℝ) • center)).comp
      (Measure.measurePreserving_neg volume)
  have hTemb : MeasurableEmbedding T := by
    let e : Score ≃ₜ Score := (Homeomorph.neg Score).trans
      (Homeomorph.addLeft ((2 : ℝ) • center))
    exact e.measurableEmbedding
  have himage : T '' Metric.closedBall center w = Metric.closedBall center w := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall] at hy ⊢
      have hid : (2 : ℝ) • center - y - center = -(y - center) := by module
      have hd : dist (T y) center = dist y center := by
        rw [dist_eq_norm, dist_eq_norm, show T y - center = -(y - center) by
          exact hid]
        exact norm_neg _
      simpa [hd] using hy
    · intro hx
      refine ⟨T x, ?_, ?_⟩
      · rw [Metric.mem_closedBall] at hx ⊢
        have hid : (2 : ℝ) • center - x - center = -(x - center) := by module
        have hd : dist (T x) center = dist x center := by
          rw [dist_eq_norm, dist_eq_norm, show T x - center = -(x - center) by
            exact hid]
          exact norm_neg _
        simpa [hd] using hx
      · simp [T]
  have hodd : ∀ x, packingAngularTerm b cA delta w center (T x) =
      -packingAngularTerm b cA delta w center x := by
    intro x
    unfold packingAngularTerm packingDirectionCos
    have hdist : dist (T x) center = dist x center := by
      rw [dist_eq_norm, dist_eq_norm, show T x - center = -(x - center) by
        dsimp [T]
        module]
      exact norm_neg _
    rw [hdist]
    by_cases hx : dist x center = 0
    · simp [hx]
    · simp only [hx, if_false]
      simp [T]
      ring
  have hchange := hT.setIntegral_image_emb hTemb
    (packingAngularTerm b cA delta w center) (Metric.closedBall center w)
  rw [himage] at hchange
  simp_rw [hodd] at hchange
  rw [integral_neg] at hchange
  linarith [hchange]

/-- A separated angular density integrates over each complete packing disk to
the disk's ordinary Lebesgue area, independently of every Boolean bit. -/
-- @node: packingAngularDensity_integral_closedBall
lemma packingAngularDensity_integral_closedBall {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k)) :
    (∫ x : Score in Metric.closedBall (centers j) w,
      packingAngularDensity b cA delta w centers omega x) =
      (volume (Metric.closedBall (centers j) w)).toReal := by
  have hconst : IntegrableOn (fun _ : Score ↦ (1 : ℝ))
      (Metric.closedBall (centers j) w) :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hterms : ∀ i : Fin M, IntegrableOn
      (fun x : Score ↦ if omega i then
        packingAngularTerm b cA delta w (centers i) x else 0)
      (Metric.closedBall (centers j) w) := by
    intro i
    by_cases hi : omega i = true
    · simpa [hi] using
        (packingAngularTerm_continuous hb hscale
          (centers i)).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    · have hif : omega i = false := Bool.eq_false_of_not_eq_true hi
      simpa [hif] using continuous_const.continuousOn.integrableOn_compact
        (K := Metric.closedBall (centers j) w) (isCompact_closedBall _ _)
  unfold packingAngularDensity
  rw [integral_add hconst (integrable_finset_sum _ fun i _ ↦ hterms i),
    integral_const]
  rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  simp only [smul_eq_mul, mul_one]
  rw [integral_finset_sum _ fun i _ ↦ hterms i, add_eq_left]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : omega i = true
  · simp only [hi, if_true]
    by_cases hij : i = j
    · subst i
      exact packingAngularTerm_integral_closedBall (b := b) (cA := cA)
        (delta := delta) (w := w) (centers j)
    · apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem
        Metric.isClosed_closedBall.measurableSet] with x hx
      apply packingAngularTerm_eq_zero_of_bandwidth_le_dist hw
      rw [Metric.mem_closedBall] at hx
      have htri : dist (centers i) (centers j) ≤
          dist (centers i) x + dist x (centers j) := dist_triangle _ _ _
      have hs := hsep i j hij
      rw [dist_comm (centers i) x] at htri
      linarith
  · have hif : omega i = false := Bool.eq_false_of_not_eq_true hi
    simp [hif]

end CausalSmith.Stat.BddUniformLogPenalty
