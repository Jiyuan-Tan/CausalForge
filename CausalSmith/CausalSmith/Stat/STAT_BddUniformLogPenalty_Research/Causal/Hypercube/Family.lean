import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Profiles
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareClassGeometry
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.CoordinateEnvelope

/-!
# Decorated laws in the causal hard family

This module packages the normalized angular score measure and the two
Bernoulli profiles into the selected-kernel potential-outcome law used at
each hypercube vertex.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The causal hard law at one Boolean vertex.  Its score marginal is the
angular design on the fixed square and its selected arm kernels are exactly
the Bernoulli kernels used to construct the joint potential-outcome law. -/
-- @node: causalHardA1A2Law
noncomputable def causalHardA1A2Law {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare) : A1A2Law := by
  let nu := causalHardScoreMeasure b cA delta w centers omega
  let p0 := causalHardControlProfile
  let p1 := causalHardTreatmentProfile delta w centers omega
  have hp := causalHardProfiles_measurable delta w centers omega
  letI : IsProbabilityMeasure nu :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega hb hscale hcA
      hdelta hw hsep hcell
  exact causalBernoulliA1A2Law nu causalHardSquare
    (causalHardSquare \ causalHardArmOne) causalHardArmOne
    (frontier causalHardArmOne)
    (causalHardScoreDensity b cA delta w centers omega) p0 p1
    hp.1 hp.2
    (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).1.1)
    (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).1.2)
    (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).2.1)
    (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).2.2)
    causalHardArmZero_measurableSet causalHardArmOne_measurableSet
    causalHardAssignment_partition causalHardAssignment_frontier.symm
    causalHardFrontier_compact_and_interior.2 rfl
    (causalHardScoreMeasure_support centers omega hb hscale hcA hdelta hw hsep).symm

/-- Every vertex law has the prescribed common support and assignment
geometry. -/
-- @node: causalHardA1A2Law_geometry
lemma causalHardA1A2Law_geometry {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    P.support = causalHardSquare ∧
      P.A1 = causalHardArmOne ∧
      P.A0 = causalHardSquare \ causalHardArmOne ∧
      P.boundary = frontier causalHardArmOne := by
  simp [causalHardA1A2Law, causalBernoulliA1A2Law]

/-- At every score, the hard law's selected conditional means are the two
profiles supplied to its Bernoulli kernels. -/
-- @node: causalHardA1A2Law_muPO
lemma causalHardA1A2Law_muPO {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    (t : Bool) (x : Score) :
    (causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
      hsep hcell).muPO t x =
      if t then causalHardTreatmentProfile delta w centers omega x
      else causalHardControlProfile x := by
  cases t <;> rfl

/-- Every indexed coordinate partial of the constant control profile is
`1/2` at order zero and vanishes at positive order. -/
-- @node: causalHardControlProfile_coordinatePartial
lemma causalHardControlProfile_coordinatePartial (alpha : Fin 2 → ℕ)
    (x : Score) :
    coordinatePartial causalHardControlProfile alpha x =
      if coordinateMultiOrder alpha = 0 then 1 / 2 else 0 := by
  unfold coordinatePartial causalHardControlProfile
  by_cases hk : coordinateMultiOrder alpha = 0
  · have ha : alpha = fun _ => 0 := by
      change alpha 0 + alpha 1 = 0 at hk
      funext i
      fin_cases i
      · simpa using Nat.eq_zero_of_add_eq_zero_right hk
      · simpa using Nat.eq_zero_of_add_eq_zero_left hk
    subst alpha
    change (iteratedFDeriv ℝ 0 (fun _ : Score => (1 / 2 : ℝ)) x) _ = 1 / 2
    exact rfl
  · rw [iteratedFDeriv_const_of_ne hk]
    simp [hk]

/-- The common control profile has the paper's Euclidean smooth-extension
envelope for every bound at least `1/2`. -/
-- @node: causalHardControlProfile_euclideanCExtEnvelope
lemma causalHardControlProfile_euclideanCExtEnvelope (p : ℕ) {L : ℝ}
    (hL : 1 / 2 ≤ L) :
    EuclideanCExtEnvelope causalHardControlProfile p L causalHardSquare := by
  refine ⟨Set.univ, isOpen_univ, subset_univ _, causalHardControlProfile,
    contDiffOn_const, (fun _ _ => rfl), ?_, ?_, ?_⟩
  · refine ⟨1 / 2, ?_⟩
    rintro r ⟨alpha, halpha, x, hx, rfl⟩
    rw [causalHardControlProfile_coordinatePartial]
    split <;> norm_num
  · refine ⟨0, ?_⟩
    rintro r ⟨alpha, halpha, x, hx, z, hz, hxz, rfl⟩
    simp [causalHardControlProfile_coordinatePartial]
  · have hnonempty : (coordinatePartialValues causalHardControlProfile p
        causalHardSquare).Nonempty := by
      refine ⟨1 / 2, fun _ => 0, by simp [coordinateMultiOrder],
        scorePoint 0 0, ?_, ?_⟩
      · intro i
        fin_cases i <;> norm_num [scorePoint]
      · norm_num [causalHardControlProfile_coordinatePartial,
          coordinateMultiOrder]
    have hpartial : sSup (coordinatePartialValues causalHardControlProfile p
        causalHardSquare) ≤ 1 / 2 := csSup_le hnonempty (by
      rintro r ⟨alpha, halpha, x, hx, rfl⟩
      rw [causalHardControlProfile_coordinatePartial]
      split <;> norm_num)
    have hlip : sSup (coordinatePartialLipschitzValues
        causalHardControlProfile p causalHardSquare) ≤ 0 := csSup_le (by
      refine ⟨0, fun _ => 0, by simp [coordinateMultiOrder],
        scorePoint 0 0, ?_, scorePoint 1 0, ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> norm_num [scorePoint]
      · intro i
        fin_cases i <;> norm_num [scorePoint]
      · intro h
        have hcoord := congrArg (fun y : Score => y 0) h
        norm_num [scorePoint] at hcoord
      · simp [causalHardControlProfile_coordinatePartial]) (by
        rintro r ⟨alpha, halpha, x, hx, z, hz, hxz, rfl⟩
        simp [causalHardControlProfile_coordinatePartial])
    linarith

/-- Every hard-family vertex satisfies the smooth-extension clause for its
control-arm regression. -/
-- @node: causalHardA1A2Law_control_euclideanCExtEnvelope
lemma causalHardA1A2Law_control_euclideanCExtEnvelope {M : ℕ}
    (p : ℕ) (b cA delta w : ℝ) (centers : Fin M → Score)
    (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    {L : ℝ} (hL : 1 / 2 ≤ L) :
    EuclideanCExtEnvelope
      ((causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
        hsep hcell).muPO false) p L causalHardSquare := by
  exact causalHardControlProfile_euclideanCExtEnvelope p hL

/-- Every complete hard cell has the advertised bit-independent probability
under the full potential-outcome law. -/
-- @node: causalHardA1A2Law_cell_mass
lemma causalHardA1A2Law_cell_mass {M : ℕ} (j : Fin M)
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare) :
    (causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
      hsep hcell).law {z | causalScore z ∈ causalHardCell (centers j) w} =
      ENNReal.ofReal (Real.pi * w ^ 2 / 36) := by
  let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
    hsep hcell
  have hC : MeasurableSet (causalHardCell (centers j) w) :=
    Metric.isClosed_closedBall.measurableSet
  rw [show {z | causalScore z ∈ causalHardCell (centers j) w} =
      causalScore ⁻¹' causalHardCell (centers j) w by rfl]
  rw [← Measure.map_apply (by unfold causalScore; fun_prop) hC]
  rw [P.marginal_eq]
  change causalHardScoreMeasure b cA delta w centers omega
      (causalHardCell (centers j) w) = _
  exact causalHardScoreMeasure_cell_mass j centers omega hb hscale hcA hdelta hw
    hsep (hcell j)

/-- The full potential-outcome law restricted to one hard cell depends on a
vertex only through the bit indexing that cell. -/
-- @node: causalHardA1A2Law_restrict_cell_eq
lemma causalHardA1A2Law_restrict_cell_eq {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare)
    {omega omega' : Fin M → Bool} {j : Fin M}
    (hbit : omega j = omega' j) :
    (causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
      hsep hcell).law.restrict
        {z | causalScore z ∈ causalHardCell (centers j) w} =
      (causalHardA1A2Law b cA delta w centers omega' hb hscale hcA hdelta hw
        hsep hcell).law.restrict
          {z | causalScore z ∈ causalHardCell (centers j) w} := by
  let nu := causalHardScoreMeasure b cA delta w centers omega
  let nu' := causalHardScoreMeasure b cA delta w centers omega'
  let p0 := causalHardControlProfile
  let p1 := causalHardTreatmentProfile delta w centers omega
  let p1' := causalHardTreatmentProfile delta w centers omega'
  have hp := causalHardProfiles_measurable delta w centers omega
  have hp' := causalHardProfiles_measurable delta w centers omega'
  letI : IsProbabilityMeasure nu :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega hb hscale hcA
      hdelta hw hsep hcell
  letI : IsProbabilityMeasure nu' :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega' hb hscale hcA
      hdelta hw hsep hcell
  have hparam : ∀ x ∈ causalHardCell (centers j) w, p1 x = p1' x := by
    intro x hx
    unfold p1 p1' causalHardTreatmentProfile clippedPackingRegression
    rw [packingRegression_eq_on_cell hw hsep hbit hx]
  exact causalBernoulliPotentialOutcomeMeasure_restrict_score_eq
      nu nu' p0 p1 p0 p1' hp.1 hp.2 hp'.1 hp'.2
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).1.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).1.2)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).2.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).2.2)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).1.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).1.2)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).2.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).2.2)
      Metric.isClosed_closedBall.measurableSet
      (causalHardScoreMeasure_restrict_cell_eq hw hsep hbit)
      (fun _ _ ↦ rfl) hparam

/-- Away from every hard cell, the full potential-outcome law is independent
of the Boolean vertex. -/
-- @node: causalHardA1A2Law_restrict_off_cells_eq
lemma causalHardA1A2Law_restrict_off_cells_eq {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare)
    (omega omega' : Fin M → Bool) :
    (causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
      hsep hcell).law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w} =
      (causalHardA1A2Law b cA delta w centers omega' hb hscale hcA hdelta hw
        hsep hcell).law.restrict
          {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w} := by
  let nu := causalHardScoreMeasure b cA delta w centers omega
  let nu' := causalHardScoreMeasure b cA delta w centers omega'
  let p0 := causalHardControlProfile
  let p1 := causalHardTreatmentProfile delta w centers omega
  let p1' := causalHardTreatmentProfile delta w centers omega'
  have hp := causalHardProfiles_measurable delta w centers omega
  have hp' := causalHardProfiles_measurable delta w centers omega'
  letI : IsProbabilityMeasure nu :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega hb hscale hcA
      hdelta hw hsep hcell
  letI : IsProbabilityMeasure nu' :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega' hb hscale hcA
      hdelta hw hsep hcell
  have hparam : ∀ x ∈ (⋃ j, causalHardCell (centers j) w)ᶜ,
      p1 x = p1' x := by
    intro x hx
    have hxBalls : ∀ j, x ∉ causalHardCell (centers j) w := by
      intro j hxj
      exact hx (Set.mem_iUnion.2 ⟨j, hxj⟩)
    unfold p1 p1' causalHardTreatmentProfile clippedPackingRegression
    rw [packingRegression_eq_off_cells hw omega hxBalls,
      packingRegression_eq_off_cells hw omega' hxBalls]
  exact causalBernoulliPotentialOutcomeMeasure_restrict_score_eq
      nu nu' p0 p1 p0 p1' hp.1 hp.2 hp'.1 hp'.2
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).1.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).1.2)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).2.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega x).2.2)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).1.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).1.2)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).2.1)
      (fun x ↦ (causalHardProfiles_mem_unitInterval delta w centers omega' x).2.2)
      (MeasurableSet.iUnion fun _ ↦
        Metric.isClosed_closedBall.measurableSet).compl
      (causalHardScoreMeasure_restrict_compl_cells_eq hw omega omega')
      (fun _ _ ↦ rfl) hparam

/-- Flipping one vertex bit changes the treatment effect at the corresponding
cell center by exactly the bump amplitude. -/
-- @node: causalHardA1A2Law_tau_center_eq_of_bit_eq
lemma causalHardA1A2Law_tau_center_eq_of_bit_eq {M : ℕ} (j : Fin M)
    (b cA delta w : ℝ) (centers : Fin M → Score)
    (omega omega' : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : ∀ k, centers k ∈ causalHardSquare)
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare)
    (hbit : omega j = omega' j) :
    (causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
        hsep hcell).tau (centers j) =
      (causalHardA1A2Law b cA delta w centers omega' hb hscale hcA hdelta hw
        hsep hcell).tau (centers j) := by
  have hleft := causalHardTreatmentProfile_eq_packingRegression_on_square
    hdelta.le hdeltaSmall hw hsep omega (hcenter j)
  have hright := causalHardTreatmentProfile_eq_packingRegression_on_square
    hdelta.le hdeltaSmall hw hsep omega' (hcenter j)
  have hreg := packingRegression_eq_on_cell (b := (1 / 16 : ℝ))
    (delta := delta) hw hsep hbit (Metric.mem_closedBall_self hw.le)
  change causalHardTreatmentProfile delta w centers omega (centers j) -
      causalHardControlProfile (centers j) =
    causalHardTreatmentProfile delta w centers omega' (centers j) -
      causalHardControlProfile (centers j)
  rw [hleft, hright, hreg]

/-- Flipping one vertex bit changes the treatment effect at the corresponding
cell center by exactly the bump amplitude. -/
-- @node: causalHardA1A2Law_tau_center_flip
lemma causalHardA1A2Law_tau_center_flip {M : ℕ} (j : Fin M)
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : ∀ k, centers k ∈ causalHardSquare)
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    |(causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
        hsep hcell).tau (centers j) -
      (causalHardA1A2Law b cA delta w centers
        (Function.update omega j (!omega j)) hb hscale hcA hdelta hw
        hsep hcell).tau (centers j)| = delta := by
  have hprofile := causalHardTreatmentProfile_center_flip hdelta.le hdeltaSmall
    hw hsep hcenter omega j
  simpa [A1A2Law.tau, causalHardA1A2Law_muPO] using hprofile

/-- The already-constructed hard law simultaneously supplies the common
geometry, exact cell masses, bit locality, off-cell agreement, and target
separation needed by the final hypercube assembly. -/
-- @node: causalHardA1A2Law_vertex_core
lemma causalHardA1A2Law_vertex_core {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : ∀ k, centers k ∈ causalHardSquare)
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    let P := fun omega => causalHardA1A2Law b cA delta w centers omega
      hb hscale hcA hdelta hw hsep hcell
    (∀ omega, (P omega).support = causalHardSquare ∧
      (P omega).A1 = causalHardArmOne ∧
      (P omega).A0 = causalHardSquare \ causalHardArmOne ∧
      (P omega).boundary = frontier causalHardArmOne) ∧
    (∀ omega j, (P omega).law
      {z | causalScore z ∈ causalHardCell (centers j) w} =
        ENNReal.ofReal (Real.pi * w ^ 2 / 36)) ∧
    (∀ omega omega' j, omega j = omega' j →
      (P omega).law.restrict
          {z | causalScore z ∈ causalHardCell (centers j) w} =
        (P omega').law.restrict
          {z | causalScore z ∈ causalHardCell (centers j) w}) ∧
    (∀ omega omega', (P omega).law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w} =
      (P omega').law.restrict
        {z | causalScore z ∉ ⋃ j, causalHardCell (centers j) w}) ∧
    ∀ omega j, |(P omega).tau (centers j) -
      (P (Function.update omega j (!omega j))).tau (centers j)| = delta := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro omega
    exact causalHardA1A2Law_geometry b cA delta w centers omega hb hscale
      hcA hdelta hw hsep hcell
  · intro omega j
    exact causalHardA1A2Law_cell_mass j b cA delta w centers omega hb hscale
      hcA hdelta hw hsep hcell
  · intro omega omega' j hbit
    exact causalHardA1A2Law_restrict_cell_eq hb hscale hcA hdelta hw hsep
      hcell hbit
  · intro omega omega'
    exact causalHardA1A2Law_restrict_off_cells_eq hb hscale hcA hdelta hw
      hsep hcell omega omega'
  · intro omega j
    exact causalHardA1A2Law_tau_center_flip j b cA delta w centers omega hb
      hscale hcA hdelta hdeltaSmall hw hsep hcenter hcell

/-- Every selected conditional outcome kernel in the hard family obeys the
all-orders moment envelope, uniformly over scores and vertices. -/
-- @node: causalHardA1A2Law_condAbsMoment_le
lemma causalHardA1A2Law_condAbsMoment_le {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    {ν L : ℝ} (hν : 2 ≤ ν) (hL : 1 ≤ L) (t : Bool) (x : Score) :
    (causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
      hsep hcell).condAbsMoment ν t x ≤ ENNReal.ofReal L := by
  have hp := causalHardProfiles_measurable delta w centers omega
  have hp1 (z : Score) : causalHardControlProfile z ≤ 1 :=
    (causalHardProfiles_mem_unitInterval delta w centers omega z).1.2
  have hp2 (z : Score) :
      causalHardTreatmentProfile delta w centers omega z ≤ 1 :=
    (causalHardProfiles_mem_unitInterval delta w centers omega z).2.2
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal L := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hL
  cases t with
  | false =>
      exact (causalSelectedBernoulliKernel_condAbsMoment_le_one
        causalHardControlProfile hp.1 hp1 hν x).trans hone
  | true =>
      exact (causalSelectedBernoulliKernel_condAbsMoment_le_one
        (causalHardTreatmentProfile delta w centers omega) hp.2 hp2 hν x).trans hone

/-- The hard law's density is continuous on its support and obeys every
class envelope `L ≥ 48`. -/
-- @node: causalHardA1A2Law_density_certificates
lemma causalHardA1A2Law_density_certificates {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    {L : ℝ} (hL : 48 ≤ L) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    ContinuousOn P.density P.support ∧
      ∀ x ∈ P.support, L⁻¹ ≤ P.density x ∧ P.density x ≤ L := by
  dsimp only
  have hLpos : 0 < L := (by norm_num : (0 : ℝ) < 48).trans_le hL
  have hinv : L⁻¹ ≤ (48 : ℝ)⁻¹ :=
    (inv_le_inv₀ hLpos (by norm_num : (0 : ℝ) < 48)).mpr hL
  constructor
  · exact (causalHardScoreDensity_continuous centers omega hb hscale).continuousOn
  · intro x hx
    have hd := causalHardScoreDensity_mem_Icc (b := b) hcA hdelta hw hsep omega x
    exact ⟨hinv.trans (by norm_num at hd ⊢; exact hd.1),
      hd.2.trans (by linarith)⟩

/-- On the hard square, the selected Bernoulli kernels have exactly the
decorated pointwise means and variances, and their variances obey every
class envelope `L ≥ 48`. -/
-- @node: causalHardA1A2Law_kernel_certificates
lemma causalHardA1A2Law_kernel_certificates {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    {L : ℝ} (hL : 48 ≤ L) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    (∀ t x, x ∈ P.support → P.muPO t x = ∫ y, y ∂P.condKer t x) ∧
    (∀ t x, x ∈ P.support →
      P.sigmaSqPO t x = ProbabilityTheory.variance id (P.condKer t x)) ∧
    (∀ t, ContinuousOn (P.sigmaSqPO t) P.support ∧
      ∀ x ∈ P.support, L⁻¹ ≤ P.sigmaSqPO t x ∧ P.sigmaSqPO t x ≤ L) := by
  dsimp only
  have hp := causalHardProfiles_measurable delta w centers omega
  have hLpos : 0 < L := (by norm_num : (0 : ℝ) < 48).trans_le hL
  have hinv : L⁻¹ ≤ (48 : ℝ)⁻¹ :=
    (inv_le_inv₀ hLpos (by norm_num : (0 : ℝ) < 48)).mpr hL
  refine ⟨?_, ?_, ?_⟩
  · intro t x hx
    cases t with
    | false =>
        exact (causalSelectedBernoulliKernel_integral_id
          causalHardControlProfile hp.1
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).1.1)
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).1.2)
          x).symm
    | true =>
        exact (causalSelectedBernoulliKernel_integral_id
          (causalHardTreatmentProfile delta w centers omega) hp.2
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).2.1)
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).2.2)
          x).symm
  · intro t x hx
    cases t with
    | false =>
        exact (causalSelectedBernoulliKernel_variance_id
          causalHardControlProfile hp.1
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).1.1)
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).1.2)
          x).symm
    | true =>
        exact (causalSelectedBernoulliKernel_variance_id
          (causalHardTreatmentProfile delta w centers omega) hp.2
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).2.1)
          (fun z => (causalHardProfiles_mem_unitInterval delta w centers omega z).2.2)
          x).symm
  · intro t
    cases t with
    | false =>
        constructor
        · change ContinuousOn (fun _ : Score => (1 / 2 : ℝ) * (1 - 1 / 2))
            causalHardSquare
          exact continuous_const.continuousOn
        · intro x hx
          change L⁻¹ ≤ (1 / 2 : ℝ) * (1 - 1 / 2) ∧
            (1 / 2 : ℝ) * (1 - 1 / 2) ≤ L
          constructor <;> norm_num <;> linarith
    | true =>
        let f := causalHardTreatmentProfile delta w centers omega
        have hf : Continuous f :=
          clippedPackingRegression_continuous (1 / 16) delta w centers omega
        constructor
        · exact (hf.mul (continuous_const.sub hf)).continuousOn
        · intro x hx
          have hprob : f x ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ) :=
            causalHardTreatmentProfile_mem_middleHalf hdelta.le
              hdeltaSmall hw hsep omega hx
          change L⁻¹ ≤ f x * (1 - f x) ∧ f x * (1 - f x) ≤ L
          constructor
          · apply hinv.trans
            nlinarith [hprob.1, hprob.2]
          · nlinarith [hprob.1, hprob.2]

/-- Every hard-family vertex has the complete fixed-rectangle geometry block
required by `A1A2Class`, including rectifiability and Hausdorff bounds. -/
-- @node: causalHardA1A2Law_class_geometry
lemma causalHardA1A2Law_class_geometry {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    {L : ℝ} (hL : 48 ≤ L) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    MeasurableSet P.A0 ∧ MeasurableSet P.A1 ∧
      P.A0 ∪ P.A1 = P.support ∧ Disjoint P.A0 P.A1 ∧
      P.boundary = frontier P.A0 ∩ frontier P.A1 ∧
      IsCompact P.boundary ∧ P.boundary ⊆ interior P.support ∧
      RectifiableCurve P.boundary ∧
      ENNReal.ofReal L⁻¹ ≤ Measure.hausdorffMeasure 1 P.boundary ∧
      Measure.hausdorffMeasure 1 P.boundary ≤ ENNReal.ofReal L := by
  dsimp only
  refine ⟨causalHardArmZero_measurableSet, causalHardArmOne_measurableSet,
    causalHardAssignment_partition.1, causalHardAssignment_partition.2,
    ?_, causalHardFrontier_compact_and_interior.1,
    causalHardFrontier_compact_and_interior.2,
    causalHardFrontier_rectifiableCurve,
    (causalHardFrontier_hausdorff_bounds hL).1,
    (causalHardFrontier_hausdorff_bounds hL).2⟩
  exact causalHardAssignment_frontier.symm

/-- Once the four genuinely analytic hard-square leaves are available, all
remaining clauses of `A1A2Class` follow from the explicit score law,
Bernoulli kernels, profiles, and fixed rectangle geometry. -/
-- @node: causalHardA1A2Law_mem_class_of_analytic_certificates
lemma causalHardA1A2Law_mem_class_of_analytic_certificates {M : ℕ}
    (p : ℕ) (ν L b cA delta w : ℝ) (centers : Fin M → Score)
    (omega : Fin M → Bool) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 16) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    (hν : 2 ≤ ν) (hL : 48 ≤ L) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    EuclideanCExtEnvelope (P.muPO true) p L P.support →
    PopulationGramFloor P p L →
    (∀ t x h, x ∈ P.boundary → 0 < h → h ≤ L⁻¹ →
      ENNReal.ofReal L⁻¹ ≤ armLocalMass P t x h) →
    (∀ t x s, x ∈ P.boundary → 0 < s → s ≤ L⁻¹ →
      0 < armSliceDensityMass P t x s ∧ armSliceDensityMass P t x s < ∞) →
    A1A2Class p ν L P := by
  dsimp only
  intro hTreatment hGram hLocalMass hSlice
  have hDensity := causalHardA1A2Law_density_certificates b cA delta w centers
    omega hb hscale hcA hdelta hw hsep hcell hL
  have hKernel := causalHardA1A2Law_kernel_certificates b cA delta w centers
    omega hb hscale hcA hdelta hdeltaSmall hw hsep hcell hL
  have hGeometry := causalHardA1A2Law_class_geometry b cA delta w centers omega
    hb hscale hcA hdelta hw hsep hcell hL
  let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
    hdelta hw hsep hcell
  have hMoment : ∀ t x, x ∈ P.support →
      P.condAbsMoment ν t x ≤ ENNReal.ofReal L := by
    intro t x hx
    exact causalHardA1A2Law_condAbsMoment_le b cA delta w centers omega hb
      hscale hcA hdelta hw hsep hcell hν (by linarith) t x
  let K : A1A2KernelWitness P ν L :=
    { condKer := P.condKer
      condKer_markov := P.condKer_markov
      condKer_disint := P.condKer_disint
      mean_eq := hKernel.1
      variance_eq := hKernel.2.1
      moment_le := hMoment }
  have hK : Nonempty (A1A2KernelWitness P ν L) := ⟨K⟩
  refine ⟨hν, by linarith, causalHardSquare_rectangularScoreSupport (by linarith),
    hDensity.1, hDensity.2, ?_, hKernel.2.2,
    ⟨hK, selectedA1A2CondKer_mean_eq hK⟩,
    selectedA1A2CondKer_variance_eq hK,
    selectedA1A2CondAbsMoment_le hK,
    hGeometry, euclidean_balls_vc, hGram, hLocalMass, hSlice⟩
  · intro t
    cases t with
    | false =>
        exact causalHardA1A2Law_control_euclideanCExtEnvelope p b cA delta w
          centers omega hb hscale hcA hdelta hw hsep hcell (by linarith)
    | true => exact hTreatment

end CausalSmith.Stat.BddUniformLogPenalty
