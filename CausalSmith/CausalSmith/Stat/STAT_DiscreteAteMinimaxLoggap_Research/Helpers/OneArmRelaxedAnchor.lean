import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmProductConditioning

/-!
# Relaxed deterministic-anchor configurations

The source D.2 construction adds the same deterministic anchor to both fuzzy
hypotheses and only then normalizes the resulting near-unit mass vector.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

/-- The unnormalized mass vector on m+1 covariate cells obtained by prepending a
deterministic anchor cell, carrying mass `anchor`, to the m random active cells
whose masses are `q`.  Cell 0 is the anchor and cell `i+1` carries mass `q i`. -/
noncomputable def oneArmRelaxedAnchoredMass {m : ℕ}
    (anchor : ℝ) (q : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases anchor q

/-- The total mass of the anchored vector is the anchor mass plus the total mass
of the active cells. -/
lemma oneArmRelaxedAnchoredMass_sum {m : ℕ} (anchor : ℝ) (q : Fin m → ℝ) :
    ∑ r, oneArmRelaxedAnchoredMass anchor q r = anchor + ∑ i, q i := by
  rw [Fin.sum_univ_succ]
  simp [oneArmRelaxedAnchoredMass]

/-- If the anchor mass and every active-cell mass are nonnegative, then so is
every entry of the anchored mass vector. -/
lemma oneArmRelaxedAnchoredMass_nonneg {m : ℕ} {anchor : ℝ}
    (q : Fin m → ℝ) (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i) :
    ∀ r, 0 ≤ oneArmRelaxedAnchoredMass anchor q r := by
  intro r
  exact Fin.cases ha (fun i => hq i) r

/-- Normalize a common deterministic anchor together with the random active
cells.  The anchor has treated mean zero and therefore contributes no target. -/
noncomputable def oneArmRelaxedAnchoredControlZero
    {n m : ℕ} {epsilon anchor : ℝ} (q pi mu : Fin m → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i)
    (hS : 0 < anchor + ∑ i, q i)
    (hpi : ∀ i, pi i ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ i, mu i ∈ Set.Icc (0 : ℝ) 1) :
    ControlZeroLaw n (m + 1) epsilon :=
  oneArmNormalizedControlZero
    (oneArmRelaxedAnchoredMass anchor q)
    (oneArmAnchoredPropensity epsilon pi)
    (oneArmAnchoredOutcomeMean mu)
    he0 hehalf
    (oneArmRelaxedAnchoredMass_nonneg q ha hq)
    (by simpa [oneArmRelaxedAnchoredMass_sum] using hS)
    (fun r => by
      refine Fin.cases ?_ (fun i => hpi i) r
      change epsilon ∈ Set.Icc epsilon (1 - epsilon)
      exact ⟨le_rfl, by linarith⟩)
    (fun r => by
      refine Fin.cases ?_ (fun i => hmu i) r
      change (0 : ℝ) ∈ Set.Icc 0 1
      norm_num)

/-- Normalizing the relaxed anchored vector changes the active treated target
by at most its total-mass defect. -/
lemma oneArmRelaxedAnchoredControlZero_functional_sub_le
    {n m : ℕ} {epsilon anchor : ℝ} (q pi mu : Fin m → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i)
    (hS : 0 < anchor + ∑ i, q i)
    (hpi : ∀ i, pi i ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ i, mu i ∈ Set.Icc (0 : ℝ) 1)
    (hpi_pos : ∀ i, 0 < pi i) :
    |treatedFunctional
        ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu he0 hehalf
          ha hq hS hpi hmu : ControlZeroLaw n (m + 1) epsilon)).1 -
        ∑ i, q i * mu i| ≤
      |(anchor + ∑ i, q i) - 1| := by
  have hfullpi : ∀ r, 0 < oneArmAnchoredPropensity epsilon pi r := by
    intro r
    exact Fin.cases he0 (fun i => hpi_pos i) r
  have hbase := oneArmNormalizedControlZero_functional_sub_le
    (n := n) (epsilon := epsilon)
    (oneArmRelaxedAnchoredMass anchor q)
    (oneArmAnchoredPropensity epsilon pi)
    (oneArmAnchoredOutcomeMean mu)
    he0 hehalf (oneArmRelaxedAnchoredMass_nonneg q ha hq)
    (by simpa [oneArmRelaxedAnchoredMass_sum] using hS)
    (fun r => by
      refine Fin.cases ?_ (fun i => hpi i) r
      change epsilon ∈ Set.Icc epsilon (1 - epsilon)
      exact ⟨le_rfl, by linarith⟩)
    (fun r => by
      refine Fin.cases ?_ (fun i => hmu i) r
      change (0 : ℝ) ∈ Set.Icc 0 1
      norm_num)
    hfullpi
  simpa [oneArmRelaxedAnchoredControlZero,
    oneArmRelaxedAnchoredMass_sum, oneArmRelaxedAnchoredMass,
    oneArmAnchoredOutcomeMean, Fin.sum_univ_succ] using hbase

/-- The simultaneous D.2 good event for a deterministic common anchor. -/
def oneArmRelaxedAnchoredGood {alpha : Type*} {m : ℕ}
    (anchor : ℝ) (q mu : alpha → ℝ) (theta massRadius targetRadius : ℝ)
    (z : Fin m → alpha) : Prop :=
  0 < anchor + ∑ i, q (z i) ∧
  |(anchor + ∑ i, q (z i)) - 1| ≤ massRadius ∧
  |(∑ i, q (z i) * mu (z i)) - theta| ≤ targetRadius

/-- Every relaxed-good realization maps to a normalized control-zero law. -/
noncomputable def oneArmRelaxedLawOfGoodAtoms
    {alpha : Type*} {n m : ℕ}
    {epsilon anchor theta massRadius targetRadius : ℝ}
    (q pi mu : alpha → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ x, 0 ≤ q x)
    (hpi : ∀ x, pi x ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (z : {z : Fin m → alpha //
      oneArmRelaxedAnchoredGood anchor q mu theta massRadius targetRadius z}) :
    ControlZeroLaw n (m + 1) epsilon :=
  oneArmRelaxedAnchoredControlZero
    (fun i => q (z.1 i)) (fun i => pi (z.1 i)) (fun i => mu (z.1 i))
    he0 hehalf ha (fun i => hq (z.1 i)) z.2.1
    (fun i => hpi (z.1 i)) (fun i => hmu (z.1 i))

/-- For any realization in the relaxed good event, the treated functional of the
law built from it lies within `massRadius + targetRadius` of the design target
`theta`: the normalization error is controlled by the mass defect and the raw
active target is within `targetRadius` of `theta` by definition of the good
event. -/
lemma oneArmRelaxedLawOfGoodAtoms_target
    {alpha : Type*} {n m : ℕ}
    {epsilon anchor theta massRadius targetRadius : ℝ}
    (q pi mu : alpha → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ x, 0 ≤ q x)
    (hpi : ∀ x, pi x ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ x, mu x ∈ Set.Icc (0 : ℝ) 1)
    (hpi_pos : ∀ x, 0 < pi x)
    (z : {z : Fin m → alpha //
      oneArmRelaxedAnchoredGood anchor q mu theta massRadius targetRadius z}) :
    |treatedFunctional
        (oneArmRelaxedLawOfGoodAtoms (n := n) q pi mu he0 hehalf ha hq hpi hmu z).1 -
      theta| ≤ massRadius + targetRadius := by
  have hnorm := oneArmRelaxedAnchoredControlZero_functional_sub_le
    (n := n) (epsilon := epsilon)
    (fun i => q (z.1 i)) (fun i => pi (z.1 i)) (fun i => mu (z.1 i))
    he0 hehalf ha (fun i => hq (z.1 i)) z.2.1
    (fun i => hpi (z.1 i)) (fun i => hmu (z.1 i))
    (fun i => hpi_pos (z.1 i))
  have htri :
      |treatedFunctional
          (oneArmRelaxedLawOfGoodAtoms (n := n) q pi mu he0 hehalf ha hq hpi hmu z).1 -
        theta| ≤
      |treatedFunctional
          (oneArmRelaxedLawOfGoodAtoms (n := n) q pi mu he0 hehalf ha hq hpi hmu z).1 -
          ∑ i, q (z.1 i) * mu (z.1 i)| +
        |(∑ i, q (z.1 i) * mu (z.1 i)) - theta| := by
    exact abs_sub_le _ _ _
  exact htri.trans (add_le_add (hnorm.trans z.2.2.1) z.2.2.2)

/-- Centering the common anchor at `1-massCenter` turns the usual two
concentration inequalities directly into the relaxed good event. -/
lemma oneArmProductConcentrationGood_relaxed
    {alpha : Type*} {m : ℕ} (q mu : alpha → ℝ)
    (massCenter theta massRadius targetRadius : ℝ)
    (hmassRadius : massRadius < 1) (z : Fin m → alpha)
    (hmass : |(∑ i, q (z i)) - massCenter| < massRadius)
    (htarget : |(∑ i, q (z i) * mu (z i)) - theta| < targetRadius) :
    oneArmRelaxedAnchoredGood (1 - massCenter) q mu theta
      massRadius targetRadius z := by
  have hlower := (abs_lt.mp hmass).1
  refine ⟨?_, ?_, htarget.le⟩
  · linarith
  · have hid : (1 - massCenter + ∑ i, q (z i)) - 1 =
        (∑ i, q (z i)) - massCenter := by ring
    rw [hid]
    exact hmass.le

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
