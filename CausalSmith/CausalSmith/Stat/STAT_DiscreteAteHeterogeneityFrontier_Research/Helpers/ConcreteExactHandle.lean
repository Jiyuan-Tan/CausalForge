import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.BinaryPadding

/-! # Concrete exact-family handle facts

This module packages the canonical full-data coupling and the deterministic
zero-padding identities used by the exact half of the least-favorable handle.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set

private abbrev BinLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw

private abbrev BinObs :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

-- @node: binaryPadFullObs
/-- Include a binary full-data record on the first `m` cells into an ambient
alphabet of size `d`. -/
def binaryPadFullObs {m d : ℕ} (hmd : m ≤ d) :
    BinaryFullObs m → BinaryFullObs d :=
  fun z => ⟨⟨z.x, lt_of_lt_of_le z.x.isLt hmd⟩, z.a, z.b0, z.b1⟩

-- @node: binaryOutcomePMF_binaryPadLaw
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding a binary law leaves
  its conditional outcome PMFs unchanged on the embedded coordinates](goal). -/
lemma binaryOutcomePMF_binaryPadLaw {m d : ℕ} (hmd : m ≤ d)
    (P : BinLaw m) (a : Bool) (k : Fin m) :
    binaryOutcomePMF (binaryPadLaw hmd P) a
        ⟨k, lt_of_lt_of_le k.isLt hmd⟩ =
      binaryOutcomePMF P a k := by
  apply PMF.ext
  intro b
  simp only [binaryOutcomePMF, PMF.ofFintype_apply]
  rw [binaryPadLaw_outcomeMean_image]

-- @node: binaryPadFullObs_independentLift
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding commutes with the
  independent full-data lift of an observation](goal). -/
lemma binaryPadFullObs_independentLift {m d : ℕ} (hmd : m ≤ d)
    (z : BinObs m) (other : Bool) :
    binaryPadFullObs hmd (binaryIndependentLift z other) =
      binaryIndependentLift (binaryPadObs hmd z) other := by
  rcases z with ⟨k, a, y⟩
  cases a <;> rfl

-- @node: binaryIndependentFullPMF_binaryPadLaw
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [the canonical independent
  binary full-data coupling commutes with zero-mass cell padding](goal). -/
lemma binaryIndependentFullPMF_binaryPadLaw {m d : ℕ} (hmd : m ≤ d)
    (P : BinLaw m) :
    PMF.map (binaryPadFullObs hmd) (binaryIndependentFullPMF P) =
      binaryIndependentFullPMF (binaryPadLaw hmd P) := by
  unfold binaryIndependentFullPMF
  rw [PMF.map_bind, binaryPadLaw, PMF.bind_map]
  apply congrArg (PMF.bind P.pmf)
  funext z
  rw [PMF.map_comp]
  simp only [Function.comp_apply]
  change PMF.map (binaryPadFullObs hmd ∘ binaryIndependentLift z)
      (binaryOutcomePMF P (!z.2.1) z.1) =
    PMF.map (binaryIndependentLift (binaryPadObs hmd z))
      (binaryOutcomePMF (binaryPadLaw hmd P) (!z.2.1)
        (binaryPadObs hmd z).1)
  rw [show (binaryPadObs hmd z).1 =
        ⟨z.1, lt_of_lt_of_le z.1.isLt hmd⟩ from rfl,
    binaryOutcomePMF_binaryPadLaw hmd P (!z.2.1) z.1]
  congr 1
  funext other
  exact binaryPadFullObs_independentLift hmd z other

-- @node: binaryIndependentFullCoupling_spec
/-- [The independent-potential-outcome lift used by `affineBinaryRealLaw` is a full-data coupling
  of its binary observed law](goal). -/
lemma binaryIndependentFullCoupling_spec {d : ℕ} (P : BinLaw d) :
    BinaryFullCoupling P (binaryIndependentFullPMF P).toMeasure := by
  constructor
  · infer_instance
  · rw [PMF.toMeasure_map BinaryFullObs.observed _ (measurable_of_finite _)]
    exact congrArg PMF.toMeasure (map_binaryIndependentFullPMF_observed P)

-- @node: affineBinaryPadded_fullLaw
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [the full-data law of the
  padded affine embedding is exactly the affine pushforward of the canonical independent binary
  coupling](goal). -/
lemma affineBinaryPadded_fullLaw {m d : ℕ} (hmd : m ≤ d) (M : ℝ)
    (P : BinLaw m) :
    (affineBinaryRealLaw M (binaryPadLaw hmd P)).fullLaw =
      Measure.map (BinaryFullObs.affine M
        (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩))
        (binaryIndependentFullPMF P).toMeasure := by
  change
    (PMF.map (BinaryFullObs.affine M (fun k : Fin d => k))
      (binaryIndependentFullPMF (binaryPadLaw hmd P))).toMeasure = _
  rw [← binaryIndependentFullPMF_binaryPadLaw hmd P, PMF.map_comp]
  have hfun :
      BinaryFullObs.affine M (fun k : Fin d => k) ∘ binaryPadFullObs hmd =
        BinaryFullObs.affine M
          (fun k : Fin m => ⟨k, lt_of_lt_of_le k.isLt hmd⟩) := by
    funext z
    rfl
  rw [hfun]
  exact (PMF.toMeasure_map _ _ (by fun_prop)).symm

-- @node: affineBinaryPadded_observedLaw
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [the observed law of a padded
  affine source is the deterministic coordinatewise padding-and-scaling pushforward of the source
  observation](goal). -/
lemma affineBinaryPadded_observedLaw {m d : ℕ} (hmd : m ≤ d) (M : ℝ)
    (P : BinLaw m) :
    (affineBinaryRealLaw M (binaryPadLaw hmd P)).observedLaw =
      Measure.map (fun z : BinObs m => affineObserved M (binaryPadObs hmd z))
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P) := by
  rw [(affineBinaryRealLaw_embedding M (binaryPadLaw hmd P)).1,
    binaryPadLaw_obsLaw, Measure.map_map]
  · rfl
  · exact measurable_affineObserved M
  · exact measurable_of_finite _

-- @node: affineBinaryPadded_cellMass_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding and affine outcome
  scaling preserve every source cell mass on the embedded coordinates](goal). -/
lemma affineBinaryPadded_cellMass_image {m d : ℕ} (hmd : m ≤ d) (M : ℝ)
    (P : BinLaw m) (k : Fin m) :
    (affineBinaryRealLaw M (binaryPadLaw hmd P)).cellMass
        ⟨k, lt_of_lt_of_le k.isLt hmd⟩ =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k := by
  exact binaryPadLaw_cellMass_image hmd P k

-- @node: affineBinaryPadded_cellMass_off_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the stated condition on
  the cell holds](hyp:hk), [every ambient coordinate outside the padded source image has zero
  mass](goal). -/
lemma affineBinaryPadded_cellMass_off_image {m d : ℕ} (hmd : m ≤ d) (M : ℝ)
    (P : BinLaw m) (k : Fin d)
    (hk : ∀ r : Fin m, (⟨r, lt_of_lt_of_le r.isLt hmd⟩ : Fin d) ≠ k) :
    (affineBinaryRealLaw M (binaryPadLaw hmd P)).cellMass k = 0 := by
  exact binaryPadLaw_cellMass_off_image hmd P k hk

-- @node: affineBinaryPadded_rawAteFormula
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the source law satisfies
  the stated model condition](hyp:hP), [the exact padded affine embedding multiplies the binary
  ATE by `M`](goal). -/
lemma affineBinaryPadded_rawAteFormula {m d : ℕ} (hmd : m ≤ d)
    {epsilon M : ℝ} (P : BinLaw m)
    (hP : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P) :
    rawAteFormula (affineBinaryRealLaw M (binaryPadLaw hmd P)) =
      M * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P := by
  rw [rawAteFormula_eq_mul_binaryAte_of_embedding
      (affineBinaryRealLaw_embedding M (binaryPadLaw hmd P))
      (binaryPadLaw_overlap hmd hP),
    binaryPadLaw_ateFunctional hmd hP]

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
