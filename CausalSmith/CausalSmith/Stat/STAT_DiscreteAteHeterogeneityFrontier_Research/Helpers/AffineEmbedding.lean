/- Binary-to-real affine embedding primitives and sample transport identities. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ParametricLower
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.CitedGates
import Causalean.Stat.Minimax.MinimaxRisk
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set

/-- A binary full-data record used to state law-level source couplings. -/
structure BinaryFullObs (d : ℕ) where
  x : Fin d
  a : Bool
  b0 : Bool
  b1 : Bool
  deriving Fintype, DecidableEq

/-- Equality of binary full-data records is decidable. -/
add_decl_doc instDecidableEqBinaryFullObs

/-- The space of binary full-data records is finite. -/
add_decl_doc instFintypeBinaryFullObs

/-- Binary full-data records carry the discrete measurable structure. -/
instance {d : ℕ} : MeasurableSpace (BinaryFullObs d) := ⊤

/-- The observed binary record selected from a binary full-data record. -/
def BinaryFullObs.observed {d : ℕ} (z : BinaryFullObs d) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs d :=
  (z.x, z.a, if z.a then z.b1 else z.b0)

/-- Deterministic affine scaling of both binary potential outcomes. -/
noncomputable def BinaryFullObs.affine {d e : ℕ} (M : ℝ) (pad : Fin d → Fin e)
    (z : BinaryFullObs d) : FullObs e :=
  let scale (b : Bool) := M * ((if b then 1 else 0) - 1 / 2)
  ⟨pad z.x, z.a, scale z.b0, scale z.b1,
    if z.a then scale z.b1 else scale z.b0⟩

/-- A binary potential-outcome coupling has the prescribed observed source law. -/
def BinaryFullCoupling {d : ℕ}
    (P : CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw d)
    (R : Measure (BinaryFullObs d)) : Prop :=
  IsProbabilityMeasure R ∧
    Measure.map BinaryFullObs.observed R =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P

-- @node: binaryFullLift
/-- Lift an observed binary record to consistent binary full data by using a
fixed value for the unobserved potential outcome. -/
def binaryFullLift {d : ℕ}
    (z : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs d) : BinaryFullObs d :=
  if z.2.1 then ⟨z.1, true, false, z.2.2⟩
  else ⟨z.1, false, z.2.2, false⟩

-- @node: binaryFullLift_observed
/-- [Observing the canonical full-data lift recovers the source record](goal). -/
lemma binaryFullLift_observed {d : ℕ}
    (z : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs d) :
    (binaryFullLift z).observed = z := by
  cases z with
  | mk x rest =>
      cases rest with
      | mk a b => cases a <;> rfl

-- @node: canonicalBinaryFullCoupling
/-- The pushforward of a binary observation law by the canonical lift is a
probability coupling with exactly the prescribed observed margin. -/
noncomputable def canonicalBinaryFullCoupling {d : ℕ}
    (P : CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw d) :
    Measure (BinaryFullObs d) :=
  Measure.map binaryFullLift
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P)

-- @node: canonicalBinaryFullCoupling_spec
/-- [The canonical lifted law satisfies the binary coupling interface](goal). -/
lemma canonicalBinaryFullCoupling_spec {d : ℕ}
    (P : CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw d) :
    BinaryFullCoupling P (canonicalBinaryFullCoupling P) := by
  constructor
  · exact Measure.isProbabilityMeasure_map (by fun_prop)
  · unfold canonicalBinaryFullCoupling
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    convert Measure.map_id
    funext z
    exact binaryFullLift_observed z

private abbrev BinLaw := CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw

/-- The deterministic affine pushforward on an observed binary record. -/
noncomputable def affineObserved {d : ℕ} (M : ℝ)
    (z : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs d) : Obs d :=
  ⟨z.1, z.2.1, M * ((if z.2.2 then 1 else 0) - 1 / 2)⟩

-- @node: observed_affine_binaryFullObs
/-- [Observing an affinely scaled full-data record is the same as affinely scaling its observed
  binary record](goal). -/
lemma observed_affine_binaryFullObs {d : ℕ} (M : ℝ) (z : BinaryFullObs d) :
    FullObs.observed (BinaryFullObs.affine M (fun k => k) z) =
      affineObserved M z.observed := by
  cases z with
  | mk x a b0 b1 => cases a <;> rfl

-- @node: affineCanonicalFullLaw_observed_margin
/-- [The affine image of the canonical binary full-data coupling has the expected affinely
  transformed observed margin](goal). -/
lemma affineCanonicalFullLaw_observed_margin {d : ℕ} (M : ℝ) (P : BinLaw d) :
    Measure.map FullObs.observed
        (Measure.map (BinaryFullObs.affine M (fun k => k))
          (canonicalBinaryFullCoupling P)) =
      Measure.map (affineObserved M)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hc := (canonicalBinaryFullCoupling_spec P).2
  rw [← hc, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  exact observed_affine_binaryFullObs M z

/-- The totalized binary conditional outcome law in one arm and cell. -/
noncomputable def binaryConditionalOutcomeLaw {d : ℕ} (P : BinLaw d)
    (a : Bool) (k : Fin d) : Measure Bool :=
  ENNReal.ofReal
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a false /
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a) •
      Measure.dirac false +
    ENNReal.ofReal
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a true /
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a) •
      Measure.dirac true

/-- One law-level affine binary-to-real pushforward.  The same `M`-indexed map
pins the observed law, every positive arm-cell conditional outcome law, and a
full-data potential-outcome coupling. -/
def AffineBinaryEmbedding {d : ℕ} (M : ℝ) (P : BinLaw d) (Q : RealLaw d) : Prop :=
  Q.observedLaw = Measure.map (affineObserved M)
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P) ∧
  (∀ k, Q.cellMass k =
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k) ∧
  (∀ k, Q.propensity k =
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P k) ∧
  (∀ a k, 0 < CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a →
    Q.outcomeLaw a k = Measure.map
      (fun b : Bool => M * ((if b then 1 else 0) - 1 / 2))
      (binaryConditionalOutcomeLaw P a k)) ∧
  (∀ a k, Q.outcomeMean a k = M *
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k - 1 / 2)) ∧
  ∃ R : Measure (BinaryFullObs d),
    BinaryFullCoupling P R ∧
      Q.fullLaw = Measure.map (BinaryFullObs.affine M (fun k => k)) R

-- @node: measurable_affineObserved
/-- [The one-record affine binary-to-real observation map is measurable](goal). -/
lemma measurable_affineObserved {d : ℕ} (M : ℝ) :
    Measurable (affineObserved (d := d) M) := by
  rw [measurable_comap_iff]
  change Measurable (fun z :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs d =>
    (z.1, z.2.1, M * ((if z.2.2 then 1 else 0) - 1 / 2)))
  fun_prop

-- @node: productLaw_eq_map_affineObserved_of_embedding
/-- [An affine embedding transports the whole finite sample coordinatewise](goal). -/
lemma productLaw_eq_map_affineObserved_of_embedding {n d : ℕ} {M : ℝ}
    {P : BinLaw d} {Q : RealLaw d} (h : AffineBinaryEmbedding M P Q) :
    productLaw n Q = Measure.map
      (fun sample : Fin n →
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs d =>
        fun i => affineObserved M (sample i))
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P n) := by
  unfold productLaw CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw
  rw [h.1]
  exact (Causalean.Stat.map_pi_finCoordinatewise n
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P)
    (measurable_affineObserved M)).symm

-- @node: rawAteFormula_affine_binary
/-- [The real-outcome g-formula of an affine binary embedding is the binary weighted regression
  contrast multiplied by the affine slope](goal). -/
lemma rawAteFormula_affine_binary {d : ℕ} {M : ℝ}
    {P : BinLaw d} {Q : RealLaw d} (h : AffineBinaryEmbedding M P Q) :
    rawAteFormula Q = M * ∑ k : Fin d,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k *
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k) := by
  rcases h with ⟨_hobs, hmass, _hprop, _houtcomeLaw, hmean, _hfull⟩
  unfold rawAteFormula cellEffect
  simp_rw [hmass, hmean]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

-- @node: rawAteFormula_eq_mul_binaryAte_of_embedding
/-- If [the source law satisfies overlap](hyp:hoverlap), [under binary overlap, the preceding
  scaling identity is exactly scaling of the source ATE functional](goal). -/
lemma rawAteFormula_eq_mul_binaryAte_of_embedding {d : ℕ} {epsilon M : ℝ}
    {P : BinLaw d} {Q : RealLaw d} (h : AffineBinaryEmbedding M P Q)
    (hoverlap : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P) :
    rawAteFormula Q = M *
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P := by
  rw [rawAteFormula_affine_binary h,
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_weighted_regression
      P hoverlap]

/-- If [the outcome scale is nonnegative](hyp:hM0) and [the outcome scale satisfies its stated
  bound](hyp:hM) and [the source parameter set has the stated form](hyp:hsource) and [the affine
  embedding identity holds](hyp:hembed) and [the source law satisfies overlap](hyp:hoverlap) and
  [the transported family belongs to the target model class](hyp:hmembership), [a genuinely hard
  binary family transfers to the ambient minimax problem through any affine embedding whose images
  have model-class witnesses](goal). -/
-- @node: minimaxRisk_ge_of_affine_binary_hard_family
lemma minimaxRisk_ge_of_affine_binary_hard_family {n d : ℕ}
    {epsilon M sigma L : ℝ} (hM0 : 0 ≤ M) (hM : M ≠ 0)
    (source : Set (BinLaw d))
    (hsource : ∀ est : (Fin n →
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs d) → ℝ,
      Measurable est → ∃ P ∈ source,
        L ≤ CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P n)
          est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P))
    (Phi : BinLaw d → RealLaw d)
    (hembed : ∀ P, AffineBinaryEmbedding M P (Phi P))
    (hoverlap : ∀ P ∈ source,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P)
    (hmembership : ∀ P ∈ source,
      ∃ Q : ModelClass d epsilon M sigma, Q.law = Phi P) :
    M ^ 2 * L ≤ minimaxRisk n d epsilon M sigma := by
  let est0 : Estimator n d M :=
    ⟨fun _ ↦ 0, measurable_const, fun _ ↦ by simp [hM0]⟩
  letI : Nonempty (Estimator n d M) := ⟨est0⟩
  unfold minimaxRisk
  apply le_ciInf
  intro est
  let I := {P : BinLaw d // P ∈ source}
  have htransport :=
    Causalean.Stat.forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport_pi
      (Iota := I) (n := n)
      (P := fun j => CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw j.1)
      (Q := fun j => (Phi j.1).observedLaw)
      (theta := fun j =>
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional j.1)
      (phi := affineObserved M) (a := M) (b := 0) (L := L)
      hM (measurable_affineObserved M)
      (fun j => (hembed j.1).1)
      (by
        intro sourceEst hmeas
        obtain ⟨P, hP, hrisk⟩ := hsource sourceEst hmeas
        exact ⟨⟨P, hP⟩, by
          simpa [Causalean.Stat.sqRisk,
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse,
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw] using hrisk⟩)
      est.1 est.2.1
  obtain ⟨j, hj⟩ := htransport
  obtain ⟨Q, hQ⟩ := hmembership j.1 j.2
  have htau : rawAteFormula Q.law =
      M * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional j.1 := by
    rw [hQ]
    exact rawAteFormula_eq_mul_binaryAte_of_embedding
      (hembed j.1) (hoverlap j.1 j.2)
  have hrisk : M ^ 2 * L ≤ mse Q.law est.1 := by
    rw [← htau] at hj
    simpa [Causalean.Stat.sqRisk, productLaw, mse, hQ] using hj
  have hb : BddAbove (Set.range (fun R : ModelClass d epsilon M sigma ↦
      mse R.law est.1)) := by
    refine ⟨(2 * M) ^ 2, ?_⟩
    rintro _ ⟨R, rfl⟩
    exact test_model_mse_le R est
  exact hrisk.trans (le_ciSup hb Q)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
