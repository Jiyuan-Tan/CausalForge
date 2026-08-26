/- Zero-mass padding of finite binary observation laws. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.AffineMembership

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory

private abbrev BinLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw
private abbrev BinObs :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

-- @node: half_le_natFloor_of_one_le
/-- If [the scalar satisfies the stated range condition](hyp:hx), [above one, the natural floor
  retains at least half of a nonnegative real](goal). -/
lemma half_le_natFloor_of_one_le {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (Nat.floor x : ℝ) := by
  by_cases hx2 : x ≤ 2
  · have hfloor : 1 ≤ Nat.floor x := Nat.le_floor (n := 1) (a := x) (by simpa using hx)
    have hfloorR : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hfloor
    linarith
  · have hfloor := Nat.sub_one_lt_floor x
    have hxlarge : 2 < x := lt_of_not_ge hx2
    linarith

-- @node: binaryPadObs
/-- Include a binary observation on the first `m` cells into an alphabet of
size `d`. -/
def binaryPadObs {m d : ℕ} (hmd : m ≤ d) : BinObs m → BinObs d :=
  fun z ↦ (⟨z.1, lt_of_lt_of_le z.1.isLt hmd⟩, z.2.1, z.2.2)

-- @node: binaryPadObs_injective
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [the zero-padding map from
  the source observation alphabet into the larger alphabet is injective](goal). -/
lemma binaryPadObs_injective {m d : ℕ} (hmd : m ≤ d) :
    Function.Injective (binaryPadObs hmd) := by
  intro z w hzw
  rcases z with ⟨x, a, y⟩
  rcases w with ⟨x', a', y'⟩
  simp only [binaryPadObs, Prod.mk.injEq] at hzw
  obtain ⟨hx, ha, hy⟩ := hzw
  subst a'
  subst y'
  have : x = x' := Fin.ext (congrArg (fun q : Fin d => q.val) hx)
  subst x'
  rfl

-- @node: binaryPadLaw
/-- Push a binary law into the first `m` cells of a larger alphabet, assigning
zero probability to all unused cells. -/
noncomputable def binaryPadLaw {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m) : BinLaw d :=
  ⟨PMF.map (binaryPadObs hmd) P.pmf⟩

-- @node: binaryPadLaw_obsLaw
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [the observed-data law after
  padding is the pushforward of the source law under the padding map](goal). -/
lemma binaryPadLaw_obsLaw {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw (binaryPadLaw hmd P) =
      Measure.map (binaryPadObs hmd)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P) := by
  exact (PMF.toMeasure_map (binaryPadObs hmd) P.pmf (measurable_of_finite _)).symm

-- @node: binaryPadLaw_jointMass_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding preserves joint
  probabilities on embedded source cells](goal). -/
lemma binaryPadLaw_jointMass_image {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m)
    (k : Fin m) (a y : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass (binaryPadLaw hmd P)
        ⟨k, lt_of_lt_of_le k.isLt hmd⟩ a y =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass P k a y := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass binaryPadLaw
  rw [PMF.map_apply]
  rw [tsum_eq_single (k, a, y)]
  · simp [binaryPadObs]
  · intro z hz
    have hne :
        (⟨k, lt_of_lt_of_le k.isLt hmd⟩, a, y) ≠ binaryPadObs hmd z := by
      intro heq
      exact hz ((binaryPadObs_injective hmd) (by simpa [binaryPadObs] using heq)).symm
    simp [hne]

-- @node: binaryPadLaw_jointMass_off_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the stated condition on
  the cell holds](hyp:hk), [padding assigns zero joint probability to every cell outside the
  embedded source alphabet](goal). -/
lemma binaryPadLaw_jointMass_off_image {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m)
    (k : Fin d) (hk : ∀ r : Fin m, (⟨r, lt_of_lt_of_le r.isLt hmd⟩ : Fin d) ≠ k)
    (a y : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass (binaryPadLaw hmd P) k a y = 0 := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.jointMass binaryPadLaw
  rw [PMF.map_apply]
  rw [tsum_fintype]
  apply (ENNReal.toReal_eq_zero_iff _).mpr
  left
  apply Finset.sum_eq_zero
  intro z _hz
  rcases z with ⟨r, b, c⟩
  have hne : (k, a, y) ≠ binaryPadObs hmd (r, b, c) := by
    intro h
    exact hk r (congrArg Prod.fst h).symm
  simp [hne]

-- @node: binaryPadLaw_cellMass_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding preserves cell
  probabilities on embedded source cells](goal). -/
lemma binaryPadLaw_cellMass_image {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m)
    (k : Fin m) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass (binaryPadLaw hmd P)
        ⟨k, lt_of_lt_of_le k.isLt hmd⟩ =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
  simp_rw [binaryPadLaw_jointMass_image]

-- @node: binaryPadLaw_cellMass_off_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the stated condition on
  the cell holds](hyp:hk), [padding assigns zero cell probability outside the embedded source
  alphabet](goal). -/
lemma binaryPadLaw_cellMass_off_image {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m)
    (k : Fin d) (hk : ∀ r : Fin m, (⟨r, lt_of_lt_of_le r.isLt hmd⟩ : Fin d) ≠ k) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass (binaryPadLaw hmd P) k = 0 := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
  simp_rw [binaryPadLaw_jointMass_off_image hmd P k hk]
  simp

-- @node: binaryPadLaw_armMass_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding preserves
  arm-specific cell probabilities on embedded source cells](goal). -/
lemma binaryPadLaw_armMass_image {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m)
    (k : Fin m) (a : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass (binaryPadLaw hmd P)
        ⟨k, lt_of_lt_of_le k.isLt hmd⟩ a =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass P k a := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.armMass
  simp_rw [binaryPadLaw_jointMass_image]

-- @node: binaryPadLaw_propensity_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding preserves
  propensities on embedded source cells](goal). -/
lemma binaryPadLaw_propensity_image {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m)
    (k : Fin m) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity (binaryPadLaw hmd P)
        ⟨k, lt_of_lt_of_le k.isLt hmd⟩ =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity P k := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.propensity
  rw [binaryPadLaw_armMass_image, binaryPadLaw_cellMass_image]

-- @node: binaryPadLaw_outcomeMean_image
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd), [padding preserves
  conditional outcome means on embedded source cells](goal). -/
lemma binaryPadLaw_outcomeMean_image {m d : ℕ} (hmd : m ≤ d) (P : BinLaw m)
    (k : Fin m) (a : Bool) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean (binaryPadLaw hmd P) a
        ⟨k, lt_of_lt_of_le k.isLt hmd⟩ =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k := by
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean
  rw [binaryPadLaw_jointMass_image, binaryPadLaw_armMass_image]

-- @node: binaryPadLaw_overlap
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the source law satisfies
  the stated model condition](hyp:hP), [the binary pad law preserves the overlap condition](goal). -/
lemma binaryPadLaw_overlap {m d : ℕ} (hmd : m ≤ d) {epsilon : ℝ} {P : BinLaw m}
    (hP : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon (binaryPadLaw hmd P) := by
  intro k hk
  by_cases himage : ∃ r : Fin m, (⟨r, lt_of_lt_of_le r.isLt hmd⟩ : Fin d) = k
  · obtain ⟨r, rfl⟩ := himage
    rw [binaryPadLaw_propensity_image]
    apply hP r
    simpa [binaryPadLaw_cellMass_image] using hk
  · have hoff : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
        (binaryPadLaw hmd P) k = 0 := by
      unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
      simp_rw [binaryPadLaw_jointMass_off_image hmd P k (by simpa using himage)]
      simp
    linarith

-- @node: binaryPadLaw_ateFunctional
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the source law satisfies
  the stated model condition](hyp:hP), [zero-mass padding preserves the binary
  average-treatment-effect functional](goal). -/
lemma binaryPadLaw_ateFunctional {m d : ℕ} (hmd : m ≤ d) {epsilon : ℝ} {P : BinLaw m}
    (hP : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P) :
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional (binaryPadLaw hmd P) =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P := by
  rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_weighted_regression _
      (binaryPadLaw_overlap hmd hP),
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_weighted_regression _ hP]
  classical
  let f : Fin m → Fin d := fun r ↦ ⟨r, lt_of_lt_of_le r.isLt hmd⟩
  let g : Fin d → ℝ := fun k ↦
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass (binaryPadLaw hmd P) k *
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean (binaryPadLaw hmd P) true k -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean (binaryPadLaw hmd P) false k)
  calc
    ∑ k : Fin d, g k = ∑ k ∈ Finset.image f Finset.univ, g k := by
      symm
      apply Finset.sum_subset
      · simp
      · intro k _hk hkimage
        have himage : ¬ ∃ r : Fin m, f r = k := by simpa using hkimage
        have hoff : CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
            (binaryPadLaw hmd P) k = 0 := by
          unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass
          simp_rw [binaryPadLaw_jointMass_off_image hmd P k (by simpa [f] using himage)]
          simp
        simp [g, hoff]
    _ = ∑ r : Fin m, g (f r) := by
      exact Finset.sum_image (fun _ _ _ _ h =>
        Fin.ext (congrArg (fun q : Fin d => q.val) h))
    _ = ∑ k : Fin m,
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k *
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k) := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp [g, f, binaryPadLaw_cellMass_image, binaryPadLaw_outcomeMean_image]

-- @node: affineBinaryPaddedLaw_exactHomogeneity
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the stated condition on
  the source size or matching order holds](hyp:hm) and [the source law satisfies the stated model
  condition](hyp:hP), [padding by zero-mass cells preserves exact treatment-effect homogeneity in
  the support-qualified real-outcome model](goal). -/
lemma affineBinaryPaddedLaw_exactHomogeneity {m d : ℕ} (hmd : m ≤ d) (hm : 0 < m)
    {epsilon M : ℝ} {P : BinLaw m} (hP : BinaryExactHomogeneous epsilon P) :
    ApproximateHomogeneity M 0 (affineBinaryRealLaw M (binaryPadLaw hmd P)) := by
  have hate (r : Fin m) :
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P =
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true r -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false r := by
    rw [CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional_eq_weighted_regression P hP.1]
    simp_rw [hP.2.1, hP.2.2 _ r]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [nsmul_eq_mul, hmR]
  intro k hk
  have himage : ∃ r : Fin m, (⟨r, lt_of_lt_of_le r.isLt hmd⟩ : Fin d) = k := by
    by_contra hnot
    have hoff := binaryPadLaw_cellMass_off_image hmd P k (by simpa using hnot)
    have hmass : (affineBinaryRealLaw M (binaryPadLaw hmd P)).cellMass k = 0 := by
      change CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass (binaryPadLaw hmd P) k = 0
      exact hoff
    linarith
  obtain ⟨r, rfl⟩ := himage
  have hembed := affineBinaryRealLaw_embedding M (binaryPadLaw hmd P)
  have hraw : rawAteFormula (affineBinaryRealLaw M (binaryPadLaw hmd P)) =
      M * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P := by
    rw [rawAteFormula_eq_mul_binaryAte_of_embedding hembed (binaryPadLaw_overlap hmd hP.1),
      binaryPadLaw_ateFunctional hmd hP.1]
  unfold cellDeviation cellEffect
  change |M * (_ - 1 / 2) - M * (_ - 1 / 2) - _| ≤ 0 * M
  rw [binaryPadLaw_outcomeMean_image, binaryPadLaw_outcomeMean_image, hraw, hate r]
  ring_nf
  simp

-- @node: affineBinaryPaddedLaw_model
/-- The padded affine image of an exact binary source law belongs to every
nonnegative-radius ambient class. -/
noncomputable def affineBinaryPaddedLaw_model {m d : ℕ} (hmd : m ≤ d) (hm : 0 < m)
    {epsilon M sigma : ℝ} (P : BinLaw m)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (hM : 1 ≤ M)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (hP : BinaryExactHomogeneous epsilon P) :
    ModelClass d epsilon M sigma where
  law := affineBinaryRealLaw M (binaryPadLaw hmd P)
  epsilon_pos := he0
  epsilon_lt_half := he1
  M_ge_one := hM
  sigma_nonneg := hs0
  sigma_le_two := hs2
  consistency := affineBinaryRealLaw_consistency M (binaryPadLaw hmd P)
  exchangeability := affineBinaryRealLaw_exchangeability M (binaryPadLaw hmd P)
  overlap := affineBinaryRealLaw_overlap (binaryPadLaw_overlap hmd hP.1)
  mean_normalization := affineBinaryRealLaw_meanNormalization (le_trans zero_le_one hM)
  second_moment := affineBinaryRealLaw_secondCentralMoment (le_trans zero_le_one hM)
  homogeneity := by
    intro k hk
    have hz := affineBinaryPaddedLaw_exactHomogeneity hmd hm hP k hk
    rw [zero_mul] at hz
    have hnonneg : 0 ≤ sigma * M := mul_nonneg hs0 (le_trans zero_le_one hM)
    exact hz.trans hnonneg

-- @node: minimaxRisk_ge_of_padded_exact_hard_family
/-- If [the source alphabet embeds in the target alphabet](hyp:hmd) and [the stated condition on
  the source size or matching order holds](hyp:hm) and [the overlap constant is positive](hyp:he0)
  and [the overlap constant is below one half](hyp:he1) and [the outcome scale satisfies its
  stated bound](hyp:hM) and [the heterogeneity radius is nonnegative](hyp:hs0) and [the
  heterogeneity radius is at most two](hyp:hs2) and [the source parameter set has the stated
  form](hyp:hsource), [a hard exact binary family on `m` cells transfers to the real-outcome
  problem on any larger alphabet by zero-mass padding followed by affine scaling](goal). -/
lemma minimaxRisk_ge_of_padded_exact_hard_family {n m d : ℕ}
    {epsilon M sigma L : ℝ} (hmd : m ≤ d) (hm : 0 < m)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hM : 1 ≤ M) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2)
    (hsource : ∀ est : (Fin n → BinObs m) → ℝ, Measurable est →
      ∃ P : BinaryExactLaw n m epsilon,
        L ≤ CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1)) :
    M ^ 2 * L ≤ minimaxRisk n d epsilon M sigma := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMne : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM)
  let est0 : Estimator n d M :=
    ⟨fun _ ↦ 0, measurable_const, fun _ ↦ by simp [hM0]⟩
  letI : Nonempty (Estimator n d M) := ⟨est0⟩
  unfold minimaxRisk
  apply le_ciInf
  intro est
  let Phi : BinaryExactLaw n m epsilon → RealLaw d := fun P ↦
    affineBinaryRealLaw M (binaryPadLaw hmd P.1)
  let phi : BinObs m → Obs d := fun z ↦ affineObserved M (binaryPadObs hmd z)
  have hphi : Measurable phi :=
    (measurable_affineObserved M).comp (measurable_of_finite _)
  have hobs (P : BinaryExactLaw n m epsilon) :
      (Phi P).observedLaw = Measure.map phi
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1) := by
    change (affineBinaryRealLaw M (binaryPadLaw hmd P.1)).observedLaw = _
    rw [(affineBinaryRealLaw_embedding M (binaryPadLaw hmd P.1)).1,
      binaryPadLaw_obsLaw, Measure.map_map]
    · rfl
    · exact measurable_affineObserved M
    · exact measurable_of_finite _
  have htransport :=
    Causalean.Stat.forall_estimator_exists_sqRisk_ge_of_deterministic_affine_transport_pi
      (Iota := BinaryExactLaw n m epsilon) (n := n)
      (P := fun j ↦ CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw j.1)
      (Q := fun j ↦ (Phi j).observedLaw)
      (theta := fun j ↦ CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional j.1)
      (phi := phi) (a := M) (b := 0) (L := L)
      hMne hphi hobs
      (by
        intro sourceEst hmeas
        obtain ⟨P, hrisk⟩ := hsource sourceEst hmeas
        exact ⟨P, by
          simpa [Causalean.Stat.sqRisk,
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse,
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw] using hrisk⟩)
      est.1 est.2.1
  obtain ⟨P, hP⟩ := htransport
  let Q : ModelClass d epsilon M sigma :=
    affineBinaryPaddedLaw_model hmd hm P.1 he0 he1 hM hs0 hs2 P.2
  have hQ : Q.law = Phi P := rfl
  have htau : rawAteFormula Q.law =
      M * CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1 := by
    change rawAteFormula (affineBinaryRealLaw M (binaryPadLaw hmd P.1)) = _
    rw [rawAteFormula_eq_mul_binaryAte_of_embedding
      (affineBinaryRealLaw_embedding M (binaryPadLaw hmd P.1))
      (binaryPadLaw_overlap hmd P.2.1), binaryPadLaw_ateFunctional hmd P.2.1]
  have hrisk : M ^ 2 * L ≤ mse Q.law est.1 := by
    rw [← htau] at hP
    rw [hQ] at hP
    rw [hQ]
    simpa [Causalean.Stat.sqRisk, productLaw, mse, Phi] using hP
  have hb : BddAbove (Set.range (fun R : ModelClass d epsilon M sigma ↦
      mse R.law est.1)) := by
    refine ⟨(2 * M) ^ 2, ?_⟩
    rintro _ ⟨R, rfl⟩
    exact test_model_mse_le R est
  exact hrisk.trans (le_ciSup hb Q)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
