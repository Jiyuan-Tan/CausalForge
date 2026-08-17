import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.FiniteMaxLowerBound

/-!
# Point-indexed converse on the causal A1/A2 class

The proof uses the fixed-geometry hypercube, binomial good-count conditioning,
the decentralized direct-product certificate, and outer-integral packaging.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: causalEuclideanCExtEnvelope_abs_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma causalEuclideanCExtEnvelope_abs_le {f : Score → ℝ} {p : ℕ} {L : ℝ}
    {S : Set Score} (hf : EuclideanCExtEnvelope f p L S)
    {x : Score} (hx : x ∈ S) : |f x| ≤ L := by
  rcases hf with ⟨U, hU, hSU, g, hg, hgf, hpartialBdd, hlipBdd, hsum⟩
  have hmem : |g x| ∈ coordinatePartialValues g p S := by
    refine ⟨fun _ => 0, ?_, x, hx, ?_⟩
    · simp [coordinateMultiOrder]
    · unfold coordinatePartial
      simp only [coordinateMultiOrder, Pi.zero_apply, add_zero]
      exact congrArg abs
        (iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := g) (x := x)
          (coordinateDirections (fun _ : Fin 2 => 0))).symm
  have hle : |g x| ≤ sSup (coordinatePartialValues g p S) :=
    le_csSup hpartialBdd hmem
  have hlipnonneg : 0 ≤ sSup (coordinatePartialLipschitzValues g p S) := by
    apply Real.sSup_nonneg
    rintro r ⟨alpha, ha, y, hy, z, hz, hyz, rfl⟩
    positivity
  rw [← hgf hx]
  linarith

-- @node: causalOuterLIntegral_mono
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma causalOuterLIntegral_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f g : Ω → ℝ≥0∞} (hfg : f ≤ g) :
    MeasureTheory.outerLIntegral μ f ≤ MeasureTheory.outerLIntegral μ g := by
  unfold MeasureTheory.outerLIntegral
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  apply le_iInf
  intro hgG
  exact iInf_le_of_le G (iInf_le_of_le hG
    (iInf_le_of_le (fun x => (hfg x).trans (hgG x)) le_rfl))

-- @node: causalFinitePackingLoss_le_boundaryLoss
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma causalFinitePackingLoss_le_boundaryLoss {n M : ℕ}
    (rho : A1A2RuleFun n) (P : A1A2Law) (centers : Fin M → Score)
    (hcenters : ∀ j, centers j ∈ P.boundary) :
    causalFinitePackingLoss rho P centers ≤ a1a2BoundaryLoss rho P := by
  intro w
  unfold causalFinitePackingLoss a1a2BoundaryLoss
  apply iSup_le
  intro j
  exact le_iSup_of_le (centers j) (le_iSup_of_le (hcenters j) le_rfl)

/-- Membership in the single fixed support, assignment rectangle, and
interior boundary used by the causal hard subclass. -/
def CausalHardGeometryLaw (P : A1A2Law) : Prop :=
  P.support = causalHardSquare ∧
  P.A1 = causalHardArmOne ∧
  P.A0 = causalHardSquare \ causalHardArmOne ∧
  P.boundary = frontier causalHardArmOne

-- @node: a1a2_finite_max_eventually_lower
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma a1a2_finite_max_eventually_lower (p : ℕ) :
    ∃ L0 : ℝ, 48 ≤ L0 ∧ ∀ ν : ℝ, 2 ≤ ν → ∀ L : ℝ, L0 ≤ L →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
        ∀ rhoRule : A1A2RuleFun n,
          rhoRule ∈ A1A2PointIndexedDecisionClass n p ν L →
          ∃ P : A1A2Law, ∃ M : ℕ, ∃ centers : Fin M → Score,
            A1A2Class p ν L P ∧ CausalHardGeometryLaw P ∧
            (∀ j, centers j ∈ P.boundary) ∧
            Measurable (causalFinitePackingLoss rhoRule P centers) ∧
            ENNReal.ofReal (c * frontierRate n) ≤
              ∫⁻ w, causalFinitePackingLoss rhoRule P centers w
                ∂causalSampleLaw P n := by
  obtain ⟨L0, hL0, hcube⟩ := cty_a1_a2_rectangle_angular_hypercube p
  refine ⟨L0, hL0, ?_⟩
  intro ν hν L hL
  obtain ⟨c0, A, C, C0, hc0, hA, hC, hC0, hp0, δ0, hδ0, hfamily⟩ :=
    hcube ν hν L hL
  let q := p + 1
  have hq : 1 ≤ q := by omega
  let z : ℝ := 128 * (q : ℝ) * C0
  have hz : 0 < z := by dsimp [z]; positivity
  let gamma : ℝ := min 1 z⁻¹
  have hgamma : 0 < gamma := lt_min (by norm_num) (inv_pos.mpr hz)
  have hgamma1 : gamma ≤ 1 := min_le_left _ _
  have hgammaz : gamma ≤ z⁻¹ := min_le_right _ _
  have hgamma4 : gamma ^ 4 ≤ gamma := by
    nlinarith [sq_nonneg gamma, mul_self_le_mul_self (le_of_lt hgamma) hgamma1]
  have hsmall : 128 * (q : ℝ) * C0 * gamma ^ 4 ≤ 1 := by
    have hzgam : z * gamma ≤ 1 := by
      calc z * gamma ≤ z * z⁻¹ := mul_le_mul_of_nonneg_left hgammaz hz.le
           _ = 1 := mul_inv_cancel₀ hz.ne'
    dsimp [z] at hzgam
    nlinarith
  let d : ℝ := (1 / 2 : ℝ) * (1 - Real.exp (-(1 : ℝ) / 2))
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (by norm_num) (sub_pos.mpr (by
      rw [Real.exp_lt_one_iff]
      norm_num))
  let c : ℝ := gamma * d / 8
  have hc : 0 < c := div_pos (mul_pos hgamma hd) (by norm_num)
  have hdeltaEvent : ∀ᶠ n : ℕ in atTop,
      gamma * frontierRate n ≤ δ0 := by
    have ht : Tendsto (fun n : ℕ => gamma * frontierRate n) atTop (nhds 0) := by
      simpa using frontierRate_tendsto_zero.const_mul gamma
    filter_upwards [ht.eventually (Iio_mem_nhds hδ0)] with n hn
    exact hn.le
  have hklEvent := causalScaledFrontier_eventually_klBudget q hq c0 gamma C0
    hc0 hgamma hC0.le hsmall
  have htailEvent : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
        (c / (2 * L)) * frontierRate n := by
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (hL0.trans hL)
    have hcoef : 0 < c / (2 * L) := div_pos hc (mul_pos (by norm_num) hLpos)
    have h := poisson_remainder_isLittleO_frontier.def hcoef
    filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with n hnrm hn
    have he0 : 0 ≤ Real.exp (-(n : ℝ) * (1 - Real.log 2)) := Real.exp_pos _ |>.le
    have hr0 : 0 ≤ frontierRate n := (frontierRate_pos hn).le
    simpa [abs_of_nonneg he0, abs_of_nonneg hr0] using hnrm
  obtain ⟨Nδ, hNδ⟩ := eventually_atTop.1 hdeltaEvent
  obtain ⟨Nkl, hNkl⟩ := eventually_atTop.1 hklEvent
  obtain ⟨Ntail, hNtail⟩ := eventually_atTop.1 htailEvent
  refine ⟨c, hc, max 2 (max Nδ (max Nkl Ntail)), ?_⟩
  intro n hn rhoRule hrule
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnδ : Nδ ≤ n := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hn)
  have hnkl : Nkl ≤ n := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hntail : Ntail ≤ n := le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  let Δ := gamma * frontierRate n
  have hΔ : 0 < Δ := mul_pos hgamma (frontierRate_pos hn2)
  have hΔ0 : Δ ≤ δ0 := hNδ n hnδ
  obtain ⟨M, w, rhoCell, centers, laws, Q, _hc, _hA, _hC, _hC0,
    _hp0, hrho, hMlower, hw, hrhoEq, hcenters, hcells, hsep, hdis,
    hclass, hgeom, hmass, hlocal, hoff, hprob, hmap, htargetLocal,
    htau, _hradius, _htail, hkl01, _hkl10⟩ := hfamily Δ hΔ hΔ0
  have hqcast : (q : ℝ) = (p : ℝ) + 1 := by simp [q]
  have hMlower' : c0 * Real.rpow Δ (-(1 : ℝ) / (q : ℝ)) ≤ M := by
    simpa [hqcast] using hMlower
  have hM : 1 ≤ M := by
    have hleft : 0 < c0 * Real.rpow Δ (-(1 : ℝ) / (q : ℝ)) :=
      mul_pos hc0 (Real.rpow_pos_of_pos hΔ _)
    have : (0 : ℝ) < M := hleft.trans_le hMlower'
    exact_mod_cast this
  have hbudget : C0 * (n : ℝ) * Δ ^ 4 ≤ (1 / 4 : ℝ) * Real.log M :=
    hNkl n hnkl M (by simpa [Δ] using hMlower')
  have hcellKL : ∀ j, InformationTheory.klDiv (Q j false) (Q j true) *
      ENNReal.ofReal (2 * n * rhoCell) ≤
        ENNReal.ofReal ((1 / 4 : ℝ) * Real.log M) := by
    intro j
    calc
      InformationTheory.klDiv (Q j false) (Q j true) *
          ENNReal.ofReal (2 * n * rhoCell) ≤
        ENNReal.ofReal (C0 * Δ ^ 4 / w ^ 2) *
          ENNReal.ofReal (2 * n * rhoCell) := mul_le_mul_left (hkl01 j) _
      _ = ENNReal.ofReal ((C0 * Δ ^ 4 / w ^ 2) * (2 * n * rhoCell)) := by
        rw [← ENNReal.ofReal_mul]
        positivity
      _ ≤ ENNReal.ofReal (C0 * (n : ℝ) * Δ ^ 4) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hrhoEq]
        have hpi : Real.pi ≤ 4 := Real.pi_le_four
        have hwne : w ≠ 0 := by
          intro hwz
          rw [hwz] at hrhoEq
          norm_num at hrhoEq
          linarith
        have hw2 : 0 < w ^ 2 := sq_pos_of_ne_zero hwne
        calc
          (C0 * Δ ^ 4 / w ^ 2) *
              (2 * (n : ℕ) * (Real.pi * w ^ 2 / 36)) =
              C0 * (n : ℝ) * Δ ^ 4 * (Real.pi / 18) := by field_simp; ring
          _ ≤ C0 * (n : ℝ) * Δ ^ 4 := by
            have hbase : 0 ≤ C0 * (n : ℝ) * Δ ^ 4 := by positivity
            have : Real.pi / 18 ≤ 1 := by linarith [Real.pi_le_four]
            nlinarith
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget
  obtain ⟨T, hT⟩ := hrule
  let omega0 : Fin M → Bool := fun _ => false
  let P0 := laws omega0
  let values : Fin M → Bool → ℝ := fun j b =>
    (laws (causalPackingSingleBit j b)).tau (centers j)
  have hgeomP0 : ∀ omega, (laws omega).support = P0.support ∧
      (laws omega).A1 = P0.A1 ∧ (laws omega).A0 = P0.A0 ∧
      (laws omega).boundary = P0.boundary := by
    intro omega
    simp only [P0]
    exact ⟨(hgeom omega).1.trans (hgeom omega0).1.symm,
      (hgeom omega).2.1.trans (hgeom omega0).2.1.symm,
      (hgeom omega).2.2.1.trans (hgeom omega0).2.2.1.symm,
      (hgeom omega).2.2.2.trans (hgeom omega0).2.2.2.symm⟩
  have herror := causalPackingCoordinatewiseError_lower_bound hM T P0 centers
    values w rhoCell (1 / 4) hdis laws Q hprob hrho hmass hmap hgeomP0
    (by norm_num) hcellKL
  have hfiniteCoeff : ENNReal.ofReal d ≤ ENNReal.ofReal
      ((1 / 2 : ℝ) * (1 - Real.exp (-((M : ℝ) ^ (1 - (1 / 4 : ℝ))) / 2))) := by
    apply ENNReal.ofReal_le_ofReal
    have hpow : 1 ≤ (M : ℝ) ^ (1 - (1 / 4 : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
    have hexp := Real.exp_le_exp.mpr (show
      -((M : ℝ) ^ (1 - (1 / 4 : ℝ))) / 2 ≤ -(1 : ℝ) / 2 by linarith)
    dsimp [d]
    linarith
  have hcoord : ENNReal.ofReal d ≤ coordinatewiseErrorProbability
      (fun j b => causalPackingCellExperiment
        (causalPackingFinitePartition centers w hdis) laws (2 * n) j b)
      (causalPackingCommonExperiment
        (causalPackingFinitePartition centers w hdis) laws (2 * n))
      (fun j => compressCausalPackingCell P0 centers j)
      (causalPackingPoissonDecoder T P0 centers values) := hfiniteCoeff.trans herror
  have hvalues : ∀ omega j, (laws omega).tau (centers j) = values j (omega j) := by
    intro omega j
    exact htargetLocal omega (causalPackingSingleBit j (omega j)) j (by
      simp [causalPackingSingleBit])
  have hseparation : ∀ j, Δ ≤ |values j true - values j false| := by
    intro j
    have hh := htau (causalPackingSingleBit j false) j
    have hup : Function.update (causalPackingSingleBit j false) j
        (!(causalPackingSingleBit j false j)) = causalPackingSingleBit j true := by
      funext k
      by_cases hk : k = j
      · subst k; simp [causalPackingSingleBit]
      · simp [Function.update, causalPackingSingleBit, hk]
    rw [hup] at hh
    simpa [values, abs_sub_comm] using hh.symm.le
  obtain ⟨omega, hpoisson⟩ :=
    exists_vertex_causalPoissonLoss_ge_coordinatewiseError T P0 centers values
      w rhoCell Δ hdis laws hrho hmass hlocal hoff hvalues hseparation
  let P := laws omega
  have hP := hclass omega
  have hG : CausalHardGeometryLaw P := hgeom omega
  have hcentersP : ∀ j, centers j ∈ P.boundary := by
    intro j
    rw [hG.2.2.2]
    exact (mem_frontier_causalHardArmOne_iff (centers j)).2
      ⟨by linarith [(hcenters j).1], by linarith [(hcenters j).2.1],
        by linarith [(hcenters j).2.2], by linarith [(hcenters j).2.2],
        Or.inr (Or.inr (Or.inl (hcenters j).2.2))⟩
  have hmeas := causalFinitePackingLoss_measurable rhoRule ⟨T, hT⟩ P hP centers hcentersP
  have hsection : ∀ sample j, rhoRule sample (knownGeometry P) (centers j) =
      T.map (knownGeometry P) (centers j)
        (signedDistanceData n P sample (centers j)) := by
    intro sample j
    exact hT P hP sample (centers j) (hcentersP j)
  have hknown : knownGeometry P0 = knownGeometry P := by
    exact knownGeometry_eq_of_components_eq P0 P
      ⟨(hgeomP0 omega).1.symm, (hgeomP0 omega).2.1.symm,
        (hgeomP0 omega).2.2.1.symm, (hgeomP0 omega).2.2.2.symm⟩
  have hbound : ∀ j, |values j (omega j)| ≤ 2 * L := by
    intro j
    rw [← hvalues omega j]
    have hsupport : centers j ∈ P.support := by
      rw [hG.1]
      intro i
      fin_cases i
      · change -3 ≤ centers j 0 ∧ centers j 0 ≤ 3
        exact ⟨by linarith [(hcenters j).1], by linarith [(hcenters j).2.1]⟩
      · change -3 ≤ centers j 1 ∧ centers j 1 ≤ 3
        exact ⟨by linarith [(hcenters j).2.2], by linarith [(hcenters j).2.2]⟩
    have hmu (t : Bool) : |P.muPO t (centers j)| ≤ L :=
      causalEuclideanCExtEnvelope_abs_le (hP.2.2.2.2.2.1 t) hsupport
    unfold A1A2Law.tau
    exact (abs_sub _ _).trans (by linarith [hmu true, hmu false])
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  have hdepois := globalCausalPackingPoissonRisk_le_fixedRisk_add_tail
    T rhoRule P0 P centers values omega hknown hsection (hvalues omega) hmeas
      (2 * L) hbound
  have hmain : ENNReal.ofReal (Δ / 2) * ENNReal.ofReal d ≤
      ∫⁻ s, globalCausalPackingPoissonLoss T P0 centers values omega s
        ∂canonicalMarkedPoissonSampleLaw P.law packingMarkLaw (2 * n) :=
    (mul_le_mul_right hcoord _).trans hpoisson
  have htailReal : (2 * L) * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
      c * frontierRate n := by
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (hL0.trans hL)
    have h2L : 0 ≤ 2 * L := mul_nonneg (by norm_num) hLpos.le
    have := mul_le_mul_of_nonneg_left (hNtail n hntail) h2L
    calc
      _ ≤ (2 * L) * ((c / (2 * L)) * frontierRate n) := this
      _ = _ := by field_simp
  have h2L : 0 ≤ 2 * L := by
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (hL0.trans hL)
    positivity
  have htailENN : ENNReal.ofReal (2 * L) *
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) ≤
      ENNReal.ofReal (c * frontierRate n) := by
    rw [← ENNReal.ofReal_mul h2L]
    exact ENNReal.ofReal_le_ofReal htailReal
  have hmainEq : ENNReal.ofReal (Δ / 2) * ENNReal.ofReal d =
      ENNReal.ofReal (4 * (c * frontierRate n)) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Δ / 2)]
    congr 1
    dsimp [Δ, c]
    ring
  refine ⟨P, M, centers, hP, hG, hcentersP, hmeas, ?_⟩
  have hcr0 : 0 ≤ c * frontierRate n :=
    mul_nonneg hc.le (frontierRate_pos hn2).le
  have hsum : ENNReal.ofReal (c * frontierRate n) +
      ENNReal.ofReal (c * frontierRate n) ≤
      (∫⁻ sample, causalFinitePackingLoss rhoRule P centers sample
        ∂causalSampleLaw P n) + ENNReal.ofReal (c * frontierRate n) := by
    calc
      _ ≤ ENNReal.ofReal (4 * (c * frontierRate n)) := by
        rw [← ENNReal.ofReal_add hcr0 hcr0]
        apply ENNReal.ofReal_le_ofReal
        linarith
      _ = _ := hmainEq.symm
      _ ≤ _ := hmain
      _ ≤ (∫⁻ sample, causalFinitePackingLoss rhoRule P centers sample
          ∂causalSampleLaw P n) +
          (ENNReal.ofReal (2 * L) * ENNReal.ofReal
            (Real.exp (-(n : ℝ) * (1 - Real.log 2)))) := hdepois
      _ ≤ _ := add_le_add_right htailENN _
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hsum

/-- The causal outer risk after restricting the law supremum to the fixed
hard geometry. -/
noncomputable def a1a2FixedGeometryOuterRisk
    (n p : ℕ) (ν L : ℝ) : ℝ≥0∞ :=
  ⨅ rho : A1A2RuleFun n,
    ⨅ (_hrho : rho ∈ A1A2PointIndexedDecisionClass n p ν L),
      ⨆ P : A1A2Law, ⨆ (_hP : A1A2Class p ν L P),
        ⨆ (_hG : CausalHardGeometryLaw P),
          MeasureTheory.outerLIntegral (causalSampleLaw P n) (a1a2BoundaryLoss rho P)

-- @node: lintegral_le_outerLIntegral_of_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma lintegral_le_outerLIntegral_of_measurable {Ω : Type*}
    [TopologicalSpace Ω] [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) ≤ MeasureTheory.outerLIntegral μ f := by
  unfold MeasureTheory.outerLIntegral
  apply le_iInf
  intro g
  apply le_iInf
  intro hg
  apply le_iInf
  intro hfg
  exact lintegral_mono hfg

-- @node: a1a2OuterRisk_eventually_lower
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma a1a2OuterRisk_eventually_lower (p : ℕ) :
    ∃ L0 : ℝ, 48 ≤ L0 ∧ ∀ ν : ℝ, 2 ≤ ν → ∀ L : ℝ, L0 ≤ L →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
        ENNReal.ofReal (c * frontierRate n) ≤
          a1a2OuterRisk n p ν L ∧
        ENNReal.ofReal (c * frontierRate n) ≤
          a1a2FixedGeometryOuterRisk n p ν L := by
  obtain ⟨L0, hL0, hlower⟩ := a1a2_finite_max_eventually_lower p
  refine ⟨L0, hL0, ?_⟩
  intro ν hν L hL
  obtain ⟨c, hc, N, hN⟩ := hlower ν hν L hL
  refine ⟨c, hc, N, ?_⟩
  intro n hn
  constructor
  · unfold a1a2OuterRisk
    apply le_iInf
    intro rho
    apply le_iInf
    intro hrho
    obtain ⟨P, M, centers, hP, hG, hcenters, hmeas, hfin⟩ :=
      hN n hn rho hrho
    refine hfin.trans ?_
    have houter : (∫⁻ w, causalFinitePackingLoss rho P centers w
        ∂causalSampleLaw P n) ≤
        MeasureTheory.outerLIntegral (causalSampleLaw P n)
          (a1a2BoundaryLoss rho P) := by
      exact (lintegral_le_outerLIntegral_of_measurable _ hmeas).trans
        (causalOuterLIntegral_mono _
          (causalFinitePackingLoss_le_boundaryLoss rho P centers hcenters))
    exact houter.trans (le_iSup_of_le P (le_iSup_of_le hP le_rfl))
  · unfold a1a2FixedGeometryOuterRisk
    apply le_iInf
    intro rho
    apply le_iInf
    intro hrho
    obtain ⟨P, M, centers, hP, hG, hcenters, hmeas, hfin⟩ :=
      hN n hn rho hrho
    refine hfin.trans ?_
    have houter : (∫⁻ w, causalFinitePackingLoss rho P centers w
        ∂causalSampleLaw P n) ≤
        MeasureTheory.outerLIntegral (causalSampleLaw P n)
          (a1a2BoundaryLoss rho P) := by
      exact (lintegral_le_outerLIntegral_of_measurable _ hmeas).trans
        (causalOuterLIntegral_mono _
          (causalFinitePackingLoss_le_boundaryLoss rho P centers hcenters))
    exact houter.trans
      (le_iSup_of_le P (le_iSup_of_le hP (le_iSup_of_le hG le_rfl)))

-- @node: thm:cty-a1-a2-point-indexed-log-converse-all-orders
/-- For every polynomial order and moment exponent, the causal point-indexed
outer-expectation minimax risk has a positive normalized liminf once the
uniform envelope exceeds a threshold depending only on `p`. -/
theorem cty_a1_a2_point_indexed_log_converse (p : ℕ) :
    ∃ L0 : ℝ, 48 ≤ L0 ∧ ∀ ν : ℝ, 2 ≤ ν → ∀ L : ℝ, L0 ≤ L →
      ∃ c : ℝ, 0 < c ∧
        liminf (scaledRisk (fun n => a1a2OuterRisk n p ν L)) atTop =
          liminf (normalizedRisk (fun n => a1a2OuterRisk n p ν L)) atTop ∧
        ENNReal.ofReal c ≤
          liminf (normalizedRisk (fun n => a1a2OuterRisk n p ν L)) atTop ∧
        ENNReal.ofReal c ≤
          liminf (normalizedRisk
            (fun n => a1a2FixedGeometryOuterRisk n p ν L)) atTop := by
  obtain ⟨L0, hL0, hlower⟩ := a1a2OuterRisk_eventually_lower p
  refine ⟨L0, hL0, ?_⟩
  intro ν hν L hL
  obtain ⟨c, hc, N, hN⟩ := hlower ν hν L hL
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · apply le_antisymm
    · apply Filter.liminf_le_liminf
      · exact scaledRisk_eventually_eq_normalizedRisk _ |>.le
      · isBoundedDefault
      · isBoundedDefault
    · apply Filter.liminf_le_liminf
      · exact scaledRisk_eventually_eq_normalizedRisk _ |>.symm.le
      · isBoundedDefault
      · isBoundedDefault
  · apply le_liminf_of_le
    · isBoundedDefault
    · filter_upwards [eventually_ge_atTop (max N 2)] with n hn
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
      have hrate0 : ENNReal.ofReal (frontierRate n) ≠ 0 := by
        simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using frontierRate_pos hn2
      unfold normalizedRisk
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl hrate0) (Or.inl ENNReal.ofReal_ne_top)).2
      rw [← ENNReal.ofReal_mul hc.le]
      exact (hN n hnN).1
  · apply le_liminf_of_le
    · isBoundedDefault
    · filter_upwards [eventually_ge_atTop (max N 2)] with n hn
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
      have hrate0 : ENNReal.ofReal (frontierRate n) ≠ 0 := by
        simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using frontierRate_pos hn2
      unfold normalizedRisk
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl hrate0) (Or.inl ENNReal.ofReal_ne_top)).2
      rw [← ENNReal.ofReal_mul hc.le]
      exact (hN n hnN).2

end CausalSmith.Stat.BddUniformLogPenalty
