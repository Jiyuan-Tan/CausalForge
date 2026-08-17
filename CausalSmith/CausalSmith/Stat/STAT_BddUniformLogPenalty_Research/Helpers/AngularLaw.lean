import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularPacking
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.BumpHolderScaling

/-!
# Faithful Bernoulli--Gaussian regression laws

This file packages the measure-theoretic assembly common to every vertex of
the angular hard family.  Given a normalized score design with its exact
support and a bounded measurable regression, it constructs a `CtyLaw` whose
declared density, regression, and conditional variance are the corresponding
functionals of the joint Bernoulli-plus-Gaussian law.
-/

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The faithful CTY law obtained from a score design and a measurable
Bernoulli regression by adding independent standard Gaussian noise. -/
-- @node: bernoulliGaussianCtyLaw
noncomputable def bernoulliGaussianCtyLaw
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (S : Set Score) (density p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hmarginal : nu = volume.withDensity
      (fun x => ENNReal.ofReal (S.indicator density x)))
    (hsupport : S = nu.support) (hclosed : IsClosed S)
    (hdensityPos : ∀ x ∈ S, 0 < density x) : CtyLaw where
  law := jointBernoulliGaussianLaw nu p hp
  support := S
  density := density
  mu := p
  sigmaSq := fun x => 1 + p x * (1 - p x)
  law_isProbability :=
    jointBernoulliGaussianLaw_isProbabilityMeasure nu p hp hp0 hp1
  sq_integrable :=
    jointBernoulliGaussianLaw_memLp_fst_two nu p hp hp0 hp1
  marginal_eq := by
    rw [jointBernoulliGaussianLaw_map_snd nu p hp hp0 hp1]
    exact hmarginal
  support_eq_marginal_support := by
    rw [jointBernoulliGaussianLaw_map_snd nu p hp hp0 hp1]
    exact hsupport
  support_closed := hclosed
  density_pos := hdensityPos
  mu_condMean := by
    simpa [jointBernoulliGaussianLaw_map_snd nu p hp hp0 hp1] using
      jointBernoulliGaussianLaw_condMean nu p hp hp0 hp1
  sigmaSq_condVar := by
    simpa [jointBernoulliGaussianLaw_map_snd nu p hp hp0 hp1] using
      jointBernoulliGaussianLaw_condVar nu p hp hp0 hp1

/-- The packaged Bernoulli--Gaussian law belongs to the CTY class once the
geometric, density, Holder, and variance certificates for its supplied
profiles have been established. -/
-- @node: bernoulliGaussianCtyLaw_mem_nonparametricClass
lemma bernoulliGaussianCtyLaw_mem_nonparametricClass
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (q : ℕ) (L : ℝ) (S : Set Score) (density p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hmarginal : nu = volume.withDensity
      (fun x => ENNReal.ofReal (S.indicator density x)))
    (hsupport : S = nu.support) (hclosed : IsClosed S)
    (hdensityPos : ∀ x ∈ S, 0 < density x)
    (hq : 1 ≤ q) (hL : 4 ≤ L)
    (hdensityContinuous : ContinuousOn density S)
    (hcompact : IsCompact S) (hsubset : S ⊆ scoreCube L)
    (hdensityEnvelope : ∀ x ∈ S, L⁻¹ ≤ density x ∧ density x ≤ L)
    (hrectifiable : RectifiableBoundary S)
    (hholder : EuclideanHolderBallStd p (q : ℝ) L S)
    (hvarianceContinuous : ContinuousOn (fun x => 1 + p x * (1 - p x)) S)
    (hvarianceEnvelope :
      ∀ x ∈ S, L⁻¹ ≤ 1 + p x * (1 - p x) ∧ 1 + p x * (1 - p x) ≤ L) :
    CtyNonparametricClass q L
      (bernoulliGaussianCtyLaw nu S density p hp hp0 hp1 hmarginal
        hsupport hclosed hdensityPos) := by
  exact ⟨hq, hL, hdensityContinuous, hcompact, hsubset, hdensityEnvelope,
    hrectifiable, hholder, hvarianceContinuous, hvarianceEnvelope⟩

/-- The score marginal of the packaged CTY law is the input design measure. -/
-- @node: bernoulliGaussianCtyLaw_map_snd
lemma bernoulliGaussianCtyLaw_map_snd
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (S : Set Score) (density p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hmarginal : nu = volume.withDensity
      (fun x => ENNReal.ofReal (S.indicator density x)))
    (hsupport : S = nu.support) (hclosed : IsClosed S)
    (hdensityPos : ∀ x ∈ S, 0 < density x) :
    Measure.map Prod.snd
        (bernoulliGaussianCtyLaw nu S density p hp hp0 hp1 hmarginal
          hsupport hclosed hdensityPos).law = nu := by
  exact jointBernoulliGaussianLaw_map_snd nu p hp hp0 hp1

/-- The packaged CTY law exposes the supplied regression pointwise, including
at boundary points where the conditional-mean identity itself is only a.e. -/
-- @node: bernoulliGaussianCtyLaw_mu
lemma bernoulliGaussianCtyLaw_mu
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (S : Set Score) (density p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hmarginal : nu = volume.withDensity
      (fun x => ENNReal.ofReal (S.indicator density x)))
    (hsupport : S = nu.support) (hclosed : IsClosed S)
    (hdensityPos : ∀ x ∈ S, 0 < density x) :
    (bernoulliGaussianCtyLaw nu S density p hp hp0 hp1 hmarginal
      hsupport hclosed hdensityPos).mu = p := rfl

/-- The packaged CTY law exposes the Bernoulli-plus-Gaussian conditional
variance pointwise. -/
-- @node: bernoulliGaussianCtyLaw_sigmaSq
lemma bernoulliGaussianCtyLaw_sigmaSq
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (S : Set Score) (density p : Score → ℝ)
    (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hmarginal : nu = volume.withDensity
      (fun x => ENNReal.ofReal (S.indicator density x)))
    (hsupport : S = nu.support) (hclosed : IsClosed S)
    (hdensityPos : ∀ x ∈ S, 0 < density x) :
    (bernoulliGaussianCtyLaw nu S density p hp hp0 hp1 hmarginal
      hsupport hclosed hdensityPos).sigmaSq =
        fun x => 1 + p x * (1 - p x) := rfl

/-- The faithful law at one vertex of the angular packing family.  Its score
design is the angularly tilted square density and its Bernoulli regression is
the globally clipped packing regression, which agrees with the smooth paper
regression throughout the square. -/
-- @node: angularPackingCtyLaw
noncomputable def angularPackingCtyLaw {M : ℕ}
    (b cA delta w : ℝ) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k)) : CtyLaw := by
  let nu : Measure Score :=
    angularDesignMeasure b cA delta w (angularGridCenter M) omega
  let density : Score → ℝ :=
    angularDesignDensity b cA delta w (angularGridCenter M) omega
  let p : Score → ℝ :=
    clippedPackingRegression b delta w (angularGridCenter M) omega
  letI : IsProbabilityMeasure nu :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw hwQuarter hsep omega
  apply bernoulliGaussianCtyLaw nu packingSquare density p
    (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega)
    (fun x ↦ (clippedPackingRegression_mem_Icc
      b delta w (angularGridCenter M) omega x).1)
    (fun x ↦ (clippedPackingRegression_mem_Icc
      b delta w (angularGridCenter M) omega x).2)
  · unfold nu density packingSquare angularDesignMeasure
    congr 1
    funext x
    by_cases hx : x ∈ scoreCube (1 / 2 : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      simp [angularDesignDensity_eq_zero_off_square hx]
  · unfold nu packingSquare
    exact (angularDesignMeasure_support hb hscale hcA hdelta hw hsep omega).symm
  · exact packingSquare_isCompact.isClosed
  · intro x hx
    exact angularDesignDensity_pos hcA hdelta hw hsep omega hx

/-- Every angular packing law has the fixed square as its declared support. -/
-- @node: angularPackingCtyLaw_support
lemma angularPackingCtyLaw_support {M : ℕ}
    (b cA delta w : ℝ) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k)) :
    (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
      hwQuarter hsep).support = packingSquare := rfl

/-- The score marginal of an angular packing law is exactly its explicitly
constructed angular design measure. -/
-- @node: angularPackingCtyLaw_map_snd
lemma angularPackingCtyLaw_map_snd {M : ℕ}
    (b cA delta w : ℝ) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k)) :
    Measure.map Prod.snd
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
          hwQuarter hsep).law =
      angularDesignMeasure b cA delta w (angularGridCenter M) omega := by
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep omega
  unfold angularPackingCtyLaw
  exact jointBernoulliGaussianLaw_map_snd
    (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
    (clippedPackingRegression b delta w (angularGridCenter M) omega)
    (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega)
    (fun x ↦ (clippedPackingRegression_mem_Icc
      b delta w (angularGridCenter M) omega x).1)
    (fun x ↦ (clippedPackingRegression_mem_Icc
      b delta w (angularGridCenter M) omega x).2)

/-- On the square, the angular packing law's regression is exactly the smooth
packing regression used in the paper construction. -/
-- @node: angularPackingCtyLaw_mu_eq_on_square
lemma angularPackingCtyLaw_mu_eq_on_square {M : ℕ}
    {b cA delta w : ℝ} {omega : Fin M → Bool}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    {x : Score} (hx : x ∈ packingSquare) :
    (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
      hwQuarter hsep).mu x =
      packingRegression b delta w (angularGridCenter M) omega x := by
  change clippedPackingRegression b delta w (angularGridCenter M) omega x = _
  exact clippedPackingRegression_eq_on_square
    hbSmall hdelta.le hdeltaSmall hw hsep omega hx

/-- At every grid center, the faithful law's regression equals the Boolean
center value used by the finite packing certificate. -/
-- @node: angularPackingCtyLaw_mu_center
lemma angularPackingCtyLaw_mu_center {M : ℕ}
    {b cA delta w : ℝ} {omega : Fin M → Bool}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (j : Fin M) :
    (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
      hwQuarter hsep).mu (angularGridCenter M j) =
      packingCenterValue b delta (angularGridCenter M) j (omega j) := by
  rw [angularPackingCtyLaw_mu_eq_on_square hb hbSmall hscale hcA hdelta
    hdeltaSmall hw hwQuarter hsep
      (packingSquare_isCompact.isClosed.frontier_subset
        (angularGridCenter_mem_packingSquare_frontier M j))]
  exact packingRegression_eq_packingCenterValue omega j hw hsep

/-- All non-Hölder obligations for membership of an angular packing vertex in
the CTY class follow from the explicit square design and Bernoulli--Gaussian
construction.  The remaining hypothesis is precisely the scaled-bump Hölder
estimate. -/
-- @node: angularPackingCtyLaw_mem_nonparametricClass_of_holder
lemma angularPackingCtyLaw_mem_nonparametricClass_of_holder {M q : ℕ}
    {L b cA delta w : ℝ} (omega : Fin M → Bool)
    (hq : 1 ≤ q) (hL : 4 ≤ L) (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (hholder : EuclideanHolderBallStd
      (clippedPackingRegression b delta w (angularGridCenter M) omega)
      (q : ℝ) L packingSquare) :
    CtyNonparametricClass q L
      (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
        hwQuarter hsep) := by
  let nu : Measure Score :=
    angularDesignMeasure b cA delta w (angularGridCenter M) omega
  let density : Score → ℝ :=
    angularDesignDensity b cA delta w (angularGridCenter M) omega
  let p : Score → ℝ :=
    clippedPackingRegression b delta w (angularGridCenter M) omega
  letI : IsProbabilityMeasure nu :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw hwQuarter hsep omega
  have hmarginal : nu = volume.withDensity
      (fun x ↦ ENNReal.ofReal (packingSquare.indicator density x)) := by
    unfold nu density packingSquare angularDesignMeasure
    congr 1
    funext x
    by_cases hx : x ∈ scoreCube (1 / 2 : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      simp [angularDesignDensity_eq_zero_off_square hx]
  have hsupport : packingSquare = nu.support := by
    unfold nu packingSquare
    exact (angularDesignMeasure_support hb hscale hcA hdelta hw hsep omega).symm
  have hdensityPos : ∀ x ∈ packingSquare, 0 < density x := by
    intro x hx
    exact angularDesignDensity_pos hcA hdelta hw hsep omega hx
  have hdensityContinuous : ContinuousOn density packingSquare := by
    exact angularDesignDensity_continuousOn hb hscale _ omega
  have hdensityEnvelope : ∀ x ∈ packingSquare,
      L⁻¹ ≤ density x ∧ density x ≤ L := by
    intro x hx
    change L⁻¹ ≤
      angularDesignDensity b cA delta w (angularGridCenter M) omega x ∧
      angularDesignDensity b cA delta w (angularGridCenter M) omega x ≤ L
    have hd := angularDesignDensity_mem_Icc
      (b := b) hcA hdelta hw hsep omega hx
    have hLpos : 0 < L := by linarith
    constructor
    · have hinv : L⁻¹ ≤ (4 : ℝ)⁻¹ :=
        (inv_le_inv₀ hLpos (by norm_num)).2 hL
      norm_num at hinv
      exact hinv.trans (by linarith [hd.1])
    · linarith [hd.2]
  have hvarianceContinuous : ContinuousOn (fun x ↦ 1 + p x * (1 - p x))
      packingSquare := by
    have hpcont : Continuous p := by
      exact clippedPackingRegression_continuous
        b delta w (angularGridCenter M) omega
    exact (continuous_const.add (hpcont.mul (continuous_const.sub hpcont))).continuousOn
  have hvarianceEnvelope : ∀ x ∈ packingSquare,
      L⁻¹ ≤ 1 + p x * (1 - p x) ∧ 1 + p x * (1 - p x) ≤ L := by
    intro x hx
    have hp : clippedPackingRegression b delta w (angularGridCenter M) omega x ∈
        Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
      rw [clippedPackingRegression_eq_on_square hbSmall hdelta.le hdeltaSmall
        hw hsep omega hx]
      exact packingRegression_mem_Icc hbSmall hdelta.le hdeltaSmall hw hsep omega hx
    have hv :=
      Causalean.Mathlib.InformationTheory.one_add_mul_one_sub_mem_Icc hp
    have hLpos : 0 < L := by linarith
    constructor
    · exact ((inv_le_one₀ hLpos).2 (by linarith)).trans hv.1
    · exact hv.2.trans (by linarith)
  exact bernoulliGaussianCtyLaw_mem_nonparametricClass
    (nu := nu) (q := q) (L := L) (S := packingSquare)
    (density := density) (p := p)
    (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega)
    (fun x ↦ (clippedPackingRegression_mem_Icc
      b delta w (angularGridCenter M) omega x).1)
    (fun x ↦ (clippedPackingRegression_mem_Icc
      b delta w (angularGridCenter M) omega x).2)
    hmarginal hsupport packingSquare_isCompact.isClosed hdensityPos hq hL
    hdensityContinuous packingSquare_isCompact
    (packingSquare_subset_scoreCube (by linarith)) hdensityEnvelope
    packingSquare_rectifiableBoundary hholder hvarianceContinuous hvarianceEnvelope

end CausalSmith.Stat.BddUniformLogPenalty
