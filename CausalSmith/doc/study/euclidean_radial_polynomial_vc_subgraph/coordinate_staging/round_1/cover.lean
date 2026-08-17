import Causalean.Stat.Concentration.Covering.EuclideanRadialPolynomial.Geometry
import Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Algebra

/-!
# Uniform polynomial covers for radial monomials

This module converts the finite-trace pseudo-dimension certificate into a
uniform polynomial `L²(Q)` covering certificate.  The measure `Q` remains
arbitrary throughout, so atoms on moving annulus boundaries are included.

It also supplies two general assembly tools: pullback of a covering class
along an arbitrary nonempty parameter map (using internal representatives at
twice the preliminary radius), and the covering certificate for any bounded
finite class.  These tools let later score constructions reuse the existing
sum and product closure lemmas.
-/

namespace Causalean.Stat.Concentration.EuclideanRadialPolynomial

open Causalean.Stat.Concentration
open MeasureTheory

universe u v w

/-- A positive common envelope for all radial powers from zero through `p`
on an annulus whose upper relative radius is `b`. -/
def radialMonomialEnvelope (b : ℝ) (p : ℕ) : ℝ :=
  (max 1 b) ^ p

/-- A compactly supported Euclidean radial monomial is Borel measurable in
the observation for every fixed center and degree. -/
theorem radialAnnulusMonomial_measurable
    (d k : ℕ) (q a b : ℝ) (x : EuclideanPoint d) :
    Measurable (radialAnnulusMonomial d q a b k x) := by
  unfold radialAnnulusMonomial
  have hd : Measurable (fun z : EuclideanPoint d => dist z x) :=
    measurable_id.dist measurable_const
  refine Measurable.ite ?_ ((hd.div measurable_const).pow_const k) measurable_const
  simpa only [Set.setOf_and] using
    (measurableSet_le measurable_const hd).inter
      (measurableSet_le hd measurable_const)

/-- Every degree `k ≤ p` radial monomial on an ordered nonnegative annulus is
bounded in absolute value by `radialMonomialEnvelope b p`. -/
theorem abs_radialAnnulusMonomial_le
    (d p k : ℕ) {q a b : ℝ}
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) (hk : k ≤ p)
    (x z : EuclideanPoint d) :
    |radialAnnulusMonomial d q a b k x z| ≤
      radialMonomialEnvelope b p := by
  rw [radialAnnulusMonomial]
  split_ifs with h
  · rw [abs_of_nonneg (pow_nonneg (div_nonneg dist_nonneg hq.le) _)]
    have hrb : dist z x / q ≤ b := (div_le_iff₀ hq).2 h.2
    have hrM : dist z x / q ≤ max 1 b := hrb.trans (le_max_right _ _)
    have hM : 1 ≤ max 1 b := le_max_left _ _
    exact (pow_le_pow_left₀ (div_nonneg dist_nonneg hq.le) hrM k).trans
      (pow_le_pow_right₀ hM hk)
  · rw [abs_zero]
    exact pow_nonneg (le_trans (by norm_num) (le_max_left 1 b)) p

private lemma measureL2Dist_eq_lpNorm' {𝒳 : Type u} [MeasurableSpace 𝒳]
    (Q : Measure 𝒳) (f g : 𝒳 → ℝ) (hf : Measurable f) (hg : Measurable g) :
    measureL2Dist Q f g = lpNorm (fun x => f x - g x) (2 : ENNReal) Q := by
  have h := lpNorm_nnreal_eq_integral_norm_rpow (μ := Q) (f := fun x => f x - g x)
    (p := (2 : NNReal)) (by norm_num) (hf.sub hg).aestronglyMeasurable
  have h' : lpNorm (fun x => f x - g x) (2 : ENNReal) Q =
      (∫ x, ‖f x - g x‖ ^ (2 : ℝ) ∂Q) ^ ((2 : ℝ)⁻¹) := by
    simpa using h
  rw [measureL2Dist, h']
  norm_num [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]

private lemma measureL2Dist_triangle' {𝒳 : Type u} [MeasurableSpace 𝒳]
    {Q : Measure 𝒳} [IsFiniteMeasure Q]
    (f g h : 𝒳 → ℝ) (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {U : ℝ} (hfU : ∀ x, |f x| ≤ U) (hgU : ∀ x, |g x| ≤ U) :
    measureL2Dist Q f h ≤ measureL2Dist Q f g + measureL2Dist Q g h := by
  let df : 𝒳 → ℝ := fun x => f x - g x
  let dg : 𝒳 → ℝ := fun x => g x - h x
  have hdf : Measurable df := hf.sub hg
  have hdf_mem : MemLp df (2 : ENNReal) Q :=
    MemLp.of_bound hdf.aestronglyMeasurable (2 * U) <| Filter.Eventually.of_forall fun x => by
      dsimp [df]
      simpa [Real.norm_eq_abs] using
        (abs_sub (f x) (g x)).trans (by nlinarith [hfU x, hgU x])
  have htri := lpNorm_add_le hdf_mem (p := (2 : ENNReal)) (by norm_num) (g := dg)
  rw [measureL2Dist_eq_lpNorm' Q f h hf hh,
    measureL2Dist_eq_lpNorm' Q f g hf hg,
    measureL2Dist_eq_lpNorm' Q g h hg hh]
  have hfun : (fun x => f x - h x) = df + dg := by
    funext x
    dsimp [df, dg]
    ring
  rwa [hfun]

/-- Pulling a polynomial-cover class back along an arbitrary parameter map
preserves a polynomial `L²` covering certificate when the new parameter type
is nonempty.  Cover centers are replaced by occupied-class representatives,
which costs only a factor two in radius. -/
theorem HasPolynomialL2Cover.pullback
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {ι : Type v} {κ : Type w} [Nonempty κ]
    {F : ι → 𝒳 → ℝ} {U : ℝ}
    (hF : HasPolynomialL2Cover F U) (e : κ → ι) :
    HasPolynomialL2Cover (fun k => F (e k)) U := by
  refine ⟨hF.envelope_pos, fun k => hF.measurable (e k),
    fun k => hF.envelope (e k), ?_⟩
  obtain ⟨A, p, hA, hent⟩ := hF.entropy
  refine ⟨2 * A, p, by nlinarith, ?_⟩
  intro Q hQ ε hε hε1
  have hhalf : 0 < ε / 2 := by positivity
  have hhalf1 : ε / 2 ≤ 1 := by linarith
  obtain ⟨C, hCcard, hCcover⟩ := hent Q hQ (ε / 2) hhalf hhalf1
  classical
  choose center hcenter_mem hcenter_dist using fun k => hCcover (e k)
  let occupied : Finset ι := C.filter fun i => ∃ k, center k = i
  let representative : ι → κ := fun i =>
    if hi : ∃ k, center k = i then Classical.choose hi else Classical.choice inferInstance
  refine ⟨occupied.image representative, ?_, ?_⟩
  · calc
      (occupied.image representative).card ≤ occupied.card := Finset.card_image_le
      _ ≤ C.card := Finset.card_filter_le _ _
      _ ≤ Nat.ceil ((A / (ε / 2)) ^ p) := hCcard
      _ = Nat.ceil (((2 * A) / ε) ^ p) := by
        congr 2
        field_simp
  · intro k
    have hocc : center k ∈ occupied := by
      simp only [occupied, Finset.mem_filter]
      exact ⟨hcenter_mem k, ⟨k, rfl⟩⟩
    have hrep_center : center (representative (center k)) = center k := by
      dsimp only [representative]
      split
      · next h => exact Classical.choose_spec h
      · next h => exact (h ⟨k, rfl⟩).elim
    refine ⟨representative (center k), Finset.mem_image.mpr
      ⟨center k, hocc, rfl⟩, ?_⟩
    letI : IsProbabilityMeasure Q := hQ
    calc
      measureL2Dist Q (F (e k)) (F (e (representative (center k)))) ≤
          measureL2Dist Q (F (e k)) (F (center k)) +
            measureL2Dist Q (F (center k)) (F (e (representative (center k)))) :=
        measureL2Dist_triangle' _ _ _ (hF.measurable _) (hF.measurable _)
          (hF.measurable _) (hF.envelope _) (hF.envelope _)
      _ = measureL2Dist Q (F (e k)) (F (center k)) +
            measureL2Dist Q (F (e (representative (center k)))) (F (center k)) := by
        congr 1
        simp only [measureL2Dist]
        congr 2
        funext x
        ring
      _ < ε * U := by
        have hrep_dist :
            measureL2Dist Q (F (e (representative (center k)))) (F (center k)) <
              ε / 2 * U := by
          simpa only [hrep_center] using hcenter_dist (representative (center k))
        nlinarith [hcenter_dist k, hrep_dist]

/-- Pullback preserves named entropy witnesses, with the explicit factor-two
radius cost used by the ordinary pullback construction. -/
theorem HasPolynomialL2CoverWith.pullback
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {ι : Type v} {κ : Type w} [Nonempty κ]
    {F : ι → 𝒳 → ℝ} {U A : ℝ} {p : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p) (e : κ → ι) :
    HasPolynomialL2CoverWith (fun k => F (e k)) U (2 * A) p := by
  refine ⟨HasPolynomialL2Cover.pullback hF.forget e, by linarith [hF.one_le_base], ?_⟩
  intro Q hQ ε hε hε1
  have hhalf : 0 < ε / 2 := by positivity
  have hhalf1 : ε / 2 ≤ 1 := by linarith
  obtain ⟨C, hCcard, hCcover⟩ := hF.entropy Q hQ (ε / 2) hhalf hhalf1
  classical
  choose center hcenter_mem hcenter_dist using fun k => hCcover (e k)
  let occupied : Finset ι := C.filter fun i => ∃ k, center k = i
  let representative : ι → κ := fun i =>
    if hi : ∃ k, center k = i then Classical.choose hi else Classical.choice inferInstance
  refine ⟨occupied.image representative, ?_, ?_⟩
  · calc
      (occupied.image representative).card ≤ occupied.card := Finset.card_image_le
      _ ≤ C.card := Finset.card_filter_le _ _
      _ ≤ Nat.ceil ((A / (ε / 2)) ^ p) := hCcard
      _ = Nat.ceil (((2 * A) / ε) ^ p) := by
        congr 2
        field_simp
  · intro k
    have hocc : center k ∈ occupied := by
      simp only [occupied, Finset.mem_filter]
      exact ⟨hcenter_mem k, ⟨k, rfl⟩⟩
    have hrep_center : center (representative (center k)) = center k := by
      dsimp only [representative]
      split
      · next h => exact Classical.choose_spec h
      · next h => exact (h ⟨k, rfl⟩).elim
    refine ⟨representative (center k), Finset.mem_image.mpr
      ⟨center k, hocc, rfl⟩, ?_⟩
    letI : IsProbabilityMeasure Q := hQ
    calc
      measureL2Dist Q (F (e k)) (F (e (representative (center k)))) ≤
          measureL2Dist Q (F (e k)) (F (center k)) +
            measureL2Dist Q (F (center k)) (F (e (representative (center k)))) :=
        measureL2Dist_triangle' _ _ _ (hF.forget.measurable _)
          (hF.forget.measurable _) (hF.forget.measurable _)
          (hF.forget.envelope _) (hF.forget.envelope _)
      _ = measureL2Dist Q (F (e k)) (F (center k)) +
            measureL2Dist Q (F (e (representative (center k)))) (F (center k)) := by
        congr 1
        simp only [measureL2Dist]
        congr 2
        funext x
        ring
      _ < ε * U := by
        have hrep_dist :
            measureL2Dist Q (F (e (representative (center k)))) (F (center k)) <
              ε / 2 * U := by
          simpa only [hrep_center] using hcenter_dist (representative (center k))
        nlinarith [hcenter_dist k, hrep_dist]

/-- A parameterwise pullback preserves entropy witnesses uniformly over the
outer parameter family. -/
theorem HasUniformPolynomialL2CoverOver.pullback
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {S : Type*} {ι : S → Type v} {κ : S → Type w}
    {F : (s : S) → ι s → 𝒳 → ℝ} {U : S → ℝ}
    (hF : HasUniformPolynomialL2CoverOver S F U)
    (hκ : ∀ s, Nonempty (κ s))
    (e : (s : S) → κ s → ι s) :
    HasUniformPolynomialL2CoverOver S (fun s k => F s (e s k)) U := by
  obtain ⟨A, p, hF⟩ := hF
  refine ⟨2 * A, p, fun s => ?_⟩
  letI : Nonempty (κ s) := hκ s
  exact HasPolynomialL2CoverWith.pullback (hF s) (e s)

/-- Enlarging the positive envelope of a polynomial `L²` covering
certificate preserves the certificate and its polynomial constants. -/
theorem HasPolynomialL2Cover.monoEnvelope
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {ι : Type v} {F : ι → 𝒳 → ℝ} {U V : ℝ}
    (hF : HasPolynomialL2Cover F U) (hUV : U ≤ V) :
    HasPolynomialL2Cover F V := by
  refine ⟨hF.envelope_pos.trans_le hUV, hF.measurable,
    fun i x => (hF.envelope i x).trans hUV, ?_⟩
  obtain ⟨A, p, hA, hent⟩ := hF.entropy
  refine ⟨A, p, hA, ?_⟩
  intro Q hQ ε hε hε1
  obtain ⟨C, hCcard, hCcover⟩ := hent Q hQ ε hε hε1
  refine ⟨C, hCcard, ?_⟩
  intro i
  obtain ⟨j, hjC, hij⟩ := hCcover i
  exact ⟨j, hjC, hij.trans_le (mul_le_mul_of_nonneg_left hUV hε.le)⟩

/-- Enlarging an envelope preserves named entropy witnesses. -/
theorem HasPolynomialL2CoverWith.monoEnvelope
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {ι : Type v} {F : ι → 𝒳 → ℝ} {U V A : ℝ} {p : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p) (hUV : U ≤ V) :
    HasPolynomialL2CoverWith F V A p := by
  refine ⟨Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasPolynomialL2Cover.monoEnvelope
    hF.forget hUV, hF.one_le_base, ?_⟩
  intro Q hQ ε hε hε1
  obtain ⟨C, hCcard, hCcover⟩ := hF.entropy Q hQ ε hε hε1
  refine ⟨C, hCcard, ?_⟩
  intro i
  obtain ⟨j, hjC, hij⟩ := hCcover i
  exact ⟨j, hjC, hij.trans_le (mul_le_mul_of_nonneg_left hUV hε.le)⟩

/-- A parameterwise envelope enlargement preserves uniform named witnesses. -/
theorem HasUniformPolynomialL2CoverOver.monoEnvelope
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {S : Type*} {ι : S → Type v}
    {F : (s : S) → ι s → 𝒳 → ℝ} {U V : S → ℝ}
    (hF : HasUniformPolynomialL2CoverOver S F U)
    (hUV : ∀ s, U s ≤ V s) :
    HasUniformPolynomialL2CoverOver S F V := by
  obtain ⟨A, p, hF⟩ := hF
  exact ⟨A, p, fun s =>
    Causalean.Stat.Concentration.EuclideanRadialPolynomial.HasPolynomialL2CoverWith.monoEnvelope
      (hF s) (hUV s)⟩

/-- Every finite family of measurable functions bounded by a positive common
envelope has a uniform polynomial `L²` covering certificate. -/
theorem finiteClass_hasPolynomialL2Cover
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {ι : Type v} [Fintype ι]
    (F : ι → 𝒳 → ℝ) {U : ℝ}
    (hU : 0 < U) (hmeas : ∀ i, Measurable (F i))
    (hbound : ∀ i x, |F i x| ≤ U) :
    HasPolynomialL2Cover F U := by
  refine ⟨hU, hmeas, hbound, max 1 (Fintype.card ι : ℝ), 1,
    le_max_left _ _, ?_⟩
  intro Q hQ ε hε hε1
  classical
  refine ⟨Finset.univ, ?_, ?_⟩
  · rw [Finset.card_univ]
    have hA0 : 0 ≤ max 1 (Fintype.card ι : ℝ) :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    have hreal : (Fintype.card ι : ℝ) ≤ max 1 (Fintype.card ι : ℝ) / ε := by
      calc
        (Fintype.card ι : ℝ) ≤ max 1 (Fintype.card ι : ℝ) := le_max_right _ _
        _ ≤ max 1 (Fintype.card ι : ℝ) / ε := by
          apply (le_div_iff₀ hε).2
          nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hε1)]
    have hnat : Fintype.card ι ≤ Nat.ceil (max 1 (Fintype.card ι : ℝ) / ε) := by
      exact_mod_cast hreal.trans (Nat.le_ceil (max 1 (Fintype.card ι : ℝ) / ε))
    simpa using hnat
  · intro i
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [measureL2Dist, mul_pos hε hU]

/-- A finite bounded measurable class has named entropy witnesses depending
only on its cardinality. -/
theorem finiteClass_hasPolynomialL2CoverWith
    {𝒳 : Type u} [MeasurableSpace 𝒳]
    {ι : Type v} [Fintype ι]
    (F : ι → 𝒳 → ℝ) {U : ℝ}
    (hU : 0 < U) (hmeas : ∀ i, Measurable (F i))
    (hbound : ∀ i x, |F i x| ≤ U) :
    HasPolynomialL2CoverWith F U (max 1 (Fintype.card ι : ℝ)) 1 := by
  refine ⟨finiteClass_hasPolynomialL2Cover F hU hmeas hbound,
    le_max_left _ _, ?_⟩
  intro Q hQ ε hε hε1
  classical
  refine ⟨Finset.univ, ?_, ?_⟩
  · rw [Finset.card_univ]
    have hA0 : 0 ≤ max 1 (Fintype.card ι : ℝ) :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    have hreal : (Fintype.card ι : ℝ) ≤ max 1 (Fintype.card ι : ℝ) / ε := by
      calc
        (Fintype.card ι : ℝ) ≤ max 1 (Fintype.card ι : ℝ) := le_max_right _ _
        _ ≤ max 1 (Fintype.card ι : ℝ) / ε := by
          apply (le_div_iff₀ hε).2
          nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hε1)]
    have hnat : Fintype.card ι ≤ Nat.ceil (max 1 (Fintype.card ι : ℝ) / ε) := by
      exact_mod_cast hreal.trans (Nat.le_ceil (max 1 (Fintype.card ι : ℝ) / ε))
    simpa using hnat
  · intro i
    refine ⟨i, Finset.mem_univ _, ?_⟩
    simp [measureL2Dist, mul_pos hε hU]

/-- Moving-center radial monomials of every degree from zero through `p` have
a polynomial `L²(Q)` cover with a positive constant envelope, uniformly over
every probability measure `Q`. -/
theorem radialMonomialClass_hasPolynomialL2Cover
    (d p : ℕ) {q a b : ℝ}
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) :
    HasPolynomialL2Cover (radialMonomialClass d p q a b)
      (radialMonomialEnvelope b p) := by
  apply (radialMonomialClass_hasPseudoDimAtMost d p hq ha hab).hasPolynomialL2Cover
  · intro θ
    exact radialAnnulusMonomial_measurable d θ.2.1 q a b θ.1
  · unfold radialMonomialEnvelope
    positivity
  · intro θ z
    apply abs_radialAnnulusMonomial_le d p θ.2.1 hq ha hab
    exact Nat.le_of_lt_succ θ.2.2

/-- A fixed degree `k ≤ p` of the moving-center radial class has the same
uniform polynomial cover and envelope as the full degree vector. -/
theorem radialAnnulusMonomial_hasPolynomialL2Cover
    (d p k : ℕ) {q a b : ℝ}
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) (hk : k ≤ p) :
    HasPolynomialL2Cover
      (fun x : EuclideanPoint d => radialAnnulusMonomial d q a b k x)
      (radialMonomialEnvelope b p) := by
  let degree : Fin (p + 1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
  simpa [radialMonomialClass, degree] using
    HasPolynomialL2Cover.pullback
      (radialMonomialClass_hasPolynomialL2Cover d p hq ha hab)
      (fun x : EuclideanPoint d => (x, degree))

/-- Evaluation of the radial-monomial class after a measurable Euclidean
location map on a general observation space. -/
noncomputable def radialMonomialOn
    {Ω : Type u} [MeasurableSpace Ω]
    (d p : ℕ) (loc : Ω → EuclideanPoint d) (q a b : ℝ)
    (θ : RadialMonomialParam d p) (ω : Ω) : ℝ :=
  radialMonomialClass d p q a b θ (loc ω)

/-- Composing the radial class with any measurable Euclidean location map
preserves its uniform polynomial `L²` covering certificate. -/
theorem radialMonomialOn_hasPolynomialL2Cover
    {Ω : Type u} [MeasurableSpace Ω]
    (d p : ℕ) (loc : Ω → EuclideanPoint d) {q a b : ℝ}
    (hloc : Measurable loc)
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) :
    HasPolynomialL2Cover (radialMonomialOn d p loc q a b)
      (radialMonomialEnvelope b p) := by
  apply (HasPseudoDimAtMost.compDomain
    (radialMonomialClass_hasPseudoDimAtMost d p hq ha hab) loc).hasPolynomialL2Cover
  · intro θ
    exact (radialAnnulusMonomial_measurable d θ.2.1 q a b θ.1).comp hloc
  · unfold radialMonomialEnvelope
    positivity
  · intro θ ω
    apply abs_radialAnnulusMonomial_le d p θ.2.1 hq ha hab
    exact Nat.le_of_lt_succ θ.2.2

/-- The moving-center radial class after a measurable location map has the
canonical named VC-subgraph entropy witnesses. -/
theorem radialMonomialOn_hasPolynomialL2CoverWith
    {Ω : Type u} [MeasurableSpace Ω]
    (d p : ℕ) (loc : Ω → EuclideanPoint d) {q a b : ℝ}
    (hloc : Measurable loc)
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) :
    HasPolynomialL2CoverWith (radialMonomialOn d p loc q a b)
      (radialMonomialEnvelope b p) 16
      (8 * (radialPseudoDimBound d p + 1)) := by
  apply (HasPseudoDimAtMost.compDomain
    (radialMonomialClass_hasPseudoDimAtMost d p hq ha hab) loc).hasPolynomialL2CoverWith
  · intro θ
    exact (radialAnnulusMonomial_measurable d θ.2.1 q a b θ.1).comp hloc
  · unfold radialMonomialEnvelope
    positivity
  · intro θ ω
    apply abs_radialAnnulusMonomial_le d p θ.2.1 hq ha hab
    exact Nat.le_of_lt_succ θ.2.2

/-- Multiplying a moving-center radial monomial by any bounded measurable
finite family of signed arms preserves a uniform polynomial cover.  Boolean
arms and the two signs are obtained by taking a finite arm type and values in
`{0,1}` or `{-1,1}`. -/
theorem finiteSignedArmRadial_hasPolynomialL2Cover
    {Ω : Type u} [MeasurableSpace Ω]
    {A : Type v} [Fintype A]
    (d p : ℕ) (loc : Ω → EuclideanPoint d)
    (arm : A → Ω → ℝ) {q a b : ℝ}
    (hloc : Measurable loc)
    (harmMeas : ∀ s, Measurable (arm s))
    (harmBound : ∀ s ω, |arm s ω| ≤ 1)
    (hq : 0 < q) (ha : 0 ≤ a) (hab : a ≤ b) :
    HasPolynomialL2Cover
      (fun θ : RadialMonomialParam d p × A => fun ω =>
        radialMonomialOn d p loc q a b θ.1 ω * arm θ.2 ω)
      (radialMonomialEnvelope b p) := by
  classical
  have hU : 0 < radialMonomialEnvelope b p := by
    unfold radialMonomialEnvelope
    positivity
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI : IsEmpty A := hA
      refine ⟨hU, ?_, ?_, ?_⟩
      · intro θ
        exact isEmptyElim θ.2
      · intro θ
        exact isEmptyElim θ.2
      · refine ⟨1, 0, le_rfl, ?_⟩
        intro Q hQ ε hε hε1
        refine ⟨∅, by simp, ?_⟩
        intro θ
        exact isEmptyElim θ.2
  | inr hA =>
      letI : Nonempty A := hA
      have hrad := radialMonomialOn_hasPolynomialL2Cover d p loc hloc hq ha hab
      have harm : HasPolynomialL2Cover arm 1 :=
        finiteClass_hasPolynomialL2Cover arm (by norm_num) harmMeas harmBound
      simpa using hrad.mul harm

end Causalean.Stat.Concentration.EuclideanRadialPolynomial
