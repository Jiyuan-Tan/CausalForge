/- Fixed-interior tightness and localization of the shrinking-radius gap. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.RateAlgebra

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Filter

/-- Selector benchmark `q` before saturation. -/
noncomputable def selectorBenchmark (n d : ℕ) (sigma : ℝ) : ℝ :=
  1 / (n : ℝ) + min (polynomialComponent n d)
    (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2)

/-- Product-form converse benchmark `ell`. -/
noncomputable def productBenchmark (n d : ℕ) (sigma : ℝ) : ℝ :=
  baseRate n d + sigma ^ 2 * polynomialComponent n d

/-- One of the three regimes in which the proved benchmarks match uniformly. -/
def MatchingElbow (K : ℝ) (n d : ℕ) (sigma : ℝ) : Prop :=
  1 ≤ polynomialComponent n d ∨
  polynomialComponent n d ≤ K * baseRate n d ∨
  sigma ^ 2 ≤ K * baseRate n d

/-- Divergence of the selector/converse benchmark ratio along a sequence. -/
def BenchmarkRatioDiverges (dseq : ℕ → ℕ) (sseq : ℕ → ℝ) : Prop :=
  Tendsto (fun n => frontierRate n (dseq n) (sseq n) /
    converseRate n (dseq n) (sseq n)) atTop atTop

/-- Two positive sequences have the same order eventually. -/
def EventuallySameOrder (f g : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ᶠ n in atTop, c * g n ≤ f n ∧ f n ≤ C * g n

/-- If [the heterogeneity radius is nonnegative](hyp:_hsigma_nonneg) and [the heterogeneity radius
  is at most two](hyp:_hsigma_two) and [the stated lower bound holds](hyp:hlower) and [the stated
  upper bound holds](hyp:hupper), [in the nonsaturated triangular regime, the selector benchmark
  is within a factor two of the additive benchmark using `min (u, sigma²)`](goal). -/
lemma selectorBenchmark_triangular (n d : ℕ) (sigma : ℝ)
    (_hsigma_nonneg : 0 ≤ sigma) (_hsigma_two : sigma ≤ 2)
    (hlower : logEN n ^ 2 < d) (hupper : (d : ℝ) < n * logEN n) :
    (1 / 2 : ℝ) *
        (baseRate n d + min (polynomialComponent n d) (sigma ^ 2)) ≤
      selectorBenchmark n d sigma ∧
    selectorBenchmark n d sigma ≤
      baseRate n d + min (polynomialComponent n d) (sigma ^ 2) := by
  have hd : 0 < (d : ℝ) := lt_of_le_of_lt (sq_nonneg (logEN n)) hlower
  have hnR : 0 < (n : ℝ) := by
    have hprod : 0 < (n : ℝ) * logEN n := hd.trans hupper
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    by_contra hn_not
    have hn_eq : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn_not) hn0
    rw [hn_eq, zero_mul] at hprod
    exact (lt_irrefl 0 hprod)
  have hn : 0 < n := by exact_mod_cast hnR
  have hlog : 0 < logEN n := by
    have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    linarith [Real.log_nonneg hn_one]
  have hnSq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hlogSq : 0 < logEN n ^ 2 := sq_pos_of_pos hlog
  let a : ℝ := 1 / (n : ℝ)
  let t : ℝ := (d : ℝ) / (n : ℝ) ^ 2
  let u : ℝ := polynomialComponent n d
  let s : ℝ := sigma ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have htu : t ≤ u := by
    dsimp [t, u, polynomialComponent]
    rw [div_le_div_iff₀ hnSq (mul_pos hnSq hlogSq)]
    have hmul := mul_lt_mul_of_pos_left hlower (mul_pos hd hnSq)
    nlinarith
  have hu_one : u < 1 := by
    dsimp [u, polynomialComponent]
    rw [div_lt_one (mul_pos hnSq hlogSq)]
    nlinarith [(sq_lt_sq₀ hd.le (mul_nonneg hnR.le hlog.le)).2 hupper]
  have hgeneric :
      (1 / 2 : ℝ) * (a + t + min u s) ≤ a + min u (s + t) ∧
      a + min u (s + t) ≤ a + t + min u s := by
    constructor
    · by_cases hmid : u ≤ s + t
      · rw [min_eq_left hmid]
        have hmin : min u s ≤ u := min_le_left _ _
        nlinarith
      · rw [min_eq_right (le_of_not_ge hmid)]
        have hsu : s ≤ u := by nlinarith
        rw [min_eq_right hsu]
        nlinarith
    · by_cases hus : u ≤ s
      · rw [min_eq_left hus]
        have hmid : min u (s + t) ≤ u := min_le_left _ _
        nlinarith
      · rw [min_eq_right (le_of_not_ge hus)]
        have hmid : min u (s + t) ≤ s + t := min_le_right _ _
        nlinarith
  simpa [selectorBenchmark, baseRate, a, t, u, s, min_eq_left hu_one.le,
    add_assoc] using hgeneric

-- @node: polynomialComponent_le_baseRate_iff
/-- If [the sample is nonempty](hyp:hn), [the polynomial component is below the base rate exactly
  at the displayed constant-free algebraic elbow](goal). -/
lemma polynomialComponent_le_baseRate_iff (n d : ℕ) (hn : 0 < n) :
    polynomialComponent n d ≤ baseRate n d ↔
      (d : ℝ) ^ 2 ≤ n * logEN n ^ 2 + d * logEN n ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    linarith [Real.log_nonneg hn_one]
  rw [polynomialComponent, div_le_iff₀ (mul_pos (sq_pos_of_pos hnR)
    (sq_pos_of_pos hlog))]
  have halg : baseRate n d * ((n : ℝ) ^ 2 * logEN n ^ 2) =
      (n : ℝ) * logEN n ^ 2 + (d : ℝ) * logEN n ^ 2 := by
    unfold baseRate
    field_simp [hnR.ne']
  rw [halg]

-- @node: polynomialComponent_le_baseRate_of_le_sqrt
/-- If [the sample is nonempty](hyp:hn) and [the alphabet size satisfies the stated
  condition](hyp:hd), [the small-alphabet condition `d ≤ sqrt(n) log(en)` implies the polynomial
  component is below the base rate](goal). -/
lemma polynomialComponent_le_baseRate_of_le_sqrt (n d : ℕ) (hn : 0 < n)
    (hd : (d : ℝ) ≤ Real.sqrt n * logEN n) :
    polynomialComponent n d ≤ baseRate n d := by
  rw [polynomialComponent_le_baseRate_iff n d hn]
  have hnR : 0 ≤ (n : ℝ) := by positivity
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ logEN n := by
    have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnRpos.ne', Real.log_exp]
    linarith [Real.log_nonneg hn_one]
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ hd0 (mul_nonneg hsqrt hlog)).2 hd
  rw [mul_pow, Real.sq_sqrt hnR] at hsq
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) (sq_nonneg (logEN n))]

-- @node: polynomialComponent_le_baseRate_of_le_log_sq
/-- If [the sample is nonempty](hyp:hn) and [the alphabet size satisfies the stated
  condition](hyp:hd), [the regime `d ≤ log(en)²` is contained in the constant-free algebraic
  elbow](goal). -/
lemma polynomialComponent_le_baseRate_of_le_log_sq (n d : ℕ) (hn : 0 < n)
    (hd : (d : ℝ) ≤ logEN n ^ 2) :
    polynomialComponent n d ≤ baseRate n d := by
  rw [polynomialComponent_le_baseRate_iff n d hn]
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hlogSq : 0 ≤ logEN n ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hd hd0,
    mul_nonneg hn0 hlogSq]

/-- If [the sample is nonempty](hyp:hn) and [the radius is bounded away from
  zero](hyp:hsigmaLower) and [the heterogeneity radius is nonnegative](hyp:_hsigma_nonneg) and
  [the heterogeneity radius is at most two](hyp:_hsigma_two) and [the heterogeneity radius
  satisfies the stated bound](hyp:hsigma), [at a fixed positive radius, the selector benchmark is
  bounded by a constant multiple of the product-form converse benchmark, uniformly in the
  alphabet](goal). -/
lemma frontierRate_le_converseRate_fixed_radius (n d : ℕ) (sigma sigmaLower : ℝ)
    (hn : 0 < n) (hsigmaLower : 0 < sigmaLower)
    (_hsigma_nonneg : 0 ≤ sigma) (_hsigma_two : sigma ≤ 2)
    (hsigma : sigmaLower ≤ sigma) :
    frontierRate n d sigma ≤
      max 1 (sigmaLower ^ (-2 : ℤ)) * converseRate n d sigma := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ 1 / (n : ℝ) := by positivity
  have ht : 0 ≤ (d : ℝ) / (n : ℝ) ^ 2 := by positivity
  have hu : 0 ≤ polynomialComponent n d := by
    unfold polynomialComponent
    positivity
  have hs : sigmaLower ^ 2 ≤ sigma ^ 2 := by nlinarith
  have hsl2 : 0 < sigmaLower ^ 2 := sq_pos_of_pos hsigmaLower
  have hcoef_one : 1 ≤ max 1 (sigmaLower ^ (-2 : ℤ)) := le_max_left _ _
  have hcoef_inv : (sigmaLower ^ 2)⁻¹ ≤
      max 1 (sigmaLower ^ (-2 : ℤ)) := by
    simpa [zpow_neg, zpow_two] using
      (le_max_right (1 : ℝ) (sigmaLower ^ (-2 : ℤ)))
  have hfront : frontierRate n d sigma ≤
      1 / (n : ℝ) + min 1 (polynomialComponent n d) := by
    unfold frontierRate
    gcongr
    exact min_le_left _ _
  have hscale : min 1 (polynomialComponent n d) ≤
      (sigmaLower ^ 2)⁻¹ *
        (sigma ^ 2 * min 1 (polynomialComponent n d)) := by
    have hm : 0 ≤ min 1 (polynomialComponent n d) := le_min zero_le_one hu
    calc
      min 1 (polynomialComponent n d) =
          (sigmaLower ^ 2)⁻¹ *
            (sigmaLower ^ 2 * min 1 (polynomialComponent n d)) := by
        field_simp
      _ ≤ (sigmaLower ^ 2)⁻¹ *
            (sigma ^ 2 * min 1 (polynomialComponent n d)) := by
        gcongr
  calc
    frontierRate n d sigma ≤
        1 / (n : ℝ) + min 1 (polynomialComponent n d) := hfront
    _ ≤ max 1 (sigmaLower ^ (-2 : ℤ)) * (1 / (n : ℝ)) +
        max 1 (sigmaLower ^ (-2 : ℤ)) *
          (sigma ^ 2 * min 1 (polynomialComponent n d)) := by
      exact add_le_add (by nlinarith [hcoef_one, ha])
        (hscale.trans (mul_le_mul_of_nonneg_right hcoef_inv (by positivity)))
    _ ≤ max 1 (sigmaLower ^ (-2 : ℤ)) * converseRate n d sigma := by
      unfold converseRate
      have hc : 0 ≤ max 1 (sigmaLower ^ (-2 : ℤ)) := zero_le_one.trans hcoef_one
      have htc : 0 ≤ min 1 ((d : ℝ) / (n : ℝ) ^ 2) := le_min zero_le_one ht
      nlinarith

-- @node: frontierRate_le_converseRate_matching_elbow
/-- If [the sample is nonempty](hyp:hn) and [the polynomial or elbow parameter satisfies its
  stated bound](hyp:hK) and [the matching-elbow condition holds](hyp:helbow), [in any matching
  elbow, the selector benchmark is bounded by `1 + K` times the converse benchmark](goal). -/
lemma frontierRate_le_converseRate_matching_elbow (n d : ℕ) (sigma K : ℝ)
    (hn : 0 < n) (hK : 0 ≤ K) (helbow : MatchingElbow K n d sigma) :
    frontierRate n d sigma ≤ (1 + K) * converseRate n d sigma := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < 1 / (n : ℝ) := by positivity
  have ht : 0 ≤ (d : ℝ) / (n : ℝ) ^ 2 := by positivity
  have hu : 0 ≤ polynomialComponent n d := by
    unfold polynomialComponent
    positivity
  have hs : 0 ≤ sigma ^ 2 := sq_nonneg _
  have hm : 0 ≤ min 1 (polynomialComponent n d) := le_min zero_le_one hu
  have hconv0 : 0 ≤ converseRate n d sigma := by
    unfold converseRate
    positivity
  rcases helbow with hu_one | hu_base | hs_base
  · have hfront : frontierRate n d sigma ≤
        1 / (n : ℝ) + min 1 (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) := by
      unfold frontierRate collisionComponent
      gcongr
      exact min_le_right _ _
    have hconv : 1 / (n : ℝ) +
          min 1 (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) ≤
        converseRate n d sigma := by
      unfold converseRate
      by_cases ht_one : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1
      · rw [min_eq_right ht_one, min_eq_left hu_one]
        nlinarith [min_le_right (1 : ℝ)
          (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2)]
      · rw [min_eq_left (le_of_not_ge ht_one), min_eq_left hu_one]
        nlinarith [min_le_left (1 : ℝ)
          (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2)]
    exact (hfront.trans hconv).trans
      (by nlinarith [hconv0])
  · by_cases ht_one : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1
    · have hfront : frontierRate n d sigma ≤
          1 / (n : ℝ) + polynomialComponent n d := by
        unfold frontierRate
        nlinarith [min_le_right (1 : ℝ)
          (min (polynomialComponent n d) (collisionComponent n d sigma)),
          min_le_left (polynomialComponent n d) (collisionComponent n d sigma)]
      have hbase : baseRate n d ≤ converseRate n d sigma := by
        unfold baseRate converseRate
        rw [min_eq_right ht_one]
        nlinarith
      calc
        frontierRate n d sigma ≤ 1 / (n : ℝ) + polynomialComponent n d := hfront
        _ ≤ (1 + K) * baseRate n d := by
          unfold baseRate at hu_base ⊢
          nlinarith [ha.le, ht]
        _ ≤ (1 + K) * converseRate n d sigma := by gcongr
    · have hfront : frontierRate n d sigma ≤ 1 / (n : ℝ) + 1 := by
        unfold frontierRate
        gcongr
        exact min_le_left _ _
      have hconv : 1 / (n : ℝ) + 1 ≤ converseRate n d sigma := by
        unfold converseRate
        rw [min_eq_left (le_of_not_ge ht_one)]
        nlinarith
      exact (hfront.trans hconv).trans
        (by nlinarith [hconv0])
  · by_cases ht_one : (d : ℝ) / (n : ℝ) ^ 2 ≤ 1
    · have hfront : frontierRate n d sigma ≤
          baseRate n d + sigma ^ 2 := by
        unfold frontierRate collisionComponent baseRate
        nlinarith [min_le_right (1 : ℝ)
          (min (polynomialComponent n d)
            (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2)),
          min_le_right (polynomialComponent n d)
            (sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2)]
      have hbase : baseRate n d ≤ converseRate n d sigma := by
        unfold baseRate converseRate
        rw [min_eq_right ht_one]
        nlinarith
      calc
        frontierRate n d sigma ≤ baseRate n d + sigma ^ 2 := hfront
        _ ≤ (1 + K) * baseRate n d := by nlinarith [hs_base]
        _ ≤ (1 + K) * converseRate n d sigma := by gcongr
    · have hfront : frontierRate n d sigma ≤ 1 / (n : ℝ) + 1 := by
        unfold frontierRate
        gcongr
        exact min_le_left _ _
      have hconv : 1 / (n : ℝ) + 1 ≤ converseRate n d sigma := by
        unfold converseRate
        rw [min_eq_left (le_of_not_ge ht_one)]
        nlinarith
      exact (hfront.trans hconv).trans
        (by nlinarith [hconv0])

/-- If [the overlap constant is positive](hyp:hepsilon) and [the overlap constant is below one
  half](hyp:hepsilon_half) and [the radius is bounded away from zero](hyp:hsigmaLower), [the
  two-sided minimax bracket and fixed-radius benchmark comparison give uniform minimax equivalence
  at every radius bounded away from zero](goal). -/
lemma fixed_radius_minimax_equivalence (epsilon sigmaLower : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2)
    (hsigmaLower : 0 < sigmaLower) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma →
        sigmaLower ≤ sigma → sigma ≤ 2 →
        c * M ^ 2 * frontierRate n d sigma ≤
          minimaxRisk n d epsilon M sigma ∧
        minimaxRisk n d epsilon M sigma ≤
          C * M ^ 2 * frontierRate n d sigma := by
  obtain ⟨c0, C0, hc0, _hc0_one, _hC0_one, hc0C0, hall⟩ :=
    two_sided_minimax_bracket_all_d epsilon hepsilon hepsilon_half
  let D := max 1 (sigmaLower ^ (-2 : ℤ))
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨c0 / D, C0, div_pos hc0 hD, ?_, ?_⟩
  · exact (div_le_self hc0.le (le_max_left _ _)).trans hc0C0
  · intro n d M sigma hn hd hM hsigma_nonneg hsigma hsigma_two
    obtain ⟨hlower, hupper⟩ :=
      hall n d M sigma hn hd hM (le_trans (le_of_lt hsigmaLower) hsigma) hsigma_two
    refine ⟨?_, hupper⟩
    have hrate := frontierRate_le_converseRate_fixed_radius n d sigma sigmaLower
      hn hsigmaLower hsigma_nonneg hsigma_two hsigma
    calc
      c0 / D * M ^ 2 * frontierRate n d sigma =
          (c0 / D) * (M ^ 2 * frontierRate n d sigma) := by ring
      _ ≤ (c0 / D) * (M ^ 2 * (D * converseRate n d sigma)) := by
        gcongr
      _ = c0 * M ^ 2 * converseRate n d sigma := by
        field_simp [D, hD.ne']
        <;> ring
      _ ≤ minimaxRisk n d epsilon M sigma := hlower

-- @node: matching_elbow_minimax_equivalence
/-- If [the overlap constant is positive](hyp:hepsilon) and [the overlap constant is below one
  half](hyp:hepsilon_half) and [the polynomial or elbow parameter satisfies its stated
  bound](hyp:hK), [the two-sided minimax bracket and elbow comparison give uniform minimax
  equivalence in each of the three matching regimes](goal). -/
lemma matching_elbow_minimax_equivalence (epsilon K : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2) (hK : 0 ≤ K) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
        MatchingElbow K n d sigma →
        c * M ^ 2 * frontierRate n d sigma ≤
          minimaxRisk n d epsilon M sigma ∧
        minimaxRisk n d epsilon M sigma ≤
          C * M ^ 2 * frontierRate n d sigma := by
  obtain ⟨c0, C0, hc0, _hc0_one, _hC0_one, hc0C0, hall⟩ :=
    two_sided_minimax_bracket_all_d epsilon hepsilon hepsilon_half
  have hD : 0 < 1 + K := by linarith
  refine ⟨c0 / (1 + K), C0, div_pos hc0 hD, ?_, ?_⟩
  · exact (div_le_self hc0.le (by linarith)).trans hc0C0
  · intro n d M sigma hn hd hM hsigma hsigma_two helbow
    obtain ⟨hlower, hupper⟩ :=
      hall n d M sigma hn hd hM hsigma hsigma_two
    refine ⟨?_, hupper⟩
    have hrate := frontierRate_le_converseRate_matching_elbow n d sigma K hn hK helbow
    calc
      c0 / (1 + K) * M ^ 2 * frontierRate n d sigma =
          (c0 / (1 + K)) * (M ^ 2 * frontierRate n d sigma) := by ring
      _ ≤ (c0 / (1 + K)) *
          (M ^ 2 * ((1 + K) * converseRate n d sigma)) := by
        gcongr
      _ = c0 * M ^ 2 * converseRate n d sigma := by
        field_simp [hD.ne']
        <;> ring
      _ ≤ minimaxRisk n d epsilon M sigma := hlower

-- @node: logEN_tendsto_atTop
/-- [The paper's logarithmic scale diverges with the sample size](goal). -/
lemma logEN_tendsto_atTop : Tendsto logEN atTop atTop := by
  have hlognat : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun n : ℕ => 1 + Real.log (n : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop hlognat
  apply hadd.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [logEN, Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]

-- @node: logEN_pow_div_tendsto_zero
/-- [Every fixed natural power of `log(en)` is negligible relative to `n`](goal). -/
lemma logEN_pow_div_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => logEN n ^ k / (n : ℝ)) atTop (nhds 0) := by
  have harg : Tendsto (fun n : ℕ => Real.exp 1 * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (Real.exp_pos 1)
  have hreal : Tendsto (fun x : ℝ => Real.log x ^ k / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
  have hmul := (hreal.comp harg).const_mul (Real.exp 1)
  have heq : (fun n : ℕ => logEN n ^ k / (n : ℝ)) =ᶠ[atTop]
      (fun n => Real.exp 1 *
        ((fun x : ℝ => Real.log x ^ k / x) (Real.exp 1 * (n : ℝ)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [logEN]
    field_simp [Real.exp_ne_zero 1,
      (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  simpa using hmul.congr' heq.symm

-- @node: diagonal_selector_product_formulas
/-- If [the sample is nonempty](hyp:hn), [on the diagonal witness, the selector and product
  benchmarks have the explicit reciprocal-log formulas used in the rate comparison](goal). -/
lemma diagonal_selector_product_formulas (n : ℕ) (hn : 0 < n) :
    selectorBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) =
        1 / (n : ℝ) + 1 / logEN n ^ 2 ∧
    productBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) =
        2 / (n : ℝ) + 1 / logEN n ^ 3 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 1 ≤ logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast hn))
  have hL0 : 0 < logEN n := zero_lt_one.trans_le hL
  have hbase : baseRate n n = 2 / (n : ℝ) := by
    unfold baseRate
    field_simp [hnR.ne']
    ring
  have hpoly : polynomialComponent n n = 1 / logEN n ^ 2 := by
    unfold polynomialComponent
    field_simp [hnR.ne']
  have hsigma : ((logEN n) ^ (-1 / 2 : ℝ)) ^ 2 = (logEN n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
    exact Real.rpow_neg_one _
  have hinv : 1 / logEN n ^ 2 ≤ (logEN n)⁻¹ := by
    rw [div_le_iff₀ (sq_pos_of_pos hL0)]
    field_simp [hL0.ne']
    nlinarith
  have hmin : 1 / logEN n ^ 2 ≤
      (logEN n)⁻¹ + (n : ℝ) / (n : ℝ) ^ 2 :=
    hinv.trans (le_add_of_nonneg_right (by positivity))
  constructor
  · rw [selectorBenchmark, hpoly, hsigma, min_eq_left hmin]
  · rw [productBenchmark, hbase, hpoly, hsigma]
    field_simp [hL0.ne']

-- @node: diagonal_residual_wedge
/-- [The diagonal sequence `d=n`, `sigma=log(en)^(-1/2)` lies in the residual wedge](goal). -/
lemma diagonal_residual_wedge : ResidualWedge (fun n => n)
    (fun n => (logEN n) ^ (-1 / 2 : ℝ)) := by
  have hLinv : Tendsto (fun n => (logEN n)⁻¹) atTop (nhds 0) :=
    logEN_tendsto_atTop.inv_tendsto_atTop
  have hLinvSq : Tendsto (fun n => (logEN n ^ 2)⁻¹) atTop (nhds 0) := by
    have h := hLinv.pow 2
    have heq : (fun n => (logEN n)⁻¹ ^ 2) =
        (fun n => (logEN n ^ 2)⁻¹) := by
      funext n
      rw [← inv_pow]
    convert h.congr' (Filter.Eventually.of_forall fun n => congrFun heq n) using 1 <;>
      norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hL1 : 1 ≤ logEN n := by
      have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
      rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
      exact le_add_of_nonneg_right (Real.log_nonneg hnR)
    have hs0 : 0 ≤ (logEN n) ^ (-1 / 2 : ℝ) :=
      Real.rpow_nonneg (zero_le_one.trans hL1) _
    have hpow : (logEN n) ^ (-1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
    exact ⟨hn, hs0, hpow.trans (by norm_num)⟩
  · have h := (logEN_pow_div_tendsto_zero 2).const_mul 2
    have heq : (fun n : ℕ => 2 * (logEN n ^ 2 / (n : ℝ))) =ᶠ[atTop]
        (fun n => baseRate n n / polynomialComponent n n) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      unfold baseRate polynomialComponent
      field_simp [hnR]
      ring
    convert h.congr' heq using 1 <;> norm_num
  · apply hLinvSq.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold polynomialComponent
    field_simp [hnR]
  · have h := (logEN_pow_div_tendsto_zero 1).const_mul 2
    have heq : (fun n : ℕ => 2 * (logEN n ^ 1 / (n : ℝ))) =ᶠ[atTop]
        (fun n => baseRate n n / ((logEN n) ^ (-1 / 2 : ℝ)) ^ 2) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hnRone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hL0 : 0 < logEN n := by
        rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
        linarith [Real.log_nonneg hnRone]
      have hsigma : ((logEN n) ^ (-1 / 2 : ℝ)) ^ 2 = (logEN n)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        norm_num
        exact Real.rpow_neg_one _
      rw [hsigma]
      unfold baseRate
      field_simp [hnR.ne', hL0.ne']
      ring
    convert h.congr' heq using 1 <;> norm_num
  · apply hLinv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hL0 : 0 < logEN n := by
      have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hnR
      rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
      linarith [Real.log_nonneg hnR]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
    exact (Real.rpow_neg_one _).symm

-- @node: diagonal_benchmark_eventually_same_order
/-- [The diagonal selector/product ratio is eventually between one third and twice the logarithmic
  scale](goal). -/
lemma diagonal_benchmark_eventually_same_order : EventuallySameOrder
      (fun n => selectorBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) /
        productBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ))) logEN := by
  refine ⟨1 / 3, 2, by norm_num, by norm_num, ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, logEN n ^ 3 / (n : ℝ) < 1 :=
    (logEN_pow_div_tendsto_zero 3).eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall] with n hn hsmalln
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnRone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 1 ≤ logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    exact le_add_of_nonneg_right (Real.log_nonneg hnRone)
  rw [(diagonal_selector_product_formulas n hn).1,
    (diagonal_selector_product_formulas n hn).2]
  have hL0 : 0 < logEN n := zero_lt_one.trans_le hL
  have hden : 0 < 2 / (n : ℝ) + 1 / logEN n ^ 3 := by positivity
  constructor
  · rw [le_div_iff₀ hden]
    field_simp [hnR.ne', hL0.ne'] at hsmalln ⊢
    nlinarith
  · rw [div_le_iff₀ hden]
    field_simp [hnR.ne', hL0.ne'] at hsmalln ⊢
    nlinarith [sq_nonneg (logEN n - 1)]

-- @node: diagonal_benchmark_ratio_tendsto_atTop
/-- [The diagonal selector/product benchmark ratio diverges](goal). -/
lemma diagonal_benchmark_ratio_tendsto_atTop : Tendsto (fun n =>
      selectorBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) /
        productBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ))) atTop atTop := by
  obtain ⟨c, _C, hc, _hcC, hlower⟩ := diagonal_benchmark_eventually_same_order
  exact tendsto_atTop_mono' atTop (hlower.mono fun n hn => hn.1)
    (logEN_tendsto_atTop.const_mul_atTop hc)

-- @node: benchmark_divergence_eventually_avoids_elbows
/-- If [the sequence is eventually in the admissible parameter range](hyp:hvalid) and [the
  benchmark ratio diverges](hyp:hdiv) and [the polynomial or elbow parameter satisfies its stated
  bound](hyp:hK), [a diverging benchmark ratio eventually leaves every fixed matching
  elbow](goal). -/
lemma benchmark_divergence_eventually_avoids_elbows
    (dseq : ℕ → ℕ) (sseq : ℕ → ℝ)
    (hvalid : ∀ᶠ t in atTop, 1 ≤ dseq t ∧ 0 ≤ sseq t ∧ sseq t ≤ 2)
    (hdiv : BenchmarkRatioDiverges dseq sseq) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ t in atTop, ¬ MatchingElbow K t (dseq t) (sseq t) := by
  have hlarge : ∀ᶠ t in atTop,
      1 + K < frontierRate t (dseq t) (sseq t) /
        converseRate t (dseq t) (sseq t) :=
    hdiv (eventually_gt_atTop (1 + K))
  filter_upwards [hvalid, eventually_gt_atTop (0 : ℕ), hlarge] with n hv hn hlarge_n
  intro helbow
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu : 0 ≤ polynomialComponent n (dseq n) := by
    unfold polynomialComponent
    positivity
  have hconv : 0 < converseRate n (dseq n) (sseq n) := by
    unfold converseRate
    have ha : 0 < 1 / (n : ℝ) := by positivity
    have hdterm : 0 ≤ min 1 ((dseq n : ℝ) / (n : ℝ) ^ 2) := by positivity
    have huterm : 0 ≤ min 1 (polynomialComponent n (dseq n)) :=
      le_min zero_le_one hu
    nlinarith [sq_nonneg (sseq n), mul_nonneg (sq_nonneg (sseq n)) huterm]
  have hrate := frontierRate_le_converseRate_matching_elbow
    n (dseq n) (sseq n) K hn hK helbow
  have hratio : frontierRate n (dseq n) (sseq n) /
      converseRate n (dseq n) (sseq n) ≤ 1 + K := by
    rw [div_le_iff₀ hconv]
    exact hrate
  linarith

set_option maxHeartbeats 800000 in
-- @node: benchmark_divergence_implies_residual_wedge
/-- If [the sequence is eventually in the admissible parameter range](hyp:hvalid) and [the
  benchmark ratio diverges](hyp:hdiv), [divergence of the all-alphabet benchmark ratio forces all
  four defining limits of the residual shrinking-radius wedge](goal). -/
lemma benchmark_divergence_implies_residual_wedge
    (dseq : ℕ → ℕ) (sseq : ℕ → ℝ)
    (hvalid : ∀ᶠ t in atTop, 1 ≤ dseq t ∧ 0 ≤ sseq t ∧ sseq t ≤ 2)
    (hdiv : BenchmarkRatioDiverges dseq sseq) : ResidualWedge dseq sseq := by
  have hbu : Tendsto (fun n => baseRate n (dseq n) /
      polynomialComponent n (dseq n)) atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [hvalid, eventually_gt_atTop (0 : ℕ)] with n hv hn
      have hu : 0 < polynomialComponent n (dseq n) := by
        unfold polynomialComponent
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
        have hdR : 0 < (dseq n : ℝ) := by exact_mod_cast hv.1
        have hL : 0 < logEN n := by
          rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
          have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith [Real.log_nonneg hnOne]
        positivity
      have hb : 0 ≤ baseRate n (dseq n) := by unfold baseRate; positivity
      exact ha.trans_le (div_nonneg hb hu.le)
    · intro a ha
      let K := a⁻¹
      have hK : 0 ≤ K := inv_nonneg.mpr ha.le
      have havoid := benchmark_divergence_eventually_avoids_elbows
        dseq sseq hvalid hdiv K hK
      filter_upwards [hvalid, eventually_gt_atTop (0 : ℕ), havoid] with n hv hn hne
      have hu : 0 < polynomialComponent n (dseq n) := by
        unfold polynomialComponent
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
        have hdR : 0 < (dseq n : ℝ) := by exact_mod_cast hv.1
        have hL : 0 < logEN n := by
          rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
          have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith [Real.log_nonneg hnOne]
        positivity
      have hnot : ¬ polynomialComponent n (dseq n) ≤
          K * baseRate n (dseq n) := fun h => hne (Or.inr (Or.inl h))
      rw [div_lt_iff₀ hu]
      dsimp [K] at hnot
      have := lt_of_not_ge hnot
      field_simp [ha.ne'] at this ⊢
      nlinarith
  have hbs : Tendsto (fun n => baseRate n (dseq n) / (sseq n) ^ 2)
      atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [hvalid] with n hv
      exact ha.trans_le (div_nonneg (by unfold baseRate; positivity) (sq_nonneg _))
    · intro a ha
      let K := a⁻¹
      have hK : 0 ≤ K := inv_nonneg.mpr ha.le
      have havoid := benchmark_divergence_eventually_avoids_elbows
        dseq sseq hvalid hdiv K hK
      filter_upwards [hvalid, havoid] with n hv hne
      have hspos : 0 < (sseq n) ^ 2 := by
        have hnot : ¬ (sseq n) ^ 2 ≤ K * baseRate n (dseq n) :=
          fun h => hne (Or.inr (Or.inr h))
        have hb : 0 ≤ baseRate n (dseq n) := by unfold baseRate; positivity
        nlinarith [mul_nonneg hK hb]
      have hnot : ¬ (sseq n) ^ 2 ≤ K * baseRate n (dseq n) :=
        fun h => hne (Or.inr (Or.inr h))
      rw [div_lt_iff₀ hspos]
      dsimp [K] at hnot
      have := lt_of_not_ge hnot
      field_simp [ha.ne'] at this ⊢
      nlinarith
  have hs0 : Tendsto (fun n => (sseq n) ^ 2) atTop (nhds 0) := by
    refine tendsto_order.2 ⟨fun a ha => ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun n => ha.trans_le (sq_nonneg _)
    · intro a ha
      let r := Real.sqrt a
      have hr : 0 < r := Real.sqrt_pos.2 ha
      let D := max 1 (r ^ (-2 : ℤ))
      have hlarge : ∀ᶠ n in atTop, D < frontierRate n (dseq n) (sseq n) /
          converseRate n (dseq n) (sseq n) := hdiv (eventually_gt_atTop D)
      filter_upwards [hvalid, eventually_gt_atTop (0 : ℕ), hlarge] with n hv hn hlarge_n
      by_contra hnot
      have hrs : r ≤ sseq n := by
        have hsnonneg := hv.2.1
        nlinarith [Real.sq_sqrt ha.le]
      have hrate := frontierRate_le_converseRate_fixed_radius
        n (dseq n) (sseq n) r hn hr hv.2.1 hv.2.2 hrs
      have hconv : 0 < converseRate n (dseq n) (sseq n) := by
        unfold converseRate
        have ha_n : 0 < 1 / (n : ℝ) := by positivity
        have hu : 0 ≤ polynomialComponent n (dseq n) := by
          unfold polynomialComponent
          positivity
        have hm : 0 ≤ min 1 (polynomialComponent n (dseq n)) :=
          le_min zero_le_one hu
        have hdterm : 0 ≤ min 1 ((dseq n : ℝ) / (n : ℝ) ^ 2) := by positivity
        nlinarith [mul_nonneg (sq_nonneg (sseq n)) hm]
      have hratio : frontierRate n (dseq n) (sseq n) /
          converseRate n (dseq n) (sseq n) ≤ D := by
        rw [div_le_iff₀ hconv]
        exact hrate
      linarith
  have hu0 : Tendsto (fun n => polynomialComponent n (dseq n))
      atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact Filter.Eventually.of_forall fun n => ha.trans_le (by
        unfold polynomialComponent
        positivity)
    · intro a ha
      have havoid0 := benchmark_divergence_eventually_avoids_elbows
        dseq sseq hvalid hdiv 0 (le_refl 0)
      by_cases ha1 : 1 ≤ a
      · filter_upwards [havoid0] with n hne
        exact (lt_of_not_ge fun h => hne (Or.inl h)).trans_le ha1
      · have ha_lt_one : a < 1 := lt_of_not_ge ha1
        have hbu_half : ∀ᶠ n in atTop,
            baseRate n (dseq n) / polynomialComponent n (dseq n) < 1 / 2 :=
          hbu.eventually (Iio_mem_nhds (by norm_num))
        have hs_half : ∀ᶠ n in atTop, (sseq n) ^ 2 < a / 2 :=
          hs0.eventually (Iio_mem_nhds (by linarith))
        have hlarge : ∀ᶠ n in atTop, a⁻¹ <
            frontierRate n (dseq n) (sseq n) /
              converseRate n (dseq n) (sseq n) :=
          hdiv (eventually_gt_atTop a⁻¹)
        filter_upwards [hvalid, eventually_gt_atTop (0 : ℕ), havoid0,
          hbu_half, hs_half, hlarge] with n hv hn hne hbu_n hs_n hlarge_n
        by_contra hua
        have hu_ge : a ≤ polynomialComponent n (dseq n) := le_of_not_gt hua
        have hu_lt : polynomialComponent n (dseq n) < 1 :=
          lt_of_not_ge fun h => hne (Or.inl h)
        have hu_pos : 0 < polynomialComponent n (dseq n) := ha.trans_le hu_ge
        have hb_lt : baseRate n (dseq n) < polynomialComponent n (dseq n) / 2 := by
          rw [div_lt_iff₀ hu_pos] at hbu_n
          nlinarith
        have ht_lt : (dseq n : ℝ) / (n : ℝ) ^ 2 <
            polynomialComponent n (dseq n) / 2 :=
          (show (dseq n : ℝ) / (n : ℝ) ^ 2 ≤ baseRate n (dseq n) by
            unfold baseRate
            linarith [show 0 ≤ 1 / (n : ℝ) by positivity]).trans_lt hb_lt
        have hs_lt : (sseq n) ^ 2 < polynomialComponent n (dseq n) / 2 :=
          hs_n.trans_le (div_le_div_of_nonneg_right hu_ge (by norm_num))
        have hsum : (sseq n) ^ 2 + (dseq n : ℝ) / (n : ℝ) ^ 2 <
            polynomialComponent n (dseq n) := by linarith
        have ht_one : (dseq n : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by linarith
        have hconv : 0 < converseRate n (dseq n) (sseq n) := by
          unfold converseRate
          positivity
        have hform_front : frontierRate n (dseq n) (sseq n) =
            baseRate n (dseq n) + (sseq n) ^ 2 := by
          unfold frontierRate collisionComponent baseRate
          rw [min_eq_right hsum.le, min_eq_right (by linarith)]
          ring
        have hform_conv : converseRate n (dseq n) (sseq n) =
            baseRate n (dseq n) + (sseq n) ^ 2 *
              polynomialComponent n (dseq n) := by
          unfold converseRate baseRate
          rw [min_eq_right ht_one, min_eq_right hu_lt.le]
        have hb0 : 0 ≤ baseRate n (dseq n) := by unfold baseRate; positivity
        have hsnonneg : 0 ≤ (sseq n) ^ 2 := sq_nonneg _
        have hrate : frontierRate n (dseq n) (sseq n) /
            converseRate n (dseq n) (sseq n) ≤ a⁻¹ := by
          have hden : 0 < baseRate n (dseq n) + (sseq n) ^ 2 *
              polynomialComponent n (dseq n) := hform_conv ▸ hconv
          rw [hform_front, hform_conv, div_le_iff₀ hden]
          field_simp [ha.ne']
          nlinarith [mul_le_mul_of_nonneg_left hu_ge hsnonneg]
        linarith
  exact ⟨hvalid, hbu, hu0, hbs, hs0⟩
-- @node: thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d
/-- [The benchmarks match at every fixed positive radius and in each stated elbow regime; any
  divergence is confined to the residual wedge, which is nonempty](goal). -/
theorem fixed_interior_tightness_and_shrinking_radius_gap_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    (∀ n d : ℕ, ∀ sigma : ℝ,
      0 ≤ sigma → sigma ≤ 2 →
      logEN n ^ 2 < d → (d : ℝ) < n * logEN n →
      (1 / 2 : ℝ) *
          (baseRate n d + min (polynomialComponent n d) (sigma ^ 2)) ≤
        selectorBenchmark n d sigma ∧
      selectorBenchmark n d sigma ≤
        baseRate n d + min (polynomialComponent n d) (sigma ^ 2) ∧
      productBenchmark n d sigma =
        baseRate n d + sigma ^ 2 * polynomialComponent n d) ∧
    (∀ sigmaLower : ℝ, 0 < sigmaLower → sigmaLower ≤ 2 →
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ n d : ℕ, ∀ M sigma : ℝ,
          0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma →
          sigmaLower ≤ sigma → sigma ≤ 2 →
          c * M ^ 2 * frontierRate n d sigma ≤
            minimaxRisk n d epsilon M sigma ∧
          minimaxRisk n d epsilon M sigma ≤
            C * M ^ 2 * frontierRate n d sigma) ∧
    (∀ K : ℝ, 0 ≤ K →
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ n d : ℕ, ∀ M sigma : ℝ,
          0 < n → 0 < d → 1 ≤ M → 0 ≤ sigma → sigma ≤ 2 →
          MatchingElbow K n d sigma →
          c * M ^ 2 * frontierRate n d sigma ≤
            minimaxRisk n d epsilon M sigma ∧
          minimaxRisk n d epsilon M sigma ≤
            C * M ^ 2 * frontierRate n d sigma) ∧
    (∀ n d : ℕ, 0 < n →
      (polynomialComponent n d ≤ baseRate n d ↔
        (d : ℝ) ^ 2 ≤ n * logEN n ^ 2 + d * logEN n ^ 2)) ∧
    (∀ n d : ℕ, 0 < n →
      (d : ℝ) ≤ Real.sqrt n * logEN n →
      polynomialComponent n d ≤ baseRate n d) ∧
    (∀ n d : ℕ, 0 < n →
      (d : ℝ) ≤ logEN n ^ 2 →
      polynomialComponent n d ≤ baseRate n d) ∧
    (∀ dseq : ℕ → ℕ, ∀ sseq : ℕ → ℝ,
      (∀ᶠ t in atTop, 1 ≤ dseq t ∧ 0 ≤ sseq t ∧ sseq t ≤ 2) →
      BenchmarkRatioDiverges dseq sseq → ResidualWedge dseq sseq) ∧
    ResidualWedge (fun n => n) (fun n => (logEN n) ^ (-1 / 2 : ℝ)) ∧
    EventuallySameOrder
      (fun n => selectorBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) /
        productBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)))
      logEN ∧
    Tendsto (fun n =>
      selectorBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) /
        productBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ))) atTop atTop := by
  intro epsilon hepsilon hepsilon_half
  refine ⟨?_,
    (fun sigmaLower hsigmaLower _ =>
      fixed_radius_minimax_equivalence epsilon sigmaLower hepsilon hepsilon_half
        hsigmaLower),
    (fun K hK =>
      matching_elbow_minimax_equivalence epsilon K hepsilon hepsilon_half hK),
    (fun n d hn => polynomialComponent_le_baseRate_iff n d hn),
    (fun n d hn hd => polynomialComponent_le_baseRate_of_le_sqrt n d hn hd),
    (fun n d hn hd => polynomialComponent_le_baseRate_of_le_log_sq n d hn hd), ?_,
    diagonal_residual_wedge, diagonal_benchmark_eventually_same_order,
    diagonal_benchmark_ratio_tendsto_atTop⟩
  · intro n d sigma hsigma hsigma_two hlower hupper
    obtain ⟨hlo, hup⟩ := selectorBenchmark_triangular n d sigma
      hsigma hsigma_two hlower hupper
    exact ⟨hlo, hup, rfl⟩
  · intro dseq sseq hvalid hdiv
    exact benchmark_divergence_implies_residual_wedge dseq sseq hvalid hdiv

-- @node: thm:fixed-interior-tightness-and-shrinking-radius-gap
/-- [Restricted-range specialization of the fixed-interior and shrinking-radius phase
  theorem](goal). -/
theorem fixed_interior_tightness_and_shrinking_radius_gap :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ c_epsilon : ℝ, 0 < c_epsilon ∧
      (∀ n d : ℕ, ∀ sigma : ℝ,
        0 ≤ sigma → sigma ≤ 2 →
        logEN n ^ 2 < d → (d : ℝ) < n * logEN n →
        (1 / 2 : ℝ) *
            (baseRate n d + min (polynomialComponent n d) (sigma ^ 2)) ≤
          selectorBenchmark n d sigma ∧
        selectorBenchmark n d sigma ≤
          baseRate n d + min (polynomialComponent n d) (sigma ^ 2) ∧
        productBenchmark n d sigma =
          baseRate n d + sigma ^ 2 * polynomialComponent n d) ∧
      (∀ sigmaLower : ℝ, 0 < sigmaLower → sigmaLower ≤ 2 →
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          ∀ n d : ℕ, ∀ M sigma : ℝ,
            0 < n → 0 < d → 1 ≤ M → -- @realizes M(range [1,infinity))
            0 ≤ sigma → sigmaLower ≤ sigma → sigma ≤ 2 →
            (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
            c * M ^ 2 * frontierRate n d sigma ≤
              minimaxRisk n d epsilon M sigma ∧
            minimaxRisk n d epsilon M sigma ≤
              C * M ^ 2 * frontierRate n d sigma) ∧
      (∀ K : ℝ, 0 ≤ K →
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          ∀ n d : ℕ, ∀ M sigma : ℝ,
            0 < n → 0 < d → 1 ≤ M → -- @realizes M(range [1,infinity))
            0 ≤ sigma → sigma ≤ 2 →
            MatchingElbow K n d sigma →
            c * M ^ 2 * frontierRate n d sigma ≤
              minimaxRisk n d epsilon M sigma ∧
            minimaxRisk n d epsilon M sigma ≤
              C * M ^ 2 * frontierRate n d sigma) ∧
      (∀ n d : ℕ, 0 < n →
        (polynomialComponent n d ≤ baseRate n d ↔
          (d : ℝ) ^ 2 ≤ n * logEN n ^ 2 + d * logEN n ^ 2)) ∧
      (∀ dseq : ℕ → ℕ, ∀ sseq : ℕ → ℝ,
        (∀ᶠ t in atTop, 1 ≤ dseq t ∧ 0 ≤ sseq t ∧ sseq t ≤ 2) →
        BenchmarkRatioDiverges dseq sseq → ResidualWedge dseq sseq) ∧
      ResidualWedge (fun n => n) (fun n => (logEN n) ^ (-1 / 2 : ℝ)) ∧
      EventuallySameOrder
        (fun n => selectorBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) /
          productBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)))
        logEN ∧
      Tendsto (fun n =>
        selectorBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ)) /
          productBenchmark n n ((logEN n) ^ (-1 / 2 : ℝ))) atTop atTop := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨htriangular, hfixed, helbows, hexact_algebra, _hsqrt, _hsmall,
      hwedge, hwitness, hsame_order, hdiverges⟩ :=
    fixed_interior_tightness_and_shrinking_radius_gap_all_d
      epsilon hepsilon hepsilon_half
  refine ⟨1, zero_lt_one, ?_⟩
  exact ⟨htriangular, fun sigmaLower hsigmaLower hsigmaLower_two => by
      obtain ⟨c, C, hc, hcC, hall⟩ :=
        hfixed sigmaLower hsigmaLower hsigmaLower_two
      exact ⟨c, C, hc, hcC,
        fun n d M sigma hn hd hM hsigma_nonneg hsigma hsigma_two _ =>
          hall n d M sigma hn hd hM hsigma_nonneg hsigma hsigma_two⟩,
    fun K hK => by
      obtain ⟨c, C, hc, hcC, hall⟩ := helbows K hK
      exact ⟨c, C, hc, hcC, fun n d M sigma hn hd hM hsigma hsigma_two helbow =>
        hall n d M sigma hn hd hM hsigma hsigma_two helbow⟩,
    hexact_algebra, hwedge, hwitness, hsame_order, hdiverges⟩

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
