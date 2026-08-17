import Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Algebraic closure interfaces for polynomial `L²` entropy

This module packages uniform polynomial covering as a reusable certificate and
states its finite sum and finite product closures.  Parametric and indicator
constructions are developed in `Parametric`.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory
open Causalean.Stat.Concentration
open scoped BigOperators

universe u v w

variable {𝒳 : Type u} [MeasurableSpace 𝒳]

private lemma measureL2Dist_eq_lpNorm (Q : Measure 𝒳) (f g : 𝒳 → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    measureL2Dist Q f g = lpNorm (fun x => f x - g x) (2 : ENNReal) Q := by
  have h := lpNorm_nnreal_eq_integral_norm_rpow (μ := Q) (f := fun x => f x - g x)
    (p := (2 : NNReal)) (by norm_num) (hf.sub hg).aestronglyMeasurable
  have h' : lpNorm (fun x => f x - g x) (2 : ENNReal) Q =
      (∫ x, ‖f x - g x‖ ^ (2 : ℝ) ∂Q) ^ ((2 : ℝ)⁻¹) := by
    simpa using h
  rw [measureL2Dist, h']
  norm_num [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]

private lemma measureL2Dist_add_le [IsFiniteMeasure Q]
    (f₁ f₂ g₁ g₂ : 𝒳 → ℝ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    {U : ℝ} (hf_bound : ∀ x, |f₁ x| ≤ U) (hf₂_bound : ∀ x, |f₂ x| ≤ U) :
    measureL2Dist Q (fun x => f₁ x + g₁ x) (fun x => f₂ x + g₂ x) ≤
      measureL2Dist Q f₁ f₂ + measureL2Dist Q g₁ g₂ := by
  let f : 𝒳 → ℝ := fun x => f₁ x - f₂ x
  let g : 𝒳 → ℝ := fun x => g₁ x - g₂ x
  have hf_meas : Measurable f := hf₁.sub hf₂
  have hg_meas : Measurable g := hg₁.sub hg₂
  have hf_mem : MemLp f (2 : ENNReal) Q :=
    MemLp.of_bound hf_meas.aestronglyMeasurable (2 * U) <| Filter.Eventually.of_forall fun x => by
      dsimp [f]
      exact (abs_sub _ _).trans (by nlinarith [hf_bound x, hf₂_bound x])
  have hadd := lpNorm_add_le hf_mem (p := (2 : ENNReal)) (by norm_num) (g := g)
  rw [measureL2Dist_eq_lpNorm Q _ _ (hf₁.fun_add hg₁) (hf₂.fun_add hg₂),
    measureL2Dist_eq_lpNorm Q _ _ hf₁ hf₂,
    measureL2Dist_eq_lpNorm Q _ _ hg₁ hg₂]
  have hfun : (fun x => (f₁ x + g₁ x) - (f₂ x + g₂ x)) = f + g := by
    funext x
    dsimp [f, g]
    ring
  rw [hfun]
  exact hadd

private lemma lpNorm_mul_le_of_bound_left {Q : Measure 𝒳} [IsFiniteMeasure Q]
    (a b : 𝒳 → ℝ)
    (ha : Measurable a) (hb : Measurable b) {U M : ℝ}
    (hU : 0 ≤ U) (haU : ∀ x, |a x| ≤ U) (hbM : ∀ x, |b x| ≤ M) :
    lpNorm (fun x => a x * b x) (2 : ENNReal) Q ≤
      U * lpNorm b (2 : ENNReal) Q := by
  have hb_mem : MemLp b (2 : ENNReal) Q :=
    MemLp.of_bound (μ := Q) hb.aestronglyMeasurable M <| Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hbM x
  have hab_mem : MemLp (fun x => a x * b x) (2 : ENNReal) Q :=
    MemLp.of_bound (μ := Q) (ha.mul hb).aestronglyMeasurable (U * M) <|
      Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (haU x) (hbM x) (abs_nonneg _) hU
  have hUb_mem : MemLp (fun x => U * b x) (2 : ENNReal) Q := hb_mem.const_mul U
  have henorm : eLpNorm (fun x => a x * b x) (2 : ENNReal) Q ≤
      eLpNorm (fun x => U * b x) (2 : ENNReal) Q :=
    eLpNorm_mono_ae <| Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hU]
      exact mul_le_mul_of_nonneg_right (haU x) (abs_nonneg _)
  have hreal :=
    (ENNReal.toReal_le_toReal hab_mem.eLpNorm_ne_top hUb_mem.eLpNorm_ne_top).2 henorm
  rw [toReal_eLpNorm (ha.fun_mul hb).aestronglyMeasurable,
    toReal_eLpNorm (measurable_const.fun_mul hb).aestronglyMeasurable] at hreal
  have hfun : (fun x => U * b x) = U • b := by rfl
  rw [hfun, lpNorm_const_smul] at hreal
  simpa [Real.norm_eq_abs, abs_of_nonneg hU] using hreal

private lemma measureL2Dist_mul_le {Q : Measure 𝒳} [IsFiniteMeasure Q]
    (f₁ f₂ g₁ g₂ : 𝒳 → ℝ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hf₁_bound : ∀ x, |f₁ x| ≤ U) (hf₂_bound : ∀ x, |f₂ x| ≤ U)
    (hg₁_bound : ∀ x, |g₁ x| ≤ V) (hg₂_bound : ∀ x, |g₂ x| ≤ V) :
    measureL2Dist Q (fun x => f₁ x * g₁ x) (fun x => f₂ x * g₂ x) ≤
      V * measureL2Dist Q f₁ f₂ + U * measureL2Dist Q g₁ g₂ := by
  let df : 𝒳 → ℝ := fun x => f₁ x - f₂ x
  let dg : 𝒳 → ℝ := fun x => g₁ x - g₂ x
  let a : 𝒳 → ℝ := fun x => g₁ x * df x
  let b : 𝒳 → ℝ := fun x => f₂ x * dg x
  have hdf : Measurable df := hf₁.sub hf₂
  have hdg : Measurable dg := hg₁.sub hg₂
  have ha : Measurable a := hg₁.mul hdf
  have hb : Measurable b := hf₂.mul hdg
  have ha_mem : MemLp a (2 : ENNReal) Q :=
    MemLp.of_bound (μ := Q) ha.aestronglyMeasurable (V * (2 * U)) <|
      Filter.Eventually.of_forall fun x => by
        dsimp [a, df]
        rw [abs_mul]
        exact mul_le_mul (hg₁_bound x)
          ((abs_sub (f₁ x) (f₂ x)).trans (by nlinarith [hf₁_bound x, hf₂_bound x]))
          (abs_nonneg _) hV
  have htri := lpNorm_add_le ha_mem (p := (2 : ENNReal)) (by norm_num) (g := b)
  have ha_le : lpNorm a (2 : ENNReal) Q ≤ V * lpNorm df (2 : ENNReal) Q :=
    lpNorm_mul_le_of_bound_left (M := 2 * U) g₁ df hg₁ hdf hV hg₁_bound (fun x =>
      (abs_sub (f₁ x) (f₂ x)).trans (by nlinarith [hf₁_bound x, hf₂_bound x]))
  have hb_le : lpNorm b (2 : ENNReal) Q ≤ U * lpNorm dg (2 : ENNReal) Q :=
    lpNorm_mul_le_of_bound_left (M := 2 * V) f₂ dg hf₂ hdg hU hf₂_bound (fun x =>
      (abs_sub (g₁ x) (g₂ x)).trans (by nlinarith [hg₁_bound x, hg₂_bound x]))
  rw [measureL2Dist_eq_lpNorm Q _ _ (hf₁.fun_mul hg₁) (hf₂.fun_mul hg₂),
    measureL2Dist_eq_lpNorm Q _ _ hf₁ hf₂,
    measureL2Dist_eq_lpNorm Q _ _ hg₁ hg₂]
  have hfun : (fun x => f₁ x * g₁ x - f₂ x * g₂ x) = a + b := by
    funext x
    dsimp [a, b, df, dg]
    ring
  rw [hfun]
  exact htri.trans (add_le_add ha_le hb_le)

private lemma ceil_mul_le_ceil_poly {A B ε : ℝ} {p q : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Nat.ceil ((2 * A / ε) ^ p) * Nat.ceil ((2 * B / ε) ^ q) ≤
      Nat.ceil (((8 * A * B) / ε) ^ (p + q + 2)) := by
  have hx : 1 ≤ (2 * A / ε) ^ p :=
    one_le_pow₀ ((one_le_div hε).2 (by nlinarith))
  have hy : 1 ≤ (2 * B / ε) ^ q :=
    one_le_pow₀ ((one_le_div hε).2 (by nlinarith))
  have hcx : (Nat.ceil ((2 * A / ε) ^ p) : ℝ) < (2 * A / ε) ^ p + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hcy : (Nat.ceil ((2 * B / ε) ^ q) : ℝ) < (2 * B / ε) ^ q + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceilx : (Nat.ceil ((2 * A / ε) ^ p) : ℝ) ≤ 2 * (2 * A / ε) ^ p := by
    nlinarith
  have hceily : (Nat.ceil ((2 * B / ε) ^ q) : ℝ) ≤ 2 * (2 * B / ε) ^ q := by
    nlinarith
  have hbaseA : 2 * A / ε ≤ 8 * A * B / ε := by
    apply (div_le_div_iff₀ hε hε).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hbaseB : 2 * B / ε ≤ 8 * A * B / ε := by
    apply (div_le_div_iff₀ hε hε).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hz2 : 2 ≤ 8 * A * B / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hreal :
      ((Nat.ceil ((2 * A / ε) ^ p) * Nat.ceil ((2 * B / ε) ^ q) : ℕ) : ℝ) ≤
        ((8 * A * B) / ε) ^ (p + q + 2) := by
    push_cast
    have hpa : (2 * A / ε) ^ p ≤ (8 * A * B / ε) ^ p :=
      pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 * A / ε by positivity) hbaseA p
    have hpb : (2 * B / ε) ^ q ≤ (8 * A * B / ε) ^ q :=
      pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 * B / ε by positivity) hbaseB q
    have hmul : (2 * A / ε) ^ p * (2 * B / ε) ^ q ≤
        (8 * A * B / ε) ^ p * (8 * A * B / ε) ^ q := by
      calc
        (2 * A / ε) ^ p * (2 * B / ε) ^ q ≤
            (8 * A * B / ε) ^ p * (2 * B / ε) ^ q :=
          mul_le_mul_of_nonneg_right hpa (by positivity)
        _ ≤ (8 * A * B / ε) ^ p * (8 * A * B / ε) ^ q :=
          mul_le_mul_of_nonneg_left hpb (by positivity)
    calc
      (Nat.ceil ((2 * A / ε) ^ p) : ℝ) * Nat.ceil ((2 * B / ε) ^ q) ≤
          (2 * (2 * A / ε) ^ p) * (Nat.ceil ((2 * B / ε) ^ q) : ℝ) :=
        mul_le_mul_of_nonneg_right hceilx (Nat.cast_nonneg _)
      _ ≤ (2 * (2 * A / ε) ^ p) * (2 * (2 * B / ε) ^ q) :=
        mul_le_mul_of_nonneg_left hceily (by positivity)
      _ = 4 * ((2 * A / ε) ^ p * (2 * B / ε) ^ q) := by ring
      _ ≤ 4 * ((8 * A * B / ε) ^ p * (8 * A * B / ε) ^ q) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 4 * (8 * A * B / ε) ^ (p + q) := by rw [pow_add]
      _ ≤ (8 * A * B / ε) ^ (p + q) * (8 * A * B / ε) ^ 2 := by
        have hzpow : 0 ≤ (8 * A * B / ε) ^ (p + q) := by positivity
        have hzsq : 4 ≤ (8 * A * B / ε) ^ 2 := by
          nlinarith [sq_nonneg (8 * A * B / ε - 2)]
        nlinarith
      _ = ((8 * A * B) / ε) ^ (p + q + 2) := by
        rw [pow_add]
        ring
  have hfinal := hreal.trans (Nat.le_ceil (((8 * A * B) / ε) ^ (p + q + 2)))
  exact_mod_cast hfinal

/-- A class has uniform polynomial `L²` entropy with envelope `U` when it is
measurable, pointwise bounded by `U`, and admits one polynomial cover bound for
every probability measure and every relative radius in `(0,1]`. -/
structure HasPolynomialL2Cover {ι : Type v} (F : ι → 𝒳 → ℝ) (U : ℝ) : Prop where
  envelope_pos : 0 < U
  measurable : ∀ i, Measurable (F i)
  envelope : ∀ i x, |F i x| ≤ U
  entropy : ∃ (A : ℝ) (p : ℕ), 1 ≤ A ∧
    ∀ (Q : Measure 𝒳) (_hQ : IsProbabilityMeasure Q) (ε : ℝ),
      0 < ε → ε ≤ 1 →
        L2CoveringNumberLe Q F (ε * U) (Nat.ceil ((A / ε) ^ p))

private theorem HasPolynomialL2Cover.reindex
    {ι : Type v} {κ : Type w} {F : ι → 𝒳 → ℝ} {U : ℝ}
    (hF : HasPolynomialL2Cover F U) (e : κ ≃ ι) :
    HasPolynomialL2Cover (fun k => F (e k)) U := by
  refine ⟨hF.envelope_pos, fun k => hF.measurable (e k), fun k => hF.envelope (e k), ?_⟩
  obtain ⟨A, p, hA, hent⟩ := hF.entropy
  refine ⟨A, p, hA, ?_⟩
  intro Q hQ ε hε hε1
  obtain ⟨C, hCcard, hCcover⟩ := hent Q hQ ε hε hε1
  classical
  let emb : ι ↪ κ := e.symm.toEmbedding
  refine ⟨C.map emb, ?_, ?_⟩
  · simpa [emb] using hCcard
  · intro k
    obtain ⟨i, hiC, hi⟩ := hCcover (e k)
    refine ⟨e.symm i, Finset.mem_map.mpr ⟨i, hiC, rfl⟩, ?_⟩
    simpa using hi

/-- A bounded measurable pseudo-dimension class carries a uniform polynomial
`L²` covering certificate. -/
theorem HasPseudoDimAtMost.hasPolynomialL2Cover
    {ι : Type v} [Nonempty ι] {F : ι → 𝒳 → ℝ} {d : ℕ} {U : ℝ}
    (hpdim : HasPseudoDimAtMost F d)
    (hmeas : ∀ i, Measurable (F i))
    (hU : 0 < U) (henvelope : ∀ i x, |F i x| ≤ U) :
    HasPolynomialL2Cover F U := by
  refine ⟨hU, hmeas, henvelope, 16, 8 * (d + 1), by norm_num, ?_⟩
  intro Q hQ ε hε hε1
  letI : IsProbabilityMeasure Q := hQ
  simpa only [vcSubgraphCoverBound] using
    (real_vcSubgraph_l2_covering F d hmeas hpdim hU hε hε1 henvelope Q)

/-- Negating every member of a polynomial-entropy class preserves its
envelope and uniform polynomial `L²` entropy. -/
theorem HasPolynomialL2Cover.neg
    {ι : Type v} {F : ι → 𝒳 → ℝ} {U : ℝ}
    (hF : HasPolynomialL2Cover F U) :
    HasPolynomialL2Cover (fun i x => -F i x) U := by
  refine ⟨hF.envelope_pos, fun i => (hF.measurable i).neg, ?_, ?_⟩
  · intro i x
    simpa using hF.envelope i x
  · obtain ⟨A, p, hA, hent⟩ := hF.entropy
    refine ⟨A, p, hA, ?_⟩
    intro Q hQ ε hε hε1
    obtain ⟨C, hCcard, hCcover⟩ := hent Q hQ ε hε hε1
    refine ⟨C, hCcard, ?_⟩
    intro i
    obtain ⟨j, hjC, hij⟩ := hCcover i
    refine ⟨j, hjC, ?_⟩
    have heq : measureL2Dist Q (fun x => -F i x) (fun x => -F j x) =
        measureL2Dist Q (F i) (F j) := by
      rw [measureL2Dist_eq_lpNorm Q _ _ (hF.measurable i).fun_neg (hF.measurable j).fun_neg,
        measureL2Dist_eq_lpNorm Q _ _ (hF.measurable i) (hF.measurable j)]
      have hfun : (fun x => -F i x - -F j x) = -(fun x => F i x - F j x) := by
        funext x
        simp only [Pi.neg_apply]
        ring
      rw [hfun, lpNorm_neg]
    rwa [heq]

/-- Pointwise addition of two independently indexed polynomial-entropy
classes has uniform polynomial `L²` entropy with summed envelope. -/
theorem HasPolynomialL2Cover.add
    {ι : Type v} {κ : Type w} {F : ι → 𝒳 → ℝ} {G : κ → 𝒳 → ℝ} {U V : ℝ}
    (hF : HasPolynomialL2Cover F U)
    (hG : HasPolynomialL2Cover G V) :
    HasPolynomialL2Cover (fun p : ι × κ => fun x => F p.1 x + G p.2 x) (U + V) := by
  have hU : 0 < U := hF.envelope_pos
  have hV : 0 < V := hG.envelope_pos
  refine ⟨by positivity, fun p => (hF.measurable p.1).add (hG.measurable p.2), ?_, ?_⟩
  · intro p x
    exact (abs_add_le _ _).trans (add_le_add (hF.envelope p.1 x) (hG.envelope p.2 x))
  · obtain ⟨A, p, hA, hentF⟩ := hF.entropy
    obtain ⟨B, q, hB, hentG⟩ := hG.entropy
    refine ⟨8 * A * B, p + q + 2, by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)], ?_⟩
    intro Q hQ ε hε hε1
    have hhalf : 0 < ε / 2 := by positivity
    have hhalf1 : ε / 2 ≤ 1 := by linarith
    obtain ⟨CF, hCFcard, hCFcover⟩ := hentF Q hQ (ε / 2) hhalf hhalf1
    obtain ⟨CG, hCGcard, hCGcover⟩ := hentG Q hQ (ε / 2) hhalf hhalf1
    rw [show A / (ε / 2) = 2 * A / ε by field_simp] at hCFcard
    rw [show B / (ε / 2) = 2 * B / ε by field_simp] at hCGcard
    classical
    refine ⟨CF ×ˢ CG, ?_, ?_⟩
    · rw [Finset.card_product]
      exact (Nat.mul_le_mul hCFcard hCGcard).trans
        (ceil_mul_le_ceil_poly hA hB hε hε1)
    · intro a
      obtain ⟨i, hiC, hi⟩ := hCFcover a.1
      obtain ⟨j, hjC, hj⟩ := hCGcover a.2
      refine ⟨(i, j), Finset.mem_product.mpr ⟨hiC, hjC⟩, ?_⟩
      haveI : IsProbabilityMeasure Q := hQ
      calc
        measureL2Dist Q (fun x => F a.1 x + G a.2 x) (fun x => F i x + G j x) ≤
            measureL2Dist Q (F a.1) (F i) + measureL2Dist Q (G a.2) (G j) :=
          measureL2Dist_add_le _ _ _ _ (hF.measurable a.1) (hF.measurable i)
            (hG.measurable a.2) (hG.measurable j) (hF.envelope a.1)
            (hF.envelope i)
        _ < ε * (U + V) := by nlinarith

/-- Pointwise multiplication of two independently indexed bounded
polynomial-entropy classes has uniform polynomial `L²` entropy with product
envelope. -/
theorem HasPolynomialL2Cover.mul
    {ι : Type v} {κ : Type w} {F : ι → 𝒳 → ℝ} {G : κ → 𝒳 → ℝ} {U V : ℝ}
    (hF : HasPolynomialL2Cover F U)
    (hG : HasPolynomialL2Cover G V) :
    HasPolynomialL2Cover (fun p : ι × κ => fun x => F p.1 x * G p.2 x) (U * V) := by
  have hU : 0 < U := hF.envelope_pos
  have hV : 0 < V := hG.envelope_pos
  refine ⟨mul_pos hU hV, fun p => (hF.measurable p.1).mul (hG.measurable p.2), ?_, ?_⟩
  · intro p x
    rw [abs_mul]
    exact mul_le_mul (hF.envelope p.1 x) (hG.envelope p.2 x) (abs_nonneg _) hU.le
  · obtain ⟨A, p, hA, hentF⟩ := hF.entropy
    obtain ⟨B, q, hB, hentG⟩ := hG.entropy
    refine ⟨8 * A * B, p + q + 2, by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)], ?_⟩
    intro Q hQ ε hε hε1
    have hhalf : 0 < ε / 2 := by positivity
    have hhalf1 : ε / 2 ≤ 1 := by linarith
    obtain ⟨CF, hCFcard, hCFcover⟩ := hentF Q hQ (ε / 2) hhalf hhalf1
    obtain ⟨CG, hCGcard, hCGcover⟩ := hentG Q hQ (ε / 2) hhalf hhalf1
    rw [show A / (ε / 2) = 2 * A / ε by field_simp] at hCFcard
    rw [show B / (ε / 2) = 2 * B / ε by field_simp] at hCGcard
    classical
    refine ⟨CF ×ˢ CG, ?_, ?_⟩
    · rw [Finset.card_product]
      exact (Nat.mul_le_mul hCFcard hCGcard).trans
        (ceil_mul_le_ceil_poly hA hB hε hε1)
    · intro z
      obtain ⟨i, hiC, hi⟩ := hCFcover z.1
      obtain ⟨j, hjC, hj⟩ := hCGcover z.2
      refine ⟨(i, j), Finset.mem_product.mpr ⟨hiC, hjC⟩, ?_⟩
      haveI : IsProbabilityMeasure Q := hQ
      calc
        measureL2Dist Q (fun x => F z.1 x * G z.2 x) (fun x => F i x * G j x) ≤
            V * measureL2Dist Q (F z.1) (F i) +
              U * measureL2Dist Q (G z.2) (G j) :=
          measureL2Dist_mul_le _ _ _ _ (hF.measurable z.1) (hF.measurable i)
            (hG.measurable z.2) (hG.measurable j) hU.le hV.le (hF.envelope z.1)
            (hF.envelope i) (hG.envelope z.2) (hG.envelope j)
        _ < ε * (U * V) := by nlinarith

/-- A fixed finite sum of independently indexed polynomial-entropy classes
again has uniform polynomial `L²` entropy, with the sum of the envelopes. -/
theorem HasPolynomialL2Cover.finSum
    {K : Type w} [Fintype K] [Nonempty K]
    {ι : K → Type v} {F : (k : K) → ι k → 𝒳 → ℝ} {U : K → ℝ}
    (hF : ∀ k, HasPolynomialL2Cover (F k) (U k)) :
    HasPolynomialL2Cover
      (fun θ : (k : K) → ι k => fun x => ∑ k, F k (θ k) x)
      (∑ k, U k) := by
  classical
  let P : ∀ (K : Type w) [Fintype K], Prop := fun K _ =>
    Nonempty K → ∀ (ι : K → Type v) (F : (k : K) → ι k → 𝒳 → ℝ) (U : K → ℝ),
      (∀ k, HasPolynomialL2Cover (F k) (U k)) →
        HasPolynomialL2Cover
          (fun θ : (k : K) → ι k => fun x => ∑ k, F k (θ k) x) (∑ k, U k)
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ K
    (inferInstance : Nonempty K) ι F U hF
  · intro α β _ e ih hβ ι F U hF
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let hα : Nonempty α := ⟨e.symm (Classical.choice hβ)⟩
    have hc := ih hα (fun a => ι (e a)) (fun a => F (e a)) (fun a => U (e a))
      (fun a => hF (e a))
    let eθ : ((b : β) → ι b) ≃ ((a : α) → ι (e a)) :=
      (Equiv.piCongrLeft ι e).symm
    have hclass :
        (fun θ : (b : β) → ι b => fun x => ∑ b, F b (θ b) x) =
          (fun θ : (b : β) → ι b => fun x => ∑ a, F (e a) (θ (e a)) x) := by
      funext θ x
      exact (e.sum_comp (fun b => F b (θ b) x)).symm
    have hUeq : (∑ b, U b) = ∑ a, U (e a) := (e.sum_comp U).symm
    rw [hclass, hUeq]
    simpa [eθ] using hc.reindex eθ
  · intro h
    exact isEmptyElim (Classical.choice h)
  · intro α _ ih _ ι F U hF
    by_cases hα : Nonempty α
    · have htail := ih hα (fun a => ι (some a)) (fun a => F (some a))
        (fun a => U (some a)) (fun a => hF (some a))
      have hadd := (hF none).add htail
      let split : ((k : Option α) → ι k) ≃
          (ι none × ((a : α) → ι (some a))) :=
        { toFun := fun θ => (θ none, fun a => θ (some a))
          invFun := fun p k => Option.rec p.1 p.2 k
          left_inv := fun θ => by funext k; cases k <;> rfl
          right_inv := fun p => by cases p; rfl }
      simp only [Fintype.sum_option]
      exact hadd.reindex split
    · letI : IsEmpty α := not_nonempty_iff.mp hα
      let single : ((k : Option α) → ι k) ≃ ι none :=
        { toFun := fun θ => θ none
          invFun := fun i k => Option.rec i (fun a => isEmptyElim a) k
          left_inv := fun θ => by funext k; cases k with
            | none => rfl
            | some a => exact isEmptyElim a
          right_inv := fun i => rfl }
      simp only [Fintype.sum_option, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact (hF none).reindex single

/-- A fixed finite product of independently indexed polynomial-entropy
classes again has uniform polynomial `L²` entropy, with the product envelope. -/
theorem HasPolynomialL2Cover.finProd
    {K : Type w} [Fintype K] [Nonempty K]
    {ι : K → Type v} {F : (k : K) → ι k → 𝒳 → ℝ} {U : K → ℝ}
    (hF : ∀ k, HasPolynomialL2Cover (F k) (U k)) :
    HasPolynomialL2Cover
      (fun θ : (k : K) → ι k => fun x => ∏ k, F k (θ k) x)
      (∏ k, U k) := by
  classical
  let P : ∀ (K : Type w) [Fintype K], Prop := fun K _ =>
    Nonempty K → ∀ (ι : K → Type v) (F : (k : K) → ι k → 𝒳 → ℝ) (U : K → ℝ),
      (∀ k, HasPolynomialL2Cover (F k) (U k)) →
        HasPolynomialL2Cover
          (fun θ : (k : K) → ι k => fun x => ∏ k, F k (θ k) x) (∏ k, U k)
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ K
    (inferInstance : Nonempty K) ι F U hF
  · intro α β _ e ih hβ ι F U hF
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let hα : Nonempty α := ⟨e.symm (Classical.choice hβ)⟩
    have hc := ih hα (fun a => ι (e a)) (fun a => F (e a)) (fun a => U (e a))
      (fun a => hF (e a))
    let eθ : ((b : β) → ι b) ≃ ((a : α) → ι (e a)) :=
      (Equiv.piCongrLeft ι e).symm
    have hclass :
        (fun θ : (b : β) → ι b => fun x => ∏ b, F b (θ b) x) =
          (fun θ : (b : β) → ι b => fun x => ∏ a, F (e a) (θ (e a)) x) := by
      funext θ x
      exact (e.prod_comp (fun b => F b (θ b) x)).symm
    have hUeq : (∏ b, U b) = ∏ a, U (e a) := (e.prod_comp U).symm
    rw [hclass, hUeq]
    simpa [eθ] using hc.reindex eθ
  · intro h
    exact isEmptyElim (Classical.choice h)
  · intro α _ ih _ ι F U hF
    by_cases hα : Nonempty α
    · have htail := ih hα (fun a => ι (some a)) (fun a => F (some a))
        (fun a => U (some a)) (fun a => hF (some a))
      have hmul := (hF none).mul htail
      let split : ((k : Option α) → ι k) ≃
          (ι none × ((a : α) → ι (some a))) :=
        { toFun := fun θ => (θ none, fun a => θ (some a))
          invFun := fun p k => Option.rec p.1 p.2 k
          left_inv := fun θ => by funext k; cases k <;> rfl
          right_inv := fun p => by cases p; rfl }
      simp only [Fintype.prod_option]
      exact hmul.reindex split
    · letI : IsEmpty α := not_nonempty_iff.mp hα
      let single : ((k : Option α) → ι k) ≃ ι none :=
        { toFun := fun θ => θ none
          invFun := fun i k => Option.rec i (fun a => isEmptyElim a) k
          left_inv := fun θ => by funext k; cases k with
            | none => rfl
            | some a => exact isEmptyElim a
          right_inv := fun i => rfl }
      simp only [Fintype.prod_option, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      exact (hF none).reindex single

/-- A polynomial `L²` covering certificate with named entropy witnesses.
Unlike `HasPolynomialL2Cover`, this form retains the particular base and
integer exponent, so a family of constructions can share witnesses before
its observation-specific parameters are introduced. -/
structure HasPolynomialL2CoverWith
    {ι : Type v} (F : ι → 𝒳 → ℝ) (U A : ℝ) (p : ℕ) : Prop where
  toHasPolynomialL2Cover : HasPolynomialL2Cover F U
  one_le_base : 1 ≤ A
  entropy : ∀ (Q : Measure 𝒳) (_hQ : IsProbabilityMeasure Q) (ε : ℝ),
    0 < ε → ε ≤ 1 →
      L2CoveringNumberLe Q F (ε * U) (Nat.ceil ((A / ε) ^ p))

/-- Forgetting the named witnesses gives the ordinary polynomial-cover
certificate. -/
theorem HasPolynomialL2CoverWith.forget
    {ι : Type v} {F : ι → 𝒳 → ℝ} {U A : ℝ} {p : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p) :
    HasPolynomialL2Cover F U :=
  hF.toHasPolynomialL2Cover

/-- Enlarging a named envelope preserves its entropy witnesses. -/
-- @node: HasPolynomialL2CoverWith.enlargeEnvelope
theorem HasPolynomialL2CoverWith.enlargeEnvelope
    {ι : Type v} {F : ι → 𝒳 → ℝ} {U V A : ℝ} {p : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p) (hUV : U ≤ V) :
    HasPolynomialL2CoverWith F V A p := by
  have hV : 0 < V := hF.forget.envelope_pos.trans_le hUV
  refine ⟨⟨hV, hF.forget.measurable,
    fun i x => (hF.forget.envelope i x).trans hUV, A, p,
      hF.one_le_base, ?_⟩, hF.one_le_base, ?_⟩ <;>
    intro Q hQ ε hε hε1
  · obtain ⟨C, hCcard, hCcover⟩ := hF.entropy Q hQ ε hε hε1
    refine ⟨C, hCcard, fun i => ?_⟩
    obtain ⟨j, hjC, hij⟩ := hCcover i
    exact ⟨j, hjC, hij.trans_le (mul_le_mul_of_nonneg_left hUV hε.le)⟩
  · obtain ⟨C, hCcard, hCcover⟩ := hF.entropy Q hQ ε hε hε1
    refine ⟨C, hCcard, fun i => ?_⟩
    obtain ⟨j, hjC, hij⟩ := hCcover i
    exact ⟨j, hjC, hij.trans_le (mul_le_mul_of_nonneg_left hUV hε.le)⟩

/-- A bounded measurable pseudo-dimension class has the canonical named
entropy witnesses used by the VC-subgraph covering theorem. -/
theorem HasPseudoDimAtMost.hasPolynomialL2CoverWith
    {ι : Type v} [Nonempty ι] {F : ι → 𝒳 → ℝ} {d : ℕ} {U : ℝ}
    (hpdim : HasPseudoDimAtMost F d)
    (hmeas : ∀ i, Measurable (F i))
    (hU : 0 < U) (henvelope : ∀ i x, |F i x| ≤ U) :
    HasPolynomialL2CoverWith F U 16 (8 * (d + 1)) := by
  refine ⟨hpdim.hasPolynomialL2Cover hmeas hU henvelope, by norm_num, ?_⟩
  intro Q hQ ε hε hε1
  letI : IsProbabilityMeasure Q := hQ
  simpa only [vcSubgraphCoverBound] using
    (real_vcSubgraph_l2_covering F d hmeas hpdim hU hε hε1 henvelope Q)

private theorem HasPolynomialL2CoverWith.reindex
    {ι : Type v} {κ : Type w} {F : ι → 𝒳 → ℝ} {U A : ℝ} {p : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p) (e : κ ≃ ι) :
    HasPolynomialL2CoverWith (fun k => F (e k)) U A p := by
  refine ⟨hF.forget.reindex e, hF.one_le_base, ?_⟩
  intro Q hQ ε hε hε1
  obtain ⟨C, hCcard, hCcover⟩ := hF.entropy Q hQ ε hε hε1
  classical
  let emb : ι ↪ κ := e.symm.toEmbedding
  refine ⟨C.map emb, ?_, ?_⟩
  · simpa [emb] using hCcard
  · intro k
    obtain ⟨i, hiC, hi⟩ := hCcover (e k)
    refine ⟨e.symm i, Finset.mem_map.mpr ⟨i, hiC, rfl⟩, ?_⟩
    simpa using hi

/-- Negation preserves named polynomial-cover witnesses. -/
theorem HasPolynomialL2CoverWith.neg
    {ι : Type v} {F : ι → 𝒳 → ℝ} {U A : ℝ} {p : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p) :
    HasPolynomialL2CoverWith (fun i x => -F i x) U A p := by
  refine ⟨hF.forget.neg, hF.one_le_base, ?_⟩
  intro Q hQ ε hε hε1
  obtain ⟨C, hCcard, hCcover⟩ := hF.entropy Q hQ ε hε hε1
  refine ⟨C, hCcard, ?_⟩
  intro i
  obtain ⟨j, hjC, hij⟩ := hCcover i
  refine ⟨j, hjC, ?_⟩
  have heq : measureL2Dist Q (fun x => -F i x) (fun x => -F j x) =
      measureL2Dist Q (F i) (F j) := by
    rw [measureL2Dist_eq_lpNorm Q _ _ (hF.forget.measurable i).fun_neg
      (hF.forget.measurable j).fun_neg,
      measureL2Dist_eq_lpNorm Q _ _ (hF.forget.measurable i)
        (hF.forget.measurable j)]
    have hfun : (fun x => -F i x - -F j x) = -(fun x => F i x - F j x) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [hfun, lpNorm_neg]
  rwa [heq]

/-- Addition combines named polynomial-cover witnesses by the same explicit
formula as the ordinary cover algebra. -/
theorem HasPolynomialL2CoverWith.add
    {ι : Type v} {κ : Type w} {F : ι → 𝒳 → ℝ} {G : κ → 𝒳 → ℝ}
    {U V A B : ℝ} {p q : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p)
    (hG : HasPolynomialL2CoverWith G V B q) :
    HasPolynomialL2CoverWith
      (fun z : ι × κ => fun x => F z.1 x + G z.2 x)
      (U + V) (8 * A * B) (p + q + 2) := by
  have hA := hF.one_le_base
  have hB := hG.one_le_base
  have hU := hF.forget.envelope_pos
  have hV := hG.forget.envelope_pos
  refine ⟨hF.forget.add hG.forget, by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)], ?_⟩
  intro Q hQ ε hε hε1
  have hhalf : 0 < ε / 2 := by positivity
  have hhalf1 : ε / 2 ≤ 1 := by linarith
  obtain ⟨CF, hCFcard, hCFcover⟩ := hF.entropy Q hQ (ε / 2) hhalf hhalf1
  obtain ⟨CG, hCGcard, hCGcover⟩ := hG.entropy Q hQ (ε / 2) hhalf hhalf1
  rw [show A / (ε / 2) = 2 * A / ε by field_simp] at hCFcard
  rw [show B / (ε / 2) = 2 * B / ε by field_simp] at hCGcard
  classical
  refine ⟨CF ×ˢ CG, ?_, ?_⟩
  · rw [Finset.card_product]
    exact (Nat.mul_le_mul hCFcard hCGcard).trans
      (ceil_mul_le_ceil_poly hA hB hε hε1)
  · intro z
    obtain ⟨i, hiC, hi⟩ := hCFcover z.1
    obtain ⟨j, hjC, hj⟩ := hCGcover z.2
    refine ⟨(i, j), Finset.mem_product.mpr ⟨hiC, hjC⟩, ?_⟩
    haveI : IsProbabilityMeasure Q := hQ
    calc
      measureL2Dist Q (fun x => F z.1 x + G z.2 x)
          (fun x => F i x + G j x) ≤
          measureL2Dist Q (F z.1) (F i) + measureL2Dist Q (G z.2) (G j) :=
        measureL2Dist_add_le _ _ _ _ (hF.forget.measurable z.1)
          (hF.forget.measurable i) (hG.forget.measurable z.2)
          (hG.forget.measurable j) (hF.forget.envelope z.1)
          (hF.forget.envelope i)
      _ < ε * (U + V) := by nlinarith

/-- Multiplication combines named polynomial-cover witnesses by the same
explicit formula as the ordinary cover algebra. -/
theorem HasPolynomialL2CoverWith.mul
    {ι : Type v} {κ : Type w} {F : ι → 𝒳 → ℝ} {G : κ → 𝒳 → ℝ}
    {U V A B : ℝ} {p q : ℕ}
    (hF : HasPolynomialL2CoverWith F U A p)
    (hG : HasPolynomialL2CoverWith G V B q) :
    HasPolynomialL2CoverWith
      (fun z : ι × κ => fun x => F z.1 x * G z.2 x)
      (U * V) (8 * A * B) (p + q + 2) := by
  have hA := hF.one_le_base
  have hB := hG.one_le_base
  have hU := hF.forget.envelope_pos
  have hV := hG.forget.envelope_pos
  refine ⟨hF.forget.mul hG.forget, by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)], ?_⟩
  intro Q hQ ε hε hε1
  have hhalf : 0 < ε / 2 := by positivity
  have hhalf1 : ε / 2 ≤ 1 := by linarith
  obtain ⟨CF, hCFcard, hCFcover⟩ := hF.entropy Q hQ (ε / 2) hhalf hhalf1
  obtain ⟨CG, hCGcard, hCGcover⟩ := hG.entropy Q hQ (ε / 2) hhalf hhalf1
  rw [show A / (ε / 2) = 2 * A / ε by field_simp] at hCFcard
  rw [show B / (ε / 2) = 2 * B / ε by field_simp] at hCGcard
  classical
  refine ⟨CF ×ˢ CG, ?_, ?_⟩
  · rw [Finset.card_product]
    exact (Nat.mul_le_mul hCFcard hCGcard).trans
      (ceil_mul_le_ceil_poly hA hB hε hε1)
  · intro z
    obtain ⟨i, hiC, hi⟩ := hCFcover z.1
    obtain ⟨j, hjC, hj⟩ := hCGcover z.2
    refine ⟨(i, j), Finset.mem_product.mpr ⟨hiC, hjC⟩, ?_⟩
    haveI : IsProbabilityMeasure Q := hQ
    calc
      measureL2Dist Q (fun x => F z.1 x * G z.2 x)
          (fun x => F i x * G j x) ≤
          V * measureL2Dist Q (F z.1) (F i) +
            U * measureL2Dist Q (G z.2) (G j) :=
        measureL2Dist_mul_le _ _ _ _ (hF.forget.measurable z.1)
          (hF.forget.measurable i) (hG.forget.measurable z.2)
          (hG.forget.measurable j) hF.forget.envelope_pos.le
          hG.forget.envelope_pos.le (hF.forget.envelope z.1)
          (hF.forget.envelope i) (hG.forget.envelope z.2)
          (hG.forget.envelope j)
      _ < ε * (U * V) := by nlinarith

/-- If an assembled class has envelope `c * V` but a direct pointwise bound
by `V`, shrinking the envelope by the fixed factor `c` costs the same factor
in the named entropy base. -/
theorem HasPolynomialL2CoverWith.tightenEnvelopeBy
    {ι : Type v} {F : ι → 𝒳 → ℝ} {V A c : ℝ} {p : ℕ}
    (hF : HasPolynomialL2CoverWith F (c * V) A p)
    (hc : 1 ≤ c) (hV : 0 < V) (hbound : ∀ i x, |F i x| ≤ V) :
    HasPolynomialL2CoverWith F V (c * A) p := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hbaseOne : 1 ≤ c * A := by
    simpa only [one_mul] using
      (mul_le_mul hc hF.one_le_base (by norm_num : (0 : ℝ) ≤ 1) hc0.le)
  refine ⟨⟨hV, hF.forget.measurable, hbound, c * A, p,
    hbaseOne, ?_⟩, hbaseOne, ?_⟩
  · intro Q hQ ε hε hε1
    have hec : 0 < ε / c := div_pos hε hc0
    have hec1 : ε / c ≤ 1 := by
      apply (div_le_one hc0).2
      exact hε1.trans hc
    have hradius : (ε / c) * (c * V) = ε * V := by field_simp
    have hbase : A / (ε / c) = (c * A) / ε := by field_simp
    simpa only [hradius, hbase] using hF.entropy Q hQ (ε / c) hec hec1
  · intro Q hQ ε hε hε1
    have hec : 0 < ε / c := div_pos hε hc0
    have hec1 : ε / c ≤ 1 := by
      apply (div_le_one hc0).2
      exact hε1.trans hc
    have hradius : (ε / c) * (c * V) = ε * V := by field_simp
    have hbase : A / (ε / c) = (c * A) / ε := by field_simp
    simpa only [hradius, hbase] using hF.entropy Q hQ (ε / c) hec hec1

/-- A collection has polynomial-cover witnesses uniform over an auxiliary
parameter type when the named base and exponent precede that parameter. -/
def HasUniformPolynomialL2CoverOver
    (S : Type*) {ι : S → Type v}
    (F : (s : S) → ι s → 𝒳 → ℝ) (U : S → ℝ) : Prop :=
  ∃ A : ℝ, ∃ p : ℕ, ∀ s, HasPolynomialL2CoverWith (F s) (U s) A p

/-- Uniform named covers are stable under pointwise negation. -/
theorem HasUniformPolynomialL2CoverOver.neg
    {S : Type*} {ι : S → Type v}
    {F : (s : S) → ι s → 𝒳 → ℝ} {U : S → ℝ}
    (hF : HasUniformPolynomialL2CoverOver S F U) :
    HasUniformPolynomialL2CoverOver S
      (fun s i x => -F s i x) U := by
  obtain ⟨A, p, hF⟩ := hF
  exact ⟨A, p, fun s => (hF s).neg⟩

/-- Uniform named covers are stable under pointwise addition. -/
theorem HasUniformPolynomialL2CoverOver.add
    {S : Type*} {ι : S → Type v} {κ : S → Type w}
    {F : (s : S) → ι s → 𝒳 → ℝ} {G : (s : S) → κ s → 𝒳 → ℝ}
    {U V : S → ℝ}
    (hF : HasUniformPolynomialL2CoverOver S F U)
    (hG : HasUniformPolynomialL2CoverOver S G V) :
    HasUniformPolynomialL2CoverOver S
      (fun s (z : ι s × κ s) x => F s z.1 x + G s z.2 x)
      (fun s => U s + V s) := by
  obtain ⟨A, p, hF⟩ := hF
  obtain ⟨B, q, hG⟩ := hG
  exact ⟨8 * A * B, p + q + 2, fun s => (hF s).add (hG s)⟩

/-- Uniform named covers are stable under pointwise multiplication. -/
theorem HasUniformPolynomialL2CoverOver.mul
    {S : Type*} {ι : S → Type v} {κ : S → Type w}
    {F : (s : S) → ι s → 𝒳 → ℝ} {G : (s : S) → κ s → 𝒳 → ℝ}
    {U V : S → ℝ}
    (hF : HasUniformPolynomialL2CoverOver S F U)
    (hG : HasUniformPolynomialL2CoverOver S G V) :
    HasUniformPolynomialL2CoverOver S
      (fun s (z : ι s × κ s) x => F s z.1 x * G s z.2 x)
      (fun s => U s * V s) := by
  obtain ⟨A, p, hF⟩ := hF
  obtain ⟨B, q, hG⟩ := hG
  exact ⟨8 * A * B, p + q + 2, fun s => (hF s).mul (hG s)⟩

/-- A nonempty finite sum preserves entropy witnesses uniformly over all
auxiliary parameters. -/
theorem HasUniformPolynomialL2CoverOver.finSum
    {S : Type*} {K : Type w} [Fintype K] [Nonempty K]
    {ι : (s : S) → K → Type v}
    {F : (s : S) → (k : K) → ι s k → 𝒳 → ℝ}
    {U : S → K → ℝ}
    (hF : ∀ k, HasUniformPolynomialL2CoverOver S
      (fun s => F s k) (fun s => U s k)) :
    HasUniformPolynomialL2CoverOver S
      (fun s (θ : (k : K) → ι s k) x => ∑ k, F s k (θ k) x)
      (fun s => ∑ k, U s k) := by
  classical
  let P : ∀ (K : Type w) [Fintype K], Prop := fun K _ =>
    Nonempty K → ∀ (ι : (s : S) → K → Type v)
      (F : (s : S) → (k : K) → ι s k → 𝒳 → ℝ) (U : S → K → ℝ),
      (∀ k, HasUniformPolynomialL2CoverOver S
        (fun s => F s k) (fun s => U s k)) →
      HasUniformPolynomialL2CoverOver S
        (fun s (θ : (k : K) → ι s k) x => ∑ k, F s k (θ k) x)
        (fun s => ∑ k, U s k)
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ K
    (inferInstance : Nonempty K) ι F U hF
  · intro α β _ e ih hβ ι F U hF
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let hα : Nonempty α := ⟨e.symm (Classical.choice hβ)⟩
    have hc := ih hα (fun s a => ι s (e a))
      (fun s a => F s (e a)) (fun s a => U s (e a)) (fun a => hF (e a))
    obtain ⟨A, p, hc⟩ := hc
    refine ⟨A, p, fun s => ?_⟩
    let eθ : ((b : β) → ι s b) ≃ ((a : α) → ι s (e a)) :=
      (Equiv.piCongrLeft (ι s) e).symm
    have hclass :
        (fun θ : (b : β) → ι s b => fun x => ∑ b, F s b (θ b) x) =
          (fun θ : (b : β) → ι s b => fun x => ∑ a, F s (e a) (θ (e a)) x) := by
      funext θ x
      exact (e.sum_comp (fun b => F s b (θ b) x)).symm
    have hUeq : (∑ b, U s b) = ∑ a, U s (e a) :=
      (e.sum_comp (U s)).symm
    change HasPolynomialL2CoverWith
      (fun θ : (b : β) → ι s b => fun x => ∑ b, F s b (θ b) x)
      (∑ b, U s b) A p
    rw [hclass, hUeq]
    simpa [eθ] using (hc s).reindex eθ
  · intro h
    exact isEmptyElim (Classical.choice h)
  · intro α _ ih _ ι F U hF
    by_cases hα : Nonempty α
    · have htail := ih hα (fun s a => ι s (some a))
        (fun s a => F s (some a)) (fun s a => U s (some a))
        (fun a => hF (some a))
      have hadd := (hF none).add htail
      obtain ⟨A, p, hadd⟩ := hadd
      refine ⟨A, p, fun s => ?_⟩
      let split : ((k : Option α) → ι s k) ≃
          (ι s none × ((a : α) → ι s (some a))) :=
        { toFun := fun θ => (θ none, fun a => θ (some a))
          invFun := fun z k => Option.rec z.1 z.2 k
          left_inv := fun θ => by funext k; cases k <;> rfl
          right_inv := fun z => by cases z; rfl }
      simp only [Fintype.sum_option]
      exact (hadd s).reindex split
    · letI : IsEmpty α := not_nonempty_iff.mp hα
      obtain ⟨A, p, hone⟩ := hF none
      refine ⟨A, p, fun s => ?_⟩
      let single : ((k : Option α) → ι s k) ≃ ι s none :=
        { toFun := fun θ => θ none
          invFun := fun i k => Option.rec i (fun a => isEmptyElim a) k
          left_inv := fun θ => by funext k; cases k with
            | none => rfl
            | some a => exact isEmptyElim a
          right_inv := fun i => rfl }
      simp only [Fintype.sum_option, Finset.univ_eq_empty, Finset.sum_empty,
        add_zero]
      exact (hone s).reindex single

end Causalean.Stat.Concentration
