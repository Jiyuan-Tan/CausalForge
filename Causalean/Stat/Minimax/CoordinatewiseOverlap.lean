import Causalean.Stat.Minimax.TotalVariation
import Causalean.Stat.Minimax.Assouad
import Causalean.Stat.Minimax.BretagnolleHuber
import Causalean.Stat.Minimax.HellingerAffinity
import Causalean.Mathlib.InformationTheory.KLBind
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Constructions.Pi
import Causalean.Stat.Minimax.MaximalCoupling

/-!
# Coordinatewise overlap direct-product bound

This file states a world-independent decentralized testing bound. Each decoder
may inspect its compressed local coordinate, all other coordinates, and a
common ancillary variable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Causalean.Stat

/-- The law of a compressed local observation. -/
noncomputable def compressedCoordinateLaw {Z S : Type*}
    [MeasurableSpace Z] [MeasurableSpace S]
    (compress : Z → S) (Q : Measure Z) : Measure S :=
  Measure.map compress Q

/-- Measurable finite-coordinate compression cannot increase KL divergence. -/
-- @node: compressedCoordinateLaw_klDiv_le
lemma compressedCoordinateLaw_klDiv_le {Z S : Type*}
    [MeasurableSpace Z] [MeasurableSpace S]
    (compress : Z → S) (hcompress : Measurable compress) (μ ν : Measure Z)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (compressedCoordinateLaw compress μ)
        (compressedCoordinateLaw compress ν) ≤
      InformationTheory.klDiv μ ν := by
  exact Causalean.Mathlib.InformationTheory.Measure.klDiv_map_le hcompress

/-- The average probability that every decentralized decoder recovers its bit
under the uniform hypercube prior and the conditionally independent product
experiment. -/
noncomputable def coordinatewiseSuccessProbability
    {M : ℕ} {Z S : Fin M → Type*} {A : Type*}
    [∀ j, MeasurableSpace (Z j)] [∀ j, MeasurableSpace (S j)]
    [MeasurableSpace A]
    (Q : ∀ j, Bool → Measure (Z j)) (R : Measure A)
    [∀ j b, IsProbabilityMeasure (Q j b)] [IsProbabilityMeasure R]
    (compress : ∀ j, Z j → S j)
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool) : ℝ≥0∞ :=
  (∑ omega : Fin M → Bool,
      (R.prod (Measure.pi (fun j => Q j (omega j))))
        {data | ∀ j,
          decoder j (compress j (data.2 j)) data.2 data.1 = omega j}) /
    ((2 : ℝ≥0∞) ^ M)

/-- The common-part overlap of the two compressed laws at coordinate `j`. -/
noncomputable def coordinateOverlap
    {M : ℕ} {Z S : Fin M → Type*}
    [∀ j, MeasurableSpace (Z j)] [∀ j, MeasurableSpace (S j)]
    (Q : ∀ j, Bool → Measure (Z j)) (compress : ∀ j, Z j → S j)
    (j : Fin M) : ℝ :=
  1 - Causalean.Stat.tvDist
    (compressedCoordinateLaw (compress j) (Q j false))
    (compressedCoordinateLaw (compress j) (Q j true))

/-- Select the raw coordinate corresponding to a hypercube vertex from a
coordinatewise pair coupling. -/
-- @node: selectCoupledRaw
def selectCoupledRaw {M : ℕ} {Z : Fin M → Type*}
    (omega : Fin M → Bool) (z : (j : Fin M) → Z j × Z j) :
    (j : Fin M) → Z j :=
  fun j => if omega j then (z j).2 else (z j).1

/-- Simultaneous correctness of all decentralized decoders on a coupled raw
sample selected by `omega`. -/
-- @node: coupledDecoderGood
def coupledDecoderGood
    {M : ℕ} {Z S : Fin M → Type*} {A : Type*}
    (compress : ∀ j, Z j → S j)
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool)
    (omega : Fin M → Bool) (z : (j : Fin M) → Z j × Z j) (a : A) : Prop :=
  ∀ j, decoder j (compress j (selectCoupledRaw omega z j))
    (selectCoupledRaw omega z) a = omega j

-- @node: coupledGoodIndicator
/-- The ENNReal indicator of simultaneous decoder correctness. -/
noncomputable def coupledGoodIndicator
    {M : ℕ} {Z S : Fin M → Type*} {A : Type*}
    (compress : ∀ j, Z j → S j)
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool)
    (omega : Fin M → Bool) (z : (j : Fin M) → Z j × Z j) (a : A) : ℝ≥0∞ := by
  classical
  exact if coupledDecoderGood compress decoder omega z a then 1 else 0

-- @node: coupledDecoderGood_flip_exclusive
/-- If the two compressed versions agree at coordinate `j`, simultaneous
correctness is impossible at both endpoints of the corresponding cube edge. -/
lemma coupledDecoderGood_flip_exclusive
    {M : ℕ} {Z S : Fin M → Type*} {A : Type*}
    (compress : ∀ j, Z j → S j)
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool)
    (hlocal : ∀ j s z z' a,
      (∀ k, k ≠ j → z k = z' k) → decoder j s z a = decoder j s z' a)
    (omega : Fin M → Bool) (z : (j : Fin M) → Z j × Z j) (a : A)
    (j : Fin M) (heq : compress j (z j).1 = compress j (z j).2) :
    ¬ (coupledDecoderGood compress decoder omega z a ∧
      coupledDecoderGood compress decoder (Causalean.Stat.flipBit j omega) z a) := by
  rintro ⟨hgood, hflip⟩
  have hother : ∀ k, k ≠ j →
      selectCoupledRaw omega z k =
        selectCoupledRaw (Causalean.Stat.flipBit j omega) z k := by
    intro k hkj
    simp [selectCoupledRaw, Causalean.Stat.flipBit, hkj]
  have hs : compress j (selectCoupledRaw omega z j) =
      compress j (selectCoupledRaw (Causalean.Stat.flipBit j omega) z j) := by
    cases hbit : omega j <;> simp [selectCoupledRaw, Causalean.Stat.flipBit, hbit, heq]
  have hout := hlocal j (compress j (selectCoupledRaw omega z j))
    (selectCoupledRaw omega z)
    (selectCoupledRaw (Causalean.Stat.flipBit j omega) z) a hother
  have h1 := hgood j
  have h2 := hflip j
  rw [← hs] at h2
  rw [hout, h2, Causalean.Stat.flipBit_self] at h1
  cases hbit : omega j <;> simp [hbit] at h1

-- @node: coupledDecoderGood_count_le_half
/-- Once one coupled coordinate has equal compressions, at most half of the
hypercube vertices can be simultaneously decoded correctly. -/
lemma coupledDecoderGood_count_le_half
    {M : ℕ} {Z S : Fin M → Type*} {A : Type*}
    (compress : ∀ j, Z j → S j)
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool)
    (hlocal : ∀ j s z z' a,
      (∀ k, k ≠ j → z k = z' k) → decoder j s z a = decoder j s z' a)
    (z : (j : Fin M) → Z j × Z j) (a : A) (j : Fin M)
    (heq : compress j (z j).1 = compress j (z j).2) :
    (∑ omega : Fin M → Bool,
      coupledGoodIndicator compress decoder omega z a) ≤
      (2 : ℝ≥0∞) ^ M / 2 := by
  classical
  let I : (Fin M → Bool) → ℝ≥0∞ := fun omega =>
    coupledGoodIndicator compress decoder omega z a
  have hpair : ∀ omega, I omega + I (Causalean.Stat.flipBit j omega) ≤ 1 := by
    intro omega
    by_cases h1 : coupledDecoderGood compress decoder omega z a
    · have h2 : ¬ coupledDecoderGood compress decoder
          (Causalean.Stat.flipBit j omega) z a := fun h =>
        coupledDecoderGood_flip_exclusive compress decoder hlocal omega z a j heq ⟨h1, h⟩
      simp [I, coupledGoodIndicator, h1, h2]
    · by_cases h2 : coupledDecoderGood compress decoder
          (Causalean.Stat.flipBit j omega) z a <;>
        simp [I, coupledGoodIndicator, h1, h2]
  have hreindex : ∑ omega, I (Causalean.Stat.flipBit j omega) = ∑ omega, I omega :=
    Equiv.sum_comp (Causalean.Stat.flipPerm j) I
  have hsum : 2 * ∑ omega, I omega ≤ ∑ _omega : Fin M → Bool, (1 : ℝ≥0∞) := by
    calc
      2 * ∑ omega, I omega =
          (∑ omega, I omega) + ∑ omega, I (Causalean.Stat.flipBit j omega) := by
            rw [hreindex]; ring
      _ = ∑ omega, (I omega + I (Causalean.Stat.flipBit j omega)) := by
        rw [Finset.sum_add_distrib]
      _ ≤ ∑ _omega : Fin M → Bool, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun omega _ => hpair omega
  rw [show (∑ _omega : Fin M → Bool, (1 : ℝ≥0∞)) = (2 : ℝ≥0∞) ^ M by simp] at hsum
  rw [ENNReal.le_div_iff_mul_le (Or.inr (by norm_num)) (Or.inr (by norm_num))]
  simpa [mul_comm] using hsum

-- @node: half_integral_abs_rnDeriv_sub_le_tvDist
/-- For two probability measures dominated by a common finite measure, half the
`L¹` distance between their Radon--Nikodym densities is bounded by total
variation. This is the reverse Scheffé inequality needed to construct the
common submeasure in the maximal-coupling argument. -/
lemma half_integral_abs_rnDeriv_sub_le_tvDist
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν ξ : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsFiniteMeasure ξ] (hμξ : μ ≪ ξ) (hνξ : ν ≪ ξ) :
    (1 / 2 : ℝ) * ∫ x, |(μ.rnDeriv ξ x).toReal - (ν.rnDeriv ξ x).toReal| ∂ξ
      ≤ Causalean.Stat.tvDist μ ν := by
  let p : Ω → ℝ := fun x => (μ.rnDeriv ξ x).toReal
  let q : Ω → ℝ := fun x => (ν.rnDeriv ξ x).toReal
  let d : Ω → ℝ := fun x => p x - q x
  let A : Set Ω := {x | 0 ≤ d x}
  have hp : Integrable p ξ := Measure.integrable_toReal_rnDeriv
  have hq : Integrable q ξ := Measure.integrable_toReal_rnDeriv
  have hd : Integrable d ξ := hp.sub hq
  have hA : MeasurableSet A := by
    dsimp [A, d, p, q]
    exact measurableSet_le measurable_const
      ((Measure.measurable_rnDeriv μ ξ).ennreal_toReal.sub
        (Measure.measurable_rnDeriv ν ξ).ennreal_toReal)
  have hd0 : ∫ x, d x ∂ξ = 0 := by
    rw [show d = fun x => p x - q x from rfl, integral_sub hp hq]
    rw [show p = fun x => (μ.rnDeriv ξ x).toReal from rfl,
      show q = fun x => (ν.rnDeriv ξ x).toReal from rfl,
      Measure.integral_toReal_rnDeriv hμξ,
      Measure.integral_toReal_rnDeriv hνξ]
    simp only [probReal_univ, sub_self]
  have hsplit : ∫ x in A, d x ∂ξ + ∫ x in Aᶜ, d x ∂ξ = 0 := by
    rw [MeasureTheory.integral_add_compl hA hd, hd0]
  have hpos : 0 ≤ ∫ x in A, d x ∂ξ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hA] with x hx
    exact hx
  have habsA : ∫ x in A, |d x| ∂ξ = ∫ x in A, d x ∂ξ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hA] with x hx
    rw [abs_of_nonneg]
    exact hx
  have habsAc : ∫ x in Aᶜ, |d x| ∂ξ = -(∫ x in Aᶜ, d x ∂ξ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hA.compl] with x hx
    change ¬ 0 ≤ d x at hx
    rw [not_le] at hx
    rw [abs_of_neg hx]
  have habs : ∫ x, |d x| ∂ξ = 2 * ∫ x in A, d x ∂ξ := by
    rw [← MeasureTheory.integral_add_compl hA hd.abs, habsA, habsAc]
    linarith
  have hgap : μ.real A - ν.real A = ∫ x in A, d x ∂ξ := by
    rw [show d = fun x => p x - q x from rfl,
      integral_sub hp.integrableOn hq.integrableOn,
      show p = fun x => (μ.rnDeriv ξ x).toReal from rfl,
      show q = fun x => (ν.rnDeriv ξ x).toReal from rfl,
      Measure.setIntegral_toReal_rnDeriv hμξ,
      Measure.setIntegral_toReal_rnDeriv hνξ]
  have htv := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := μ) (ν := ν) hA
  rw [hgap, abs_of_nonneg hpos] at htv
  change (1 / 2 : ℝ) * ∫ x, |d x| ∂ξ ≤ _
  rw [habs]
  linarith

-- @node: overlap_ge_exp_neg_klBudget
/-- A nonnegative finite KL budget yields the corresponding
Bretagnolle--Huber lower bound on testing overlap. -/
lemma overlap_ge_exp_neg_klBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hB : 0 ≤ B)
    (hKL : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal B) :
    (1 / 2 : ℝ) * Real.exp (-B) ≤ 1 - Causalean.Stat.tvDist μ ν := by
  have hfin : InformationTheory.klDiv μ ν ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal B ≠ ⊤) hKL
  have hKLreal : (InformationTheory.klDiv μ ν).toReal ≤ B := by
    rw [← ENNReal.toReal_ofReal hB]
    exact ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top |>.2 hKL
  calc
    (1 / 2 : ℝ) * Real.exp (-B) ≤
        (1 / 2 : ℝ) * Real.exp (-(InformationTheory.klDiv μ ν).toReal) := by
      gcongr
    _ ≤ 1 - Causalean.Stat.tvDist μ ν :=
      Causalean.Stat.bretagnolle_huber_affinity μ ν
        (InformationTheory.klDiv_ne_top_iff.mp hfin).1 hfin

-- @node: prod_one_sub_le_exp_neg_sum
/-- A product of complementary overlap probabilities is bounded by the
exponential of minus their sum. -/
lemma prod_one_sub_le_exp_neg_sum
    {M : ℕ} (ρ : Fin M → ℝ)
    (hρ1 : ∀ j, ρ j ≤ 1) :
    (∏ j, (1 - ρ j)) ≤ Real.exp (-∑ j, ρ j) := by
  calc
    (∏ j, (1 - ρ j)) ≤ ∏ j, Real.exp (-ρ j) := by
      apply Finset.prod_le_prod
      · intro j _
        linarith [hρ1 j]
      · intro j _
        linarith [Real.add_one_le_exp (-ρ j)]
    _ = Real.exp (-∑ j, ρ j) := by
      rw [← Real.exp_sum]
      congr 1
      simp

-- @node: prod_one_sub_le_exp_neg_card_mul
/-- A common coordinatewise overlap floor `c` bounds the complementary product
by `exp (-M * c)`. -/
lemma prod_one_sub_le_exp_neg_card_mul
    {M : ℕ} (ρ : Fin M → ℝ) (c : ℝ)
    (hρ1 : ∀ j, ρ j ≤ 1) (hc : ∀ j, c ≤ ρ j) :
    (∏ j, (1 - ρ j)) ≤ Real.exp (-(M : ℝ) * c) := by
  refine (prod_one_sub_le_exp_neg_sum ρ hρ1).trans ?_
  rw [Real.exp_le_exp]
  have hsum : (M : ℝ) * c ≤ ∑ j, ρ j := by
    calc
      (M : ℝ) * c = ∑ _j : Fin M, c := by simp
      _ ≤ ∑ j, ρ j := Finset.sum_le_sum (fun j _ => hc j)
  linarith

-- @node: tvDist_eq_zero_of_klBudget_nonpos
/-- A nonpositive real KL budget forces two probability measures to coincide,
and hence forces their total variation distance to vanish. -/
lemma tvDist_eq_zero_of_klBudget_nonpos
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (hB : B ≤ 0)
    (hKL : InformationTheory.klDiv μ ν ≤ ENNReal.ofReal B) :
    Causalean.Stat.tvDist μ ν = 0 := by
  have hKL0 : InformationTheory.klDiv μ ν = 0 := by
    apply le_antisymm
    · simpa [ENNReal.ofReal_eq_zero.mpr hB] using hKL
    · exact bot_le
  have hmeasure : μ = ν := InformationTheory.klDiv_eq_zero_iff.mp hKL0
  subst ν
  simp [Causalean.Stat.tvDist]

-- @node: card_mul_exp_neg_log_eq_rpow
/-- The exponential KL-overlap floor has the expected power-law scaling after
multiplication by the number of coordinates. -/
lemma card_mul_exp_neg_log_eq_rpow
    {M : ℕ} (hM : 1 ≤ M) (κ : ℝ) :
    (M : ℝ) * ((1 / 2 : ℝ) * Real.exp (-(κ * Real.log M))) =
      (M : ℝ) ^ (1 - κ) / 2 := by
  have hMr : (0 : ℝ) < M := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  rw [Real.rpow_def_of_pos hMr]
  rw [show Real.log (M : ℝ) * (1 - κ) =
      Real.log (M : ℝ) + -(κ * Real.log (M : ℝ)) by ring,
    Real.exp_add, Real.exp_log hMr]
  ring

-- @node: coordinateOverlap_product_le_of_nonnegative_kl
/-- Under a nonnegative logarithmic KL budget, the product of coordinatewise
total-variation factors has the finite-`M` exponential bound. -/
lemma coordinateOverlap_product_le_of_nonnegative_kl
    {M : ℕ} (hM : 1 ≤ M)
    {Z S : Fin M → Type*}
    [∀ j, MeasurableSpace (Z j)] [∀ j, MeasurableSpace (S j)]
    (Q : ∀ j, Bool → Measure (Z j)) [∀ j b, IsProbabilityMeasure (Q j b)]
    (compress : ∀ j, Z j → S j) (hcompress : ∀ j, Measurable (compress j))
    {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hKL : ∀ j,
      InformationTheory.klDiv
        (compressedCoordinateLaw (compress j) (Q j false))
        (compressedCoordinateLaw (compress j) (Q j true)) ≤
          ENNReal.ofReal (κ * Real.log M)) :
    (∏ j, (1 - coordinateOverlap Q compress j)) ≤
      Real.exp (-((M : ℝ) ^ (1 - κ)) / 2) := by
  letI mapProb (j : Fin M) (b : Bool) :
      IsProbabilityMeasure (compressedCoordinateLaw (compress j) (Q j b)) :=
    Measure.isProbabilityMeasure_map (hcompress j).aemeasurable
  have hlog : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  have hover_le_one : ∀ j, coordinateOverlap Q compress j ≤ 1 := by
    intro j
    unfold coordinateOverlap
    linarith [Causalean.Stat.tvDist_nonneg (μ := compressedCoordinateLaw
      (compress j) (Q j false)) (ν := compressedCoordinateLaw
      (compress j) (Q j true))]
  have hover_floor : ∀ j,
      (1 / 2 : ℝ) * Real.exp (-(κ * Real.log M)) ≤
        coordinateOverlap Q compress j := by
    intro j
    exact overlap_ge_exp_neg_klBudget _ _ (mul_nonneg hκ0 hlog) (hKL j)
  have hprod := prod_one_sub_le_exp_neg_card_mul
    (fun j => coordinateOverlap Q compress j)
    ((1 / 2 : ℝ) * Real.exp (-(κ * Real.log M)))
    hover_le_one hover_floor
  rw [show -(M : ℝ) * ((1 / 2 : ℝ) * Real.exp (-(κ * Real.log M))) =
      -((M : ℝ) * ((1 / 2 : ℝ) * Real.exp (-(κ * Real.log M)))) by ring,
    card_mul_exp_neg_log_eq_rpow hM κ] at hprod
  simpa only [neg_div] using hprod

-- @node: ennreal_error_lower_bound_of_success_upper_bound
/-- A real-valued product bound below one converts an ENNReal simultaneous
success upper bound into the complementary error lower bound. -/
lemma ennreal_error_lower_bound_of_success_upper_bound
    {s : ℝ≥0∞} {p e : ℝ}
    (hp0 : 0 ≤ p) (he1 : e ≤ 1) (hpe : p ≤ e)
    (hs : s ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (1 + p))) :
    ENNReal.ofReal ((1 / 2 : ℝ) * (1 - e)) ≤ 1 - s := by
  have ht : 0 ≤ (1 / 2 : ℝ) * (1 - e) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr he1)
  have hu : 0 ≤ (1 / 2 : ℝ) * (1 + p) :=
    mul_nonneg (by norm_num) (by linarith)
  apply ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs)
  calc
    ENNReal.ofReal ((1 / 2 : ℝ) * (1 - e)) + s ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * (1 - e)) +
          ENNReal.ofReal ((1 / 2 : ℝ) * (1 + p)) := add_le_add_right hs _
    _ = ENNReal.ofReal
        ((1 / 2 : ℝ) * (1 - e) + (1 / 2 : ℝ) * (1 + p)) :=
      (ENNReal.ofReal_add ht hu).symm
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by linarith)
    _ = 1 := ENNReal.ofReal_one

-- @node: lem:coordinatewise-overlap-direct-product
/-- **Coordinatewise-overlap direct-product bound.**  In a conditionally independent hypercube
experiment with [at least one coordinate](hyp:hM), [per-coordinate candidate laws `Q j`, indexed
by a bit](hyp:Q), [a per-coordinate compression map `compress`](hyp:compress) that
[is measurable at every coordinate](hyp:hcompress), and [per-coordinate decoders `decoder` built
from the compressed local summary, the other coordinates' raw data, and shared
randomness](hyp:decoder) that [are jointly measurable](hyp:hdecoder) and [depend on the raw
sample at coordinate `j` only through its compressed summary, not directly on the raw value at
`j`](hyp:hlocal), then [decentralized coordinate decoders cannot on average be correct more
often than the common-part product bound built from the per-coordinate total-variation overlaps;
and if every compressed adjacent KL divergence is at most `κ log M`, the displayed finite-`M`
simultaneous-error certificate follows](goal). -/
lemma coordinatewise_overlap_direct_product
    {M : ℕ} (hM : 1 ≤ M)
    {Z S : Fin M → Type*} {A : Type*}
    [∀ j, MeasurableSpace (Z j)] [∀ j, StandardBorelSpace (Z j)]
    [∀ j, MeasurableSpace (S j)] [∀ j, StandardBorelSpace (S j)]
    [MeasurableSpace A] [StandardBorelSpace A]
    (Q : ∀ j, Bool → Measure (Z j)) (R : Measure A)
    [∀ j b, IsProbabilityMeasure (Q j b)] [IsProbabilityMeasure R]
    (compress : ∀ j, Z j → S j) (hcompress : ∀ j, Measurable (compress j))
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool)
    (hdecoder : ∀ j, Measurable
      (fun p : S j × ((k : Fin M) → Z k) × A => decoder j p.1 p.2.1 p.2.2))
    (hlocal : ∀ j s z z' a,
      (∀ k, k ≠ j → z k = z' k) → decoder j s z a = decoder j s z' a) :
    coordinatewiseSuccessProbability Q R compress decoder ≤
        ENNReal.ofReal
          ((1 / 2 : ℝ) *
            (1 + ∏ j, (1 - coordinateOverlap Q compress j))) ∧
      ∀ κ : ℝ, κ < 1 →
        (∀ j,
          InformationTheory.klDiv
            (compressedCoordinateLaw (compress j) (Q j false))
            (compressedCoordinateLaw (compress j) (Q j true)) ≤
              ENNReal.ofReal (κ * Real.log M)) →
        ENNReal.ofReal
            ((1 / 2 : ℝ) *
              (1 - Real.exp (-((M : ℝ) ^ (1 - κ)) / 2))) ≤
          1 - coordinatewiseSuccessProbability Q R compress decoder := by
  letI mapProb (j : Fin M) (b : Bool) :
      IsProbabilityMeasure (compressedCoordinateLaw (compress j) (Q j b)) :=
    Measure.isProbabilityMeasure_map (hcompress j).aemeasurable
  have hmain :
      coordinatewiseSuccessProbability Q R compress decoder ≤
        ENNReal.ofReal
          ((1 / 2 : ℝ) *
            (1 + ∏ j, (1 - coordinateOverlap Q compress j))) := by
    classical
    let gamma : ∀ j, Measure (Z j × Z j) := fun j =>
      compressionCoupling (Q j false) (Q j true) (compress j) (hcompress j)
    let Gamma : Measure ((j : Fin M) → Z j × Z j) := Measure.pi gamma
    let selected (omega : Fin M → Bool) :
        ((j : Fin M) → Z j × Z j) → ((j : Fin M) → Z j) :=
      fun z => selectCoupledRaw omega z
    have hcoord (omega : Fin M → Bool) (j : Fin M) :
        MeasurePreserving
          (fun p : Z j × Z j => if omega j then p.2 else p.1)
          (gamma j) (Q j (omega j)) := by
      cases hbit : omega j
      · constructor
        · simpa [hbit] using (measurable_fst : Measurable (Prod.fst : Z j × Z j → Z j))
        · simpa [gamma, hbit] using
            compressionCoupling_map_fst (Q j false) (Q j true)
              (compress j) (hcompress j)
      · constructor
        · simpa [hbit] using (measurable_snd : Measurable (Prod.snd : Z j × Z j → Z j))
        · simpa [gamma, hbit] using
            compressionCoupling_map_snd (Q j false) (Q j true)
              (compress j) (hcompress j)
    have hselected (omega : Fin M → Bool) :
        MeasurePreserving (selected omega) Gamma
          (Measure.pi fun j => Q j (omega j)) := by
      exact measurePreserving_pi gamma (fun j => Q j (omega j)) (hcoord omega)
    have htargetMeas (omega : Fin M → Bool) : MeasurableSet
        {data : A × ((j : Fin M) → Z j) | ∀ j,
          decoder j (compress j (data.2 j)) data.2 data.1 = omega j} := by
      rw [show {data : A × ((j : Fin M) → Z j) | ∀ j,
          decoder j (compress j (data.2 j)) data.2 data.1 = omega j} =
          ⋂ j, {data | decoder j (compress j (data.2 j)) data.2 data.1 = omega j} by
        ext data; simp]
      apply MeasurableSet.iInter
      intro j
      apply measurableSet_eq_fun _ measurable_const
      have hm := (hdecoder j).comp
        (((hcompress j).comp ((measurable_pi_apply j).comp measurable_snd)).prodMk
          (measurable_snd.prodMk measurable_fst))
      simpa only [Function.comp_def] using hm
    have hmeasure (omega : Fin M → Bool) :
        (R.prod (Measure.pi fun j => Q j (omega j)))
            {data | ∀ j,
              decoder j (compress j (data.2 j)) data.2 data.1 = omega j} =
          (R.prod Gamma)
            {data | coupledDecoderGood compress decoder omega data.2 data.1} := by
      let mp := (MeasurePreserving.id R).prod (hselected omega)
      have happ := Measure.map_apply (μ := R.prod Gamma) mp.measurable (htargetMeas omega)
      rw [mp.map_eq] at happ
      rw [happ]
      congr 1
    have hsourceMeas (omega : Fin M → Bool) : MeasurableSet
        {data : A × ((j : Fin M) → Z j × Z j) |
          coupledDecoderGood compress decoder omega data.2 data.1} := by
      exact (htargetMeas omega).preimage
        (measurable_id.prodMap (hselected omega).measurable)
    have hindMeas (omega : Fin M → Bool) : Measurable
        (fun data : A × ((j : Fin M) → Z j × Z j) =>
          coupledGoodIndicator compress decoder omega data.2 data.1) := by
      let E : Set (A × ((j : Fin M) → Z j × Z j)) :=
        {data | coupledDecoderGood compress decoder omega data.2 data.1}
      rw [show (fun data : A × ((j : Fin M) → Z j × Z j) =>
          coupledGoodIndicator compress decoder omega data.2 data.1) =
          E.indicator (fun _ => (1 : ℝ≥0∞)) by
        funext data
        by_cases hgood : coupledDecoderGood compress decoder omega data.2 data.1 <;>
          simp [coupledGoodIndicator, E, hgood]]
      exact measurable_const.indicator (hsourceMeas omega)
    have hindicator (omega : Fin M → Bool) :
        ∫⁻ data, coupledGoodIndicator compress decoder omega data.2 data.1
            ∂(R.prod Gamma) =
          (R.prod Gamma)
            {data | coupledDecoderGood compress decoder omega data.2 data.1} := by
      let E : Set (A × ((j : Fin M) → Z j × Z j)) :=
        {data | coupledDecoderGood compress decoder omega data.2 data.1}
      have hE : MeasurableSet E := hsourceMeas omega
      rw [← setLIntegral_one E]
      rw [← lintegral_indicator hE]
      apply lintegral_congr
      intro data
      by_cases hgood : coupledDecoderGood compress decoder omega data.2 data.1 <;>
        simp [coupledGoodIndicator, E, hgood]
    let N : Set ((j : Fin M) → Z j × Z j) :=
      {z | ∀ j, compress j (z j).1 ≠ compress j (z j).2}
    have hNj (j : Fin M) : MeasurableSet
        {p : Z j × Z j | compress j p.1 ≠ compress j p.2} := by
      letI : MeasurableEq (S j) := measurableEqOfStandardBorel (S j)
      exact (measurableSet_eq_fun ((hcompress j).comp measurable_fst)
        ((hcompress j).comp measurable_snd)).compl
    have hN : MeasurableSet N := by
      rw [show N = Set.univ.pi fun j =>
          {p : Z j × Z j | compress j p.1 ≠ compress j p.2} by
        ext z; simp [N]]
      exact MeasurableSet.univ_pi hNj
    have hgammaN (j : Fin M) : gamma j
        {p : Z j × Z j | compress j p.1 ≠ compress j p.2} ≤
          ENNReal.ofReal (Causalean.Stat.tvDist
            (compressedCoordinateLaw (compress j) (Q j false))
            (compressedCoordinateLaw (compress j) (Q j true))) := by
      have heq := compressionCoupling_equal_compression_mass_ge
        (Q j false) (Q j true) (compress j) (hcompress j)
      have hEqMeas : MeasurableSet
          {p : Z j × Z j | compress j p.1 = compress j p.2} := by
        letI : MeasurableEq (S j) := measurableEqOfStandardBorel (S j)
        exact measurableSet_eq_fun ((hcompress j).comp measurable_fst)
          ((hcompress j).comp measurable_snd)
      have hcompl := tsub_le_tsub_left heq 1
      rw [show {p : Z j × Z j | compress j p.1 ≠ compress j p.2} =
          {p : Z j × Z j | compress j p.1 = compress j p.2}ᶜ by ext; simp,
        measure_compl hEqMeas (measure_ne_top (gamma j) _), measure_univ]
      calc
        1 - gamma j {p : Z j × Z j | compress j p.1 = compress j p.2} ≤
            1 - ENNReal.ofReal (1 - Causalean.Stat.tvDist
              (compressedCoordinateLaw (compress j) (Q j false))
              (compressedCoordinateLaw (compress j) (Q j true))) := by
          simpa [gamma, compressedCoordinateLaw] using hcompl
        _ = ENNReal.ofReal (Causalean.Stat.tvDist
              (compressedCoordinateLaw (compress j) (Q j false))
              (compressedCoordinateLaw (compress j) (Q j true))) := by
          rw [← ENNReal.ofReal_one,
            ← ENNReal.ofReal_sub (1 : ℝ) (by
              exact sub_nonneg.mpr Causalean.Stat.tvDist_le_one)]
          congr 1
          ring
    have hGammaN : Gamma N ≤ ENNReal.ofReal
        (∏ j, Causalean.Stat.tvDist
          (compressedCoordinateLaw (compress j) (Q j false))
          (compressedCoordinateLaw (compress j) (Q j true))) := by
      change (Measure.pi gamma) N ≤ _
      rw [show N = Set.univ.pi fun j =>
        {p : Z j × Z j | compress j p.1 ≠ compress j p.2} by
          ext z; simp [N], Measure.pi_pi]
      calc
        (∏ j, gamma j {p : Z j × Z j | compress j p.1 ≠ compress j p.2}) ≤
            ∏ j, ENNReal.ofReal (Causalean.Stat.tvDist
              (compressedCoordinateLaw (compress j) (Q j false))
              (compressedCoordinateLaw (compress j) (Q j true))) :=
          Finset.prod_le_prod (fun _ _ => bot_le) (fun j _ => hgammaN j)
        _ = _ := by
          rw [ENNReal.ofReal_prod_of_nonneg]
          exact fun j _ => Causalean.Stat.tvDist_nonneg
    have hpoint (data : A × ((j : Fin M) → Z j × Z j)) :
        (∑ omega : Fin M → Bool,
          coupledGoodIndicator compress decoder omega data.2 data.1) ≤
        (2 : ℝ≥0∞) ^ M / 2 * (1 + N.indicator (fun _ => (1 : ℝ≥0∞)) data.2) := by
      by_cases hz : data.2 ∈ N
      · have htriv : (∑ omega : Fin M → Bool,
            coupledGoodIndicator compress decoder omega data.2 data.1) ≤
            (2 : ℝ≥0∞) ^ M := by
          calc
            _ ≤ ∑ _omega : Fin M → Bool, (1 : ℝ≥0∞) :=
              Finset.sum_le_sum fun omega _ => by
                by_cases hg : coupledDecoderGood compress decoder omega data.2 data.1 <;>
                  simp [coupledGoodIndicator, hg]
            _ = _ := by simp
        have hcancel : (2 : ℝ≥0∞) ^ M / 2 * (1 + 1) = (2 : ℝ≥0∞) ^ M := by
          rw [one_add_one_eq_two, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
        simpa [Set.indicator_of_mem hz, hcancel] using htriv
      · have hz' : ¬ ∀ j, compress j (data.2 j).1 ≠ compress j (data.2 j).2 := by
          simpa [N] using hz
        push_neg at hz'
        obtain ⟨j, hj⟩ := hz'
        have hhalf := coupledDecoderGood_count_le_half compress decoder hlocal
          data.2 data.1 j hj
        simpa [Set.indicator, hz] using hhalf
    have hsumMeasure :
        (∑ omega : Fin M → Bool,
          (R.prod (Measure.pi fun j => Q j (omega j)))
            {data | ∀ j,
              decoder j (compress j (data.2 j)) data.2 data.1 = omega j}) ≤
        (2 : ℝ≥0∞) ^ M / 2 * (1 + Gamma N) := by
      have hIndIntegral :
          (∫⁻ data : A × ((j : Fin M) → Z j × Z j),
            N.indicator (fun _ => (1 : ℝ≥0∞)) data.2 ∂(R.prod Gamma)) = Gamma N := by
        rw [show (fun data : A × ((j : Fin M) → Z j × Z j) =>
            N.indicator (fun _ => (1 : ℝ≥0∞)) data.2) =
            (Set.univ ×ˢ N).indicator (fun _ => (1 : ℝ≥0∞)) by
          funext data
          by_cases hz : data.2 ∈ N <;> simp [Set.indicator, hz]]
        rw [lintegral_indicator_const (MeasurableSet.univ.prod hN)]
        rw [Measure.prod_apply (MeasurableSet.univ.prod hN)]
        simp
      simp_rw [hmeasure, ← hindicator]
      rw [← lintegral_finset_sum Finset.univ (fun omega _ => hindMeas omega)]
      calc
        _ ≤ ∫⁻ data, (2 : ℝ≥0∞) ^ M / 2 *
            (1 + N.indicator (fun _ => (1 : ℝ≥0∞)) data.2) ∂(R.prod Gamma) :=
          lintegral_mono hpoint
        _ = (2 : ℝ≥0∞) ^ M / 2 * (1 + Gamma N) := by
          rw [lintegral_const_mul]
          · rw [lintegral_add_left measurable_const]
            rw [lintegral_const, measure_univ, hIndIntegral]
            simp
          · exact measurable_const.fun_add
              ((measurable_const.indicator hN).comp measurable_snd)
    unfold coordinatewiseSuccessProbability
    have hprodReal : 0 ≤ ∏ j, Causalean.Stat.tvDist
        (compressedCoordinateLaw (compress j) (Q j false))
        (compressedCoordinateLaw (compress j) (Q j true)) :=
      Finset.prod_nonneg fun j _ => Causalean.Stat.tvDist_nonneg
    calc
      _ ≤ ((2 : ℝ≥0∞) ^ M / 2 * (1 + Gamma N)) / (2 : ℝ≥0∞) ^ M :=
        ENNReal.div_le_div_right hsumMeasure _
      _ ≤ ((2 : ℝ≥0∞) ^ M / 2 *
          (1 + ENNReal.ofReal (∏ j, Causalean.Stat.tvDist
            (compressedCoordinateLaw (compress j) (Q j false))
            (compressedCoordinateLaw (compress j) (Q j true))))) /
          (2 : ℝ≥0∞) ^ M := by gcongr
      _ = ENNReal.ofReal ((1 / 2 : ℝ) *
          (1 + ∏ j, (1 - coordinateOverlap Q compress j))) := by
        rw [show (∏ j, (1 - coordinateOverlap Q compress j)) =
            ∏ j, Causalean.Stat.tvDist
              (compressedCoordinateLaw (compress j) (Q j false))
              (compressedCoordinateLaw (compress j) (Q j true)) by
          simp [coordinateOverlap]]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hprodReal]
        have ha0 : (2 : ℝ≥0∞) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
        have hatop : (2 : ℝ≥0∞) ^ M ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
        calc
          ((2 : ℝ≥0∞) ^ M / 2 *
              (1 + ENNReal.ofReal (∏ j, Causalean.Stat.tvDist
                (compressedCoordinateLaw (compress j) (Q j false))
                (compressedCoordinateLaw (compress j) (Q j true))))) /
              (2 : ℝ≥0∞) ^ M =
            (((1 + ENNReal.ofReal (∏ j, Causalean.Stat.tvDist
                (compressedCoordinateLaw (compress j) (Q j false))
                (compressedCoordinateLaw (compress j) (Q j true)))) / 2) *
              (2 : ℝ≥0∞) ^ M) / (2 : ℝ≥0∞) ^ M := by
                congr 1
                simp only [div_eq_mul_inv]
                ac_rfl
          _ = (1 + ENNReal.ofReal (∏ j, Causalean.Stat.tvDist
                (compressedCoordinateLaw (compress j) (Q j false))
                (compressedCoordinateLaw (compress j) (Q j true)))) / 2 :=
            ENNReal.mul_div_cancel_right ha0 hatop
          _ = (2 : ℝ≥0∞)⁻¹ *
              (1 + ENNReal.ofReal (∏ j, Causalean.Stat.tvDist
                (compressedCoordinateLaw (compress j) (Q j false))
                (compressedCoordinateLaw (compress j) (Q j true)))) := by
            simp only [div_eq_mul_inv]
            ac_rfl
          _ = ENNReal.ofReal (1 / 2 : ℝ) *
              (ENNReal.ofReal 1 + ENNReal.ofReal (∏ j, Causalean.Stat.tvDist
                (compressedCoordinateLaw (compress j) (Q j false))
                (compressedCoordinateLaw (compress j) (Q j true)))) := by
            have hhalfOfReal : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
              rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
                ENNReal.ofReal_inv_of_pos (by norm_num)]
              norm_num
            rw [hhalfOfReal]
            simp
  refine ⟨hmain, ?_⟩
  intro κ hκ hKL
  let p : ℝ := ∏ j, (1 - coordinateOverlap Q compress j)
  let e : ℝ := Real.exp (-((M : ℝ) ^ (1 - κ)) / 2)
  have hp0 : 0 ≤ p := by
    rw [show p = ∏ j, Causalean.Stat.tvDist
        (compressedCoordinateLaw (compress j) (Q j false))
        (compressedCoordinateLaw (compress j) (Q j true)) by
      simp [p, coordinateOverlap]]
    exact Finset.prod_nonneg fun j _ => Causalean.Stat.tvDist_nonneg
  have he1 : e ≤ 1 := by
    change Real.exp (-((M : ℝ) ^ (1 - κ)) / 2) ≤ 1
    rw [Real.exp_le_one_iff]
    have hpow : 0 ≤ (M : ℝ) ^ (1 - κ) := Real.rpow_nonneg (by positivity) _
    linarith
  have hpe : p ≤ e := by
    by_cases hκ0 : 0 ≤ κ
    · exact coordinateOverlap_product_le_of_nonnegative_kl hM Q compress hcompress
        hκ0 hKL
    · have hlog : 0 ≤ Real.log (M : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hM)
      have htv : ∀ j, Causalean.Stat.tvDist
          (compressedCoordinateLaw (compress j) (Q j false))
          (compressedCoordinateLaw (compress j) (Q j true)) = 0 := by
        intro j
        exact tvDist_eq_zero_of_klBudget_nonpos _ _
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hκ0) hlog) (hKL j)
      have hpzero : p = 0 := by
        have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one hM
        simp [p, coordinateOverlap, htv, Nat.ne_of_gt hMpos]
      rw [hpzero]
      positivity
  apply ennreal_error_lower_bound_of_success_upper_bound hp0 he1 hpe
  simpa only [p] using hmain

/-- Along any sequence `M_n → ∞` and for fixed `κ < 1`, the finite direct-product
certificate tends to one half. -/
lemma coordinatewise_overlap_direct_product_asymptotic
    (Mseq : ℕ → ℕ) (κ : ℝ) (hκ : κ < 1)
    (hMseq : Tendsto Mseq atTop atTop) :
    Tendsto
      (fun n => (1 / 2 : ℝ) *
        (1 - Real.exp (-(((Mseq n : ℕ) : ℝ) ^ (1 - κ)) / 2)))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hpow : Tendsto (fun n => ((Mseq n : ℝ) ^ (1 - κ))) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hκ)).comp
      (tendsto_natCast_atTop_atTop.comp hMseq)
  have hneg : Tendsto (fun n => -((Mseq n : ℝ) ^ (1 - κ)) / 2) atTop atBot := by
    exact (tendsto_neg_atTop_atBot.comp hpow).atBot_div_const (by norm_num)
  have hexp : Tendsto (fun n => Real.exp (-((Mseq n : ℝ) ^ (1 - κ)) / 2))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
  convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp)) using 1
  all_goals norm_num

end Causalean.Stat
