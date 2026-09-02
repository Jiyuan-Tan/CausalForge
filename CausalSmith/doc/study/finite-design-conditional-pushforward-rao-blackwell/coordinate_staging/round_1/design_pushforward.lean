import Causalean.Experimentation.DesignBased.DesignCore
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul

/-!
# Conditional means along finite-design pushforwards

This module develops finite conditional expectation along an arbitrary deterministic
coarsening of a finite randomization design. Fibers of zero design mass are totalized by a
caller-supplied default, while exact disintegration, interval preservation, and squared-loss
Rao--Blackwell contraction remain valid without uniformity, independence, surjectivity, or
full support.
-/

open scoped BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell

open Causalean.Experimentation.DesignBased

variable {Ω B V : Type*} [Fintype Ω] [Fintype B] [Fintype V]

/-- The mass of a coarsening fiber is the total probability assigned by the finite design to
source points mapped to the requested coarsened value. -/
noncomputable def fiberMass (D : FiniteDesign Ω) (φ : Ω → B) (b : B) : ℝ :=
  by
    classical
    exact ∑ ω, if φ ω = b then D.p ω else 0

/-- [A coarsening fiber's total design mass equals the probability of its value under the
pushforward design](goal). -/
theorem fiberMass_eq_map_p (D : FiniteDesign Ω) (φ : Ω → B) (b : B) :
    fiberMass D φ b = (D.map φ).p b := by
  classical
  rfl

/-- [Every coarsening fiber has nonnegative design mass](goal). -/
theorem fiberMass_nonneg (D : FiniteDesign Ω) (φ : Ω → B) (b : B) :
    0 ≤ fiberMass D φ b := by
  rw [fiberMass_eq_map_p]
  exact (D.map φ).p_nonneg b

/-- [The masses of all coarsening fibers sum to one](goal). -/
theorem fiberMass_sum (D : FiniteDesign Ω) (φ : Ω → B) :
    ∑ b, fiberMass D φ b = 1 := by
  simp only [fiberMass_eq_map_p]
  exact (D.map φ).p_sum

/-- The weighted numerator on a fiber is the sum of each matching source value multiplied by
its design probability. -/
noncomputable def fiberNumerator (D : FiniteDesign Ω) (φ : Ω → B)
    (h : Ω → V → ℝ) (b : B) (v : V) : ℝ :=
  by
    classical
    exact ∑ ω, if φ ω = b then D.p ω * h ω v else 0

/-- A source point receives its design probability divided by its fiber mass on a nonnull
matching fiber, and receives zero otherwise. -/
noncomputable def conditionalFiberWeight (D : FiniteDesign Ω) (φ : Ω → B)
    (b : B) (ω : Ω) : ℝ :=
  by
    classical
    exact if fiberMass D φ b = 0 then 0
      else if φ ω = b then D.p ω / fiberMass D φ b else 0

/-- [Conditional fiber weights are nonnegative on both positive-mass and null fibers](goal). -/
theorem conditionalFiberWeight_nonneg (D : FiniteDesign Ω) (φ : Ω → B)
    (b : B) (ω : Ω) :
    0 ≤ conditionalFiberWeight D φ b ω := by
  classical
  unfold conditionalFiberWeight
  by_cases hb : fiberMass D φ b = 0
  · simp [hb]
  by_cases hω : φ ω = b
  · simp only [hb, hω, if_false, if_true]
    exact div_nonneg (D.p_nonneg ω) (fiberMass_nonneg D φ b)
  · simp [hb, hω]

/-- [When the requested fiber has nonzero mass](hyp:hb), [its conditional weights sum to
one](goal). -/
theorem sum_conditionalFiberWeight_eq_one (D : FiniteDesign Ω) (φ : Ω → B)
    (b : B) (hb : fiberMass D φ b ≠ 0) :
    ∑ ω, conditionalFiberWeight D φ b ω = 1 := by
  classical
  simp only [conditionalFiberWeight, hb, if_false]
  calc
    (∑ ω, if φ ω = b then D.p ω / fiberMass D φ b else 0) =
        ∑ ω, (if φ ω = b then D.p ω else 0) * (fiberMass D φ b)⁻¹ := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : φ ω = b <;> simp [hω, div_eq_mul_inv]
    _ = fiberMass D φ b * (fiberMass D φ b)⁻¹ := by
      rw [← Finset.sum_mul]
      rfl
    _ = 1 := mul_inv_cancel₀ hb

/-- [If a fiber has zero design mass](hyp:hb) and [a source point maps into that
fiber](hyp:hω), [the source point itself has zero design probability](goal). -/
theorem p_eq_zero_of_mem_fiberMass_eq_zero (D : FiniteDesign Ω) (φ : Ω → B)
    (b : B) (hb : fiberMass D φ b = 0) (ω : Ω) (hω : φ ω = b) :
    D.p ω = 0 := by
  classical
  unfold fiberMass at hb
  have hnonneg : ∀ x ∈ Finset.univ,
      0 ≤ if φ x = b then D.p x else 0 := by
    intro x _
    by_cases hx : φ x = b <;> simp [hx, D.p_nonneg x]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hb
  simpa [hω] using hzero ω (Finset.mem_univ ω)

/-- [If a fiber has zero design mass](hyp:hb), [the design-weighted numerator of every
real-valued source function vanishes on that fiber](goal). -/
theorem fiberNumerator_eq_zero_of_fiberMass_eq_zero
    (D : FiniteDesign Ω) (φ : Ω → B) (h : Ω → V → ℝ)
    (b : B) (v : V) (hb : fiberMass D φ b = 0) :
    fiberNumerator D φ h b v = 0 := by
  classical
  unfold fiberNumerator
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : φ ω = b
  · simp [hω, p_eq_zero_of_mem_fiberMass_eq_zero D φ b hb ω hω]
  · simp [hω]

/-- The conditional mean along a deterministic coarsening is the design-weighted fiber mean,
with a supplied default returned exactly on zero-mass fibers. -/
noncomputable def conditionalMeanAlongMap (D : FiniteDesign Ω) (φ : Ω → B)
    (d : ℝ) (h : Ω → V → ℝ) (b : B) (v : V) : ℝ :=
  if fiberMass D φ b = 0 then d
  else fiberNumerator D φ h b v / fiberMass D φ b

/-- [On a zero-mass fiber](hyp:hb), [the guarded conditional mean equals its supplied
default](goal). -/
theorem conditionalMeanAlongMap_of_fiberMass_eq_zero
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ) (h : Ω → V → ℝ)
    (b : B) (v : V) (hb : fiberMass D φ b = 0) :
    conditionalMeanAlongMap D φ d h b v = d := by
  simp [conditionalMeanAlongMap, hb]

/-- [On a nonzero-mass fiber](hyp:hb), [the guarded conditional mean equals the source-value
average under the normalized conditional fiber weights](goal). -/
theorem conditionalMeanAlongMap_eq_sum_conditionalFiberWeight
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ) (h : Ω → V → ℝ)
    (b : B) (v : V) (hb : fiberMass D φ b ≠ 0) :
    conditionalMeanAlongMap D φ d h b v =
      ∑ ω, conditionalFiberWeight D φ b ω * h ω v := by
  classical
  simp only [conditionalMeanAlongMap, hb, if_false, fiberNumerator,
    conditionalFiberWeight]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : φ ω = b <;> simp [hω, div_eq_mul_inv]
  ring

/-- [The original design-weighted sum equals the sum of each fiber mass times its guarded
conditional mean, with null fibers contributing zero regardless of the default](goal). -/
theorem sum_fiberMass_mul_conditionalMeanAlongMap
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ)
    (h : Ω → V → ℝ) (v : B → V) :
    ∑ b, fiberMass D φ b * conditionalMeanAlongMap D φ d h b (v b) =
      ∑ ω, D.p ω * h ω (v (φ ω)) := by
  classical
  calc
    ∑ b, fiberMass D φ b * conditionalMeanAlongMap D φ d h b (v b) =
        ∑ b, fiberNumerator D φ h b (v b) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : fiberMass D φ b = 0
      · rw [conditionalMeanAlongMap_of_fiberMass_eq_zero D φ d h b (v b) hb,
          hb, zero_mul, fiberNumerator_eq_zero_of_fiberMass_eq_zero D φ h b (v b) hb]
      · simp only [conditionalMeanAlongMap, hb, if_false]
        field_simp
    _ = ∑ ω, D.p ω * h ω (v (φ ω)) := by
      unfold fiberNumerator
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      simp

/-- [The pushforward expectation of the guarded conditional mean equals the original-design
expectation of the source value evaluated at the covariate selected by its coarsening](goal). -/
theorem E_map_conditionalMeanAlongMap
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ)
    (h : Ω → V → ℝ) (v : B → V) :
    (D.map φ).E (fun b => conditionalMeanAlongMap D φ d h b (v b)) =
      D.E (fun ω => h ω (v (φ ω))) := by
  simpa only [FiniteDesign.E, ← fiberMass_eq_map_p] using
    sum_fiberMass_mul_conditionalMeanAlongMap D φ d h v

/-- [Composing the guarded conditional mean with the coarsening has the same expectation under
the original design as the corresponding source value](goal). -/
theorem E_conditionalMeanAlongMap_comp
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ)
    (h : Ω → V → ℝ) (v : B → V) :
    D.E (fun ω => conditionalMeanAlongMap D φ d h (φ ω) (v (φ ω))) =
      D.E (fun ω => h ω (v (φ ω))) := by
  rw [← D.E_map φ (fun b => conditionalMeanAlongMap D φ d h b (v b))]
  exact E_map_conditionalMeanAlongMap D φ d h v

/-- [If the default lies in a fixed closed interval](hyp:hd) and [every source value lies in
that interval](hyp:hh), [the guarded conditional mean also lies in the interval](goal). -/
theorem conditionalMeanAlongMap_mem_Icc
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ) (h : Ω → V → ℝ)
    (b : B) (v : V) {l u : ℝ} (hd : d ∈ Set.Icc l u)
    (hh : ∀ ω v, h ω v ∈ Set.Icc l u) :
    conditionalMeanAlongMap D φ d h b v ∈ Set.Icc l u := by
  classical
  by_cases hb : fiberMass D φ b = 0
  · simpa [conditionalMeanAlongMap, hb] using hd
  rw [conditionalMeanAlongMap_eq_sum_conditionalFiberWeight D φ d h b v hb]
  constructor
  · calc
      l = (∑ ω, conditionalFiberWeight D φ b ω) * l := by
        rw [sum_conditionalFiberWeight_eq_one D φ b hb, one_mul]
      _ = ∑ ω, conditionalFiberWeight D φ b ω * l := by
        rw [Finset.sum_mul]
      _ ≤ ∑ ω, conditionalFiberWeight D φ b ω * h ω v := by
        exact Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hh ω v).1
            (conditionalFiberWeight_nonneg D φ b ω)
  · calc
      ∑ ω, conditionalFiberWeight D φ b ω * h ω v ≤
          ∑ ω, conditionalFiberWeight D φ b ω * u := by
        exact Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hh ω v).2
            (conditionalFiberWeight_nonneg D φ b ω)
      _ = (∑ ω, conditionalFiberWeight D φ b ω) * u := by
        rw [Finset.sum_mul]
      _ = u := by
        rw [sum_conditionalFiberWeight_eq_one D φ b hb, one_mul]

/-- [On a nonzero-mass fiber](hyp:hb), [the squared loss of the conditional mean is at most
the conditional fiber average of the source squared losses](goal). -/
theorem conditionalMeanAlongMap_sq_le
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ)
    (h : Ω → V → ℝ) (b : B) (v : V) (t : ℝ)
    (hb : fiberMass D φ b ≠ 0) :
    (conditionalMeanAlongMap D φ d h b v - t) ^ 2 ≤
      ∑ ω, conditionalFiberWeight D φ b ω * (h ω v - t) ^ 2 := by
  classical
  rw [conditionalMeanAlongMap_eq_sum_conditionalFiberWeight D φ d h b v hb]
  have hmean :
      (∑ ω, conditionalFiberWeight D φ b ω * h ω v) - t =
        ∑ ω, conditionalFiberWeight D φ b ω * (h ω v - t) := by
    calc
      (∑ ω, conditionalFiberWeight D φ b ω * h ω v) - t =
          (∑ ω, conditionalFiberWeight D φ b ω * h ω v) -
            (∑ ω, conditionalFiberWeight D φ b ω) * t := by
        rw [sum_conditionalFiberWeight_eq_one D φ b hb, one_mul]
      _ = ∑ ω, (conditionalFiberWeight D φ b ω * h ω v -
          conditionalFiberWeight D φ b ω * t) := by
        rw [Finset.sum_mul, Finset.sum_sub_distrib]
      _ = ∑ ω, conditionalFiberWeight D φ b ω * (h ω v - t) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
  rw [hmean]
  simpa only [smul_eq_mul] using
    (show Even 2 from even_two).convexOn_pow.map_sum_le
      (fun ω _ => conditionalFiberWeight_nonneg D φ b ω)
      (sum_conditionalFiberWeight_eq_one D φ b hb)
      (fun _ _ => Set.mem_univ _)

/-- [Conditioning over the fibers of any deterministic pushforward weakly contracts
covariate-parametric squared loss under an arbitrary finite design](goal). -/
theorem E_map_conditionalMeanAlongMap_sq_le
    (D : FiniteDesign Ω) (φ : Ω → B) (d : ℝ)
    (h : Ω → V → ℝ) (v : B → V) (t : ℝ) :
    (D.map φ).E (fun b =>
        (conditionalMeanAlongMap D φ d h b (v b) - t) ^ 2) ≤
      D.E (fun ω => (h ω (v (φ ω)) - t) ^ 2) := by
  classical
  simp only [FiniteDesign.E, ← fiberMass_eq_map_p]
  rw [← sum_fiberMass_mul_conditionalMeanAlongMap D φ 0
    (fun ω v => (h ω v - t) ^ 2) v]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : fiberMass D φ b = 0
  · simp [hb]
  · apply mul_le_mul_of_nonneg_left _ (fiberMass_nonneg D φ b)
    rw [conditionalMeanAlongMap_eq_sum_conditionalFiberWeight D φ 0
      (fun ω v => (h ω v - t) ^ 2) b (v b) hb]
    exact conditionalMeanAlongMap_sq_le D φ d h b (v b) t hb

end Causalean.Stat.FiniteRaoBlackwell
