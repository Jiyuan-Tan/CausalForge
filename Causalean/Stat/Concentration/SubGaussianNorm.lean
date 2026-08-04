module

public import Causalean.Stat.Concentration.FiniteDimensionalNet
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Norm tails from finite directional nets

This file turns scalar sub-Gaussian bounds on a finite half-net into a tail
bound for the norm of a finite-dimensional random vector.  It also supplies a
dimension-only version by constructing a half-net in the supporting subspace.
-/

@[expose] public section

open MeasureTheory Module ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace Causalean

/-- Every nonzero vector in a subspace has a point in a finite half-net whose inner
product with that vector is at least half of its norm. -/
lemma half_norm_lt_inner_of_mem_net {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N : Finset E} {z : E} (V : Submodule ℝ E)
    (hnet : ∀ x ∈ V, ‖x‖ = 1 → ∃ v ∈ N, ‖x - v‖ ≤ (1 : ℝ) / 2)
    (hzV : z ∈ V) (hz : z ≠ 0) : ∃ v ∈ N, ‖z‖ / 2 ≤ ⟪v, z⟫ := by
  let x : E := ‖z‖⁻¹ • z
  have hxnorm : ‖x‖ = 1 := by
    simp [x, norm_smul, hz]
  obtain ⟨v, hvN, hv⟩ := hnet x (V.smul_mem _ hzV) hxnorm
  refine ⟨v, hvN, ?_⟩
  have hinner : ⟪x - v, x⟫ ≤ (1 : ℝ) / 2 := by
    calc
      ⟪x - v, x⟫ ≤ |⟪x - v, x⟫| := le_abs_self _
      _ ≤ ‖x - v‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ ((1 : ℝ) / 2) * 1 := mul_le_mul hv hxnorm.le (norm_nonneg _) (by norm_num)
      _ = (1 : ℝ) / 2 := by norm_num
  have hvx : (1 : ℝ) / 2 ≤ ⟪v, x⟫ := by
    have hid : ⟪x - v, x⟫ = 1 - ⟪v, x⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, hxnorm]
      ring
    linarith
  have hzrepr : z = ‖z‖ • x := by
    simp [x, smul_smul, hz]
  rw [hzrepr, inner_smul_right, norm_smul, hxnorm]
  simp only [mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hmul := mul_le_mul_of_nonneg_left hvx (norm_nonneg z)
  simpa [div_eq_mul_inv, mul_comm] using hmul

/-- If a finite half-net controls every scalar projection with unit sub-Gaussian parameter, then
the norm has a Gaussian upper tail. The support condition is only required almost everywhere. -/
theorem measure_norm_gt_le_of_half_net {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω)
    [IsFiniteMeasure P] (Z : Ω → E) (V : Submodule ℝ E) (N : Finset E)
    (hnet : ∀ x ∈ V, ‖x‖ = 1 → ∃ v ∈ N, ‖x - v‖ ≤ (1 : ℝ) / 2)
    (hZV : ∀ᵐ ω ∂P, Z ω ∈ V)
    (hsubg : ∀ v ∈ N, HasSubgaussianMGF (fun ω ↦ ⟪v, Z ω⟫) 1 P)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | 2 * t < ‖Z ω‖} ≤
      (N.card : ℝ) * Real.exp (-t ^ 2 / 2) := by
  let U : Set Ω := ⋃ v ∈ N, {ω | t ≤ ⟪v, Z ω⟫}
  have hAU : {ω | 2 * t < ‖Z ω‖} ≤ᵐ[P] U := by
    filter_upwards [hZV] with ω hω htail
    change 2 * t < ‖Z ω‖ at htail
    have hz : Z ω ≠ 0 := by
      intro hz
      simp [hz] at htail
      linarith
    obtain ⟨v, hvN, hv⟩ := half_norm_lt_inner_of_mem_net V hnet hω hz
    refine mem_iUnion₂.mpr ⟨v, hvN, ?_⟩
    change t ≤ ⟪v, Z ω⟫
    nlinarith
  calc
    P.real {ω | 2 * t < ‖Z ω‖} ≤ P.real U := by
      exact ENNReal.toReal_mono (measure_ne_top P U) (measure_mono_ae hAU)
    _ ≤ ∑ v ∈ N, P.real {ω | t ≤ ⟪v, Z ω⟫} :=
      measureReal_biUnion_finset_le N _
    _ ≤ ∑ _v ∈ N, Real.exp (-t ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa using (hsubg v hv).measure_ge_le ht
    _ = (N.card : ℝ) * Real.exp (-t ^ 2 / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- A random vector supported almost everywhere on a finite-dimensional subspace has a
dimension-only Gaussian norm tail when all unit projections in that subspace are sub-Gaussian. -/
theorem measure_norm_gt_le_five_pow_finrank {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P] (Z : Ω → E) (V : Submodule ℝ E)
    [FiniteDimensional ℝ V]
    (hZV : ∀ᵐ ω ∂P, Z ω ∈ V)
    (hsubg : ∀ v ∈ V, ‖v‖ = 1 →
      HasSubgaussianMGF (fun ω ↦ ⟪(v : E), Z ω⟫) 1 P)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | 2 * t < ‖Z ω‖} ≤
      ((5 ^ finrank ℝ V : ℕ) : ℝ) * Real.exp (-t ^ 2 / 2) := by
  obtain ⟨M, hMunit, hMnet, hMcard⟩ :=
    exists_half_net_card_le_five_pow_finrank V
  let e : V ↪ E := ⟨fun v ↦ (v : E), Subtype.coe_injective⟩
  let N : Finset E := M.map e
  have hNnet : ∀ x ∈ V, ‖x‖ = 1 →
      ∃ v ∈ N, ‖x - v‖ ≤ (1 : ℝ) / 2 := by
    intro x hxV hxnorm
    obtain ⟨v, hvM, hv⟩ := hMnet ⟨x, hxV⟩ (by simpa using hxnorm)
    refine ⟨v, Finset.mem_map.mpr ⟨v, hvM, rfl⟩, ?_⟩
    simpa using hv
  have hNsubg : ∀ v ∈ N,
      HasSubgaussianMGF (fun ω ↦ ⟪v, Z ω⟫) 1 P := by
    intro v hvN
    obtain ⟨w, hwM, rfl⟩ := Finset.mem_map.mp hvN
    exact hsubg (w : E) w.property (by simpa using hMunit w hwM)
  refine (measure_norm_gt_le_of_half_net P Z V N hNnet hZV hNsubg ht).trans ?_
  gcongr
  have hNcard : N.card ≤ 5 ^ finrank ℝ V := by
    simpa [N] using hMcard
  exact_mod_cast hNcard

end Causalean
