import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.BumpHolder

/-!
# Derivative scaling for localized packing bumps

This module records the exact iterated-Fréchet derivative formula for the
translated and rescaled bump used by the angular packing.  It is kept separate
from `BumpHolder` so the core bump module remains focused and short.
-/

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Every iterated derivative of a localized packing bump has the expected
amplitude and inverse-bandwidth scaling. -/
-- @node: localizedPackingBump_iteratedFDeriv
lemma localizedPackingBump_iteratedFDeriv (j : ℕ) (delta w : ℝ)
    (center x : Score) :
    iteratedFDeriv ℝ j (localizedPackingBump delta w center) x =
      delta • ((w⁻¹) ^ j •
        iteratedFDeriv ℝ j packingBump (w⁻¹ • (x - center))) := by
  let g : Score → ℝ := fun z => packingBump (w⁻¹ • z)
  have hg : ContDiff ℝ (j : WithTop ℕ∞) g :=
    packingBump_contDiff.of_le (WithTop.coe_le_coe.mpr le_top) |>.comp
      (by fun_prop)
  have hfun : localizedPackingBump delta w center =
      fun x => delta • g (x - center) := by
    funext y
    simp only [localizedPackingBump, g, smul_eq_mul]
  rw [hfun]
  have hgt : ContDiff ℝ (j : WithTop ℕ∞) (fun z => g (z - center)) :=
    hg.comp (by fun_prop)
  rw [iteratedFDeriv_const_smul_apply' hgt.contDiffAt]
  rw [iteratedFDeriv_comp_sub j center x]
  rw [show iteratedFDeriv ℝ j g = fun z => (w⁻¹) ^ j •
      iteratedFDeriv ℝ j packingBump (w⁻¹ • z) by
    exact iteratedFDeriv_comp_const_smul w⁻¹
      (packingBump_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))]

/-- The derivative scaling formula transfers every global normalized-bump
bound to a localized bump with the exact amplitude and bandwidth factors. -/
-- @node: localizedPackingBump_iteratedFDeriv_bound
lemma localizedPackingBump_iteratedFDeriv_bound (j : ℕ) (delta : ℝ)
    {w : ℝ} (hw : 0 < w) (center x : Score) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖iteratedFDeriv ℝ j (localizedPackingBump delta w center) x‖ ≤
        |delta| * (w⁻¹) ^ j * C := by
  rcases packingBump_iteratedFDeriv_bound j with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  rw [localizedPackingBump_iteratedFDeriv, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hw]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hC (w⁻¹ • (x - center)))
      (mul_nonneg (abs_nonneg delta) (pow_nonneg (inv_nonneg.mpr hw.le) j))

/-- The top derivative of a localized bump inherits the normalized bump's
Hölder modulus after translating and rescaling both arguments. -/
-- @node: localizedPackingBump_iteratedFDeriv_holder
lemma localizedPackingBump_iteratedFDeriv_holder (s delta : ℝ) (hs : 0 < s)
    {w : ℝ} (hw : 0 < w) (center x y : Score) :
    let k := ⌈s⌉₊ - 1
    ∃ C : ℝ, 0 ≤ C ∧
      ‖iteratedFDeriv ℝ k (localizedPackingBump delta w center) x -
          iteratedFDeriv ℝ k (localizedPackingBump delta w center) y‖ ≤
        |delta| * (w⁻¹) ^ k *
          (C * (‖x - y‖ / w) ^ (s - (k : ℝ))) := by
  let k := ⌈s⌉₊ - 1
  rcases packingBump_iteratedFDeriv_holder s hs with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  rw [localizedPackingBump_iteratedFDeriv,
    localizedPackingBump_iteratedFDeriv, ← smul_sub, ← smul_sub,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_pow, abs_inv, abs_of_pos hw]
  have hscaled :
      ‖w⁻¹ • (x - center) - w⁻¹ • (y - center)‖ = ‖x - y‖ / w := by
    have hvec : w⁻¹ • (x - center) - w⁻¹ • (y - center) =
        w⁻¹ • (x - y) := by
      rw [← smul_sub]
      congr 1
      abel
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw,
      inv_mul_eq_div]
  have htop := hC (w⁻¹ • (x - center)) (w⁻¹ • (y - center))
  rw [hscaled] at htop
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left htop
      (mul_nonneg (abs_nonneg delta) (pow_nonneg (inv_nonneg.mpr hw.le) k))

end CausalSmith.Stat.BddUniformLogPenalty
