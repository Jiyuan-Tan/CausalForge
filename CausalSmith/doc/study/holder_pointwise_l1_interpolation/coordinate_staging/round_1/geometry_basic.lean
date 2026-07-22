/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation.Kernel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Hölder interpolation cube geometry

Internal implementation layer for the multivariate Hölder pointwise-to-local-mass interpolation theorem.
-/

namespace Causalean.Stat.Nonparametric.HolderInterpolation.Internal

open MeasureTheory
open scoped BigOperators Pointwise Manifold ContDiff

/- The closed coordinatewise neighbourhood is exactly the product of its
one-dimensional coordinate intervals. -/
lemma supBall_eq_pi {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    supBall x0 r = Set.univ.pi (fun i => Set.Icc (x0 i - r) (x0 i + r)) := by
  ext x
  simp only [supBall, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · have := (abs_le).mp (h i); constructor <;> linarith [this.1, this.2]
  · rw [abs_le]; have := h i; constructor <;> linarith [this.1, this.2]

/- A finite-dimensional closed coordinatewise neighbourhood is compact. -/
lemma isCompact_supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    IsCompact (supBall x0 r) := by
  rw [supBall_eq_pi]; exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- A finite-dimensional closed coordinatewise neighbourhood is measurable. -/
lemma measurableSet_supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) :
    MeasurableSet (supBall x0 r) := by
  rw [supBall_eq_pi]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- A point belongs to its own coordinatewise neighbourhood when the radius is nonnegative. -/
lemma mem_supBall_self {d : ℕ} (x0 : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    x0 ∈ supBall x0 r := by
  intro i; simp only [sub_self, abs_zero]; exact hr

/-- **Change-of-variables control of the kernel-smoothed value (Milestone 3 plumbing).**
The absolute value of the kernel-smoothed value in `u`-coordinates is bounded by the
scaled local `L¹` mass: `|∫_{[-1,1]^d} K(u) g(x0 + h•u) du| ≤ B^d · h⁻ᵈ · ∫_{supBall x0 r} |g|`.
Uses `|K| ≤ B^d`, the affine change of variables `x = x0 + h•u`, and that the image cube
`supBall x0 h ⊆ supBall x0 r` when `h ≤ r`. -/
/--The absolute value of a kernel-smoothed function is bounded by the scaled
absolute-integral mass of that function on a containing coordinatewise neighbourhood. -/
lemma smoothed_abs_le {d : ℕ} {γ M r : ℝ} {x0 : Fin d → ℝ} {S : Set (Fin d → ℝ)}
    {k : ℝ → ℝ} {B : ℝ}
    (hr : 0 < r) (hS : supBall x0 r ⊆ S)
    (hkbd : ∀ u : Fin d → ℝ, |prodKernel k d u| ≤ B ^ d)
    (g : (Fin d → ℝ) → ℝ) (hg : HolderBallStd g γ M S)
    (h : ℝ) (hh : 0 < h) (hhr : h ≤ r) :
    |∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)|
      ≤ B ^ d * (h⁻¹) ^ d * ∫ x in supBall x0 r, |g x| := by
  have hBd0 : 0 ≤ B ^ d := le_trans (abs_nonneg _) (hkbd 0)
  have hgS : ContinuousOn g S := hg.1.continuousOn
  -- The affine map `u ↦ x0 + h•u` sends the unit cube into `S`.
  have hmaps : Set.MapsTo (fun u => x0 + h • u) (supBall (0 : Fin d → ℝ) 1) S := by
    intro u hu
    apply hS
    intro i
    have huq : (x0 + h • u) i - x0 i = h * u i := by
      simp [Pi.add_apply, Pi.smul_apply]
    rw [huq, abs_mul, abs_of_pos hh]
    have hui : |u i| ≤ 1 := by simpa using hu i
    calc h * |u i| ≤ h * 1 := mul_le_mul_of_nonneg_left hui hh.le
      _ = h := mul_one h
      _ ≤ r := hhr
  have hgcomp : ContinuousOn (fun u => g (x0 + h • u)) (supBall (0 : Fin d → ℝ) 1) :=
    hgS.comp (by fun_prop : Continuous (fun u : Fin d → ℝ => x0 + h • u)).continuousOn hmaps
  have hgcomp_int : IntegrableOn (fun u => |g (x0 + h • u)|) (supBall (0 : Fin d → ℝ) 1) :=
    (hgcomp.abs).integrableOn_compact (isCompact_supBall 0 1)
  have hg_abs_int : IntegrableOn (fun x => |g x|) (supBall x0 r) :=
    ((hgS.mono hS).abs).integrableOn_compact (isCompact_supBall x0 r)
  -- Two set identities for the affine change of variables.
  have hsmul_set : h • supBall (0 : Fin d → ℝ) 1 = supBall (0 : Fin d → ℝ) h := by
    ext x
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨u, hu, rfl⟩ i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero, abs_mul, abs_of_pos hh]
      have hui : |u i| ≤ 1 := by simpa using hu i
      calc h * |u i| ≤ h * 1 := mul_le_mul_of_nonneg_left hui hh.le
        _ = h := mul_one h
    · intro hx
      refine ⟨h⁻¹ • x, ?_, smul_inv_smul₀ hh.ne' x⟩
      intro i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero, abs_mul, abs_inv,
        abs_of_pos hh]
      have hxi : |x i| ≤ h := by simpa using hx i
      calc h⁻¹ * |x i| ≤ h⁻¹ * h := mul_le_mul_of_nonneg_left hxi (by positivity)
        _ = 1 := inv_mul_cancel₀ hh.ne'
  have hme : MeasurableEmbedding (fun w => x0 + w : (Fin d → ℝ) → (Fin d → ℝ)) :=
    (Homeomorph.addLeft x0).measurableEmbedding
  have hmp : MeasurePreserving (fun w => x0 + w) (volume : Measure (Fin d → ℝ)) volume :=
    measurePreserving_add_left volume x0
  have himg : (fun w => x0 + w) '' supBall (0 : Fin d → ℝ) h = supBall x0 h := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩ i
      simp only [Pi.add_apply, add_sub_cancel_left]
      simpa using hw i
    · intro hy
      refine ⟨y - x0, ?_, by simp⟩
      intro i
      simpa using hy i
  have htrans : ∫ y in supBall x0 h, |g y| = ∫ w in supBall (0 : Fin d → ℝ) h, |g (x0 + w)| := by
    have := hmp.setIntegral_image_emb hme (fun y => |g y|) (supBall (0 : Fin d → ℝ) h)
    rwa [himg] at this
  -- Change of variables `x = x0 + h•u` then restrict the cube to the ball of radius `r`.
  have key : ∫ u in supBall (0 : Fin d → ℝ) 1, |g (x0 + h • u)|
      ≤ (h ^ d)⁻¹ * ∫ x in supBall x0 r, |g x| := by
    have cov : ∫ u in supBall (0 : Fin d → ℝ) 1, |g (x0 + h • u)|
        = (h ^ d)⁻¹ * ∫ y in supBall x0 h, |g y| := by
      rw [Measure.setIntegral_comp_smul_of_pos (μ := volume) (fun w => |g (x0 + w)|)
        (supBall (0 : Fin d → ℝ) 1) hh, hsmul_set, Module.finrank_fin_fun, smul_eq_mul,
        ← htrans]
    rw [cov]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsub : supBall x0 h ⊆ supBall x0 r := fun x hx i => le_trans (hx i) hhr
    exact setIntegral_mono_set hg_abs_int (ae_of_all _ (fun x => abs_nonneg _))
      (ae_of_all _ (fun x hx => hsub hx))
  calc |∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)|
      = ‖∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1, ‖prodKernel k d u * g (x0 + h • u)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ u in supBall (0 : Fin d → ℝ) 1, |prodKernel k d u| * |g (x0 + h • u)| := by
        simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1, B ^ d * |g (x0 + h • u)| :=
        integral_mono_of_nonneg
          (ae_of_all _ (fun u => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
          (hgcomp_int.const_mul (B ^ d))
          (ae_of_all _ (fun u => mul_le_mul_of_nonneg_right (hkbd u) (abs_nonneg _)))
    _ = B ^ d * ∫ u in supBall (0 : Fin d → ℝ) 1, |g (x0 + h • u)| :=
        integral_const_mul _ _
    _ ≤ B ^ d * ((h ^ d)⁻¹ * ∫ x in supBall x0 r, |g x|) :=
        mul_le_mul_of_nonneg_left key hBd0
    _ = B ^ d * (h⁻¹) ^ d * ∫ x in supBall x0 r, |g x| := by rw [inv_pow]; ring

/- The tensor kernel vanishes outside the unit cube `supBall 0 1`. -/
/--A product kernel vanishes outside the unit coordinatewise cube whenever each
one-dimensional factor vanishes outside the unit interval. -/
lemma prodKernel_eq_zero_of_not_mem {d : ℕ} {k : ℝ → ℝ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    {u : Fin d → ℝ} (hu : u ∉ supBall (0 : Fin d → ℝ) 1) :
    prodKernel k d u = 0 := by
  simp only [supBall, Set.mem_setOf_eq, not_forall, not_le] at hu
  obtain ⟨i, hi⟩ := hu
  simp only [Pi.zero_apply, sub_zero] at hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hk_supp _ hi)

/- The 1-D kernel has full-line integral `1` (extend the `[-1,1]` mass by support). -/
/--The full-line integral of a unit-interval-supported kernel equals its integral
over the unit interval. -/
lemma kernel_integral_full {k : ℝ → ℝ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mass : (∫ u in Set.Icc (-1 : ℝ) 1, k u) = 1) :
    ∫ t, k t = 1 := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Icc (-1 : ℝ) 1) (f := k) (fun t ht => ?_)]
  · exact hk_mass
  · apply hk_supp
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; linarith

/- **Kernel mass over the cube.** `∫_{[-1,1]^d} K = 1`. -/
/--The product kernel has unit mass on the unit cube when its one-dimensional
factor has unit mass on the unit interval. -/
lemma prodKernel_mass_cube {d : ℕ} {k : ℝ → ℝ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mass : (∫ u in Set.Icc (-1 : ℝ) 1, k u) = 1) :
    ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u = 1 := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => prodKernel_eq_zero_of_not_mem hk_supp hu)]
  rw [prodKernel_integral, kernel_integral_full hk_supp hk_mass, one_pow]

/- **Kernel moment over the cube.** `∫ t^j k(t) dt` on the full line agrees with the
`[-1,1]` integral (support), so vanishes for `1 ≤ j ≤ m`. -/
/--A polynomial moment of a unit-interval-supported kernel is unchanged when the
integral is extended from the unit interval to the whole real line. -/
lemma kernel_moment_full {k : ℝ → ℝ} {j : ℕ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0) :
    ∫ t, t ^ j * k t = ∫ t in Set.Icc (-1 : ℝ) 1, t ^ j * k t := by
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  have hk0 : k t = 0 := by
    apply hk_supp
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; linarith
  rw [hk0, mul_zero]

/- **Multi-index moment vanishing over the cube.** For a multi-index `ν` with total
degree `1 ≤ ∑ νᵢ ≤ m`, the monomial-weighted kernel integral over the cube vanishes. -/
/--A product kernel has zero multivariate moment whenever the total positive
degree is within the range of its one-dimensional cancelled moments. -/
lemma prodKernel_multiIndex_moment_cube {d : ℕ} {k : ℝ → ℝ} {m : ℕ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ m → (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (ν : Fin d → ℕ) (hν1 : 1 ≤ ∑ i, ν i) (hνm : (∑ i, ν i) ≤ m) :
    ∫ u in supBall (0 : Fin d → ℝ) 1, (∏ i, u i ^ ν i) * prodKernel k d u = 0 := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => by rw [prodKernel_eq_zero_of_not_mem hk_supp hu, mul_zero])]
  rw [prodKernel_moment]
  -- Some coordinate `i0` has `1 ≤ ν i0 ≤ m`; its 1-D moment factor vanishes.
  obtain ⟨i0, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : (∑ i, ν i) ≠ 0)
  have hi0_1 : 1 ≤ ν i0 := Nat.one_le_iff_ne_zero.mpr hi0
  have hi0_m : ν i0 ≤ m :=
    le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)) hνm
  refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
  rw [kernel_moment_full hk_supp]
  exact hk_mom _ hi0_1 hi0_m

/- **Single-monomial (permutation) moment vanishing.** For `p : Fin j → Fin d` with
`1 ≤ j ≤ m`, `∫ (∏ₗ u_{p l}) K(u) = 0`, by regrouping the product fibrewise into a
multi-index of total degree `j`. -/
/--A product kernel annihilates every coordinate monomial whose positive total
degree lies within its cancelled-moment order. -/
lemma prodKernel_monomial_p_cube {d : ℕ} {k : ℝ → ℝ} {m j : ℕ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ m → (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (p : Fin j → Fin d) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    ∫ u in supBall (0 : Fin d → ℝ) 1, (∏ l, u (p l)) * prodKernel k d u = 0 := by
  classical
  set ν : Fin d → ℕ := fun i => (Finset.univ.filter (fun l => p l = i)).card with hνdef
  have hsum : (∑ i, ν i) = j := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin j)))
      (t := (Finset.univ : Finset (Fin d))) (f := p) (fun l _ => Finset.mem_univ (p l))
    simp only [Finset.card_univ, Fintype.card_fin] at this
    rw [hνdef]; exact this.symm
  have hreg : ∀ u : Fin d → ℝ, (∏ l : Fin j, u (p l)) = ∏ i : Fin d, u i ^ ν i := by
    intro u
    rw [← Finset.prod_fiberwise_of_maps_to (fun l _ => Finset.mem_univ (p l))
          (fun l => u (p l))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Finset.prod_congr rfl (fun l hl => by rw [(Finset.mem_filter.mp hl).2]),
        Finset.prod_const]
  simp_rw [hreg]
  exact prodKernel_multiIndex_moment_cube hk_supp hk_mom ν (by omega) (by omega)

/-- The tensor kernel is continuous when the 1-D kernel is. -/
/-- A finite product kernel is continuous when its one-dimensional factor is continuous. -/
lemma prodKernel_continuous {d : ℕ} {k : ℝ → ℝ} (hk : Continuous k) :
    Continuous (prodKernel k d) := by
  unfold prodKernel
  exact continuous_finset_prod _ (fun i _ => hk.comp (continuous_apply i))

/-- Almost every point of the closed unit cube lies in its interior (the boundary
`{∃ i, |uᵢ| = 1}` is Lebesgue-null). -/

end Causalean.Stat.Nonparametric.HolderInterpolation.Internal
