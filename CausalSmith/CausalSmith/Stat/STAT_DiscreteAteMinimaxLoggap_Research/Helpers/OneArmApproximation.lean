import Causalean.Mathlib.Analysis.EhlichZellerMesh.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A three-point obstruction for the one-arm rational approximation problem

This file isolates the elementary algebraic part of the approximation lower
bound used in the one-arm prior construction.  Evaluating the rational target
at the first three multiples of its pole scale produces a fixed linear
combination in which the nuisance reciprocal term cancels.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open Causalean.Mathlib.Analysis.EhlichZellerMesh

/-- Near the endpoint `1`, the arccosine distance is at most a constant times
the square root of the Euclidean distance. -/
lemma arccos_one_sub_le_four_sqrt {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2) :
    Real.arccos (1 - z) ≤ 4 * Real.sqrt z := by
  let t := Real.arccos (1 - z)
  have ht0 : 0 ≤ t := Real.arccos_nonneg _
  have htpi : t ≤ Real.pi := Real.arccos_le_pi _
  have harg_lo : -1 ≤ 1 - z := by linarith
  have harg_hi : 1 - z ≤ 1 := by linarith
  have hcos : Real.cos t = 1 - z := by
    exact Real.cos_arccos harg_lo harg_hi
  have hquad := Real.cos_le_one_sub_mul_cos_sq (x := t) (by
    rw [abs_of_nonneg ht0]
    exact htpi)
  rw [hcos] at hquad
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have ht_sq : t ^ 2 ≤ 8 * z := by
    have hpi_sq : Real.pi ^ 2 ≤ 16 := by nlinarith
    have hmul : 2 * t ^ 2 ≤ Real.pi ^ 2 * z := by
      have hpine : Real.pi ^ 2 ≠ 0 := by positivity
      field_simp [hpine] at hquad
      nlinarith [sq_pos_of_pos hpi0]
    nlinarith [mul_le_mul_of_nonneg_right hpi_sq hz0]
  have hsqrt0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz0
  dsimp [t] at ht0 ht_sq ⊢
  nlinarith

/-- A degree-`n` polynomial varies by at most `n` times its supremum times the
angular distance under the endpoint cosine parametrization. -/
lemma czTrig_pair_variation (P : Polynomial ℝ) (n : ℕ) (hdeg : P.natDegree ≤ n)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) Real.pi)
    (ht : t ∈ Set.Icc (0 : ℝ) Real.pi) :
    |czTrig P t - czTrig P s| ≤
      (n : ℝ) * czSup P * |t - s| := by
  have hdiff (x : ℝ) (_hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
      DifferentiableAt ℝ (czTrig P) x := by
    unfold czTrig
    fun_prop
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) Real.pi) :
      ‖deriv (czTrig P) x‖ ≤ (n : ℝ) * czSup P := by
    have hq := abs_czTrig_le_czSup P hx
    have hM := czSup_nonneg P
    have habs : |czTrig P x| ≤ |czSup P| := by
      simpa [abs_of_nonneg hM] using hq
    have hsq : (czTrig P x) ^ 2 ≤ (czSup P) ^ 2 := sq_le_sq.mpr habs
    have hrad : 0 ≤ (czSup P) ^ 2 - (czTrig P x) ^ 2 := by
      nlinarith
    have hsqrt : Real.sqrt ((czSup P) ^ 2 - (czTrig P x) ^ 2) ≤ czSup P := by
      rw [Real.sqrt_le_iff]
      constructor
      · exact hM
      · nlinarith
    rw [Real.norm_eq_abs]
    exact (czTrig_szego_deriv P n hdeg x).trans
      (mul_le_mul_of_nonneg_left hsqrt (by positivity))
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := czTrig P) (s := Set.Icc (0 : ℝ) Real.pi)
    (C := (n : ℝ) * czSup P) hdiff hderiv
    (convex_Icc (0 : ℝ) Real.pi) hs ht
  simpa [Real.norm_eq_abs] using hmv

/-- Affine reparametrization carrying `[-1,1]` to `[a,1]`. -/
noncomputable def oneArmAffinePoly (P : Polynomial ℝ) (a : ℝ) : Polynomial ℝ :=
  P.comp (Polynomial.C ((1 + a) / 2) +
    Polynomial.C ((1 - a) / 2) * Polynomial.X)

lemma oneArmAffinePoly_eval (P : Polynomial ℝ) (a y : ℝ) :
    (oneArmAffinePoly P a).eval y =
      P.eval ((1 + a) / 2 + (1 - a) / 2 * y) := by
  simp [oneArmAffinePoly]

lemma oneArmAffinePoly_natDegree_le (P : Polynomial ℝ) (a : ℝ) (n : ℕ)
    (hdeg : P.natDegree ≤ n) :
    (oneArmAffinePoly P a).natDegree ≤ n := by
  calc
    (oneArmAffinePoly P a).natDegree ≤
        P.natDegree *
          (Polynomial.C ((1 + a) / 2) +
            Polynomial.C ((1 - a) / 2) * Polynomial.X).natDegree := by
              exact Polynomial.natDegree_comp_le
    _ ≤ P.natDegree * 1 := by
      gcongr
      refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact Polynomial.natDegree_mul_le.trans (by simp)
    _ ≤ n := by simpa using hdeg

/-- A uniform bound on a polynomial over `[a,1]` transfers to the cosine
supremum of its affine reparametrization. -/
lemma oneArmAffinePoly_czSup_le {P : Polynomial ℝ} {a B : ℝ}
    (ha1 : a ≤ 1) (hB : ∀ x ∈ Set.Icc a 1, |P.eval x| ≤ B) :
    czSup (oneArmAffinePoly P a) ≤ B := by
  rcases czSup_attained (oneArmAffinePoly P a) with ⟨t, ht, hsup⟩
  rw [← hsup]
  have hcos_lo : -1 ≤ -Real.cos t := by linarith [Real.cos_le_one t]
  have hcos_hi : -Real.cos t ≤ 1 := by linarith [Real.neg_one_le_cos t]
  have hx : (1 + a) / 2 + (1 - a) / 2 * (-Real.cos t) ∈ Set.Icc a 1 := by
    constructor <;> nlinarith
  simpa [czTrig, oneArmAffinePoly_eval] using hB _ hx

/-- Endpoint variation at the second pole-scale point. -/
lemma oneArm_poly_two_mul_variation
    {P : Polynomial ℝ} {a B : ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha3 : 3 * a ≤ 1) (hdeg : P.natDegree ≤ n)
    (hB : ∀ x ∈ Set.Icc a 1, |P.eval x| ≤ B) :
    |P.eval a - P.eval (2 * a)| ≤
      4 * (n : ℝ) * B * Real.sqrt (2 * a / (1 - a)) := by
  let R := oneArmAffinePoly P a
  let t := Real.arccos (1 - 2 * a / (1 - a))
  have ha1 : a < 1 := by nlinarith
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  have hz0 : 0 ≤ 2 * a / (1 - a) := by positivity
  have hz2 : 2 * a / (1 - a) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have ht : t ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hvar := czTrig_pair_variation R n
    (oneArmAffinePoly_natDegree_le P a n hdeg)
    (s := 0) (t := t) (by constructor <;> positivity) ht
  have hsup : czSup R ≤ B := oneArmAffinePoly_czSup_le ha1.le hB
  have hB0 : 0 ≤ B := (abs_nonneg (P.eval a)).trans (hB a ⟨le_rfl, ha1.le⟩)
  have htbound : |t| ≤ 4 * Real.sqrt (2 * a / (1 - a)) := by
    rw [abs_of_nonneg (Real.arccos_nonneg _)]
    exact arccos_one_sub_le_four_sqrt hz0 hz2
  have heval0 : czTrig R 0 = P.eval a := by
    simp only [R, czTrig, oneArmAffinePoly_eval, Real.cos_zero]
    congr 1
    ring
  have hevalt : czTrig R t = P.eval (2 * a) := by
    have harg_lo : -1 ≤ 1 - 2 * a / (1 - a) := by linarith
    have harg_hi : 1 - 2 * a / (1 - a) ≤ 1 := by linarith
    have hcos : Real.cos t = 1 - 2 * a / (1 - a) :=
      Real.cos_arccos harg_lo harg_hi
    simp only [R, czTrig, oneArmAffinePoly_eval, t, hcos]
    field_simp [ne_of_gt hden]
    ring
  rw [hevalt, heval0, abs_sub_comm] at hvar
  have hvar' : |P.eval a - P.eval (2 * a)| ≤ (n : ℝ) * czSup R * |t| := by
    simpa using hvar
  calc
    |P.eval a - P.eval (2 * a)|
        ≤ (n : ℝ) * czSup R * |t| := hvar'
    _ ≤ (n : ℝ) * B * (4 * Real.sqrt (2 * a / (1 - a))) := by
      gcongr
    _ = 4 * (n : ℝ) * B * Real.sqrt (2 * a / (1 - a)) := by ring

/-- Endpoint variation at the third pole-scale point. -/
lemma oneArm_poly_three_mul_variation
    {P : Polynomial ℝ} {a B : ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha3 : 3 * a ≤ 1) (hdeg : P.natDegree ≤ n)
    (hB : ∀ x ∈ Set.Icc a 1, |P.eval x| ≤ B) :
    |P.eval a - P.eval (3 * a)| ≤
      4 * (n : ℝ) * B * Real.sqrt (4 * a / (1 - a)) := by
  let R := oneArmAffinePoly P a
  let t := Real.arccos (1 - 4 * a / (1 - a))
  have ha1 : a < 1 := by nlinarith
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  have hz0 : 0 ≤ 4 * a / (1 - a) := by positivity
  have hz2 : 4 * a / (1 - a) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have ht : t ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hvar := czTrig_pair_variation R n
    (oneArmAffinePoly_natDegree_le P a n hdeg)
    (s := 0) (t := t) (by constructor <;> positivity) ht
  have hsup : czSup R ≤ B := oneArmAffinePoly_czSup_le ha1.le hB
  have hB0 : 0 ≤ B := (abs_nonneg (P.eval a)).trans (hB a ⟨le_rfl, ha1.le⟩)
  have htbound : |t| ≤ 4 * Real.sqrt (4 * a / (1 - a)) := by
    rw [abs_of_nonneg (Real.arccos_nonneg _)]
    exact arccos_one_sub_le_four_sqrt hz0 hz2
  have heval0 : czTrig R 0 = P.eval a := by
    simp only [R, czTrig, oneArmAffinePoly_eval, Real.cos_zero]
    congr 1
    ring
  have hevalt : czTrig R t = P.eval (3 * a) := by
    have harg_lo : -1 ≤ 1 - 4 * a / (1 - a) := by linarith
    have harg_hi : 1 - 4 * a / (1 - a) ≤ 1 := by linarith
    have hcos : Real.cos t = 1 - 4 * a / (1 - a) :=
      Real.cos_arccos harg_lo harg_hi
    simp only [R, czTrig, oneArmAffinePoly_eval, t, hcos]
    field_simp [ne_of_gt hden]
    ring
  rw [hevalt, heval0, abs_sub_comm] at hvar
  have hvar' : |P.eval a - P.eval (3 * a)| ≤ (n : ℝ) * czSup R * |t| := by
    simpa using hvar
  calc
    |P.eval a - P.eval (3 * a)|
        ≤ (n : ℝ) * czSup R * |t| := hvar'
    _ ≤ (n : ℝ) * B * (4 * Real.sqrt (4 * a / (1 - a))) := by
      gcongr
    _ = 4 * (n : ℝ) * B * Real.sqrt (4 * a / (1 - a)) := by ring

/-- Uniform approximation of the rational target bounds the approximating
polynomial by the target's elementary envelope. -/
lemma oneArm_poly_bound_of_rational_approx
    {P : Polynomial ℝ} {a alpha e : ℝ} (ha0 : 0 < a)
    (happrox : ∀ x ∈ Set.Icc a 1,
      |x / (x + a) + alpha / x - P.eval x| ≤ e) :
    ∀ x ∈ Set.Icc a 1, |P.eval x| ≤ 1 + |alpha / a| + e := by
  intro x hx
  have hx0 : 0 < x := ha0.trans_le hx.1
  have hxa : 0 < x + a := add_pos hx0 ha0
  have hrat0 : 0 ≤ x / (x + a) := div_nonneg hx0.le hxa.le
  have hrat1 : x / (x + a) ≤ 1 := (div_le_one hxa).2 (by linarith)
  have halpha : |alpha / x| ≤ |alpha / a| := by
    rw [abs_div, abs_div, abs_of_pos hx0, abs_of_pos ha0]
    exact div_le_div_of_nonneg_left (abs_nonneg alpha) ha0 hx.1
  have htarget : |x / (x + a) + alpha / x| ≤ 1 + |alpha / a| := by
    calc
      |x / (x + a) + alpha / x|
          ≤ |x / (x + a)| + |alpha / x| := abs_add_le _ _
      _ ≤ 1 + |alpha / a| := by
        rw [abs_of_nonneg hrat0]
        exact add_le_add hrat1 halpha
  have hdecomp : P.eval x =
      (x / (x + a) + alpha / x) -
        (x / (x + a) + alpha / x - P.eval x) := by ring
  rw [hdecomp]
  exact (abs_sub _ _).trans (add_le_add htarget (happrox x hx))

private lemma oneArm_three_point_obstruction_aux
    {a alpha e V : ℝ} (ha : a ≠ 0) (P : ℝ → ℝ)
    (h₁ : |a / (a + a) + alpha / a - P a| ≤ e)
    (h₂ : |(2 * a) / (2 * a + a) + alpha / (2 * a) - P (2 * a)| ≤ e)
    (h₃ : |(3 * a) / (3 * a + a) + alpha / (3 * a) - P (3 * a)| ≤ e)
    (h₁₂ : |P a - P (2 * a)| ≤ V)
    (h₃₂ : |P (3 * a) - P (2 * a)| ≤ V) :
    1 / 12 ≤ 8 * e + 4 * V := by
  let f : ℝ → ℝ := fun x => x / (x + a) + alpha / x
  have hid : f a - 4 * f (2 * a) + 3 * f (3 * a) = 1 / 12 := by
    dsimp [f]
    field_simp [ha]
    ring
  have herr :
      |(f a - P a) - 4 * (f (2 * a) - P (2 * a))
          + 3 * (f (3 * a) - P (3 * a))| ≤ 8 * e := by
    have htri := abs_add_three (f a - P a)
      (-4 * (f (2 * a) - P (2 * a)))
      (3 * (f (3 * a) - P (3 * a)))
    norm_num [abs_mul] at htri
    have hf₁ : |f a - P a| ≤ e := by simpa [f] using h₁
    have hf₂ : |f (2 * a) - P (2 * a)| ≤ e := by simpa [f] using h₂
    have hf₃ : |f (3 * a) - P (3 * a)| ≤ e := by simpa [f] using h₃
    have htri' :
        |(f a - P a) - 4 * (f (2 * a) - P (2 * a))
          + 3 * (f (3 * a) - P (3 * a))| ≤
          |f a - P a| + 4 * |f (2 * a) - P (2 * a)|
            + 3 * |f (3 * a) - P (3 * a)| := by
      simpa [sub_eq_add_neg] using htri
    nlinarith
  have hP : |P a - 4 * P (2 * a) + 3 * P (3 * a)| ≤ 4 * V := by
    have hrewrite : P a - 4 * P (2 * a) + 3 * P (3 * a) =
        (P a - P (2 * a)) + 3 * (P (3 * a) - P (2 * a)) := by ring
    rw [hrewrite]
    have htri := abs_add_le (P a - P (2 * a))
      (3 * (P (3 * a) - P (2 * a)))
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at htri
    nlinarith
  have hsplit : f a - 4 * f (2 * a) + 3 * f (3 * a) =
      ((f a - P a) - 4 * (f (2 * a) - P (2 * a))
        + 3 * (f (3 * a) - P (3 * a)))
      + (P a - 4 * P (2 * a) + 3 * P (3 * a)) := by ring
  rw [hsplit] at hid
  have habs : (1 / 12 : ℝ) ≤
      |((f a - P a) - 4 * (f (2 * a) - P (2 * a))
        + 3 * (f (3 * a) - P (3 * a)))
        + (P a - 4 * P (2 * a) + 3 * P (3 * a))| := by
    rw [← hid]
    exact le_abs_self _
  exact habs.trans ((abs_add_le _ _).trans (add_le_add herr hP))

/-- A polynomial whose endpoint angular scale is sufficiently small cannot
uniformly approximate the one-arm rational target more accurately than a fixed
constant, uniformly over the reciprocal nuisance coefficient. -/
theorem oneArm_rational_approximation_lower
    {P : Polynomial ℝ} {a alpha e : ℝ} {n : ℕ}
    (ha0 : 0 < a) (ha3 : 3 * a ≤ 1) (hdeg : P.natDegree ≤ n)
    (hscale : (n : ℝ) * Real.sqrt (4 * a / (1 - a)) ≤ 1 / 10000)
    (happrox : ∀ x ∈ Set.Icc a 1,
      |x / (x + a) + alpha / x - P.eval x| ≤ e) :
    1 / 1000 ≤ e := by
  have ha1 : a < 1 := by nlinarith
  have he0 : 0 ≤ e := by
    exact (abs_nonneg _).trans (happrox a ⟨le_rfl, ha1.le⟩)
  by_contra hnot
  have he_small : e < 1 / 1000 := lt_of_not_ge hnot
  let U : ℝ := |alpha / a|
  let B : ℝ := 1 + U + e
  have hU0 : 0 ≤ U := abs_nonneg _
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have hB : ∀ x ∈ Set.Icc a 1, |P.eval x| ≤ B := by
    simpa [B, U] using oneArm_poly_bound_of_rational_approx ha0 happrox
  have hsqrt : Real.sqrt (2 * a / (1 - a)) ≤
      Real.sqrt (4 * a / (1 - a)) := by
    apply Real.sqrt_le_sqrt
    have hden : 0 < 1 - a := sub_pos.mpr ha1
    exact div_le_div_of_nonneg_right (by nlinarith) hden.le
  have h12raw := oneArm_poly_two_mul_variation ha0 ha3 hdeg hB
  have h13raw := oneArm_poly_three_mul_variation ha0 ha3 hdeg hB
  have h12 : |P.eval a - P.eval (2 * a)| ≤ 4 * B / 10000 := by
    calc
      |P.eval a - P.eval (2 * a)|
          ≤ 4 * (n : ℝ) * B * Real.sqrt (2 * a / (1 - a)) := h12raw
      _ ≤ 4 * B * ((n : ℝ) * Real.sqrt (4 * a / (1 - a))) := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4) hn0) hB0)
        nlinarith
      _ ≤ 4 * B * (1 / 10000) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hB0)
      _ = 4 * B / 10000 := by ring
  have h13 : |P.eval a - P.eval (3 * a)| ≤ 4 * B / 10000 := by
    calc
      |P.eval a - P.eval (3 * a)|
          ≤ 4 * (n : ℝ) * B * Real.sqrt (4 * a / (1 - a)) := h13raw
      _ = 4 * B * ((n : ℝ) * Real.sqrt (4 * a / (1 - a))) := by ring
      _ ≤ 4 * B * (1 / 10000) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hB0)
      _ = 4 * B / 10000 := by ring
  have h32 : |P.eval (3 * a) - P.eval (2 * a)| ≤ 8 * B / 10000 := by
    have hdecomp : P.eval (3 * a) - P.eval (2 * a) =
        (P.eval (3 * a) - P.eval a) + (P.eval a - P.eval (2 * a)) := by ring
    rw [hdecomp]
    calc
      |(P.eval (3 * a) - P.eval a) + (P.eval a - P.eval (2 * a))|
          ≤ |P.eval (3 * a) - P.eval a| + |P.eval a - P.eval (2 * a)| :=
            abs_add_le _ _
      _ ≤ 4 * B / 10000 + 4 * B / 10000 := by
        rw [abs_sub_comm (P.eval (3 * a))]
        exact add_le_add h13 h12
      _ = 8 * B / 10000 := by ring
  by_cases hU : U ≤ 1
  · have hobs := oneArm_three_point_obstruction_aux
      (a := a) (alpha := alpha) (e := e) (V := 8 * B / 10000)
      (ne_of_gt ha0) (fun x => P.eval x)
      (happrox a ⟨le_rfl, ha1.le⟩)
      (happrox (2 * a) ⟨by linarith, by linarith⟩)
      (happrox (3 * a) ⟨by linarith, ha3⟩)
      (h12.trans (by nlinarith [hB0])) h32
    dsimp [B] at hobs
    nlinarith
  · have hUlarge : 1 < U := lt_of_not_ge hU
    let f : ℝ → ℝ := fun x => x / (x + a) + alpha / x
    have hf : f a - f (2 * a) = alpha / a / 2 - 1 / 6 := by
      dsimp [f]
      field_simp [ne_of_gt ha0]
      ring
    have hlower : U / 2 - 1 / 6 ≤ |f a - f (2 * a)| := by
      rw [hf]
      have habsdiv : |alpha / a / 2| = U / 2 := by
        simp [U, abs_div]
      have hrev := abs_sub_abs_le_abs_sub (alpha / a / 2) (1 / 6)
      rw [habsdiv] at hrev
      norm_num at hrev ⊢
      exact hrev
    have hupper : |f a - f (2 * a)| ≤ 2 * e + 4 * B / 10000 := by
      have hdecomp : f a - f (2 * a) =
          (f a - P.eval a) + (P.eval a - P.eval (2 * a))
            - (f (2 * a) - P.eval (2 * a)) := by ring
      rw [hdecomp]
      calc
        |(f a - P.eval a) + (P.eval a - P.eval (2 * a))
            - (f (2 * a) - P.eval (2 * a))|
            ≤ |f a - P.eval a| + |P.eval a - P.eval (2 * a)|
                + |f (2 * a) - P.eval (2 * a)| := by
                  have htri := abs_add_three (f a - P.eval a)
                    (P.eval a - P.eval (2 * a))
                    (-(f (2 * a) - P.eval (2 * a)))
                  calc
                    _ ≤ |f a - P.eval a| + |P.eval a - P.eval (2 * a)|
                        + |P.eval (2 * a) - f (2 * a)| := by
                          simpa [sub_eq_add_neg, abs_neg] using htri
                    _ = _ := by
                      rw [abs_sub_comm (P.eval (2 * a)) (f (2 * a))]
        _ ≤ e + 4 * B / 10000 + e := by
          exact add_le_add (add_le_add
            (by simpa [f] using happrox a ⟨le_rfl, ha1.le⟩) h12)
            (by simpa [f] using happrox (2 * a) ⟨by linarith, by linarith⟩)
        _ = 2 * e + 4 * B / 10000 := by ring
    dsimp [B] at hupper
    nlinarith [hlower.trans hupper]

/-- The concrete pole scale `10⁻¹⁰ n⁻²` satisfies the endpoint angular budget
used by `oneArm_rational_approximation_lower`. -/
lemma oneArm_calibrated_angular_scale (n : ℕ) (hn : 1 ≤ n) :
    let a : ℝ := 1 / (10000000000 * (n : ℝ) ^ 2)
    (n : ℝ) * Real.sqrt (4 * a / (1 - a)) ≤ 1 / 10000 := by
  let a : ℝ := 1 / (10000000000 * (n : ℝ) ^ 2)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha_half : a ≤ 1 / 2 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 10000000000 * (n : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hden : 0 < 1 - a := by linarith
  have hinside : 4 * a / (1 - a) ≤ (1 / (10000 * (n : ℝ))) ^ 2 := by
    apply (div_le_iff₀ hden).2
    dsimp [a]
    field_simp
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hsqrt : Real.sqrt (4 * a / (1 - a)) ≤ 1 / (10000 * (n : ℝ)) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · simpa using hinside
  calc
    (n : ℝ) * Real.sqrt (4 * a / (1 - a))
        ≤ (n : ℝ) * (1 / (10000 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hsqrt hn0.le
    _ = 1 / 10000 := by field_simp

/-- Uniform constant lower bound at the concrete `n⁻²` pole scale. -/
theorem oneArm_rational_approximation_lower_calibrated
    (n : ℕ) (hn : 1 ≤ n) (alpha e : ℝ) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ n)
    (happrox : ∀ x ∈ Set.Icc
      (1 / (10000000000 * (n : ℝ) ^ 2)) 1,
      |x / (x + 1 / (10000000000 * (n : ℝ) ^ 2)) + alpha / x - P.eval x| ≤ e) :
    1 / 1000 ≤ e := by
  let a : ℝ := 1 / (10000000000 * (n : ℝ) ^ 2)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha3 : 3 * a ≤ 1 := by
    dsimp [a]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 10000000000 * (n : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  apply oneArm_rational_approximation_lower ha0 ha3 hdeg
    (oneArm_calibrated_angular_scale n hn)
  simpa [a] using happrox

/-- The values of `x / (x + a) + alpha / x` at `a`, `2a`, and `3a` have a
fixed linear combination, independent of `alpha`. -/
lemma oneArm_rational_three_point_identity {a alpha : ℝ} (ha : a ≠ 0) :
    (a / (a + a) + alpha / a)
      - 4 * ((2 * a) / (2 * a + a) + alpha / (2 * a))
      + 3 * ((3 * a) / (3 * a + a) + alpha / (3 * a)) = 1 / 12 := by
  field_simp [ha]
  ring

/-- If a function approximates the one-arm rational target at the first three
multiples of the pole scale, its error and its local oscillation cannot both be
small. -/
lemma oneArm_rational_three_point_obstruction
    {a alpha e V : ℝ} (ha : a ≠ 0)
    (P : ℝ → ℝ)
    (h₁ : |a / (a + a) + alpha / a - P a| ≤ e)
    (h₂ : |(2 * a) / (2 * a + a) + alpha / (2 * a) - P (2 * a)| ≤ e)
    (h₃ : |(3 * a) / (3 * a + a) + alpha / (3 * a) - P (3 * a)| ≤ e)
    (h₁₂ : |P a - P (2 * a)| ≤ V)
    (h₃₂ : |P (3 * a) - P (2 * a)| ≤ V) :
    1 / 12 ≤ 8 * e + 4 * V := by
  exact oneArm_three_point_obstruction_aux ha P h₁ h₂ h₃ h₁₂ h₃₂

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
