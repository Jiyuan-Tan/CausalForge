/-!
## Smooth compactly supported quartic prior

This section defines the scaled quartic beta prior used in one-dimensional
van Trees arguments.  It records its support, regularity, normalization,
guarded-score integrability, and exact inverse-square information law.
-/

open MeasureTheory Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- The smooth quartic prior is a beta-shaped probability density centered at a chosen
real value and truncated outside a chosen radius. -/
noncomputable def smoothPrior (c a θ : ℝ) : ℝ :=
  if |θ - c| < a then
    (15 / (16 * a)) * (1 - ((θ - c) / a) ^ 2) ^ 2
  else 0

/-- The smooth quartic prior derivative is its explicit piecewise polynomial
parameter derivative. -/
noncomputable def smoothPriorDeriv (c a θ : ℝ) : ℝ :=
  if |θ - c| < a then
    -(15 / (4 * a ^ 3)) * (θ - c) * (1 - ((θ - c) / a) ^ 2)
  else 0

/-- A [positive bandwidth](hyp:ha) makes [the smooth quartic prior nonnegative at every
parameter value](goal). -/
theorem smoothPrior_nonneg {c a : ℝ} (ha : 0 < a) (θ : ℝ) :
    0 ≤ smoothPrior c a θ := by
  unfold smoothPrior
  split_ifs <;> positivity

/-- Under a [positive bandwidth](hyp:ha), [the smooth quartic prior is positive exactly
inside the open interval defined by its center and bandwidth](goal). -/
theorem smoothPrior_pos_iff {c a θ : ℝ} (ha : 0 < a) :
    0 < smoothPrior c a θ ↔ |θ - c| < a := by
  unfold smoothPrior
  split_ifs with h
  · simp only [h, iff_true]
    have hr : |(θ - c) / a| < 1 := by
      rw [abs_div, abs_of_pos ha, div_lt_one ha]
      exact h
    have hs : ((θ - c) / a) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one]
      exact hr
    positivity
  · simp [h]

/-- Under a [positive bandwidth](hyp:ha), [the nonzero set of the smooth quartic prior
is exactly its open support interval](goal). -/
theorem support_smoothPrior {c a : ℝ} (ha : 0 < a) :
    Function.support (smoothPrior c a) = Ioo (c - a) (c + a) := by
  ext θ
  rw [Function.mem_support, mem_Ioo]
  constructor
  · intro hne
    have hpos : 0 < smoothPrior c a θ :=
      lt_of_le_of_ne (smoothPrior_nonneg ha θ) (Ne.symm hne)
    have habs := (smoothPrior_pos_iff ha).mp hpos
    rw [abs_lt] at habs
    constructor <;> linarith
  · rintro ⟨hleft, hright⟩
    apply ne_of_gt
    rw [smoothPrior_pos_iff ha, abs_lt]
    constructor <;> linarith

/-- Under a [positive bandwidth](hyp:ha), [the topological support of the smooth
quartic prior is exactly the corresponding closed interval](goal). -/
theorem tsupport_smoothPrior {c a : ℝ} (ha : 0 < a) :
    tsupport (smoothPrior c a) = Icc (c - a) (c + a) := by
  rw [tsupport, support_smoothPrior ha, closure_Ioo]
  linarith

/-- If [the bandwidth is positive](hyp:ha) and [the prior's left](hyp:hleft) and
[right](hyp:hright) support endpoints lie strictly inside an ambient interval, then
[every point where the prior is nonzero lies in the ambient closed interval](goal). -/
theorem support_smoothPrior_subset_Icc {ell u c a : ℝ} (ha : 0 < a)
    (hleft : ell < c - a) (hright : c + a < u) :
    Function.support (smoothPrior c a) ⊆ Icc ell u := by
  rw [support_smoothPrior ha]
  rintro θ ⟨hθleft, hθright⟩
  constructor <;> linarith

/-- If [the bandwidth is positive](hyp:ha) and [the prior's left](hyp:hleft) and
[right](hyp:hright) support endpoints lie strictly inside an ambient interval, then
[the prior's topological support lies in the ambient open interval](goal). -/
theorem tsupport_smoothPrior_subset_Ioo {ell u c a : ℝ} (ha : 0 < a)
    (hleft : ell < c - a) (hright : c + a < u) :
    tsupport (smoothPrior c a) ⊆ Ioo ell u := by
  rw [tsupport_smoothPrior ha]
  rintro θ ⟨hθleft, hθright⟩
  constructor <;> linarith

/-- If [the bandwidth is positive](hyp:ha) and [the prior's left](hyp:hleft) and
[right](hyp:hright) support endpoints lie strictly inside an ambient interval, then
[the prior vanishes at both ambient endpoints](goal). -/
theorem smoothPrior_ambient_endpoints {ell u c a : ℝ} (ha : 0 < a)
    (hleft : ell < c - a) (hright : c + a < u) :
    smoothPrior c a ell = 0 ∧ smoothPrior c a u = 0 := by
  constructor
  · unfold smoothPrior
    rw [if_neg]
    rw [abs_lt]
    intro h
    linarith
  · unfold smoothPrior
    rw [if_neg]
    rw [abs_lt]
    intro h
    linarith

private theorem hasDerivAt_smoothPrior_aux {c a : ℝ} (ha : 0 < a) (θ : ℝ) :
    HasDerivAt (smoothPrior c a) (smoothPriorDeriv c a θ) θ := by
  let p : ℝ → ℝ := fun t =>
    (15 / (16 * a)) * (1 - ((t - c) / a) ^ 2) ^ 2
  let dp : ℝ → ℝ := fun t =>
    -(15 / (4 * a ^ 3)) * (t - c) * (1 - ((t - c) / a) ^ 2)
  have hp (t : ℝ) : HasDerivAt p (dp t) t := by
    have h := ((((hasDerivAt_id t).sub_const c).div_const a).pow 2)
    have hq := (hasDerivAt_const t 1).sub h
    have h2 := hq.pow 2
    have hk := h2.const_mul (15 / (16 * a))
    have hfun : p = fun y => 15 / (16 * a) *
        (((((fun _ : ℝ => 1) - (fun x => ((id x - c) / a) ^ 2)) : ℝ → ℝ) ^ 2) y) := by
      funext x
      rfl
    rw [hfun]
    apply hk.congr_deriv
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one]
    dsimp [dp]
    field_simp [ha.ne']
    ring
  by_cases hθ : |θ - c| < a
  · have hopen : IsOpen {t : ℝ | |t - c| < a} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    have hevent : ∀ᶠ t in nhds θ, |t - c| < a := hopen.eventually_mem hθ
    have heq : smoothPrior c a =ᶠ[nhds θ] p := by
      filter_upwards [hevent] with t ht
      simp [smoothPrior, p, ht]
    have hdp : smoothPriorDeriv c a θ = dp θ := by
      simp [smoothPriorDeriv, dp, hθ]
    rw [hdp]
    exact (heq.hasDerivAt_iff).mpr (hp θ)
  · rcases lt_or_eq_of_le (le_of_not_gt hθ) with hout | habs
    ·
      have hopen : IsOpen {t : ℝ | a < |t - c|} :=
        isOpen_lt continuous_const
          (continuous_abs.comp (continuous_id.sub continuous_const))
      have hevent : ∀ᶠ t in nhds θ, a < |t - c| := hopen.eventually_mem hout
      have heq : smoothPrior c a =ᶠ[nhds θ] fun _ => 0 := by
        filter_upwards [hevent] with t ht
        simp [smoothPrior, not_lt.mpr ht.le]
      have hdzero : smoothPriorDeriv c a θ = 0 := by
        simp [smoothPriorDeriv, hθ]
      rw [hdzero]
      exact (heq.hasDerivAt_iff).mpr (hasDerivAt_const θ 0)
    · have hsq : ((θ - c) / a) ^ 2 = 1 := by
        have habssq : |θ - c| ^ 2 = a ^ 2 := congrArg (fun x : ℝ => x ^ 2) habs.symm
        rw [sq_abs] at habssq
        field_simp [ha.ne']
        nlinarith
      have hdpzero : dp θ = 0 := by simp [dp, hsq]
      have hpzero : p θ = 0 := by simp [p, hsq]
      let s : Set ℝ := {t | |t - c| < a}
      have hin : HasDerivWithinAt (smoothPrior c a) 0 s θ := by
        apply ((hp θ).congr_deriv hdpzero).hasDerivWithinAt.congr
        · intro t ht
          change |t - c| < a at ht
          rw [smoothPrior, if_pos ht]
        · simp [smoothPrior, hθ, hpzero]
      have houtside : HasDerivWithinAt (smoothPrior c a) 0 sᶜ θ := by
        apply (hasDerivAt_const θ 0).hasDerivWithinAt.congr
        · intro t ht
          have hnot : ¬|t - c| < a := ht
          simp [smoothPrior, hnot]
        · simp [smoothPrior, hθ]
      have hall := hin.union houtside
      rw [union_compl_self, hasDerivWithinAt_univ] at hall
      simpa [smoothPriorDeriv, hθ] using hall

private theorem continuous_smoothPriorDeriv {c a : ℝ} (ha : 0 < a) :
    Continuous (smoothPriorDeriv c a) := by
  unfold smoothPriorDeriv
  apply Continuous.if
  · intro θ hθ
    have habs : |θ - c| = a :=
      frontier_lt_subset_eq
        (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const hθ
    have hsq : ((θ - c) / a) ^ 2 = 1 := by
      have habssq : |θ - c| ^ 2 = a ^ 2 := congrArg (fun x : ℝ => x ^ 2) habs
      rw [sq_abs] at habssq
      field_simp [ha.ne']
      nlinarith
    simp [hsq]
  · fun_prop
  · fun_prop

/-- A [positive bandwidth](hyp:ha) makes [the smooth quartic prior continuously
differentiable](goal). -/
theorem smoothPrior_contDiff {c a : ℝ} (ha : 0 < a) :
    ContDiff ℝ 1 (smoothPrior c a) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro θ
    exact (hasDerivAt_smoothPrior_aux ha θ).differentiableAt
  · have hderiv : deriv (smoothPrior c a) = smoothPriorDeriv c a := by
      funext θ
      exact (hasDerivAt_smoothPrior_aux ha θ).deriv
    rw [hderiv]
    exact continuous_smoothPriorDeriv ha

/-- Under a [positive bandwidth](hyp:ha), [the explicit derivative representative is
the derivative of the smooth quartic prior at every parameter value](goal). -/
theorem hasDerivAt_smoothPrior {c a : ℝ} (ha : 0 < a) (θ : ℝ) :
    HasDerivAt (smoothPrior c a) (smoothPriorDeriv c a θ) θ := by
  exact hasDerivAt_smoothPrior_aux ha θ

/-- A [positive bandwidth](hyp:ha) and [ordered endpoints](hyp:hellu) ensure that [the
smooth quartic prior is absolutely continuous on the interval](goal). -/
theorem smoothPrior_absolutelyContinuousOnInterval {ell u c a : ℝ} (ha : 0 < a)
    (hellu : ell ≤ u) :
    AbsolutelyContinuousOnInterval (smoothPrior c a) ell u := by
  exact (smoothPrior_contDiff ha).contDiffOn.absolutelyContinuousOnInterval

/-- Under a [positive bandwidth](hyp:ha), [the smooth quartic density has total
Lebesgue integral one](goal). -/
theorem integral_smoothPrior_volume {c a : ℝ} (ha : 0 < a) :
    ∫ θ, smoothPrior c a θ = 1 := by
  let p : ℝ → ℝ := fun t =>
    (15 / (16 * a)) * (1 - ((t - c) / a) ^ 2) ^ 2
  have hinterval : (∫ t in c - a..c + a, p t) = 1 := by
    let f : ℝ → ℝ := fun x => (1 - x ^ 2) ^ 2
    have hf : (∫ x : ℝ in (-1)..1, f x) = 16 / 15 := by
      have hfun : f = fun x => (1 - 2 * x ^ 2) + x ^ 4 := by
        funext x
        dsimp [f]
        ring
      rw [hfun, intervalIntegral.integral_add
        (Continuous.intervalIntegrable (μ := volume)
          (by fun_prop : Continuous (fun x : ℝ => 1 - 2 * x ^ 2)) (-1) 1)
        (Continuous.intervalIntegrable (μ := volume)
          (by fun_prop : Continuous (fun x : ℝ => x ^ 4)) (-1) 1)]
      rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (μ := volume)
          (by fun_prop : Continuous (fun _ : ℝ => (1 : ℝ))) (-1) 1)
        (Continuous.intervalIntegrable (μ := volume)
          (by fun_prop : Continuous (fun x : ℝ => 2 * x ^ 2)) (-1) 1)]
      rw [intervalIntegral.integral_const_mul, integral_pow, integral_pow]
      norm_num
    dsimp [p]
    rw [intervalIntegral.integral_const_mul]
    have hcomp := intervalIntegral.integral_comp_div_sub
      (a := c - a) (b := c + a) f ha.ne' (c / a)
    have heq : (∫ t in c - a..c + a, f ((t - c) / a)) =
        a * (∫ x in (-1)..1, f x) := by
      rw [show (fun t : ℝ => f ((t - c) / a)) = fun t => f (t / a - c / a) by
        funext t
        congr 1
        field_simp [ha.ne']]
      rw [hcomp]
      congr 2 <;> field_simp [ha.ne'] <;> ring
    rw [show (fun t : ℝ => (1 - ((t - c) / a) ^ 2) ^ 2) =
      fun t => f ((t - c) / a) by rfl]
    rw [heq, hf]
    field_simp [ha.ne']
  have hfun : smoothPrior c a = (Ioo (c - a) (c + a)).indicator p := by
    funext t
    by_cases ht : |t - c| < a
    · have hmem : t ∈ Ioo (c - a) (c + a) := by
        rw [mem_Ioo]
        rw [abs_lt] at ht
        constructor <;> linarith
      simp [smoothPrior, p, ht, hmem]
    · have hnotmem : t ∉ Ioo (c - a) (c + a) := by
        rw [mem_Ioo]
        rintro ⟨hlt, hrt⟩
        apply ht
        rw [abs_lt]
        constructor <;> linarith
      simp [smoothPrior, ht, hnotmem]
  rw [hfun, integral_indicator measurableSet_Ioo]
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le (by linarith : c - a ≤ c + a)]
  exact hinterval

/-- If [the bandwidth is positive](hyp:ha) and [the prior's left](hyp:hleft) and
[right](hyp:hright) support endpoints lie in an ambient interval, then [the prior has
mass one under Lebesgue measure restricted to that interval](goal). -/
theorem integral_smoothPrior_parameterMeasure {ell u c a : ℝ} (ha : 0 < a)
    (hleft : ell ≤ c - a) (hright : c + a ≤ u) :
    ∫ θ, smoothPrior c a θ ∂parameterMeasure ell u = 1 := by
  have hsupport : Function.support (smoothPrior c a) ⊆ Icc ell u := by
    rw [support_smoothPrior ha]
    rintro θ ⟨hθl, hθr⟩
    exact ⟨hleft.trans hθl.le, hθr.le.trans hright⟩
  unfold parameterMeasure
  rw [← integral_indicator measurableSet_Icc]
  have hfun : (Icc ell u).indicator (smoothPrior c a) = smoothPrior c a := by
    funext θ
    by_cases hθ : θ ∈ Icc ell u
    · simp [hθ]
    · have hz : smoothPrior c a θ = 0 := by
        by_contra hnz
        exact hθ (hsupport hnz)
      simp [hθ, hz]
  rw [hfun, integral_smoothPrior_volume ha]

/-- A [positive bandwidth](hyp:ha) makes [the smooth quartic prior integrable on every
restricted parameter interval](goal). -/
theorem smoothPrior_integrable_parameterMeasure {ell u c a : ℝ} (ha : 0 < a) :
    Integrable (smoothPrior c a) (parameterMeasure ell u) := by
  unfold parameterMeasure
  exact (smoothPrior_contDiff ha).continuous.integrableOn_Icc

private theorem smoothPrior_scoreSq_eq_indicator {c a : ℝ} (ha : 0 < a) :
    (fun θ => smoothPrior c a θ *
      (priorScore (smoothPrior c a) (smoothPriorDeriv c a) θ) ^ 2) =
      (Ioo (c - a) (c + a)).indicator
        (fun θ => (15 / a ^ 5) * (θ - c) ^ 2) := by
  funext θ
  by_cases hθ : |θ - c| < a
  · have hmem : θ ∈ Ioo (c - a) (c + a) := by
      rw [mem_Ioo]
      rw [abs_lt] at hθ
      constructor <;> linarith
    have hpos : 0 < smoothPrior c a θ := (smoothPrior_pos_iff ha).2 hθ
    have hr : |(θ - c) / a| < 1 := by
      rw [abs_div, abs_of_pos ha, div_lt_one ha]
      exact hθ
    have hs : ((θ - c) / a) ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one]
      exact hr
    simp only [priorScore, hpos, if_true]
    rw [smoothPrior, if_pos hθ, smoothPriorDeriv, if_pos hθ]
    simp only [indicator_of_mem hmem]
    have hbase : 1 - ((θ - c) / a) ^ 2 ≠ 0 := by linarith
    have hP : (15 / (16 * a)) * (1 - ((θ - c) / a) ^ 2) ^ 2 ≠ 0 := by
      apply mul_ne_zero
      · positivity
      · exact pow_ne_zero 2 hbase
    have hdeneq : θ * c * 2 - θ ^ 2 - c ^ 2 + a ^ 2 =
        a ^ 2 * (1 - ((θ - c) / a) ^ 2) := by
      field_simp [ha.ne']
      ring
    have hden : θ * c * 2 - θ ^ 2 - c ^ 2 + a ^ 2 ≠ 0 := by
      rw [hdeneq]
      exact mul_ne_zero (pow_ne_zero 2 ha.ne') hbase
    have hsimpleeq : a ^ 2 - (θ - c) ^ 2 =
        a ^ 2 * (1 - ((θ - c) / a) ^ 2) := by
      field_simp [ha.ne']
    have hsimple : a ^ 2 - (θ - c) ^ 2 ≠ 0 := by
      rw [hsimpleeq]
      exact mul_ne_zero (pow_ne_zero 2 ha.ne') hbase
    field_simp [ha.ne', hbase, hP, hden]
    try field_simp [hsimple]
    ring
  · have hnotmem : θ ∉ Ioo (c - a) (c + a) := by
      rw [mem_Ioo]
      rintro ⟨hlt, hrt⟩
      apply hθ
      rw [abs_lt]
      constructor <;> linarith
    simp [smoothPrior, hθ, hnotmem]

private theorem smoothPrior_scoreSq_integrable_aux {ell u c a : ℝ} (ha : 0 < a) :
    Integrable
      (fun θ => smoothPrior c a θ *
        (priorScore (smoothPrior c a) (smoothPriorDeriv c a) θ) ^ 2)
      (parameterMeasure ell u) := by
  rw [smoothPrior_scoreSq_eq_indicator ha]
  unfold parameterMeasure
  apply Integrable.mono_measure _ Measure.restrict_le_self
  rw [integrable_indicator_iff measurableSet_Ioo]
  apply (by fun_prop : Continuous (fun θ : ℝ => (15 / a ^ 5) * (θ - c) ^ 2)).integrableOn_Icc.mono_set
  exact Ioo_subset_Icc_self

/-- A [positive bandwidth](hyp:ha) makes [the prior-weighted squared guarded score
strongly measurable on every restricted parameter interval](goal). -/
theorem smoothPrior_scoreSq_aestronglyMeasurable {ell u c a : ℝ} (ha : 0 < a) :
    AEStronglyMeasurable
      (fun θ => smoothPrior c a θ *
        (priorScore (smoothPrior c a) (smoothPriorDeriv c a) θ) ^ 2)
      (parameterMeasure ell u) := by
  exact (smoothPrior_scoreSq_integrable_aux ha).aestronglyMeasurable

/-- A [positive bandwidth](hyp:ha) makes [the prior-weighted squared guarded score
integrable on every restricted parameter interval](goal). -/
theorem smoothPrior_scoreSq_integrable {ell u c a : ℝ} (ha : 0 < a) :
    Integrable
      (fun θ => smoothPrior c a θ *
        (priorScore (smoothPrior c a) (smoothPriorDeriv c a) θ) ^ 2)
      (parameterMeasure ell u) := by
  exact smoothPrior_scoreSq_integrable_aux ha

/-- If [the bandwidth is positive](hyp:ha) and [the prior's left](hyp:hleft) and
[right](hyp:hright) support endpoints lie in an ambient interval, then [the prior
Fisher information equals ten divided by the squared bandwidth](goal). -/
theorem priorInformation_smoothPrior {ell u c a : ℝ} (ha : 0 < a)
    (hleft : ell ≤ c - a) (hright : c + a ≤ u) :
    priorInformation ell u (smoothPrior c a) (smoothPriorDeriv c a) = 10 / a ^ 2 := by
  unfold priorInformation
  rw [smoothPrior_scoreSq_eq_indicator ha]
  unfold parameterMeasure
  rw [← integral_indicator measurableSet_Icc]
  have hfun : (Icc ell u).indicator
      ((Ioo (c - a) (c + a)).indicator
        (fun θ => (15 / a ^ 5) * (θ - c) ^ 2)) =
      (Ioo (c - a) (c + a)).indicator
        (fun θ => (15 / a ^ 5) * (θ - c) ^ 2) := by
    funext θ
    by_cases hθ : θ ∈ Ioo (c - a) (c + a)
    · have hambient : θ ∈ Icc ell u :=
        ⟨hleft.trans hθ.1.le, hθ.2.le.trans hright⟩
      simp [hθ, hambient]
    · simp [hθ]
  rw [hfun, integral_indicator measurableSet_Ioo]
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le (by linarith : c - a ≤ c + a)]
  let f : ℝ → ℝ := fun x => (15 / a ^ 3) * x ^ 2
  have hf : (∫ x : ℝ in (-1)..1, f x) = 10 / a ^ 3 := by
    dsimp [f]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    field_simp [ha.ne']
    norm_num
  have hcomp := intervalIntegral.integral_comp_div_sub
    (a := c - a) (b := c + a) f ha.ne' (c / a)
  have heq : (∫ θ in c - a..c + a, (15 / a ^ 5) * (θ - c) ^ 2) =
      a * (∫ x in (-1)..1, f x) := by
    rw [show (fun θ : ℝ => (15 / a ^ 5) * (θ - c) ^ 2) =
      fun θ => f (θ / a - c / a) by
        funext θ
        dsimp [f]
        field_simp [ha.ne']]
    rw [hcomp]
    congr 2 <;> field_simp [ha.ne'] <;> ring
  rw [heq, hf]
  field_simp [ha.ne']

/-- If [the bandwidth is positive](hyp:ha) and [the prior's left](hyp:hleft) and
[right](hyp:hright) support endpoints lie in an ambient interval, then [the prior
Fisher information is at most forty divided by the squared bandwidth](goal). -/
theorem priorInformation_smoothPrior_le {ell u c a : ℝ} (ha : 0 < a)
    (hleft : ell ≤ c - a) (hright : c + a ≤ u) :
    priorInformation ell u (smoothPrior c a) (smoothPriorDeriv c a) ≤ 40 / a ^ 2 := by
  rw [priorInformation_smoothPrior ha hleft hright]
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos ha)).2 (by norm_num)

end Causalean.Stat.Limit.ObservationDependentVanTrees
