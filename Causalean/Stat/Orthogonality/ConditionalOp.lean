/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Envelope-based stochastic-order helpers

Conditional/envelope wrappers around `IsBigOp` and `IsLittleOp` that consume
square-envelope bounds (typically arising from a conditional second-moment
calculation under a fold-A σ-algebra) and produce the corresponding
unconditional `O_p` / `o_p` statements.

These are causal-agnostic; they consume only the predicates from
`Causalean.Stat.Limit.Convergence`.

The file also collects the Cauchy–Schwarz "integrated bias ≤ L²-norm" bound
that is consumed by both `PlugIn.lean` (single-factor bias) and
`Remainder.lean` (product-rate AIPW bias).
-/

import Causalean.Stat.Limit.Convergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Stochastic-order helpers from envelopes and L² rates

This module turns deterministic or conditional-envelope estimates into the `O_p` and `o_p`
statements used in orthogonal-learning and cross-fit arguments.  The square-envelope lemmas
`IsBigOp.of_sqEnvelope` and `IsLittleOp.of_sqEnvelope` say that an almost-sure bound
`|X_n|^2 <= c_n`, together with an `O_p` or `o_p` bound for `c_n` at rate `r_n^2`, yields the
corresponding stochastic-order bound for `X_n` at rate `r_n`.

The file also contains two generic reduction tools for truncation and bounded convergence:
`IsLittleOp.of_eq_on_asymptotic` transfers an `o_p` result across an asymptotically negligible
exception set, and `lintegral_ofReal_tendsto_zero_of_bdd_isLittleOp` upgrades bounded convergence
in probability to convergence of the nonnegative `lintegral`.

The final section packages Cauchy-Schwarz bounds in the forms needed by estimation remainders.
`abs_integral_le_eLpNorm_two` controls a mean by an L2 norm on a probability space,
`integral_abs_mul_le_eLpNorm_mul_eLpNorm` bounds an integrated product by the product of L2 norms,
and `integral_op_of_eLpNorm_op` / `integral_abs_mul_op_of_eLpNorm_op` lift random L2-rate
statements to stochastic-order bounds for integrated biases.
-/

namespace Causalean.Stat

open MeasureTheory Filter Topology ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Envelope versions of `IsBigOp` / `IsLittleOp`

A square envelope `(X_n)² ≤ c_n` plus a stochastic-order bound on `c_n`
implies the corresponding bound on `X_n` itself.  The proof uses the
elementary `{|X_n| > t} ⊆ {c_n > t²}` inclusion plus monotonicity of `μ`. -/

/-- **Square-envelope `O_p` lemma.**  If `|X_n|² ≤ c_n` μ-a.s. and `c_n` is
`O_p(rₙ²)` with `rₙ > 0`, then `X_n = O_p(rₙ)`. -/
theorem IsBigOp.of_sqEnvelope
    {Xn : ℕ → Ω → ℝ} {cn : ℕ → Ω → ℝ} {rn : ℕ → ℝ}
    (hrn : ∀ n, 0 < rn n)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, (Xn n ω) ^ 2 ≤ cn n ω)
    (hcn_BigOp : IsBigOp cn (fun n => (rn n) ^ 2) μ) :
    IsBigOp Xn rn μ := by
  intro ε hε
  rcases hcn_BigOp ε hε with ⟨K, hK⟩
  let M : ℝ := max |K| 1
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_right |K| 1)
  have hKleM2 : K ≤ M ^ 2 := by
    have hKle_abs : K ≤ |K| := le_abs_self K
    have habs_le_M : |K| ≤ M := by
      dsimp [M]
      exact le_max_left |K| 1
    have hM_le_M2 : M ≤ M ^ 2 := by
      nlinarith [hMpos, (le_max_right |K| 1 : (1 : ℝ) ≤ M)]
    exact hKle_abs.trans (habs_le_M.trans hM_le_M2)
  have hpoint : ∀ n,
      μ {ω | M * rn n < |Xn n ω|} ≤
        μ {ω | K * (rn n) ^ 2 < |cn n ω|} := by
    intro n
    apply MeasureTheory.measure_mono_ae
    filter_upwards [hbound n] with ω hb hω
    have hMr_pos : 0 < M * rn n := mul_pos hMpos (hrn n)
    have hsqX : (M * rn n) ^ 2 < (Xn n ω) ^ 2 := by
      rw [← sq_abs (Xn n ω), sq_lt_sq]
      simpa [abs_of_pos hMr_pos] using hω
    have hleft_le : K * (rn n) ^ 2 ≤ M ^ 2 * (rn n) ^ 2 :=
      mul_le_mul_of_nonneg_right hKleM2 (sq_nonneg (rn n))
    have hmul_sq : M ^ 2 * (rn n) ^ 2 = (M * rn n) ^ 2 := by ring
    have hlt_cn : K * (rn n) ^ 2 < cn n ω := by
      calc
        K * (rn n) ^ 2 ≤ M ^ 2 * (rn n) ^ 2 := hleft_le
        _ = (M * rn n) ^ 2 := hmul_sq
        _ < (Xn n ω) ^ 2 := hsqX
        _ ≤ cn n ω := hb
    exact hlt_cn.trans_le (le_abs_self (cn n ω))
  refine ⟨M, ?_⟩
  exact le_trans (Filter.limsup_le_limsup (Eventually.of_forall hpoint)) hK

/-- **Square-envelope `o_p` lemma.**  If `|X_n|² ≤ c_n` μ-a.s. and `c_n` is
`o_p(rₙ²)` with `rₙ > 0`, then `X_n = o_p(rₙ)`. -/
theorem IsLittleOp.of_sqEnvelope
    {Xn : ℕ → Ω → ℝ} {cn : ℕ → Ω → ℝ} {rn : ℕ → ℝ}
    (hrn : ∀ n, 0 < rn n)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, (Xn n ω) ^ 2 ≤ cn n ω)
    (hcn_LittleOp : IsLittleOp cn (fun n => (rn n) ^ 2) μ) :
    IsLittleOp Xn rn μ := by
  intro ε hε
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcn := hcn_LittleOp (ε ^ 2) hε2
  have hpoint : ∀ n,
      μ {ω | ε * rn n < |Xn n ω|} ≤
        μ {ω | (ε ^ 2) * (rn n) ^ 2 < |cn n ω|} := by
    intro n
    apply MeasureTheory.measure_mono_ae
    filter_upwards [hbound n] with ω hb hω
    have hεr_pos : 0 < ε * rn n := mul_pos hε (hrn n)
    have hsqX : (ε * rn n) ^ 2 < (Xn n ω) ^ 2 := by
      rw [← sq_abs (Xn n ω), sq_lt_sq]
      simpa [abs_of_pos hεr_pos] using hω
    have hmul_sq : (ε ^ 2) * (rn n) ^ 2 = (ε * rn n) ^ 2 := by ring
    have hlt_cn : (ε ^ 2) * (rn n) ^ 2 < cn n ω := by
      calc
        (ε ^ 2) * (rn n) ^ 2 = (ε * rn n) ^ 2 := hmul_sq
        _ < (Xn n ω) ^ 2 := hsqX
        _ ≤ cn n ω := hb
    exact hlt_cn.trans_le (le_abs_self (cn n ω))
  rw [ENNReal.tendsto_nhds_zero] at hcn ⊢
  intro δ hδ
  exact (hcn δ hδ).mono fun n hn => (hpoint n).trans hn

/-! ## Truncation reduction and bounded convergence

Two generic helpers needed for the fold-B centered-sum argument:

* `IsLittleOp.of_eq_on_asymptotic`: if `Xn` and `X̃n` agree outside a set
  whose `μ`-measure tends to `0` and `X̃n = o_p(rn)`, then so is `Xn`.
* `lintegral_ofReal_tendsto_zero_of_bdd_isLittleOp`: a bounded sequence of
  random variables that goes to zero in probability also goes to zero in
  `L¹` (bounded convergence in probability).
-/

/-- **Truncation reduction.**  If `Xn` differs from `Yn` only on a set whose
`μ`-measure tends to `0`, and `Yn = o_p(rn)`, then `Xn = o_p(rn)`.

**Proof outline.**  For any `ε > 0`, `{|Xn| > ε rn} ⊆ {Xn ≠ Yn} ∪ {|Yn| > ε rn}`,
so `μ{|Xn| > ε rn} ≤ μ{Xn ≠ Yn} + μ{|Yn| > ε rn}`; the first summand vanishes
by hypothesis and the second by `h_tilde`. -/
theorem IsLittleOp.of_eq_on_asymptotic
    {Xn Yn : ℕ → Ω → ℝ} {rn : ℕ → ℝ}
    (h_diff_to_zero :
      Tendsto (fun n => μ {ω | Xn n ω ≠ Yn n ω}) atTop (𝓝 0))
    (h_tilde : IsLittleOp Yn rn μ) :
    IsLittleOp Xn rn μ := by
  intro ε hε
  have hY := h_tilde ε hε
  have hpoint : ∀ n,
      μ {ω | ε * rn n < |Xn n ω|} ≤
        μ {ω | Xn n ω ≠ Yn n ω} + μ {ω | ε * rn n < |Yn n ω|} := by
    intro n
    calc
      μ {ω | ε * rn n < |Xn n ω|}
          ≤ μ ({ω | Xn n ω ≠ Yn n ω} ∪ {ω | ε * rn n < |Yn n ω|}) := by
        apply measure_mono
        intro ω hω
        by_cases hxy : Xn n ω = Yn n ω
        · exact Or.inr (by simpa [hxy] using hω)
        · exact Or.inl hxy
      _ ≤ μ {ω | Xn n ω ≠ Yn n ω} + μ {ω | ε * rn n < |Yn n ω|} :=
        MeasureTheory.measure_union_le _ _
  have hsum :
      Tendsto
        (fun n => μ {ω | Xn n ω ≠ Yn n ω} + μ {ω | ε * rn n < |Yn n ω|})
        atTop (𝓝 0) := by
    simpa using h_diff_to_zero.add hY
  rw [ENNReal.tendsto_nhds_zero] at hsum ⊢
  intro δ hδ
  exact (hsum δ hδ).mono fun n hn => (hpoint n).trans hn

/-- **Bounded convergence in probability ⇒ L¹ convergence.**
If `Xn ω ∈ [0, M]` with `M ≥ 0` deterministic, each `Xn n` is measurable, and
`Xn = o_p(1)` under `μ` (with `μ` a probability measure), then
`∫⁻ ω, ENNReal.ofReal (Xn n ω) ∂μ → 0` in `ℝ≥0∞`.

**Proof outline.**  Bounded convergence in probability: `Xn → 0` in probability
and `0 ≤ Xn ≤ M` give `Xn → 0` in `L¹(μ)`.  Concretely, for any `δ > 0`,
split `∫ Xn dμ = ∫_{Xn ≤ δ} Xn dμ + ∫_{Xn > δ} Xn dμ ≤ δ + M · μ{Xn > δ}`;
take `δ` small and `n` large. -/
theorem lintegral_ofReal_tendsto_zero_of_bdd_isLittleOp
    [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hXn_meas : ∀ n, Measurable (Xn n))
    (hXn_nonneg : ∀ n ω, 0 ≤ Xn n ω)
    (hXn_bdd : ∀ n ω, Xn n ω ≤ M)
    (hXn_op : IsLittleOp Xn (fun _ => (1 : ℝ)) μ) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (Xn n ω) ∂μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · filter_upwards with n
    simp [hδtop]
  have hδreal_pos : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ) hδtop
  let η : ℝ := δ.toReal / 4
  let α : ℝ := δ.toReal / (4 * (M + 1))
  have hηpos : 0 < η := by
    dsimp [η]
    linarith
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos hδreal_pos (mul_pos (by norm_num) (by linarith))
  have hlintegral_le : ∀ n,
      ∫⁻ ω, ENNReal.ofReal (Xn n ω) ∂μ
        ≤ ENNReal.ofReal η +
          ENNReal.ofReal M * μ {ω | η * (1 : ℝ) < |Xn n ω|} := by
    intro n
    let A : Set Ω := {ω | Xn n ω ≤ η}
    have hA : MeasurableSet A := by
      dsimp [A]
      exact measurableSet_le (hXn_meas n) measurable_const
    have hsmall :
        ∫⁻ ω in A, ENNReal.ofReal (Xn n ω) ∂μ ≤ ENNReal.ofReal η := by
      calc
        ∫⁻ ω in A, ENNReal.ofReal (Xn n ω) ∂μ
            ≤ ∫⁻ ω in A, ENNReal.ofReal η ∂μ := by
          apply setLIntegral_mono measurable_const
          intro ω hω
          exact ENNReal.ofReal_le_ofReal hω
        _ = ENNReal.ofReal η * μ A := by
          rw [setLIntegral_const]
        _ ≤ ENNReal.ofReal η * μ Set.univ := by
          exact mul_le_mul' le_rfl (measure_mono (Set.subset_univ A))
        _ = ENNReal.ofReal η := by
          simp [MeasureTheory.measure_univ]
    have hlarge :
        ∫⁻ ω in Aᶜ, ENNReal.ofReal (Xn n ω) ∂μ
          ≤ ENNReal.ofReal M * μ {ω | η * (1 : ℝ) < |Xn n ω|} := by
      calc
        ∫⁻ ω in Aᶜ, ENNReal.ofReal (Xn n ω) ∂μ
            ≤ ∫⁻ ω in Aᶜ, ENNReal.ofReal M ∂μ := by
          apply setLIntegral_mono measurable_const
          intro ω hω
          exact ENNReal.ofReal_le_ofReal (hXn_bdd n ω)
        _ = ENNReal.ofReal M * μ Aᶜ := by
          rw [setLIntegral_const]
        _ ≤ ENNReal.ofReal M * μ {ω | η * (1 : ℝ) < |Xn n ω|} := by
          apply mul_le_mul' le_rfl
          apply measure_mono
          intro ω hω
          have hη_lt : η < Xn n ω := lt_of_not_ge hω
          simpa [abs_of_nonneg (hXn_nonneg n ω)] using hη_lt
    calc
      ∫⁻ ω, ENNReal.ofReal (Xn n ω) ∂μ
          = ∫⁻ ω in A, ENNReal.ofReal (Xn n ω) ∂μ +
              ∫⁻ ω in Aᶜ, ENNReal.ofReal (Xn n ω) ∂μ := by
        exact (lintegral_add_compl (μ := μ) (fun ω => ENNReal.ofReal (Xn n ω)) hA).symm
      _ ≤ ENNReal.ofReal η +
          ENNReal.ofReal M * μ {ω | η * (1 : ℝ) < |Xn n ω|} :=
        add_le_add hsmall hlarge
  have hprob_event :=
    (ENNReal.tendsto_nhds_zero.mp (hXn_op η hηpos)) (ENNReal.ofReal α)
      (ENNReal.ofReal_pos.mpr hαpos)
  filter_upwards [hprob_event] with n hn
  have hprod_le :
      ENNReal.ofReal M * μ {ω | η * (1 : ℝ) < |Xn n ω|}
        ≤ ENNReal.ofReal M * ENNReal.ofReal α := by
    exact mul_le_mul' le_rfl hn
  have hsum_eq :
      ENNReal.ofReal η + ENNReal.ofReal M * ENNReal.ofReal α =
        ENNReal.ofReal (η + M * α) := by
    rw [← ENNReal.ofReal_mul hM]
    rw [← ENNReal.ofReal_add (le_of_lt hηpos) (mul_nonneg hM (le_of_lt hαpos))]
  have hterm_le : M * α ≤ δ.toReal / 4 := by
    dsimp [α]
    field_simp [show (4 : ℝ) * (M + 1) ≠ 0 by nlinarith]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : M ≤ M + 1) (le_of_lt hδreal_pos)]
  have hsum_lt : ENNReal.ofReal (η + M * α) < δ := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal]
    · dsimp [η]
      nlinarith
    · dsimp [η]
      nlinarith [le_of_lt hδreal_pos, hM, le_of_lt hαpos]
    · exact hδtop
  exact le_of_lt <| (hlintegral_le n).trans_lt <| lt_of_le_of_lt (add_le_add le_rfl hprod_le) <|
    hsum_eq.trans_lt hsum_lt

/-! ## Cauchy–Schwarz: integrated bias is bounded by the L²-norm

For any measure `ν` on `X` with finite mass and any `f, g ∈ L²(ν)`,

    |∫ f · g dν| ≤ ‖f‖₂ · ‖g‖₂.

The constant case `g ≡ 1` collapses to `|∫ f dν| ≤ ‖f‖₂ · √(ν univ)`.
We package both forms because the plug-in bias uses the constant case and
the AIPW remainder uses the general case. -/

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- **Constant-case Cauchy–Schwarz.**  If `ν` is a probability measure (or, more
generally, satisfies `ν univ ≤ 1`) and `f ∈ L²(ν)`, then `|∫ f dν| ≤ ‖f‖₂`. -/
theorem abs_integral_le_eLpNorm_two
    [IsProbabilityMeasure ν]
    {f : X → ℝ} (hf : MemLp f 2 ν) :
    |∫ x, f x ∂ν| ≤ (eLpNorm f 2 ν).toReal := by
  have h_l1 : |∫ x, f x ∂ν| ≤ (eLpNorm f 1 ν).toReal := by
    calc
      |∫ x, f x ∂ν| ≤ ∫ x, |f x| ∂ν := MeasureTheory.abs_integral_le_integral_abs
      _ = (eLpNorm f 1 ν).toReal := by
        rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
        simpa [Real.norm_eq_abs] using MeasureTheory.integral_norm_eq_lintegral_enorm hf.1
  exact h_l1.trans (ENNReal.toReal_mono hf.eLpNorm_ne_top
    (MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf.1))

/-- **Cauchy–Schwarz for products of L²-functions.**  If `f, g ∈ L²(ν)`, then
`∫ |f · g| dν ≤ ‖f‖₂ · ‖g‖₂`.  Stated for the absolute value of the product
because that is the form consumed by the AIPW remainder bound. -/
theorem integral_abs_mul_le_eLpNorm_mul_eLpNorm
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ∫ x, |f x * g x| ∂ν ≤ (eLpNorm f 2 ν).toReal * (eLpNorm g 2 ν).toReal := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hg
  have hholder : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g)
    (p := 2) (q := 2) hholder hf' hg'
  have hf_eq : ((∫ x, ‖f x‖ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) =
      (eLpNorm f 2 ν).toReal := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · norm_num
    · exact Real.rpow_nonneg
        (integral_nonneg_of_ae (Eventually.of_forall fun x => by positivity)) _
  have hg_eq : ((∫ x, ‖g x‖ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) =
      (eLpNorm g 2 ν).toReal := by
    rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal]
    · norm_num
    · exact Real.rpow_nonneg
        (integral_nonneg_of_ae (Eventually.of_forall fun x => by positivity)) _
  convert h using 1
  · congr 1
    funext x
    simp [Real.norm_eq_abs, abs_mul]
  · rw [hf_eq, hg_eq]

/-! ## Stochastic-order consequences of an `eLpNorm` rate

Lifts an `IsLittleOp` bound on a random L²-norm into an `IsLittleOp` bound on
the integrated bias (or the integrated absolute product).  These are the two
direct corollaries used downstream. -/

/-- **L² rate ⇒ integrated bias rate (probability measure case).**
If `eLpNorm (f n ω) 2 ν = o_p(rₙ)` and `ν` is a probability measure, then
`(∫ x, f n ω x ∂ν) = o_p(rₙ)`. -/
theorem integral_op_of_eLpNorm_op
    [IsProbabilityMeasure ν]
    {fn : ℕ → Ω → X → ℝ}
    (hfn_memLp : ∀ n ω, MemLp (fn n ω) 2 ν)
    {rn : ℕ → ℝ} (hrn : ∀ n, 0 < rn n)
    (hfn_rate :
      IsLittleOp (fun n ω => (eLpNorm (fn n ω) 2 ν).toReal) rn μ) :
    IsLittleOp (fun n ω => ∫ x, fn n ω x ∂ν) rn μ := by
  have _hrn := hrn
  intro ε hε
  have htarget := hfn_rate ε hε
  have hpoint : ∀ n,
      μ {ω | ε * rn n < |∫ x, fn n ω x ∂ν|} ≤
        μ {ω | ε * rn n < |(eLpNorm (fn n ω) 2 ν).toReal|} := by
    intro n
    apply measure_mono
    intro ω hω
    exact (lt_of_lt_of_le hω (abs_integral_le_eLpNorm_two (hfn_memLp n ω))).trans_le
      (le_abs_self _)
  rw [ENNReal.tendsto_nhds_zero] at htarget ⊢
  intro δ hδ
  exact (htarget δ hδ).mono fun n hn => (hpoint n).trans hn

/-- **L² product rate ⇒ integrated absolute-product rate.**
If `eLpNorm (f n ω) 2 ν = o_p(sₙ)` and `g ∈ L²(ν)` is fixed, then
`∫ x, |f n ω x · g x| ∂ν = o_p(sₙ · ‖g‖₂)`. -/
theorem integral_abs_mul_op_of_eLpNorm_op
    {fn : ℕ → Ω → X → ℝ} {g : X → ℝ}
    (hfn_memLp : ∀ n ω, MemLp (fn n ω) 2 ν)
    (hg_memLp : MemLp g 2 ν)
    {sn : ℕ → ℝ} (hsn : ∀ n, 0 < sn n)
    (hfn_rate :
      IsLittleOp (fun n ω => (eLpNorm (fn n ω) 2 ν).toReal) sn μ) :
    IsLittleOp
      (fun n ω => ∫ x, |fn n ω x * g x| ∂ν)
      (fun n => sn n * (eLpNorm g 2 ν).toReal) μ := by
  have _hsn := hsn
  intro ε hε
  let c : ℝ := (eLpNorm g 2 ν).toReal
  have hc_nonneg : 0 ≤ c := ENNReal.toReal_nonneg
  by_cases hc : c = 0
  · rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    filter_upwards with n
    calc
      μ {ω | ε * (sn n * (eLpNorm g 2 ν).toReal) <
          |∫ x, |fn n ω x * g x| ∂ν|} ≤ μ (∅ : Set Ω) := by
        apply measure_mono
        intro ω hω
        have hle := integral_abs_mul_le_eLpNorm_mul_eLpNorm (hfn_memLp n ω) hg_memLp
        have hI_nonneg : 0 ≤ ∫ x, |fn n ω x * g x| ∂ν :=
          integral_nonneg fun x => abs_nonneg _
        have hI_zero : ∫ x, |fn n ω x * g x| ∂ν = 0 := by
          apply le_antisymm
          · simpa [c, hc] using hle
          · exact hI_nonneg
        have hI_prod_zero : ∫ x, |fn n ω x| * |g x| ∂ν = 0 := by
          simpa [abs_mul] using hI_zero
        have hI_prod_ne_zero : ¬ ∫ x, |fn n ω x| * |g x| ∂ν = 0 := by
          simpa [c, hc, abs_mul] using hω
        exact False.elim (hI_prod_ne_zero hI_prod_zero)
      _ = 0 := by simp
      _ ≤ δ := le_of_lt hδ
  · have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc)
    have htarget := hfn_rate ε hε
    have hpoint : ∀ n,
        μ {ω | ε * (sn n * (eLpNorm g 2 ν).toReal) <
            |∫ x, |fn n ω x * g x| ∂ν|} ≤
          μ {ω | ε * sn n < |(eLpNorm (fn n ω) 2 ν).toReal|} := by
      intro n
      apply measure_mono
      intro ω hω
      have hle := integral_abs_mul_le_eLpNorm_mul_eLpNorm (hfn_memLp n ω) hg_memLp
      have hI_nonneg : 0 ≤ ∫ x, |fn n ω x * g x| ∂ν :=
        integral_nonneg fun x => abs_nonneg _
      have hI_prod_nonneg : 0 ≤ ∫ x, |fn n ω x| * |g x| ∂ν :=
        integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hIlt : ε * (sn n * c) < ∫ x, |fn n ω x * g x| ∂ν := by
        have hIlt_prod : ε * (sn n * c) < ∫ x, |fn n ω x| * |g x| ∂ν := by
          simpa [c, abs_mul, abs_of_nonneg hI_prod_nonneg] using hω
        simpa [abs_mul] using hIlt_prod
      have hnorm_nonneg : 0 ≤ (eLpNorm (fn n ω) 2 ν).toReal := ENNReal.toReal_nonneg
      have hlt : ε * sn n < (eLpNorm (fn n ω) 2 ν).toReal := by
        nlinarith
      exact hlt.trans_le (le_abs_self _)
    rw [ENNReal.tendsto_nhds_zero] at htarget ⊢
    intro δ hδ
    exact (htarget δ hδ).mono fun n hn => (hpoint n).trans hn

end Causalean.Stat
