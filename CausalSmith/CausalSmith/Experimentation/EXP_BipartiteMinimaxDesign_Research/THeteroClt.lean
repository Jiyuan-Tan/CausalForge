/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: the heterogeneous Hájek CLT

`thm:hetero-clt`. At the envelope-optimal design, the studentized Hájek estimator
is asymptotically standard normal, via a first-order linearization onto the
centered scores and the bounded-degree dependency-graph CLT.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Envelope
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers
import Causalean.Experimentation.DesignBased.GaussianCDF

set_option linter.style.longLine false
set_option linter.unusedVariables false

open scoped BigOperators Topology
open Finset Filter
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference
open Causalean.SteinMethod

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {Ix Ox : ℕ → Type*} [∀ n, Fintype (Ix n)] [∀ n, Fintype (Ox n)]
  [∀ n, DecidableEq (Ix n)] [∀ n, DecidableEq (Ox n)]

open Classical in
-- @node: def:hetero-linearization-remainder
/-- The scaled Hájek-minus-linear-score remainder appearing in the first CLT
conjunct. -/
noncomputable def heteroLinearizationRemainder
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (p : ∀ n, Ix n → ℝ) (n : ℕ) (z : Ix n → Bool) : ℝ :=
  Real.sqrt (Fintype.card (Ox n)) * ((E n).hajekEstimator (p n) z - (E n).tau)
    - (Real.sqrt (Fintype.card (Ox n)))⁻¹ * ∑ i, (E n).linScore (p n) z i

open Classical in
-- @node: conclusion:hetero-clt-linearization
/-- Scaled Hájek ratio linearization conclusion.

This is the paper-specific delta-method remainder bound: after multiplying by
`√(card Ox)`, the Hájek ratio estimator differs from the linear score sum by an
`o_p(1)` remainder. This is a conclusion of `hetero_clt`, not an input gate. -/
def HeteroLinearization
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Tendsto (fun n =>
      (D n).Pr (fun z => δ ≤
        |heteroLinearizationRemainder E p n z|))
      atTop (𝓝 0)

open Classical in
-- @node: input:hetero-clt-denominator-tightness
/-- Denominator/ratio-remainder tightness input. **DISCHARGED** (2026-07-09) by
`heteroDenominatorTightness_discharged`: `hetero_clt` supplies it internally and does NOT assume it.
It survives only as a named `Prop`, because the linearization lemma reads more clearly against it.

Formerly the honest input gate feeding the Hájek linearization. The premise is the
regularity rate supplied to `hetero_clt`: the denominator kernel bound divided by
the outcome population size vanishes. The conclusion is the tightness of the
scaled ratio remainder produced by the denominator-ratio identity and local
numerator/score moment bounds. It is intentionally not the final CLT and is not
used as a studentized convergence statement. -/
def HeteroDenominatorTightnessInput
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ)
    (ε : ℕ → ℝ) (dbar : ℝ) : Prop :=
  ∃ productTail : ∀ n, (Ix n → Bool) → ℝ,
    (Tendsto (fun n =>
        denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ))
        atTop (𝓝 0) →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => (D n).Pr (fun z => δ ≤ productTail n z))
          atTop (𝓝 0)) ∧
    ∀ᶠ n in atTop, ∀ z,
      0 ≤ productTail n z ∧ |heteroLinearizationRemainder E p n z| ≤ productTail n z

open Classical in
-- @node: lem:hetero-linearization-from-denominator-tightness
/-- The first CLT conjunct is derived from the denominator/ratio-remainder tightness
gate plus the disclosed denominator-kernel regularity condition. -/
lemma hetero_linearization_of_denominator_tightness
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool))
    (p : ∀ n, Ix n → ℝ) (ε : ℕ → ℝ) (dbar : ℝ)
    (hdenomKernel :
      Tendsto (fun n => denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ))
        atTop (𝓝 0))
    (hDenomTightness : HeteroDenominatorTightnessInput E D p ε dbar) :
    HeteroLinearization E D p := by
  rcases hDenomTightness with ⟨productTail, hProductTail, hDominates⟩
  intro δ hδ
  exact squeeze_zero'
    (by
      filter_upwards with n
      exact (D n).Pr_nonneg _)
    (by
      filter_upwards [hDominates] with n hn
      exact (D n).Pr_mono _ _ (fun z hz => le_trans hz (hn z).2))
    (hProductTail hdenomKernel δ hδ)

open Classical in
-- @node: input:hetero-clt-linscore-depgraph-clt
/-- Linear-score dependency-graph CLT input. **DISCHARGED** by
`hetero_linscore_clt_of_depgraph`: `hetero_clt` supplies it internally and does NOT assume it.
It survives only as a named `Prop`.

Formerly the non-Hájek CLT fed by the already-built bounded-degree dependency-graph
substrate: assemble the overlap graph for `linScore`, verify bounded degree,
bounded summands, mean zero, and the variance floor, then apply
`bounded_degree_dependency_clt`.  It is deliberately stated for the linear score
statistic, not for the final Hájek statistic. -/
def HeteroLinScoreCLTInput
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ) : Prop :=
  ∀ s : ℝ, Tendsto (fun n =>
      (D n).Pr (fun z =>
        ((Real.sqrt (Fintype.card (Ox n)))⁻¹ * ∑ i, (E n).linScore (p n) z i)
          / Real.sqrt ((E n).varScale (D n) (p n)) ≤ s))
      atTop (𝓝 (stdNormalCdf s))

open Classical in
-- @node: lem:linscore-sum-square-integral-varScale
/-- The second moment of the raw linear-score sum is `card(O) * varScale`.
The statement is used on the eventual nonempty outcome-array tail supplied by
`hcardO`. -/
lemma linScore_sum_square_integral_eq_card_mul_varScale
    (E : BipartiteExperiment (Ix n) (Ox n))
    (D : FiniteDesign (Ix n → Bool)) (p : Ix n → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1)
    (hcard_pos : 0 < Fintype.card (Ox n)) :
    ∫ z, (∑ i, E.linScore p z i) ^ 2 ∂D.toMeasure =
      (Fintype.card (Ox n) : ℝ) * E.varScale D p := by
  classical
  rw [FiniteDesign.integral_toMeasure]
  have hsq : ∀ z,
      (∑ i, E.linScore p z i) ^ 2 =
        ∑ i : Ox n, ∑ j : Ox n, E.linScore p z i * E.linScore p z j := by
    intro z
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [D.E_congr hsq]
  rw [FiniteDesign.E_sum]
  simp_rw [FiniteDesign.E_sum]
  have hpair := varScale_pair_moments E D p hp0 hp1 hpos hlt hBern
  have hcard_ne : (Fintype.card (Ox n) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hcard_pos)
  calc
    (∑ x : Ox n, ∑ x_1 : Ox n,
        D.E fun z => E.linScore p z x * E.linScore p z x_1)
        = (Fintype.card (Ox n) : ℝ) *
            ((Fintype.card (Ox n) : ℝ)⁻¹ *
              ∑ i : Ox n, ∑ j : Ox n,
                D.E fun z => E.linScore p z i * E.linScore p z j) := by
          field_simp [hcard_ne]
    _ = (Fintype.card (Ox n) : ℝ) * E.varScale D p := by
          rw [hpair]

open Classical in
-- @node: lem:hetero-linscore-clt-from-depgraph
/-- The linear-score CDF CLT is discharged by the bounded-degree dependency-graph
engine. The additional `hεfloor` regularity is only a uniform positivity floor:
it turns the pointwise score bound into an eventual array-uniform summand bound. -/
lemma hetero_linscore_clt_of_depgraph
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool))
    (p : ∀ n, Ix n → ℝ) (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hbdd : ∀ n, BoundedOutcomes (E n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n)
    (hnd : VarianceNondegenerate (fun n => (E n).varScale (D n) (p n))) :
    HeteroLinScoreCLTInput E D p := by
  classical
  intro s
  rcases hεfloor with ⟨ε0, hε0_pos, hε0_ev⟩
  rcases eventually_atTop.1 hε0_ev with ⟨Nε, hNε⟩
  have hε0_lt : ε0 < 1 / 2 :=
    lt_of_le_of_lt (hNε Nε le_rfl) (hε Nε).2
  have hε0 : EpsilonAdmissible ε0 := ⟨hε0_pos, hε0_lt⟩
  let X : ∀ n, Ox n → (Ix n → Bool) → ℝ :=
    fun n i z => (E n).linScore (p n) z i
  let μ : ∀ n, MeasureTheory.Measure (Ix n → Bool) := fun n => (D n).toMeasure
  let Dep : ∀ n, DepGraph (X n) (μ n) := fun n =>
    linScoreDepGraph (E n) (D n) (p n) (hp0 n) (hp1 n) (hBern n)
  let v : ℕ → ℝ := fun n => ∫ z, (depSum (X n) z) ^ 2 ∂(μ n)
  let M : ℝ := 4 * (denominatorKernelBound ε0 dbar + 2)
  have hM : 0 ≤ M := by
    have hK : 0 ≤ denominatorKernelBound ε0 dbar := denominatorKernelBound_nonneg hε0_pos
    dsimp [M]
    nlinarith
  have hbound : ∀ᶠ n in atTop, ∀ i z, |X n i z| ≤ M := by
    filter_upwards [hε0_ev] with n hn i z
    have hfloor0 : PositivityFloor ε0 (p n) := by
      intro k
      constructor
      · exact hn.trans ((hfeas n).floor k).1
      · linarith [((hfeas n).floor k).2, hn]
    exact linScore_abs_le_uniform_floor (E n) ε0 dbar hε0 (hbdd n) (hdeg n)
      (p n) (hfeas n).prob hfloor0 z i
  have hmean : ∀ n i, ∫ z, X n i z ∂(μ n) = 0 := by
    intro n i
    have hpos : ∀ k, 0 < p n k := by
      intro k
      exact lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
    have hlt : ∀ k, p n k < 1 := by
      intro k
      linarith [((hfeas n).floor k).2, (hε n).1]
    change ∫ z, (E n).linScore (p n) z i ∂(D n).toMeasure = 0
    rw [FiniteDesign.integral_toMeasure]
    exact linScore_mean_zero (E n) (D n) (p n) (hp0 n) (hp1 n) hpos hlt (hBern n) i
  have hv : ∀ n, ∫ z, (depSum (X n) z) ^ 2 ∂(μ n) = v n := by
    intro n
    rfl
  rcases hnd with ⟨c, hc, hc_ev⟩
  have hvc : ∀ᶠ n in atTop,
      c * (Fintype.card (Ox n) : ℝ) ≤ v n := by
    filter_upwards [hc_ev, hcardO.eventually_ge_atTop 1] with n hvar hncard
    have hcard_pos : 0 < Fintype.card (Ox n) :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one hncard
    have hpos : ∀ k, 0 < p n k := by
      intro k
      exact lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
    have hlt : ∀ k, p n k < 1 := by
      intro k
      linarith [((hfeas n).floor k).2, (hε n).1]
    have hv_eq :
        v n = (Fintype.card (Ox n) : ℝ) * (E n).varScale (D n) (p n) := by
      change ∫ z, (∑ i, (E n).linScore (p n) z i) ^ 2 ∂(D n).toMeasure =
        (Fintype.card (Ox n) : ℝ) * (E n).varScale (D n) (p n)
      exact linScore_sum_square_integral_eq_card_mul_varScale (E n) (D n) (p n)
        (hp0 n) (hp1 n) hpos hlt (hBern n) hcard_pos
    rw [hv_eq]
    have hmul := mul_le_mul_of_nonneg_left hvar
      (show 0 ≤ (Fintype.card (Ox n) : ℝ) by positivity)
    nlinarith
  have hclt :=
    bounded_degree_dependency_clt_eventually_bounded
      (μ := μ) (X := X) (Dep := Dep)
      (Nat.ceil Dbar + 1)
      (fun n i => by
        simpa [Dep] using linScoreDepGraph_degree_le (E n) (D n) (p n)
          (hp0 n) (hp1 n) (hBern n) (hdep n) i)
      M hM hbound hmean v hv c hc hvc hcardO s
  rw [show stdNormalCdf s = (ProbabilityTheory.gaussianReal 0 1).real (Set.Iic s) from rfl]
  refine hclt.congr' ?_
  filter_upwards [hc_ev, hcardO.eventually_ge_atTop 1] with n hvar hncard
  have hcard_pos_nat : 0 < Fintype.card (Ox n) :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one hncard
  have hcard_pos : 0 < (Fintype.card (Ox n) : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hvar_pos : 0 < (E n).varScale (D n) (p n) := lt_of_lt_of_le hc hvar
  have hpos : ∀ k, 0 < p n k := by
    intro k
    exact lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
  have hlt : ∀ k, p n k < 1 := by
    intro k
    linarith [((hfeas n).floor k).2, (hε n).1]
  have hv_eq :
      v n = (Fintype.card (Ox n) : ℝ) * (E n).varScale (D n) (p n) := by
    change ∫ z, (∑ i, (E n).linScore (p n) z i) ^ 2 ∂(D n).toMeasure =
      (Fintype.card (Ox n) : ℝ) * (E n).varScale (D n) (p n)
    exact linScore_sum_square_integral_eq_card_mul_varScale (E n) (D n) (p n)
      (hp0 n) (hp1 n) hpos hlt (hBern n) hcard_pos_nat
  have hWmeas : Measurable (fun z : Ix n → Bool =>
      depSum (X n) z / Real.sqrt (v n)) := by
    exact (Finset.measurable_sum _ fun i _ => (Dep n).meas i).div_const _
  have hset :
      ({z : Ix n → Bool |
        ((Real.sqrt (Fintype.card (Ox n)))⁻¹ * ∑ i, (E n).linScore (p n) z i)
          / Real.sqrt ((E n).varScale (D n) (p n)) ≤ s} : Set (Ix n → Bool))
        =
      (fun z : Ix n → Bool => depSum (X n) z / Real.sqrt (v n)) ⁻¹' Set.Iic s := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    rw [hv_eq, Real.sqrt_mul hcard_pos.le, div_eq_mul_inv, div_eq_mul_inv]
    dsimp [X, depSum]
    ring_nf
  rw [← FiniteDesign.toMeasure_real_setOf, hset,
    MeasureTheory.map_measureReal_apply hWmeas measurableSet_Iic]

open Classical in
-- @node: lem:hetero-clt-slutsky-transfer
/-- Studentized Slutsky/converging-together transfer for the heterogeneous Hájek
CLT. The unstudentized linearization remainder vanishes in probability; the
variance nondegeneracy floor makes the studentized remainder vanish in
probability; the generic finite-design CDF converging-together helper then
transfers the linear-score CLT to the studentized Hájek statistic. -/
lemma hetero_studentized_slutsky
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool)) (p : ∀ n, Ix n → ℝ)
    (hLinearization : HeteroLinearization E D p)
    (hLinScoreCLT : HeteroLinScoreCLTInput E D p)
    (hnd : VarianceNondegenerate (fun n => (E n).varScale (D n) (p n))) :
    ∀ s : ℝ, Tendsto (fun n =>
      (D n).Pr (fun z =>
        Real.sqrt (Fintype.card (Ox n)) * ((E n).hajekEstimator (p n) z - (E n).tau)
          / Real.sqrt ((E n).varScale (D n) (p n)) ≤ s))
      atTop (𝓝 (stdNormalCdf s)) := by
  classical
  let S : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    Real.sqrt (Fintype.card (Ox n)) * ((E n).hajekEstimator (p n) z - (E n).tau)
      / Real.sqrt ((E n).varScale (D n) (p n))
  let T : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    ((Real.sqrt (Fintype.card (Ox n)))⁻¹ * ∑ i, (E n).linScore (p n) z i)
      / Real.sqrt ((E n).varScale (D n) (p n))
  have hApprox : ∀ η : ℝ, 0 < η →
      Tendsto (fun n => (D n).Pr (fun z => η ≤ |S n z - T n z|)) atTop (𝓝 0) := by
    intro η hη
    rcases hnd with ⟨c, hc, hc_ev⟩
    have hδpos : 0 < η * Real.sqrt c := mul_pos hη (Real.sqrt_pos.mpr hc)
    refine squeeze_zero'
      (by
        filter_upwards with n
        exact (D n).Pr_nonneg _)
      ?_
      (hLinearization (η * Real.sqrt c) hδpos)
    filter_upwards [hc_ev] with n hn
    apply (D n).Pr_mono
    intro z hz
    set v : ℝ := (E n).varScale (D n) (p n) with hvdef
    have hvpos : 0 < v := lt_of_lt_of_le hc (by simpa [v] using hn)
    have hsvpos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvpos
    have hsc_le : Real.sqrt c ≤ Real.sqrt v :=
      Real.sqrt_le_sqrt (by simpa [v] using hn)
    have hdiff : S n z - T n z = heteroLinearizationRemainder E p n z / Real.sqrt v := by
      simp [S, T, heteroLinearizationRemainder, v, div_eq_mul_inv]
      ring
    rw [hdiff, abs_div, abs_of_pos hsvpos] at hz
    have hmul : η * Real.sqrt v ≤ |heteroLinearizationRemainder E p n z| :=
      (le_div_iff₀ hsvpos).mp hz
    exact (mul_le_mul_of_nonneg_left hsc_le hη.le).trans hmul
  have hT : ∀ x : ℝ,
      Tendsto (fun n => (D n).Pr (fun z => T n z ≤ x)) atTop (𝓝 (stdNormalCdf x)) := by
    intro x
    simpa [T] using hLinScoreCLT x
  simpa [S] using
    finiteDesign_cdf_converging_together
      D S T stdNormalCdf hApprox hT continuous_stdNormalCdf

open Classical Causalean.Experimentation.DesignBased.FiniteDesign in
-- @node: lem:remainder-tendsto-zero
/-- **The scaled Hájek ratio remainder vanishes in probability.** Under the design/feasibility
regularity conditions and the vanishing denominator-kernel rate, the delta-method remainder
`√n·(τ̂_H − τ) − n^{-1/2}·∑ᵢ ηᵢ` converges to zero in probability.  This is the analytic core that
discharges the disclosed denominator-tightness gate. -/
lemma remainder_tendstoInProb_zero
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool))
    (p : ∀ n, Ix n → ℝ) (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hBI : ∀ n, BipartiteInterference (E n))
    (hbdd : ∀ n, BoundedOutcomes (E n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n)
    (hreg : Tendsto (fun n => denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ))
      atTop (𝓝 0)) :
    Causalean.Experimentation.DesignBased.FiniteDesign.TendstoInProb D
      (fun n z => heteroLinearizationRemainder E p n z) (fun _ => 0) := by
  let R1 : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    (Real.sqrt (Fintype.card (Ox n)))⁻¹ * treatNumerator (E n) (p n) z
  let R0 : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    (Real.sqrt (Fintype.card (Ox n)))⁻¹ * ctrlNumerator (E n) (p n) z
  let D1 : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    ∑ i, (E n).expT z i / (E n).piT (p n) i
  let D0 : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    ∑ i, (E n).expC z i / (E n).piC (p n) i
  let Q1 : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    (Fintype.card (Ox n) : ℝ)⁻¹ * D1 n z - 1
  let Q0 : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    (Fintype.card (Ox n) : ℝ)⁻¹ * D0 n z - 1
  let RHS : ∀ n, (Ix n → Bool) → ℝ := fun n z =>
    2 * |R1 n z| * |Q1 n z| + 2 * |R0 n z| * |Q0 n z|
  have hR1 : BoundedInProb D R1 := by
    simpa [R1] using treatNumerator_scaled_boundedInProb E D p hp0 hp1 ε B dbar Dbar
      hBern hbdd hdeg hdep hfeas hε hεfloor
  have hR0 : BoundedInProb D R0 := by
    simpa [R0] using ctrlNumerator_scaled_boundedInProb E D p hp0 hp1 ε B dbar Dbar
      hBern hbdd hdeg hdep hfeas hε hεfloor
  have hQ1 : TendstoInProb D Q1 (fun _ => 0) := by
    simpa [Q1, D1] using treatDenominatorRatioCentered_tendstoInProb_zero E D p hp0 hp1
      ε B dbar Dbar hcardO hBern hdeg hdep hfeas hε hreg
  have hQ0 : TendstoInProb D Q0 (fun _ => 0) := by
    simpa [Q0, D0] using ctrlDenominatorRatioCentered_tendstoInProb_zero E D p hp0 hp1
      ε B dbar Dbar hcardO hBern hdeg hdep hfeas hε hreg
  have hT1 : TendstoInProb D (fun n z => Q1 n z * R1 n z) (fun _ => 0) :=
    hQ1.mul_boundedInProb hR1
  have hT0 : TendstoInProb D (fun n z => Q0 n z * R0 n z) (fun _ => 0) :=
    hQ0.mul_boundedInProb hR0
  have hRHS : TendstoInProb D RHS (fun _ => 0) := by
    have hst : RHS = (fun n (z : Ix n → Bool) =>
        2 * |Q1 n z * R1 n z| + 2 * |Q0 n z * R0 n z|) := by
      funext n z; simp only [RHS, abs_mul]; ring
    rw [hst]
    simpa using ((hT1.abs).const_mul 2).add ((hT0.abs).const_mul 2)
  have hRHS_nonneg : ∀ n z, 0 ≤ RHS n z := by
    intro n z
    dsimp [RHS]
    positivity
  intro δ hδ
  simp only [sub_zero]
  have hQ1half : Tendsto (fun n =>
      (D n).Pr (fun z => (1 / 2 : ℝ) ≤ |Q1 n z|)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hQ1 (1 / 2) (by norm_num)
  have hQ0half : Tendsto (fun n =>
      (D n).Pr (fun z => (1 / 2 : ℝ) ≤ |Q0 n z|)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hQ0 (1 / 2) (by norm_num)
  have hbad : Tendsto (fun n => (D n).Pr (fun z =>
      (1 / 2 : ℝ) ≤ |Q1 n z| ∨ (1 / 2 : ℝ) ≤ |Q0 n z|)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => (D n).Pr (fun z => (1 / 2 : ℝ) ≤ |Q1 n z|)
        + (D n).Pr (fun z => (1 / 2 : ℝ) ≤ |Q0 n z|)) atTop (𝓝 0) := by
      simpa using hQ1half.add hQ0half
    exact squeeze_zero (fun n => (D n).Pr_nonneg _)
      (fun n => (D n).Pr_or_le _ _) hsum
  have htail : Tendsto (fun n =>
      (D n).Pr (fun z => δ ≤ RHS n z)) atTop (𝓝 0) := by
    have h := hRHS δ hδ
    simp only [sub_zero] at h
    have hEq : ∀ n, (fun z : Ix n → Bool => δ ≤ |RHS n z|)
                  = (fun z : Ix n → Bool => δ ≤ RHS n z) := by
      intro n; funext z; rw [abs_of_nonneg (hRHS_nonneg n z)]
    simp only [hEq] at h
    exact h
  have hcard : ∀ᶠ n in atTop, 1 ≤ Fintype.card (Ox n) :=
    hcardO.eventually_ge_atTop 1
  have hbound : ∀ᶠ n in atTop,
      (D n).Pr (fun z => δ ≤ |heteroLinearizationRemainder E p n z|) ≤
        (D n).Pr (fun z => (1 / 2 : ℝ) ≤ |Q1 n z| ∨ (1 / 2 : ℝ) ≤ |Q0 n z|) +
          (D n).Pr (fun z => δ ≤ RHS n z) := by
    filter_upwards [hcard] with n hn
    refine le_trans ?_ ((D n).Pr_or_le _ _)
    apply (D n).Pr_mono
    intro z hz
    by_cases hden : (Fintype.card (Ox n) : ℝ) / 2 ≤ D1 n z ∧
        (Fintype.card (Ox n) : ℝ) / 2 ≤ D0 n z
    · right
      have hcard_pos : 0 < Fintype.card (Ox n) :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      have hpos : ∀ k, 0 < p n k := fun k =>
        lt_of_lt_of_le (hε n).1 ((hfeas n).floor k).1
      have hlt : ∀ k, p n k < 1 := fun k => by
        linarith [((hfeas n).floor k).2, (hε n).1]
      have hrem := hajek_remainder_capped_bound (E n) (p n) z (hBI n) hpos hlt hcard_pos
        hden.1 hden.2
      have hrem' : |heteroLinearizationRemainder E p n z| ≤ RHS n z := by
        simpa [heteroLinearizationRemainder, RHS, R1, R0, Q1, Q0, D1, D0] using hrem
      exact hz.trans hrem'
    · left
      rw [not_and_or] at hden
      rcases hden with hD1 | hD0
      · left
        push_neg at hD1
        have hcard_pos : 0 < (Fintype.card (Ox n) : ℝ) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have hratio : (Fintype.card (Ox n) : ℝ)⁻¹ * D1 n z < 1 / 2 := by
          have hstep := mul_lt_mul_of_pos_left hD1 (inv_pos.mpr hcard_pos)
          have heq : (Fintype.card (Ox n) : ℝ)⁻¹ * ((Fintype.card (Ox n) : ℝ) / 2) = 1 / 2 := by
            field_simp
          linarith [hstep, heq]
        have hq : Q1 n z < -(1 / 2 : ℝ) := by
          dsimp [Q1]
          linarith
        rw [abs_of_nonpos (by linarith [hq])]
        linarith
      · right
        push_neg at hD0
        have hcard_pos : 0 < (Fintype.card (Ox n) : ℝ) := by
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have hratio : (Fintype.card (Ox n) : ℝ)⁻¹ * D0 n z < 1 / 2 := by
          have hstep := mul_lt_mul_of_pos_left hD0 (inv_pos.mpr hcard_pos)
          have heq : (Fintype.card (Ox n) : ℝ)⁻¹ * ((Fintype.card (Ox n) : ℝ) / 2) = 1 / 2 := by
            field_simp
          linarith [hstep, heq]
        have hq : Q0 n z < -(1 / 2 : ℝ) := by
          dsimp [Q0]
          linarith
        rw [abs_of_nonpos (by linarith [hq])]
        linarith
  exact squeeze_zero'
    (by
      filter_upwards with n
      exact (D n).Pr_nonneg _)
    hbound
    (by simpa using hbad.add htail)

open Classical in
-- @node: lem:hetero-denominator-tightness-discharged
/-- **The disclosed denominator-tightness gate is discharged.** Choosing the dominating product tail
to be the remainder's own absolute value reduces `HeteroDenominatorTightnessInput` to
`remainder_tendstoInProb_zero`. -/
lemma heteroDenominatorTightness_discharged
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool))
    (p : ∀ n, Ix n → ℝ) (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hBI : ∀ n, BipartiteInterference (E n))
    (hbdd : ∀ n, BoundedOutcomes (E n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n) :
    HeteroDenominatorTightnessInput E D p ε dbar := by
  refine ⟨fun n z => |heteroLinearizationRemainder E p n z|, ?_, ?_⟩
  · intro hreg δ hδ
    have h := remainder_tendstoInProb_zero E D p hp0 hp1 ε B dbar Dbar hcardO hBern hBI
      hbdd hdeg hdep hfeas hε hεfloor hreg δ hδ
    simpa only [sub_zero] using h
  · exact Filter.Eventually.of_forall (fun n z => ⟨abs_nonneg _, le_refl _⟩)

open Classical in
-- @node: thm:hetero-clt
/-- **Heterogeneous Hájek CLT.** Along a sequence of feasible experiments whose
design is the envelope-optimal design, `√n{τ̂_H − τ_n}` linearizes onto
`n^{-1/2} ∑_i η_i` (the remainder vanishing in probability), and the studentized
statistic converges in distribution to `N(0,1)` (in CDF form).

`hcardEq` pins the outcome index to the paper's triangular array indexed by `1..n`:
the paper's `n` **is** the number of outcome units `|O_n|`, so the Lean normalizers
`√(card (Ox n))` and `(card (Ox n))^{-1/2}` are literally the paper's `√n` and
`n^{-1/2}` on the eventual tail.  Assuming only `card (Ox n) → ∞` would admit
sequences with `card (Ox n) ≠ n`, on which the Lean statement is *not* equivalent to
the paper's; `hcardEq : ∀ᶠ n, card (Ox n) = n` restores the identification (and the
divergence `card (Ox n) → ∞` needed by the `√n` normalizer and the bounded-degree
dependency CLT is *derived* from it, not assumed).

  The denominator-kernel rate is derived in-proof from the listed assumptions
  (bounded degree, the ε-floor, outcome-cardinality growth). The ratio-remainder
  tightness is now DERIVED in-proof by `heteroDenominatorTightness_discharged` (the
  delta-method / product-tail `o_p` envelope for the Hájek ratio remainder), so this
  theorem is UNCONDITIONAL — the former `HeteroDenominatorTightnessInput` substrate-gate
  hypothesis has been removed. The linear-score dependency-graph CLT is discharged
  from the overlap dependency graph, bounded degree, mean-zero scores, the variance
  floor, outcome-cardinality growth, and the disclosed uniform ε-floor regularity. -/
theorem hetero_clt
    (E : ∀ n, BipartiteExperiment (Ix n) (Ox n))
    (D : ∀ n, FiniteDesign (Ix n → Bool))
    (p : ∀ n, Ix n → ℝ) (hp0 : ∀ n k, 0 ≤ p n k) (hp1 : ∀ n k, p n k ≤ 1)
    (ε B : ℕ → ℝ) (dbar Dbar : ℝ)
    (hcardEq : ∀ᶠ n in atTop, Fintype.card (Ox n) = n)   -- @realizes n(the paper's stage index IS the outcome-population size: n = |O_n| = card (Ox n) on the eventual tail) @realizes O_n(carrier `Ox n`, the outcome-unit index set, whose cardinality is the paper's n)
    (hBern : ∀ n, IndepHeteroBernoulli (D n) (p n) (hp0 n) (hp1 n))
    (hBI : ∀ n, BipartiteInterference (E n))
    (hbdd : ∀ n, BoundedOutcomes (E n))
    (hdeg : ∀ n, BoundedOutcomeDegree (E n) dbar)
    (hdep : ∀ n, BoundedOverlapDependency (E n) Dbar)
    (hfeas : ∀ n, FeasibleDesign (ε n) (B n) (p n))
    (hε : ∀ n, EpsilonAdmissible (ε n))
    (hstar : ∀ n, p n = optimalDesign (E n) (ε n) (B n))
    (hεfloor : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ᶠ n in atTop, ε0 ≤ ε n)
    (hnd : VarianceNondegenerate (fun n => (E n).varScale (D n) (p n))) :
    HeteroLinearization E D p
    ∧
    (∀ s : ℝ, Tendsto (fun n =>
        (D n).Pr (fun z =>
          Real.sqrt (Fintype.card (Ox n)) * ((E n).hajekEstimator (p n) z - (E n).tau)
            / Real.sqrt ((E n).varScale (D n) (p n)) ≤ s))
        atTop (𝓝 (stdNormalCdf s))) := by
  -- Derived (not assumed): `card (Ox n) = n` eventually forces `card (Ox n) → ∞`.
  have hcardO : Tendsto (fun n => Fintype.card (Ox n)) atTop atTop :=
    tendsto_id.congr' (hcardEq.mono fun n hn => hn.symm)
  -- Derived (not assumed): the uniform ε-floor bounds the denominator kernel by a
  -- constant `denominatorKernelBound ε0 dbar`, and `card (Ox n) → ∞` kills the ratio.
  have hdenomKernel :
      Tendsto (fun n => denominatorKernelBound (ε n) dbar / (Fintype.card (Ox n) : ℝ))
        atTop (𝓝 0) := by
    exact denominatorKernelBound_div_card_tendsto_zero (Ox := Ox) ε dbar hcardO hε hεfloor
  -- The ratio-remainder tightness is now DERIVED (formerly a disclosed substrate-gate hypothesis):
  -- the delta-method / product-tail `o_p` envelope for the Hájek ratio remainder is discharged by
  -- `heteroDenominatorTightness_discharged` from the same regularity conditions.
  have hDenomTightness : HeteroDenominatorTightnessInput E D p ε dbar :=
    heteroDenominatorTightness_discharged E D p hp0 hp1 ε B dbar Dbar hcardO hBern hBI
      hbdd hdeg hdep hfeas hε hεfloor
  have hLinearization :
      HeteroLinearization E D p :=
    hetero_linearization_of_denominator_tightness E D p ε dbar hdenomKernel
      hDenomTightness
  have hLinScoreCLT : HeteroLinScoreCLTInput E D p :=
    hetero_linscore_clt_of_depgraph E D p hp0 hp1 ε B dbar Dbar hcardO hBern hbdd hdeg hdep
      hfeas hε hεfloor hnd
  refine ⟨?_, ?_⟩
  · exact hLinearization
  · exact hetero_studentized_slutsky E D p hLinearization hLinScoreCLT hnd

/-- The dependency graph for the linearized outcome scores is unchanged when the experiment,
assignment design, treatment probabilities, and Bernoulli-design condition are replaced by equal
ones. -/
add_decl_doc linScoreDepGraph.congr_simp

end CausalSmith.Experimentation.BipartiteMinimaxDesign
