/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Class-level asymptotic equicontinuity and the `StochEquicontAt` reduction

`Causalean.Stat.StochEquicontAt` (`Equicontinuity/StochEquicont.lean`) is the
empirical-process hypothesis fed to the `Z`-estimator / GMM CLTs.  As literally
stated it is an *estimator-indexed* property: it conditions on the random event
`{‖θn − θ₀‖ < δ}` and asks the centered gap `R_n` evaluated **at the random
estimator** `θn` to vanish in probability.  That statement is only true when
`θn →_p θ₀`; it bundles together two genuinely separate ingredients:

* a **class-level** Donsker / asymptotic-equicontinuity property of the score
  family `{ψ(θ,·) − ψ(θ₀,·) : ‖θ − θ₀‖ < δ}`, which does **not** depend on `θn`
  (here: `AsymptoticEquicont`);
* **consistency** `θn →_p θ₀`.

This file isolates the first ingredient as `AsymptoticEquicont` and proves the
reduction

    AsymptoticEquicont  +  consistency  ⟹  StochEquicontAt.

This is the empirical-process step of van der Vaart (1998), Lemma 19.24: the
chaining/bracketing content lives entirely in `AsymptoticEquicont` (a property
of the function class), while the passage to the estimator is the elementary
union-bound argument carried out here.  Establishing `AsymptoticEquicont` for
concrete classes (finite, bracketing-entropy, …) is the subject of the sibling
files; the deterministic-curve special case
(`empProcVec_isLittleOp_of_L2`) is proved here directly from the second-moment
bound and requires neither chaining nor consistency.

**Deferred (known gap).**  `AsymptoticEquicont` for a *continuum* function class
via bracketing-entropy chaining is NOT established here — it is a genuine Mathlib
gap (no chaining / metric-entropy integral machinery upstream).  This layer
delivers `AsymptoticEquicont ⇒ StochEquicontAt` and the deterministic-curve and
finite-class instances; the continuum chaining instance remains open and is
deliberately left as a hypothesis for downstream CLT consumers.

References: van der Vaart (1998), §19.4, Lemma 19.24; Theorem 5.41.
-/

import Causalean.Stat.EmpiricalProcess.Equicontinuity.Process
import Causalean.Stat.EmpiricalProcess.Equicontinuity.SecondMoment
import Causalean.Stat.EmpiricalProcess.Equicontinuity.StochEquicont
import Causalean.Stat.Limit.Convergence

/-! # Asymptotic Equicontinuity Modulus

This file separates class-level asymptotic equicontinuity of an empirical
process from consistency of a random estimator.  It defines
`AsymptoticEquicont`, proves `empProcVec_atEstimator_tendsto_zero`, packages the
reduction `stochEquicontAt_of_asymptoticEquicont`, and supplies the deterministic
curve witness `empProcVec_isLittleOp_of_L2` from second-moment control.  The
continuum chaining/bracketing theorem is deliberately left as an external
hypothesis. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Class-level asymptotic equicontinuity** of the score family `ψ` at `θ₀`.

For every `ε > 0` and every probability tolerance `η > 0` there is a ball radius
`δ > 0` such that, eventually in `n`, the probability that the centered
empirical process `Gₙ(ψ(θ,·) − ψ(θ₀,·))` exceeds `ε` for **some** `θ` in the
`δ`-ball is at most `η`:

    ∀ ε > 0, ∀ η > 0, ∃ δ > 0, ∀ᶠ n,
      μ {ω | ∃ θ, ‖θ − θ₀‖ < δ ∧ ε < ‖Gₙ(ψ(θ,·) − ψ(θ₀,·))(ω)‖} ≤ η.

This is the standard double-limit asymptotic equicontinuity
`lim_{δ→0} limsup_n P*(sup_{‖θ−θ₀‖<δ} |Gₙ| > ε) = 0` (van der Vaart 1998,
§19.2), phrased with an existential over `θ` rather than a (possibly
non-measurable) supremum so that the outer-measure bookkeeping is automatic.
Unlike `StochEquicontAt`, it makes no reference to an estimator sequence: it is
a property of the function class and the sample alone, and it is what
bracketing-entropy / Donsker theorems actually establish. -/
def AsymptoticEquicont (ψ : E → X → E) (θ₀ : E) (P : Measure X)
    (μ : Measure Ω) (S : IIDSample Ω X μ P) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ n in atTop,
      μ {ω | ∃ θ : E, ‖θ - θ₀‖ < δ ∧
          ε < ‖S.empProcVec (fun z => ψ θ z - ψ θ₀ z) n ω‖}
        ≤ ENNReal.ofReal η

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Empirical process at the estimator vanishes.**

If the score family is asymptotically equicontinuous (`AsymptoticEquicont`) and
`θn →_p θ₀` (consistency), then the centered empirical process evaluated at the
estimator, `Gₙ(ψ(θn,·) − ψ(θ₀,·))`, converges to `0` in probability —
*unconditionally* (no `{‖θn − θ₀‖ < δ}` conditioning).

This is the substantive conclusion; `StochEquicontAt` is an immediate corollary.
The proof is the textbook union bound: split on `{‖θn − θ₀‖ ≥ δ}` (small by
consistency) and `{‖θn − θ₀‖ < δ}` (on which the gap is witnessed by `θ = θn`,
so the event sits inside the equicontinuity event). -/
theorem empProcVec_atEstimator_tendsto_zero
    (ψ : E → X → E) (θ₀ : E)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n =>
        μ {ω | ε < ‖S.empProcVec (fun z => ψ (θn n ω) z - ψ θ₀ z) n ω‖})
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  by_cases hγtop : γ = ⊤
  · filter_upwards with n; simp [hγtop]
  have hγpos : 0 < γ.toReal := ENNReal.toReal_pos (ne_of_gt hγ) hγtop
  set η : ℝ := γ.toReal / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδpos, hAEC_event⟩ := hAEC ε hε η hηpos
  have hδhalf : 0 < δ / 2 := by positivity
  have hCons_event :=
    (ENNReal.tendsto_nhds_zero.mp (hConsistent (δ / 2) hδhalf))
      (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hηpos)
  have hsum_le : ENNReal.ofReal η + ENNReal.ofReal η ≤ γ := by
    rw [← ENNReal.ofReal_add hηpos.le hηpos.le]
    have : η + η = γ.toReal := by rw [hη]; ring
    rw [this, ENNReal.ofReal_toReal hγtop]
  filter_upwards [hAEC_event, hCons_event] with n hAEC_n hCons_n
  -- `{ε < ‖R_n‖} ⊆ {δ/2 < ‖θn − θ₀‖} ∪ {∃ θ, ‖θ − θ₀‖ < δ ∧ ε < ‖Gₙ‖}`
  have hsub :
      {ω | ε < ‖S.empProcVec (fun z => ψ (θn n ω) z - ψ θ₀ z) n ω‖}
        ⊆ {ω | δ / 2 < ‖θn n ω - θ₀‖}
          ∪ {ω | ∃ θ : E, ‖θ - θ₀‖ < δ ∧
              ε < ‖S.empProcVec (fun z => ψ θ z - ψ θ₀ z) n ω‖} := by
    intro ω hω
    by_cases hθ : ‖θn n ω - θ₀‖ < δ
    · exact Or.inr ⟨θn n ω, hθ, hω⟩
    · refine Or.inl ?_
      have hδle : δ ≤ ‖θn n ω - θ₀‖ := not_lt.mp hθ
      change δ / 2 < ‖θn n ω - θ₀‖
      linarith
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
  exact le_trans (add_le_add hCons_n hAEC_n) hsum_le

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Reduction: `StochEquicontAt` from class-level equicontinuity + consistency.**

The `Z`-estimator / GMM CLTs (`zEstimator_clt`, `gmm_asymptotically_linear`)
take `StochEquicontAt` as a hypothesis.  This theorem discharges it from the
two clean ingredients it actually decomposes into: the Donsker / asymptotic-
equicontinuity property of the score family (`AsymptoticEquicont`, independent
of `θn`) and consistency `θn →_p θ₀`.  Any `δ` works since
`empProcVec_atEstimator_tendsto_zero` already gives the *unconditional* vanishing
of the gap. -/
theorem stochEquicontAt_of_asymptoticEquicont
    (ψ : E → X → E) (θ₀ : E)
    (S : IIDSample Ω X μ P) (θn : ℕ → Ω → E)
    (hAEC : AsymptoticEquicont ψ θ₀ P μ S)
    (hConsistent :
      ∀ ε > 0, Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0)) :
    StochEquicontAt ψ θ₀ P μ S θn := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  have hgap := empProcVec_atEstimator_tendsto_zero ψ θ₀ S θn hAEC hConsistent ε hε
  refine ENNReal.tendsto_nhds_zero.mpr ?_
  intro γ hγ
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hgap) γ hγ] with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  exact hω.2

/-- **Deterministic-curve equicontinuity (non-vacuousness witness).**

Along a *deterministic* parameter sequence `θn : ℕ → E` whose score
perturbation shrinks in `L²(P)` — `∫ ‖ψ(θn,·) − ψ(θ₀,·)‖² dP → 0` — the centered
empirical-process gap is `o_p(1)`, with **no chaining and no consistency
hypothesis**: it is a direct consequence of the uniform-in-`n` Chebyshev bound
`empProcVec_chebyshev`.

This is the base case of asymptotic equicontinuity (the parameter is moved along
a fixed curve rather than over a whole ball) and certifies that the
`AsymptoticEquicont` machinery is satisfiable.  The genuinely uniform
(sup-over-ball) statement is what requires bracketing-entropy / chaining. -/
theorem empProcVec_isLittleOp_of_L2 [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (ψ : E → X → E) (θ₀ : E) (θn : ℕ → E)
    (S : IIDSample Ω X μ P)
    (hψ_meas : ∀ θ, Measurable (fun x => ψ θ x - ψ θ₀ x))
    (hψ_L2 : ∀ θ, MemLp (fun x => ψ θ x - ψ θ₀ x) 2 P)
    (hmod : Tendsto (fun n => ∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P) atTop (𝓝 0)) :
    IsLittleOp
      (fun n ω => ‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖)
      (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  have hεsq : (0 : ℝ) < ε ^ 2 := by positivity
  have hset : ∀ n,
      {ω | ε * (fun _ => (1 : ℝ)) n <
          |‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖|}
        = {ω | ε < ‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖} := by
    intro n; ext ω; simp only [Set.mem_setOf_eq, mul_one, abs_norm]
  simp_rw [hset]
  have hbound : ∀ n,
      μ {ω | ε < ‖S.empProcVec (fun z => ψ (θn n) z - ψ θ₀ z) n ω‖}
        ≤ ENNReal.ofReal (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P)
            / ENNReal.ofReal (ε ^ 2) := fun n =>
    empProcVec_chebyshev S (fun z => ψ (θn n) z - ψ θ₀ z)
      (hψ_meas (θn n)) (hψ_L2 (θn n)) n hε
  have hdiv : Tendsto (fun n => ENNReal.ofReal (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P)
      / ENNReal.ofReal (ε ^ 2)) atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n => (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P) / ε ^ 2) atTop (𝓝 0) := by
      simpa using hmod.div_const (ε ^ 2)
    have heq : ∀ n, ENNReal.ofReal (∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P)
        / ENNReal.ofReal (ε ^ 2)
        = ENNReal.ofReal ((∫ x, ‖ψ (θn n) x - ψ θ₀ x‖ ^ 2 ∂P) / ε ^ 2) := fun n =>
      (ENNReal.ofReal_div_of_pos hεsq).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiv
    (fun n => zero_le) hbound

end Causalean.Stat
