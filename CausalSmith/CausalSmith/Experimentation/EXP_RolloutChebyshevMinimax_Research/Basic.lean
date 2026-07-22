/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TV-envelope rollout node placement (Chebyshev minimax): shared core

Stage-2 scaffold for `exp_rollout_chebyshev_minimax`.

This file carries the two environment worlds (S1 the finite-population monotone-Bernoulli
rollout DESIGN world, reused from `Causalean.Experimentation.DesignBased.FiniteDesign`; S2
the real/polynomial optimal-recovery ambient over Mathlib), the four modeling/envelope
assumption `def`s (threaded Props, never discharged), the construction `def`s, the law
class structure `RolloutLawClass`, and the small inherited-setup identity
`rollout_polynomial_identity`. Each emitted top-level declaration carries its `@node` tag.

## Causalean substrate survey

| Submodule | Decision | Reason |
| --- | --- | --- |
| `Causalean.Experimentation.DesignBased.DesignCore` (`FiniteDesign`/`E`/`Var`/`Cov`) | reuse (S1) | the finite-population rollout randomization π is exactly a PMF on a finite assignment space with finite-sum moments; `Var_pi(bar_Y_j)` = `FiniteDesign.Var`, `w'Γ_P(p)w` = `FiniteDesign.Var (∑ wⱼ barYⱼ)`. |
| `Causalean.Experimentation.DesignBased.{HT,EdgeVarianceBound,CompoundVariance}` | bypass-justified | these DERIVE per-unit design variance from exposure/edge network structure; this paper ASSUMES the round-variance envelope as an input, a different (and weaker) abstraction, so the HT variance derivations are not a fit. |
| `Causalean.Experimentation.DesignBased.Optimality.Minimax` | bypass-justified | Neyman-allocation design minimax, not the ℓ¹ node-placement amplification `A_β(p)`; `lean_local_search` for amplification/mesh/Chebyshev-node returned none. |
| Mathlib `Polynomial.Chebyshev.T`, `Real.cos`, `Real.sqrt`, `sInf`/`sSup` | reuse (S2) | the schedules `S_{k,q}`, weights `W_β(p)`, amplification `A_β`/`M`, and Chebyshev/equal grids are pure real/polynomial optimal-recovery objects. |
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Round
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Causalean.Experimentation.DesignBased.DesignCore

open Causalean.Experimentation.DesignBased
open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

/-! ## Environment S1 — finite-population monotone-Bernoulli rollout DESIGN world

The randomization `π` is a `FiniteDesign Ω`: a PMF on a finite assignment space with
finite-sum `E`/`Var`/`Cov`. The round means `bar_Y_j : Ω → ℝ` are real random variables of
the realized assignment; `Var_pi(bar_Y_j)` is `FiniteDesign.Var (barY j)`, and the exact
covariance form `w'Γ_P(p)w` is `FiniteDesign.Var (fun z => ∑ j, w j * barY j z)`. The
potential outcomes `Y_i(z)`, the rollout assignment vectors `Z_j`, the population `U_n`,
the mean curve `m_P`, its polynomial coefficients `a_{P,ℓ}`, and the target `τ_P` are all
exposed at this abstract `FiniteDesign` level (matching the paper's honest scope: the
novelty is the design object, not new PO machinery).

`@env: S1` -/

/-! ### Assumption atoms (threaded Props) -/

-- @node: ass:static-rollout-consistency
/-- Static rollout potential outcomes with no carryover (CortezRodriguezEichhornYu2024):
the observed round mean equals `bar_Y_j = n⁻¹ ∑_{i∈U_n} Y_i(Z_j)`, with the potential
outcomes depending on the contemporaneous assignment vector `Z_j` (the argument of `Y`)
but not on earlier rollout steps. Inherited setup; threaded Prop, never discharged.
@realizes bar_Y_j(barY j z = n⁻¹ ∑ Y_i(Z_j))
@realizes Y_i(z)(Y : units → assignment → ℝ)
@realizes Z_j(Z j z : assignment vector at round j)
@realizes U_n(unit index Fin n) -/
def StaticRolloutConsistency (n k : ℕ) {Ω : Type*} [Fintype Ω]
    (Y : Fin n → (Fin n → Bool) → ℝ) (Z : Fin (k + 1) → Ω → (Fin n → Bool))
    (barY : Fin (k + 1) → Ω → ℝ) : Prop :=
  ∀ (j : Fin (k + 1)) (z : Ω), barY j z = (n : ℝ)⁻¹ * ∑ i, Y i (Z j z)

-- @node: ass:beta-order-polynomial
/-- β-order rollout polynomial identity (CortezEichhornYu2022): the rollout mean curve is a
degree-β polynomial `m_P(u) = ∑_{ℓ=0}^β a_{P,ℓ} uˡ` on `[0,1]`. Inherited setup; threaded Prop.
@realizes m_P(m u = ∑ a_ℓ uˡ on [0,1])
@realizes a_{P,0}, ..., a_{P,beta}(coefficient vector a : ℕ → ℝ, indices 0..β) -/
def BetaOrderPolynomial (beta : ℕ) (m : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → m u = ∑ ell ∈ Finset.range (beta + 1), a ell * u ^ ell

-- @node: ass:round-mean-variance-envelope
/-- NOVEL total-variation design envelope: for every round `j`, the design variance of the
round mean is bounded by `σ₀²/n`. The paper's declared TV envelope INPUT, not a proof
obligation; threaded Prop, never discharged.
@realizes sigma_0^2(envelope constant σ₀² with Var_pi(barY j) ≤ σ₀²/n) -/
def RoundMeanVarianceEnvelope (n k : ℕ) {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (barY : Fin (k + 1) → Ω → ℝ) (sigma0sq : ℝ) : Prop :=
  ∀ j : Fin (k + 1), D.Var (barY j) ≤ sigma0sq / (n : ℝ)

-- @node: ass:low-budget-cap
/-- Low-budget regime cap: `q ≤ q_max < 1`, with the ambient budget-cap range `q_max ∈ (0,1)`.
The leading conjunct `0 < q_max` realizes the core space of `q_max` (which is `(0,1)`, not just
`(-∞,1)`); every consumer taking `LowBudgetCap q qmax` inherits `0 < q_max` by name. Threaded
modeling Prop.
@realizes q_max(low-budget cap 0 < q_max < 1) -/
def LowBudgetCap (q qmax : ℝ) : Prop := 0 < qmax ∧ q ≤ qmax ∧ qmax < 1

/-! ## Environment S2 — real / polynomial ℓ¹ optimal-recovery ambient

Budgeted schedules `S_{k,q}`, linear-unbiased weight vectors `W_β(p)`, the ℓ¹ amplification
criterion `A_β(p)` and its minimax value `M_{β,k,q}`, the Chebyshev grid, and the equal grid
are pure real-analytic objects over `Fin (k+1) → ℝ` and `Polynomial ℝ`.

`@env: S2` -/

-- @node: def:budgeted-schedule-class
/-- Budgeted rollout schedules
`S_{k,q} = { p ∈ [0,1]^(k+1) : p₀ = 0, 0 < p₁ < ... < p_k = q }`. The paper's ambient schedule
range `p ∈ [0,1]^(k+1)` is carried by the first conjunct (each coordinate lies in `[0,1]`).
The budget `q` is the treated endpoint `p (last k) = q`; combined with `p 0 = 0`, `StrictMono p`
and `p j ∈ [0,1]` this pins the core space `q ∈ (0,1]` (`0 = p 0 < p (last k) = q ≤ 1`).
@realizes p(schedule Fin (k+1) → [0,1]: carrier ℝ + Icc range clause)
@realizes q(carrier ℝ; range (0,1] via p (last k) = q with p 0 = 0, StrictMono p, Icc clause)
@realizes S_{k,q}(p j ∈ Icc 0 1, p 0 = 0, StrictMono p, p (last k) = q) -/
def BudgetedSchedule (k : ℕ) (q : ℝ) (p : Fin (k + 1) → ℝ) : Prop :=
  (∀ j, p j ∈ Set.Icc (0 : ℝ) 1) ∧ p 0 = 0 ∧ StrictMono p ∧ p (Fin.last k) = q

-- @node: def:unbiased-weight-set
/-- Linear-unbiased rollout weights `W_β(p) = { w : ∑ⱼ wⱼ pⱼ⁰ = 0, ∑ⱼ wⱼ pⱼˡ = 1, ℓ=1..β }`.
@realizes W_beta(p)(∑ wⱼ pⱼ⁰ = 0 and ∑ wⱼ pⱼˡ = 1 for 1≤ℓ≤β)
@realizes w(weight vector Fin (k+1) → ℝ) -/
def UnbiasedWeights (beta k : ℕ) (p w : Fin (k + 1) → ℝ) : Prop :=
  (∑ j : Fin (k + 1), w j * (p j) ^ (0 : ℕ) = 0) ∧
    (∀ ell : ℕ, 1 ≤ ell → ell ≤ beta → ∑ j : Fin (k + 1), w j * (p j) ^ ell = 1)

-- @node: def:chebyshev-schedule
/-- Shifted Chebyshev-Lobatto rollout schedule `pⱼ^Ch(k,q) = q(1 - cos(π j / k))/2`.
Carrier `Fin (k+1) → ℝ` (the closed-form grid). Its core space `p^Ch(k,q) ∈ [0,1]^(k+1)` is
NOT free from the formula alone: since `1 - cos ∈ [0,2]`, each coordinate lands in `[0,q] ⊆ [0,1]`
precisely when `k ≥ 1` and `q ∈ (0,1]`. This range clause is realized by
`chebyshev_schedule_admissible`, whose conclusion `BudgetedSchedule k q (p^Ch(k,q))` carries the
`[0,1]^(k+1)` membership `∀ j, p^Ch(k,q) j ∈ Set.Icc 0 1` (its first conjunct) together with
`p 0 = 0`, `StrictMono`, `p (last k) = q` — so the carrier `def` here plus that admissibility
lemma together pin `p^Ch(k,q)` to its declared space. The budget parameter `q` (carrier `q : ℝ`)
has space `(0,1]`, pinned by the same admissibility range predicate `hq : 0 < q ∧ q ≤ 1`.
@realizes p^Ch(k,q)(carrier q(1 - cos(π j/k))/2;
  range [0,1]^(k+1) via chebyshev_schedule_admissible → BudgetedSchedule Icc clause, k≥1, q∈(0,1])
@realizes q(carrier ℝ; range 0 < q ≤ 1 pinned by chebyshev_schedule_admissible.hq) -/
noncomputable def chebyshevSchedule (k : ℕ) (q : ℝ) : Fin (k + 1) → ℝ :=
  fun j => q * (1 - Real.cos (Real.pi * (j : ℝ) / (k : ℝ))) / 2

-- @node: def:amplification-criterion
/-- Total-variation amplification of a fixed schedule `A_β(p) = inf_{w∈W_β(p)} (∑ⱼ|wⱼ|)²`.
@realizes A_beta(p)(inf over W_β(p) of (∑|wⱼ|)²) -/
noncomputable def amplification (beta k : ℕ) (p : Fin (k + 1) → ℝ) : ℝ :=
  sInf { v : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧ v = (∑ j, |w j|) ^ 2 }

-- @node: def:amplification-criterion
/-- Minimax amplification over budgeted schedules `M_{β,k,q} = inf_{p∈S_{k,q}} A_β(p)`.
@realizes M_{beta,k,q}(inf over S_{k,q} of A_β(p)) -/
noncomputable def minimaxAmplification (beta k : ℕ) (q : ℝ) : ℝ :=
  sInf { v : ℝ | ∃ p : Fin (k + 1) → ℝ, BudgetedSchedule k q p ∧ v = amplification beta k p }

/-- Minimal low-budget exponential base
`ρ_Ch(c,q_max) = inf { ρ ≥ 1 : sup_{β≥1} sup_{q∈(0,q_max]} qᵝ A_β(p^Ch(⌈cβ⌉,q))^{1/2} ρ^{-β} < ∞ }`.
The named minimax base of the shifted Chebyshev-Lobatto schedule. Carrier `ℝ`; its core space
`[1,∞)` is realized by the CONJUNCTION of (i) the `1 ≤ ρ` conjunct in the set predicate, which
makes `1` a lower bound of the defining set, and (ii) the range lemma `one_le_rhoCh` proved after
`chebyshev_minimax`, which discharges the `sInf` value itself to `1 ≤ ρ_Ch` (the element-wise
`1 ≤ ρ` conjunct alone does NOT pin the infimum, since `sInf ∅ = 0`; the value `≥ 1` needs the set
to be nonempty, from the Chebyshev upper bound). The `sup < ∞` is encoded as boundedness
`∃ M, ∀ …, qᵝ A_β^{1/2} ≤ M·ρᵝ` (equivalent to `qᵝ A_β^{1/2} ρ^{-β} ≤ M` since `ρ ≥ 1 > 0`).
@realizes rho_Ch(c,q_max)(carrier ℝ; def = minimal base infimum over the [1,∞)-predicate set) -/
noncomputable def rhoCh (c qmax : ℝ) : ℝ :=
  sInf { rho : ℝ | 1 ≤ rho ∧
    ∃ M : ℝ, ∀ beta : ℕ, 1 ≤ beta → ∀ q : ℝ, 0 < q → q ≤ qmax →
      q ^ beta * Real.sqrt (amplification beta ⌈c * (beta : ℝ)⌉₊
          (chebyshevSchedule ⌈c * (beta : ℝ)⌉₊ q)) ≤ M * rho ^ beta }

-- @node: def:rollout-law-class
/-- The static β-order rollout TV-envelope law class `P_β`, bundling the three member
assumptions plus the defining pinning of the mean curve `m_P` to the law
(`E_pi[bar_Y_j] = m_P(p_j)`, the schedule-point restriction of `m_P(u) = E_pi(bar_Y_j∣p_j=u)`;
required so `m` is not a free auxiliary widening the class).
@realizes P_beta(bundle of static-rollout, β-polynomial, variance-envelope + mean-curve pinning)
@realizes m_P(mean_curve : E_pi[barY j] = m (p j)) -/
structure RolloutLawClass (n k beta : ℕ) {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (Y : Fin n → (Fin n → Bool) → ℝ) (Z : Fin (k + 1) → Ω → (Fin n → Bool))
    (barY : Fin (k + 1) → Ω → ℝ) (m : ℝ → ℝ) (a : ℕ → ℝ) (sigma0sq : ℝ)
    (p : Fin (k + 1) → ℝ) : Prop where
  /-- Member: static rollout consistency (`ass:static-rollout-consistency`). -/
  static_rollout : StaticRolloutConsistency n k Y Z barY
  /-- Member: β-order rollout polynomial (`ass:beta-order-polynomial`). -/
  beta_polynomial : BetaOrderPolynomial beta m a
  /-- Member: round-mean TV variance envelope (`ass:round-mean-variance-envelope`). -/
  variance_envelope : RoundMeanVarianceEnvelope n k D barY sigma0sq
  /-- Defining pinning of the law functional `m_P` to the design: the round mean at round `j`
  has design expectation `m_P(p_j)`. -/
  mean_curve : ∀ j : Fin (k + 1), D.E (barY j) = m (p j)

-- @node: def:exact-nested-risk
/-- Exact finite-population nested-rollout minimax risk handle
`R_exact(β,k,q) = inf_{p∈S_{k,q}} inf_{w∈W_β(p)} sup_{P∈P_β} w'Γ_P(p)w`, where
`w'Γ_P(p)w = Var_pi(∑ⱼ wⱼ bar_Y_j)` is the exact design variance under the monotone-Bernoulli
rollout `π = D`. The supremum ranges over laws `P` (fixed potential outcomes / round means on
the common randomization `D`) in the class `RolloutLawClass`.
@realizes R_exact(beta,k,q)(inf_p inf_w sup_P w'Γ_P(p)w)
@realizes Gamma_P(p)(w'Γ_P(p)w = D.Var (∑ wⱼ barYⱼ)) -/
noncomputable def exactNestedRisk (n k beta : ℕ) {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)
    (q sigma0sq : ℝ) : ℝ :=
  sInf { rp : ℝ | ∃ p : Fin (k + 1) → ℝ, BudgetedSchedule k q p ∧
    rp = sInf { rw : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧
      rw = sSup { rP : ℝ | ∃ (Y : Fin n → (Fin n → Bool) → ℝ)
          (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
          (m : ℝ → ℝ) (a : ℕ → ℝ),
        RolloutLawClass n k beta D Y Z barY m a sigma0sq p ∧
          rP = D.Var (fun z => ∑ j, w j * barY j z) } } }

/-! ## Inherited-setup identity -/

-- @node: prop:rollout-polynomial-identity
/-- Under static rollout consistency and the β-order polynomial identity,
`τ_P = m_P(1) - m_P(0) = ∑_{ℓ=1}^β a_{P,ℓ}` (polynomial endpoint evaluation). Inherited setup
from CortezEichhornYu2022; recalled only to reduce `τ_P` to a degree-β endpoint functional. -/
lemma rollout_polynomial_identity (n k beta : ℕ) {Ω : Type*} [Fintype Ω]
    (Y : Fin n → (Fin n → Bool) → ℝ) (Z : Fin (k + 1) → Ω → (Fin n → Bool))
    (barY : Fin (k + 1) → Ω → ℝ) (m : ℝ → ℝ) (a : ℕ → ℝ)
    (hcons : StaticRolloutConsistency n k Y Z barY)
    (hpoly : BetaOrderPolynomial beta m a) :
    m 1 - m 0 = ∑ ell ∈ Finset.Icc 1 beta, a ell := by
  have _ : StaticRolloutConsistency n k Y Z barY := hcons
  have h1 : m 1 = ∑ ell ∈ Finset.range (beta + 1), a ell := by
    simpa using hpoly 1 (by norm_num)
  have h0 : m 0 = a 0 := by
    calc
      m 0 = ∑ ell ∈ Finset.range (beta + 1), a ell * 0 ^ ell := hpoly 0 (by norm_num)
      _ = a 0 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro b hb hbne
          simp [zero_pow hbne]
        · simp
  have hsplit : (∑ ell ∈ Finset.range (beta + 1), a ell) =
      a 0 + ∑ ell ∈ Finset.Icc 1 beta, a ell := by
    clear hpoly h1 h0
    induction beta with
    | zero => simp
    | succ beta ih =>
        rw [Finset.sum_range_succ]
        rw [ih]
        rw [Finset.sum_Icc_succ_top (Nat.succ_pos beta)]
        ring
  rw [h1, h0, hsplit]
  ring

end CausalSmith.Experimentation.RolloutChebyshev
