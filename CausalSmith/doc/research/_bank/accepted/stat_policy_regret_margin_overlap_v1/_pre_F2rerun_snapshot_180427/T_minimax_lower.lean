/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy-regret rate: minimax lower bound (headline converse)

Stage-2 scaffold. The explicit two-point witness, its class membership and
χ²/separation analysis, the in-core Le Cam testing lemma, the CRUX converse
`thm:minimax-lower`, and the headline corollary `thm:rate-characterization`.
Every proof body is `sorry`.
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
import Causalean.Stat.Minimax.ChiSquared
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Pi

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

/-- `{0,1}`-supported Bernoulli observation-treatment measure with `P(A=1)=p`. -/
noncomputable def bernoulliReal (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (1 : ℝ)
    + ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)

/-- `{-1,1}`-supported outcome measure with mean `m` (`P(Y=1)=(1+m)/2`). -/
noncomputable def bernoulliPM (m : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 + m) / 2) • Measure.dirac (1 : ℝ)
    + ENNReal.ofReal ((1 - m) / 2) • Measure.dirac (-1 : ℝ)

-- @node: def:two-point-witness
/-- Explicit two-point least-favorable law `P_{n,σ}` on `𝒳=ℝ` with covariate
marginal Lebesgue on `[0,1]`, active block `B_n=[0, c_B h_n^α]`, weak-arm
propensity `q_n` on `B_n`, charged treated cell carrying contrast `σ h_n`, and
off-block contrast `τ_0=(u_0+2)/2 ∈ (u_0,2)`. The weak-arm scale is EXACTLY the
displayed `q_n = qLower α γ n` (`= 1/4` if `β_{α,γ}=0`, else `h_n^{β_{α,γ}}`),
which lies in `(0,1/2]` for all large `n`; the constants admissibility
`8 c_B c_Q < log 5` (`c_Q = 1` here) is carried by the divergence lemma. -/
noncomputable def twoPointWitness (α γ u0 cB : ℝ) (n : ℕ) (σ : ℝ) :
    ObservedLaw ℝ :=
  let h := hLower α γ n
  let q := qLower α γ n
  let τ0 := (u0 + 2) / 2
  let inBlock : ℝ → Prop := fun x => 0 ≤ x ∧ x ≤ cB * h ^ α
  let prop : ℝ → ℝ := fun x => if inBlock x then q else 1 / 2
  let contrast : ℝ → ℝ := fun x => if inBlock x then σ * h else τ0
  let mu0 : ℝ → ℝ := fun x => if inBlock x then 0 else -τ0 / 2
  let mu1 : ℝ → ℝ := fun x => if inBlock x then σ * h else τ0 / 2
  let outcome : ℝ → ℝ → Measure ℝ := fun x a =>
    if inBlock x then (if a = 1 then bernoulliPM (σ * h) else Measure.dirac 0)
    else (if a = 1 then bernoulliPM (τ0 / 2) else bernoulliPM (-τ0 / 2))
  { dataMeasure :=
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).bind fun x =>
        (bernoulliReal (prop x)).bind fun a =>
          (outcome x a).map (Observation.mk x a))
    PX := volume.restrict (Set.Icc (0 : ℝ) 1)
    contrast := contrast
    propensity := prop
    mu0 := mu0
    mu1 := mu1 }

-- @node: lem:witness-membership
/-- `lem:witness-membership`. For all large `n` the two witness laws belong to
`def:law-class`, and the two explicit witness-optimal policies are
`x ↦ 1` (under `P_{n,+}`) and `x ↦ 1{x ∉ B_n}` (under `P_{n,-}`); if these belong
to `Π` they are the two policy actions of the two-point reduction. The membership
is DERIVED from the construction, not assumed. -/
lemma witness_membership (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (Policy ℝ)) (σ : ℝ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hwin : MarginWindow u0)
    (hCm : 0 < Cm) (hCo : 0 < Co) (hco : 0 < co) (hcB : 0 < cB)
    (hcBm : cB ≤ Cm) (hcBo : cB ≤ Co) (hup : 0 < underlineP)
    (huple : underlineP ≤ 1 / 4) (hσ : σ = 1 ∨ σ = -1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      LawClass α γ Cm u0 Co co underlineP policySet
        (twoPointWitness α γ u0 cB n σ) ∧
      (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n 1) x = true) ∧
      (∀ x : ℝ, lawOptimalPolicy (twoPointWitness α γ u0 cB n (-1)) x = true ↔
        ¬ (0 ≤ x ∧ x ≤ cB * (hLower α γ n) ^ α)) := by
  sorry

-- @node: lem:two-point-divergence
/-- `lem:two-point-divergence`. The per-observation χ²-divergence scales as
`χ² ≤ C h_n^{2+α+β_{α,γ}} = C h_n^{D_{α,γ}}` (i.e. `m_n q_n h_n²` with
`m_n ~ h_n^α`, `q_n ~ h_n^{β_{α,γ}}`); with `h_n = n^{-1/D_{α,γ}}` the per-draw
divergence is `≤ C/n`, so by the product identity the `n`-fold divergence is
uniformly bounded. The admissibility `8 c_B c_Q < log 5` (`c_Q = 1` for the
`qLower` weak-arm scale) keeps the product divergence below a constant. -/
lemma two_point_divergence (α γ u0 cB : ℝ) (hcB : 0 < cB) (hα : 0 ≤ α)
    (hconst : 8 * cB < Real.log 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Causalean.Stat.chiSqDiv
            (twoPointWitness α γ u0 cB n 1).dataMeasure
            (twoPointWitness α γ u0 cB n (-1)).dataMeasure
          ≤ C * (hLower α γ n) ^ (2 + α + betaAG α γ) ∧
      Causalean.Stat.chiSqDiv
          (Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n 1).dataMeasure)
          (Measure.pi fun _ : Fin n => (twoPointWitness α γ u0 cB n (-1)).dataMeasure)
        ≤ C := by
  sorry

-- @node: lem:regret-separation
/-- `lem:regret-separation`. The witness optimal labels are opposite on `B_n`,
forcing regret separation `≥ c h_n^{1+α}` for every policy. -/
lemma regret_separation (α γ u0 cB : ℝ) (policySet : Set (Policy ℝ))
    (hcB : 0 < cB) (hα : 0 ≤ α) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ π ∈ policySet,
      max (lawRegret (twoPointWitness α γ u0 cB n 1) π)
          (lawRegret (twoPointWitness α γ u0 cB n (-1)) π)
        ≥ c * (hLower α γ n) ^ (1 + α) := by
  sorry

-- @node: lem:le-cam-two-point-chisq
/-- `lem:le-cam-two-point-chisq`. In-core two-point testing lemma: a bounded
χ²-divergence forces a positive testing-error floor for every test region. -/
lemma le_cam_two_point_chisq {Ω : Type*} [MeasurableSpace Ω]
    (Pp Pm : Measure Ω) [IsProbabilityMeasure Pp] [IsProbabilityMeasure Pm]
    (Cchi : ℝ) (hac : Pp ≪ Pm)
    (hchi : Causalean.Stat.chiSqDiv Pp Pm ≤ Cchi) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Set Ω, MeasurableSet A → Pp.real Aᶜ + Pm.real A ≥ c := by
  sorry

-- @node: thm:minimax-lower
/-- `thm:minimax-lower` (CRUX). The sharp constructive converse over the
baseline observed-law class: `M_n ≥ c n^{-r_⋆(α,γ)}` for all large `n`. -/
theorem minimax_lower (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (Policy ℝ))
    (hwin : MarginWindow u0) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hCm : 0 < Cm) (hCo : 0 < Co) (hco : 0 < co) (hcB : 0 < cB)
    (hcBm : cB ≤ Cm) (hcBo : cB ≤ Co) (hup : 0 < underlineP)
    (huple : underlineP ≤ 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      minimaxRegret
          {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P}
          policySet n
        ≥ c * (n : ℝ) ^ (-(rStar α γ)) := by
  sorry

-- @node: thm:rate-characterization
/-- `thm:rate-characterization` (HEADLINE, lower-bound only).
`M_n ≥ c n^{-(1+α)/(2+α+β_{α,γ})}`. -/
theorem rate_characterization (α γ u0 cB Cm Co co underlineP : ℝ)
    (policySet : Set (Policy ℝ))
    (hwin : MarginWindow u0) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hCm : 0 < Cm) (hCo : 0 < Co) (hco : 0 < co) (hcB : 0 < cB)
    (hcBm : cB ≤ Cm) (hcBo : cB ≤ Co) (hup : 0 < underlineP)
    (huple : underlineP ≤ 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      minimaxRegret
          {P : ObservedLaw ℝ | LawClass α γ Cm u0 Co co underlineP policySet P}
          policySet n
        ≥ c * (n : ℝ) ^ (-((1 + α) / (2 + α + betaAG α γ))) := by
  sorry

end CausalSmith.Stat.PolicyRegretMarginOverlap
