/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mogstad-Torgovitsky-Walters response-type algebra

Finite binary response-type weights for the MTW multiple-IV 2SLS
characterization.  This file includes the saturated finite-support bridge from
reduced-form and first-stage moments to the response-type ratio.  The observed
measure-backed `E[h(Z)Y] / E[h(Z)D]` bridge lives in
`MultipleInstrumentIV/Population.lean`.

Source labels:

* `def:po-estimand-mtw-system`
* `thm:po-estimand-mtw-signed-decomposition`
* `prop:po-estimand-mtw-response-type-form`
* `ass:po-estimand-mtw-partial-monotonicity`
* `prop:po-estimand-mtw-positive-weights`
-/

import Causalean.PO.ID.Exact.MultipleInstrumentIV.FiniteIndex
import Causalean.Panel.Weighted.NormalizedWeights
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Pi
/-! # Multiple-Instrument IV Response Types

This file formalizes the finite response-type algebra used in the
Mogstad-Torgovitsky-Walters multiple-instrument IV decomposition. The basic
objects are `ResponseType`, `typeStep`, `ResponseTypeStats`, the unnormalized
and normalized weights `unnormTypeWeight` and `normalizedTypeWeight`, and the
finite ratio `beta2SLSFiniteAlgebra`.

The nested `PopulationBridge` structure gives a saturated finite-support
bridge from support-point outcome and treatment expansions to the response-type
ratio. Theorems `firstStageMoment_eq_typeWeightDenom`,
`reducedFormMoment_eq_typeWeightNumerator`, and
`beta2SLSPopulationBridge_eq_beta2SLSFiniteAlgebra` prove the algebraic
identification step. The sign-alignment results
`normalizedTypeWeight_nonneg_of_signAligned`,
`normalizedTypeWeight_sum_eq_one_of_pos`, and
`beta2SLSFiniteAlgebra_eq_positiveResponseTypeAverage` explain when the ratio
is a convex response-type average, while `exists_negativeNormalizedTypeWeight`
gives a concrete two-support-point counterexample with a negative normalized
weight.

The `ComponentwiseMonotoneRestriction` structure is intentionally documented as
an opaque interface, not a faithful formalization of MTW partial monotonicity. -/

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset

/-- A response type is the binary vector
`g = (D(z^1), ..., D(z^K))`. -/
abbrev ResponseType (K : ℕ) := Fin K → Bool

/-- Coerce a binary treatment indicator to the real values `0` and `1`. -/
def boolToReal (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Adjacent response increment `d_j - d_{j-1}` for a response type. -/
def typeStep {K : ℕ} (g : ResponseType K) (j : Adj K) : ℝ :=
  boolToReal (g (Adj.upper j)) - boolToReal (g (Adj.lower j))

/-- Finite response-type statistics: type masses and type-specific treatment
effects `Δ_g`, with masses forming a probability vector. -/
structure ResponseTypeStats (K : ℕ) where
  /-- Response-type mass `π_g = P(G = g)`. -/
  mass : ResponseType K → ℝ
  /-- Response-type causal effect `Δ_g`.  Zero-mass conventions are handled at
  the finite-algebra layer by multiplying by `mass`. -/
  effect : ResponseType K → ℝ
  /-- Response-type masses are nonnegative. -/
  mass_nonneg : ∀ g, 0 ≤ mass g
  /-- Response-type masses sum to one. -/
  mass_sum_one : ∑ g, mass g = 1

namespace ResponseTypeStats

variable {K : ℕ} (I : FiniteIndex K) (R : ResponseTypeStats K)

/-- Unnormalized MTW response-type weight
`λ_g = π_g Σ_j B_j (d_j - d_{j-1})`. -/
noncomputable def unnormTypeWeight (g : ResponseType K) : ℝ :=
  R.mass g * ∑ j : Adj K, I.tailCoeff j * typeStep g j

/-- First-stage denominator in response-type form, `Σ_g λ_g`. -/
noncomputable def typeWeightDenom : ℝ :=
  ∑ g : ResponseType K, R.unnormTypeWeight I g

/-- Normalized response-type weight `ω_g = λ_g / Σ_g' λ_g'`. -/
noncomputable def normalizedTypeWeight (g : ResponseType K) : ℝ :=
  Causalean.Panel.Weighted.NormalizedWeights.normalizedWeight (R.unnormTypeWeight I) g

/-- Signed response-type weighted estimand
`Σ_g ω_g Δ_g`. -/
noncomputable def responseTypeEstimand : ℝ :=
  ∑ g : ResponseType K, R.normalizedTypeWeight I g * R.effect g

/-- Finite-algebra ratio after the MTW response-type partition: numerator
`Σ_g λ_g Δ_g`, denominator `Σ_g λ_g`.  The saturated finite-support
population bridge below proves when the population 2SLS moment ratio reduces to
this finite algebraic ratio. -/
noncomputable def beta2SLSFiniteAlgebra : ℝ :=
  (∑ g : ResponseType K, R.unnormTypeWeight I g * R.effect g) /
    R.typeWeightDenom I

/-- Saturated finite-support population bridge for the MTW identification
step.  The response-type masses and effects carry the finite partition of the
population, while `baseOutcome g` records the response-type-specific baseline
mean.  The centered first-stage index makes this baseline term cancel, leaving
the telescoped adjacent treatment increments used by the finite algebra. -/
structure PopulationBridge (K : ℕ) where
  /-- Response-type masses and type-specific treatment effects. -/
  stats : ResponseTypeStats K
  /-- Response-type-specific baseline outcome mean, the term subtracted by the
  centered-index argument in the signed decomposition proof. -/
  baseOutcome : ResponseType K → ℝ

namespace PopulationBridge

variable {K : ℕ} (I : FiniteIndex K) (P : PopulationBridge K)

/-- Telescoped adjacent treatment response for support point `k`, i.e.
`Σ_{j≤k} (d_j - d_{j-1})` in zero-based Lean indexing. -/
noncomputable def telescopedTypeStep (g : ResponseType K) (k : Fin K) : ℝ :=
  ∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0

/-- Response-type expansion of the potential outcome at support point `k`
after consistency, exogeneity, and exclusion have replaced conditioning on
`Z = zᵏ` by response-type averages. -/
noncomputable def outcomeAtSupport (P : PopulationBridge K) (k : Fin K) : ℝ :=
  ∑ g : ResponseType K,
    P.stats.mass g *
      (P.baseOutcome g + telescopedTypeStep g k * P.stats.effect g)

/-- Response-type expansion of the potential treatment at support point `k`,
written in the baseline-subtracted telescoped form used by the centered-index
argument. -/
noncomputable def treatmentAtSupport (P : PopulationBridge K) (k : Fin K) : ℝ :=
  ∑ g : ResponseType K, P.stats.mass g * telescopedTypeStep g k

/-- Population reduced-form moment `E[h(Z)Y]` after the finite-support
identification reductions. -/
noncomputable def reducedFormMoment (P : PopulationBridge K) (I : FiniteIndex K) : ℝ :=
  ∑ k : Fin K, I.rho k * I.centeredIndex k * P.outcomeAtSupport k

/-- Population first-stage moment `E[h(Z)D]` after the same finite-support
identification reductions. -/
noncomputable def firstStageMoment (P : PopulationBridge K) (I : FiniteIndex K) : ℝ :=
  ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k

/-- Population multiple-IV 2SLS ratio in the saturated finite-support bridge. -/
noncomputable def beta2SLSPopulationBridge (P : PopulationBridge K) (I : FiniteIndex K) : ℝ :=
  P.reducedFormMoment I / P.firstStageMoment I

/-- The baseline outcome component vanishes because the first-stage index is
centered. -/
theorem baselineMoment_eq_zero :
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ g : ResponseType K, P.stats.mass g * P.baseOutcome g)) = 0 := by
  calc
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ g : ResponseType K, P.stats.mass g * P.baseOutcome g)) =
        (∑ k : Fin K, I.rho k * I.centeredIndex k) *
          (∑ g : ResponseType K, P.stats.mass g * P.baseOutcome g) := by
      rw [Finset.sum_mul]
    _ = 0 := by
      rw [I.centered_weight_sum_zero]
      simp

/-- The finite-support first-stage moment is the response-type denominator.
This is the denominator half of the MTW identification step. -/
theorem firstStageMoment_eq_typeWeightDenom :
    P.firstStageMoment I = P.stats.typeWeightDenom I := by
  classical
  unfold firstStageMoment treatmentAtSupport telescopedTypeStep ResponseTypeStats.typeWeightDenom
    ResponseTypeStats.unnormTypeWeight
  calc
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ g : ResponseType K,
            P.stats.mass g *
              (∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0))) =
        ∑ k : Fin K, ∑ g : ResponseType K,
          I.rho k * I.centeredIndex k *
            (P.stats.mass g *
              (∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ = ∑ g : ResponseType K, ∑ k : Fin K,
          I.rho k * I.centeredIndex k *
            (P.stats.mass g *
              (∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0)) := by
      rw [Finset.sum_comm]
    _ = ∑ g : ResponseType K,
          P.stats.mass g *
            (∑ k : Fin K,
              I.rho k * I.centeredIndex k *
                (∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0)) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = ∑ g : ResponseType K,
          P.stats.mass g * (∑ j : Adj K, I.tailCoeff j * typeStep g j) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [I.tail_sum_interchange (fun j => typeStep g j)]

/-- The finite-support reduced-form moment is the response-type numerator.
This is the numerator half of the MTW identification step. -/
theorem reducedFormMoment_eq_typeWeightNumerator :
    P.reducedFormMoment I =
      ∑ g : ResponseType K, P.stats.unnormTypeWeight I g * P.stats.effect g := by
  classical
  unfold reducedFormMoment outcomeAtSupport telescopedTypeStep
    ResponseTypeStats.unnormTypeWeight
  calc
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ g : ResponseType K,
            P.stats.mass g *
                (P.baseOutcome g +
                  (∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0) *
                    P.stats.effect g))) =
        (∑ k : Fin K,
          I.rho k * I.centeredIndex k *
            (∑ g : ResponseType K, P.stats.mass g * P.baseOutcome g)) +
          ∑ k : Fin K,
            I.rho k * I.centeredIndex k *
              (∑ g : ResponseType K,
                  P.stats.mass g *
                    ((∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0) *
                    P.stats.effect g)) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ = ∑ k : Fin K,
          I.rho k * I.centeredIndex k *
            (∑ g : ResponseType K,
              P.stats.mass g *
                ((∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0) *
                  P.stats.effect g)) := by
      rw [P.baselineMoment_eq_zero I]
      simp
    _ = ∑ k : Fin K, ∑ g : ResponseType K,
          I.rho k * I.centeredIndex k *
            (P.stats.mass g *
              ((∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0) *
                P.stats.effect g)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
    _ = ∑ g : ResponseType K,
          ∑ k : Fin K,
            I.rho k * I.centeredIndex k *
              (P.stats.mass g *
                ((∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0) *
                  P.stats.effect g)) := by
      rw [Finset.sum_comm]
    _ = ∑ g : ResponseType K,
          P.stats.mass g *
            (∑ k : Fin K,
              I.rho k * I.centeredIndex k *
                (∑ j : Adj K, if j.1.val ≤ k.val then typeStep g j else 0)) *
            P.stats.effect g := by
      apply Finset.sum_congr rfl
      intro g _hg
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    _ = ∑ g : ResponseType K,
          (P.stats.mass g * (∑ j : Adj K, I.tailCoeff j * typeStep g j)) *
            P.stats.effect g := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [I.tail_sum_interchange (fun j => typeStep g j)]

/-- Saturated finite-support MTW identification: the population 2SLS ratio
`E[h(Z)Y] / E[h(Z)D]`, after consistency/exogeneity/exclusion and telescoping,
is exactly the finite response-type ratio. -/
theorem beta2SLSPopulationBridge_eq_beta2SLSFiniteAlgebra :
    P.beta2SLSPopulationBridge I = P.stats.beta2SLSFiniteAlgebra I := by
  unfold beta2SLSPopulationBridge ResponseTypeStats.beta2SLSFiniteAlgebra
  rw [P.reducedFormMoment_eq_typeWeightNumerator I,
    P.firstStageMoment_eq_typeWeightDenom I]

end PopulationBridge

/-- MTW sign alignment: every positive-mass response type has a nonnegative
tail-weighted step contrast. -/
def SignAligned : Prop :=
  ∀ g : ResponseType K, 0 < R.mass g →
    0 ≤ ∑ j : Adj K, I.tailCoeff j * typeStep g j

/-- Opaque response-type restriction interface.

**Interface-only restriction, not a faithful formalization of MTW partial monotonicity.**

This structure is an unconstrained interface: `allowed` is an arbitrary
predicate and `step_nonneg_of_allowed` is an axiom field with no semantic
grounding.  It encodes **neither**:

- the paper's componentwise monotonicity condition `D(z_l', z_{-l}) ≥ D(z_l,
  z_{-l})` a.s. for z_l' ≥ z_l (which would require rectangular
  instrument-support modeling outside this interface), nor
- the full MTW partial-monotonicity framework from `ass:po-estimand-mtw-partial-
  monotonicity`.

There is **no theorem** in the four MTW files connecting this structure to
`SignAligned`.  The paper's key implication chain

    componentwise monotonicity → sign alignment → nonneg weights → causal interpretation

is entirely absent from the formalization (Gaps G3, G7 in
`doc/basic_concepts/po/estimand_characterization/audit/mtw.md`).  Fixing this
requires (H2) a `RectSupport` type, (H3) a `ComponentwiseMonotone_implies_SignAligned`
theorem, and (H1) a `MultipleIVSystem` wrapper.

This structure is **unused in every theorem** in the four MTW files.  Do not
treat it as a faithful representation of any causal monotonicity condition. -/
structure ComponentwiseMonotoneRestriction where
  /-- Response types admitted by the restriction.  This predicate is
  unconstrained; nothing in Lean forces it to correspond to any geometric or
  probabilistic monotonicity condition. -/
  allowed : ResponseType K → Prop
  /-- Allowed response types have nonnegative adjacent steps in the displayed
  support order.  This is an axiom field, not a derived fact. -/
  step_nonneg_of_allowed :
    ∀ g : ResponseType K, allowed g → ∀ j : Adj K, 0 ≤ typeStep g j

/-- Sign alignment and nonnegative type masses imply nonnegative unnormalized
response-type weights. -/
theorem unnormTypeWeight_nonneg_of_signAligned
    (hAlign : R.SignAligned I) (g : ResponseType K) :
    0 ≤ R.unnormTypeWeight I g := by
  unfold unnormTypeWeight
  by_cases hpos : 0 < R.mass g
  · exact mul_nonneg (R.mass_nonneg g) (hAlign g hpos)
  · have hle : R.mass g ≤ 0 := le_of_not_gt hpos
    have hmass : R.mass g = 0 := le_antisymm hle (R.mass_nonneg g)
    simp [hmass]

/-- Normalized response-type weights are nonnegative when sign alignment holds
and the denominator is positive (`prop:po-estimand-mtw-positive-weights`). -/
theorem normalizedTypeWeight_nonneg_of_signAligned
    (hAlign : R.SignAligned I) (hden : 0 < R.typeWeightDenom I)
    (g : ResponseType K) :
    0 ≤ R.normalizedTypeWeight I g := by
  exact Causalean.Panel.Weighted.NormalizedWeights.normalizedWeight_nonneg
    (R.unnormTypeWeight I) (R.unnormTypeWeight_nonneg_of_signAligned I hAlign) hden g

/-- Normalized response-type weights sum to one when the first-stage
denominator is positive. -/
theorem normalizedTypeWeight_sum_eq_one_of_pos
    (hden : 0 < R.typeWeightDenom I) :
    ∑ g : ResponseType K, R.normalizedTypeWeight I g = 1 := by
  exact Causalean.Panel.Weighted.NormalizedWeights.sum_normalizedWeight_eq_one
    (R.unnormTypeWeight I) hden

/-- Response-type form of the finite MTW ratio
(`prop:po-estimand-mtw-response-type-form`). -/
theorem beta2SLSFiniteAlgebra_eq_responseTypeWeightedSum
    (hden : R.typeWeightDenom I ≠ 0) :
    R.beta2SLSFiniteAlgebra I = R.responseTypeEstimand I := by
  have _ : R.typeWeightDenom I ≠ 0 := hden
  unfold beta2SLSFiniteAlgebra responseTypeEstimand normalizedTypeWeight
  calc
    (∑ g : ResponseType K, R.unnormTypeWeight I g * R.effect g) / R.typeWeightDenom I =
        ∑ g : ResponseType K, (R.unnormTypeWeight I g * R.effect g) / R.typeWeightDenom I := by
      rw [Finset.sum_div]
    _ = ∑ g : ResponseType K, R.unnormTypeWeight I g / R.typeWeightDenom I * R.effect g := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [div_mul_eq_mul_div]

/-- Positive-weight response-type characterization under sign alignment and a
positive first-stage denominator. -/
theorem beta2SLSFiniteAlgebra_eq_positiveResponseTypeAverage
    (hAlign : R.SignAligned I) (hden : 0 < R.typeWeightDenom I) :
    R.beta2SLSFiniteAlgebra I = R.responseTypeEstimand I ∧
      (∀ g : ResponseType K, 0 ≤ R.normalizedTypeWeight I g) ∧
      (∑ g : ResponseType K, R.normalizedTypeWeight I g = 1) := by
  constructor
  · exact R.beta2SLSFiniteAlgebra_eq_responseTypeWeightedSum I hden.ne'
  constructor
  · intro g
    exact R.normalizedTypeWeight_nonneg_of_signAligned I hAlign hden g
  · exact R.normalizedTypeWeight_sum_eq_one_of_pos I hden

end ResponseTypeStats

/-! ### Negative-weights counterexample (G4)

The paper's central message (Mogstad-Torgovitsky-Walters §3) is that 2SLS
weights *can be negative* when sign alignment fails.  The next theorem
captures this at the finite-algebra layer: with two instrument support points
and a population consisting of 1/4 compliers and 3/4 defiers, the normalized
response-type weight for the complier type is −1/2 < 0.

Source: `prop:po-estimand-mtw-response-type-form`; negative-weights remark in
MTW §3 / `rem:po-estimand-mtw-standard-monotonicity`. -/

section NegWeightExample

/-
Concrete witnesses:
  K = 2 support points, ρ = [3/4, 1/4], dhat = [0, 1].
  Response-type population: 1/4 compliers (![false, true]), 3/4 defiers (![true, false]).

Arithmetic:
  meanIndex = 1/4.  centeredIndex = [-1/4, 3/4].
  Upper tail for j = ⟨1, _⟩: {k | k.val ≥ 1} = {⟨1,_⟩}.
  tailCoeff j = ρ₁ * centeredIndex₁ = (1/4)*(3/4) = 3/16.
  typeStep complier j = boolToReal(true) − boolToReal(false) = 1.
  typeStep defier  j = boolToReal(false) − boolToReal(true)  = −1.
  λ_complier = (1/4)*(3/16)*1 = 3/64.
  λ_defier   = (3/4)*(3/16)*(−1) = −9/64.
  typeWeightDenom = 3/64 − 9/64 = −6/64 = −3/32.
  ω_complier = (3/64)/(−3/32) = −1/2 < 0.  QED.
-/

/-- Explicit K=2 finite index: ρ = [3/4, 1/4], dhat = [0, 1]. -/
private noncomputable def exIndex : FiniteIndex 2 where
  rho := ![3/4, 1/4]
  dhat := ![(0 : ℝ), 1]
  rho_nonneg := by
    intro k; fin_cases k <;>
      norm_num
  rho_sum_one := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  dhat_mono := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The unique adjacent threshold for K=2: j.val = 1. -/
private def exJ : Adj 2 := ⟨1, by decide⟩

/-! The four response types for K=2. -/
private def gNever : ResponseType 2 := ![false, false]
private def gComplier : ResponseType 2 := ![false, true]
private def gDefier : ResponseType 2 := ![true, false]
private def gAlways : ResponseType 2 := ![true, true]

/-- All four response types for K=2 are pairwise distinct. -/
private lemma gNever_ne_gComplier : gNever ≠ gComplier := by decide
private lemma gNever_ne_gDefier : gNever ≠ gDefier := by decide
private lemma gNever_ne_gAlways : gNever ≠ gAlways := by decide
private lemma gComplier_ne_gDefier : gComplier ≠ gDefier := by decide
private lemma gComplier_ne_gAlways : gComplier ≠ gAlways := by decide
private lemma gDefier_ne_gAlways : gDefier ≠ gAlways := by decide

/-- The univ Finset over `ResponseType 2` equals the explicit 4-element set. -/
private lemma responseType2_univ :
    (Finset.univ : Finset (ResponseType 2)) =
      {gNever, gComplier, gDefier, gAlways} := by
  decide

/-- The response-type mass function: 1/4 compliers, 3/4 defiers.  Defined as a
standalone function (not inline in the structure) so it has an equational lemma
that `simp`/`rw` can use, and so the structure proofs are non-recursive. -/
private noncomputable def exMass (g : ResponseType 2) : ℝ :=
  if g = gComplier then 1/4
  else if g = gDefier then 3/4
  else 0

private lemma exMass_never : exMass gNever = 0 := by
  unfold exMass
  rw [if_neg gNever_ne_gComplier, if_neg gNever_ne_gDefier]
private lemma exMass_complier : exMass gComplier = 1/4 := by
  unfold exMass; rw [if_pos rfl]
private lemma exMass_defier : exMass gDefier = 3/4 := by
  unfold exMass
  rw [if_neg gComplier_ne_gDefier.symm, if_pos rfl]
private lemma exMass_always : exMass gAlways = 0 := by
  unfold exMass
  rw [if_neg gComplier_ne_gAlways.symm, if_neg gDefier_ne_gAlways.symm]

/-- The masses sum to one over the four response types. -/
private lemma exMass_sum_one : ∑ g, exMass g = 1 := by
  rw [responseType2_univ]
  rw [Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [exMass_never, exMass_complier, exMass_defier, exMass_always]
  ring

/-- Explicit response-type statistics: 1/4 compliers, 3/4 defiers. -/
private noncomputable def exStats : ResponseTypeStats 2 where
  mass := exMass
  effect _ := 1
  mass_nonneg := by
    intro g; unfold exMass; split_ifs <;> norm_num
  mass_sum_one := exMass_sum_one

private lemma exStats_mass (g : ResponseType 2) : exStats.mass g = exMass g := rfl

/-- The tail coefficient for exJ in exIndex equals 3/16. -/
private lemma exIndex_tailCoeff : exIndex.tailCoeff exJ = 3/16 := by
  -- upperTail exJ = {k : Fin 2 | 1 ≤ k.val} = {⟨1,_⟩}
  have hUT : FiniteIndex.upperTail exJ = ({1} : Finset (Fin 2)) := by decide
  rw [FiniteIndex.tailCoeff, hUT, Finset.sum_singleton]
  change exIndex.rho 1 * exIndex.centeredIndex 1 = 3/16
  rw [FiniteIndex.centeredIndex, FiniteIndex.meanIndex]
  change (![3/4, 1/4] : Fin 2 → ℝ) 1 *
      ((![(0:ℝ), 1] : Fin 2 → ℝ) 1 -
        ∑ k, (![3/4, 1/4] : Fin 2 → ℝ) k * (![(0:ℝ), 1] : Fin 2 → ℝ) k) = 3/16
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- typeStep for the complier type at exJ equals 1. -/
private lemma exJ_step_complier : typeStep gComplier exJ = 1 := by
  change boolToReal (gComplier (Adj.upper exJ)) - boolToReal (gComplier (Adj.lower exJ)) = 1
  have hu : Adj.upper exJ = (1 : Fin 2) := by decide
  have hl : Adj.lower exJ = (0 : Fin 2) := by decide
  rw [hu, hl]
  change boolToReal ((![false, true] : ResponseType 2) 1) -
      boolToReal ((![false, true] : ResponseType 2) 0) = 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, boolToReal]
  norm_num

/-- typeStep for the defier type at exJ equals -1. -/
private lemma exJ_step_defier : typeStep gDefier exJ = -1 := by
  change boolToReal (gDefier (Adj.upper exJ)) - boolToReal (gDefier (Adj.lower exJ)) = -1
  have hu : Adj.upper exJ = (1 : Fin 2) := by decide
  have hl : Adj.lower exJ = (0 : Fin 2) := by decide
  rw [hu, hl]
  change boolToReal ((![true, false] : ResponseType 2) 1) -
      boolToReal ((![true, false] : ResponseType 2) 0) = -1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, boolToReal]
  norm_num

/-- The sum over `Adj 2` has exactly one term. -/
private lemma adj2_sum (f : Adj 2 → ℝ) :
    ∑ j : Adj 2, f j = f exJ := by
  have huniv : (Finset.univ : Finset (Adj 2)) = {exJ} := by decide
  rw [huniv, Finset.sum_singleton]

/-- unnormTypeWeight for the complier type equals 3/64. -/
private lemma exStats_unnorm_complier :
    exStats.unnormTypeWeight exIndex gComplier = 3/64 := by
  rw [ResponseTypeStats.unnormTypeWeight, adj2_sum, exStats_mass, exMass_complier,
    exIndex_tailCoeff, exJ_step_complier]
  norm_num

/-- unnormTypeWeight for the defier type equals -9/64. -/
private lemma exStats_unnorm_defier :
    exStats.unnormTypeWeight exIndex gDefier = -9/64 := by
  rw [ResponseTypeStats.unnormTypeWeight, adj2_sum, exStats_mass, exMass_defier,
    exIndex_tailCoeff, exJ_step_defier]
  norm_num

/-- unnormTypeWeight for never-taker and always-taker types equal 0. -/
private lemma exStats_unnorm_never :
    exStats.unnormTypeWeight exIndex gNever = 0 := by
  rw [ResponseTypeStats.unnormTypeWeight, adj2_sum, exStats_mass, exMass_never]
  ring

private lemma exStats_unnorm_always :
    exStats.unnormTypeWeight exIndex gAlways = 0 := by
  rw [ResponseTypeStats.unnormTypeWeight, adj2_sum, exStats_mass, exMass_always]
  ring

/-- The type-weight denominator equals -3/32. -/
private lemma exStats_denom : exStats.typeWeightDenom exIndex = -3/32 := by
  rw [ResponseTypeStats.typeWeightDenom, responseType2_univ]
  rw [Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [exStats_unnorm_never, exStats_unnorm_complier,
      exStats_unnorm_defier, exStats_unnorm_always]
  norm_num

/-- **Negative-weights theorem**: with 2 support points and a 3/4-defier
population, the complier's normalized response-type weight equals −1/2 < 0.

This formalizes the paper's central message (MTW §3): without sign alignment,
2SLS is NOT a convex average of causal effects. -/
theorem exists_negativeNormalizedTypeWeight :
    ∃ (I : FiniteIndex 2) (R : ResponseTypeStats 2) (g : ResponseType 2),
      0 < R.mass g ∧ R.normalizedTypeWeight I g < 0 := by
  refine ⟨exIndex, exStats, gComplier, ?_, ?_⟩
  · -- mass of complier type = 1/4 > 0
    rw [exStats_mass, exMass_complier]; norm_num
  · -- normalized weight = (3/64) / (-3/32) = -1/2 < 0
    rw [ResponseTypeStats.normalizedTypeWeight,
      Causalean.Panel.Weighted.NormalizedWeights.normalizedWeight]
    change exStats.unnormTypeWeight exIndex gComplier /
        (∑ k, exStats.unnormTypeWeight exIndex k) < 0
    rw [← ResponseTypeStats.typeWeightDenom, exStats_unnorm_complier, exStats_denom]
    norm_num

end NegWeightExample

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
