/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE estimation: the finite observed-data model

This is the finite observed-data layer for the structure-agnostic optimality lower bound of
doubly-robust ATE estimation (Jin–Syrgkanis 2024, *Structure-agnostic
Optimality of Doubly Robust Learning for Treatment Effect Estimation*).

The paper works on `X ∈ [0,1]^K` with `X` uniform, partitions the cube into
`M = 2^m` cells, and makes every nuisance **piecewise-constant on those cells**.
The within-cell continuum carries no information for the construction, so we
collapse each cell to a point and work with a **finite covariate** `X : C` for an
arbitrary finite type `C` (uniform mass `1/card C`), binary treatment `D : Bool`,
and binary outcome `Y : Bool`.  One observation is the finite type

  `Obs C := C × Bool × Bool`,

so every data law is a PMF on a finite type and the total-variation / χ² /
ATE quantities are all finite sums.  This is exactly the paper's cell structure,
stated directly.  (Keeping `C` general — rather than `Fin M` — lets the explicit
lower-bound construction take `C = Fin K × Bool`, the pair-index × position
structure that its sign perturbation needs; see `Construction.lean`.)

A DGP is a pair `(m, g)` with propensity `m : C → ℝ` (the conditional
`P(D = 1 | X = x)`) and outcome regression `g : Bool → C → ℝ`
(`g d x = E[Y | D = d, X = x]`).  Under conditional ignorability the ATE is

  `ate g = (1/card C) Σ_x (g true x − g false x)`.

Main definitions:

* `ValidDGP m g` — the nuisances take values in `[0,1]`;
* `obsLaw m g hv` — the single-observation law as a probability `Measure (Obs C)`;
* `ate g`, `l2sq a b` — the ATE functional and the (squared) `L²(P_X)` distance;
* `InClass mhat ghat εg εm m g` — membership in the structure-agnostic nuisance
  class `ℱ` around fixed estimates `(mhat, ghat)` with squared error budgets
  `εg` (outcome arms) and `εm` (propensity);
* `productLaw m g hv n`, `minimaxMiss …` — the `n`-sample data law and the
  worst-case-over-class probability that an estimator misses the true ATE by `s`.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Finite Observed-Data Model

This file defines the finite observed-data experiment used for structure-agnostic ATE estimation.
The covariate space is an arbitrary finite type `C`, treatment and outcome are binary, and one
observation is `Obs C = C × Bool × Bool`.

Main declarations:

* `ValidDGP`, `obsReal`, `obsPMF`, and `obsLaw` build a valid data-generating process and its
  single-observation law, with `obsReal_sum`, `obsReal_nonneg`, and `obsLaw_isProb` recording the
  finite probability facts.
* `ate` and `l2sq` define the average treatment effect and squared `L²(P_X)` nuisance distance.
* `InClass` and `InClassDGP` package the structure-agnostic nuisance class around fixed estimates.
* `productLaw`, `nMiss`, `nMSE`, and `minimaxMiss` define the sample law, miss probability,
  expected squared error, and worst-case-over-class miss probability.
* `nMiss_sq_le_nMSE` connects probability-of-miss lower bounds to mean-squared-error lower
  bounds, and `nMiss_le_minimaxMiss` embeds an in-class DGP's miss probability into the minimax
  supremum. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open scoped ENNReal BigOperators

/-- One observation: covariate `X : C`, treatment `D : Bool`, outcome `Y : Bool`. -/
abbrev Obs (C : Type*) := C × Bool × Bool

variable {C : Type*} [Fintype C]

/-- A DGP is **valid** when the propensity `m` and both outcome-regression arms
`g d` take values in `[0,1]`. -/
structure ValidDGP (m : C → ℝ) (g : Bool → C → ℝ) : Prop where
  m_mem : ∀ x, m x ∈ Set.Icc (0 : ℝ) 1
  g_mem : ∀ d x, g d x ∈ Set.Icc (0 : ℝ) 1

/-- The real-valued mass the DGP `(m, g)` assigns to the observation `z = (x, d, y)`:
`(1/card C) · P(D = d | x) · P(Y = y | d, x)`. -/
noncomputable def obsReal (m : C → ℝ) (g : Bool → C → ℝ) (z : Obs C) : ℝ :=
  (Fintype.card C : ℝ)⁻¹ * (if z.2.1 then m z.1 else 1 - m z.1)
    * (if z.2.2 then g z.2.1 z.1 else 1 - g z.2.1 z.1)

/-- The total mass of `obsReal` is `1` (for nonempty `C`): summing over `Y` gives `1`,
then over `D` gives `1`, then over `X` gives `card C · (1/card C) = 1`. -/
theorem obsReal_sum [Nonempty C] (m : C → ℝ) (g : Bool → C → ℝ) :
    ∑ z : Obs C, obsReal m g z = 1 := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- summing over `Y` then `D` collapses each cell to its mass `1/card C`
  have key : ∑ z : Obs C, obsReal m g z = ∑ _x : C, (Fintype.card C : ℝ)⁻¹ := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [obsReal, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
    ring
  rw [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Nonnegativity of `obsReal` for a valid DGP. -/
theorem obsReal_nonneg {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) (z : Obs C) : 0 ≤ obsReal m g z := by
  have hCinv : (0 : ℝ) ≤ (Fintype.card C : ℝ)⁻¹ := by positivity
  obtain ⟨hm0, hm1⟩ := hv.m_mem z.1
  refine mul_nonneg (mul_nonneg hCinv ?_) ?_
  · rcases z.2.1 with _ | _ <;> simp <;> linarith
  · obtain ⟨hg0, hg1⟩ := hv.g_mem z.2.1 z.1
    rcases z.2.2 with _ | _ <;> simp <;> linarith

/-- The single-observation law of the DGP `(m, g)` as a probability `PMF`. -/
noncomputable def obsPMF [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) : PMF (Obs C) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (obsReal m g z)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => obsReal_nonneg hv z), obsReal_sum]
    simp

variable [MeasurableSpace C]

/-- The single-observation law of the DGP `(m, g)` as a probability `Measure`. -/
noncomputable def obsLaw [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) : Measure (Obs C) :=
  (obsPMF hv).toMeasure

/-- The single-observation law of any valid data-generating process is a probability measure. -/
instance obsLaw_isProb [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) : IsProbabilityMeasure (obsLaw hv) := by
  unfold obsLaw; infer_instance

/-- The average treatment effect `(1/card C) Σ_x (g true x − g false x)`.  Depends only
on the outcome regression `g`. -/
noncomputable def ate (g : Bool → C → ℝ) : ℝ :=
  (Fintype.card C : ℝ)⁻¹ * ∑ x, (g true x - g false x)

/-- The squared `L²(P_X)` distance `(1/card C) Σ_x (a x − b x)²` between two functions of
the covariate. -/
noncomputable def l2sq (a b : C → ℝ) : ℝ :=
  (Fintype.card C : ℝ)⁻¹ * ∑ x, (a x - b x) ^ 2

/-- **Structure-agnostic nuisance class.**  A DGP `(m, g)` is in the class
`ℱ(εg, εm)` around fixed nuisance estimates `(mhat, ghat)` when it is valid and
its squared `L²(P_X)` nuisance errors are within the budgets: each outcome arm
within `εg`, the propensity within `εm`. -/
structure InClass (mhat : C → ℝ) (ghat : Bool → C → ℝ) (εg εm : ℝ)
    (m : C → ℝ) (g : Bool → C → ℝ) : Prop where
  valid : ValidDGP m g
  err_g : ∀ d, l2sq (g d) (ghat d) ≤ εg
  err_m : l2sq m mhat ≤ εm

/-- A DGP packaged with a proof that it lies in the class `ℱ(εg, εm)`. -/
def InClassDGP (mhat : C → ℝ) (ghat : Bool → C → ℝ) (εg εm : ℝ) : Type _ :=
  { p : (C → ℝ) × (Bool → C → ℝ) // InClass mhat ghat εg εm p.1 p.2 }

/-- The `n`-sample data law: the product `Measure.pi` of `n` independent copies of
the single-observation law. -/
noncomputable def productLaw [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) (n : ℕ) : Measure (Fin n → Obs C) :=
  Measure.pi (fun _ => obsLaw hv)

/-- The independent sample law of any valid data-generating process is a probability measure. -/
instance productLaw_isProb [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) (n : ℕ) : IsProbabilityMeasure (productLaw hv n) := by
  unfold productLaw; infer_instance

/-- The probability that the estimator `est`, run on `n` samples from the DGP
`(m, g)`, **misses** the true ATE `ate g` by at least `s`. -/
noncomputable def nMiss [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) (n : ℕ) (est : (Fin n → Obs C) → ℝ) (s : ℝ) : ℝ :=
  (productLaw hv n).real {x | s ≤ |est x - ate g|}

/-- The **mean-squared error** of `est` on `n` samples from the DGP `(m, g)`: the
expected squared deviation from the true ATE `ate g`.  This is the expected-risk
functional whose minimax lower bound the paper (Jin–Syrgkanis 2024, eq. for
`𝔐ⁿ,γ`) deduces — as the weaker `(1−γ)`-factor consequence — from the quantile
(probability-of-miss) form. -/
noncomputable def nMSE [Nonempty C] {m : C → ℝ} {g : Bool → C → ℝ}
    (hv : ValidDGP m g) (n : ℕ) (est : (Fin n → Obs C) → ℝ) : ℝ :=
  ∫ x, (est x - ate g) ^ 2 ∂(productLaw hv n)

/-- **Chebyshev/Markov bridge.** For [a valid data-generating process `(m, g)`](hyp:hv) and
[a nonnegative separation threshold s](hyp:hs), [the squared threshold times the probability
that an estimator misses the true average treatment effect by at least `s`, on `n` i.i.d.
draws, is at most the estimator's mean-squared error](goal). This is the quantitative form of
the paper's observation that the quantile risk lower bound implies the expected-risk one
(`𝔐ₙ,γ ≥ ρ ⟹ minimax `𝔼`-risk `≥ (1−γ)ρ`). -/
theorem nMiss_sq_le_nMSE [Nonempty C] [MeasurableSingletonClass C]
    {m : C → ℝ} {g : Bool → C → ℝ} (hv : ValidDGP m g) (n : ℕ)
    {est : (Fin n → Obs C) → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * nMiss hv n est s ≤ nMSE hv n est := by
  have hset : {x : Fin n → Obs C | s ≤ |est x - ate g|}
      = {x | s ^ 2 ≤ (est x - ate g) ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;>
      nlinarith [abs_nonneg (est x - ate g), sq_abs (est x - ate g),
        sq_nonneg (est x - ate g)]
  unfold nMiss nMSE
  rw [hset]
  exact mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg _) Integrable.of_finite (s ^ 2)

/-- **Minimax (worst-case-over-class) miss probability.**  The supremum over all
in-class DGPs of the probability that `est` misses that DGP's true ATE by `s`.
A lower bound on this quantity is a minimax lower bound: no estimator can be
within `s` of the truth with high probability uniformly over the class. -/
noncomputable def minimaxMiss [Nonempty C] (mhat : C → ℝ) (ghat : Bool → C → ℝ)
    (εg εm : ℝ) (n : ℕ) (est : (Fin n → Obs C) → ℝ) (s : ℝ) : ℝ :=
  ⨆ p : InClassDGP mhat ghat εg εm, nMiss p.2.valid n est s

/-- Each in-class miss probability is bounded above by `1` (it is a probability),
so the range of `nMiss` over the class is bounded above. -/
theorem bddAbove_nMiss_range [Nonempty C] (mhat : C → ℝ) (ghat : Bool → C → ℝ)
    (εg εm : ℝ) (n : ℕ) (est : (Fin n → Obs C) → ℝ) (s : ℝ) :
    BddAbove (Set.range fun p : InClassDGP mhat ghat εg εm => nMiss p.2.valid n est s) := by
  refine ⟨1, ?_⟩
  rintro y ⟨p, rfl⟩
  unfold nMiss
  calc (productLaw p.2.valid n).real {x | s ≤ |est x - ate p.1.2|}
      ≤ (productLaw p.2.valid n).real Set.univ :=
        measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    _ = 1 := by rw [probReal_univ]

/-- A specific in-class DGP's miss probability is `≤ minimaxMiss`. -/
theorem nMiss_le_minimaxMiss [Nonempty C] {mhat : C → ℝ} {ghat : Bool → C → ℝ}
    {εg εm : ℝ} {n : ℕ} {est : (Fin n → Obs C) → ℝ} {s : ℝ}
    (p : InClassDGP mhat ghat εg εm) :
    nMiss p.2.valid n est s ≤ minimaxMiss mhat ghat εg εm n est s :=
  le_ciSup (bddAbove_nMiss_range mhat ghat εg εm n est s) p

end Causalean.Estimation.MinimaxATE
