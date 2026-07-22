/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs
import Causalean.Mathlib.Optimization.WeightedSimplexCS

/-! # Active-set KKT lemmas (κ > 0)

Given admissible support/multiplier data `(S, λ)` for the weighted-simplex SOCP with
`κ > 0`, the induced `activeSetPoint` lies in `Δ_M`, has support exactly `S`, weighted
squared norm `(Mκ / D)²` with `D = Σ_{h∈S}(λ−αₕ)/βₕ`, objective value `M·λ`, and is the
*strict* minimizer of the SOCP over `Δ_M`. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

variable (M : ℝ) (α β : Fin 3 → ℝ) (kappa : ℝ) (S : Finset (Fin 3)) (lam : ℝ)

/-- The active-set denominator `D = Σ_{h∈S} (λ−αₕ)/βₕ` is strictly positive: `S` is
nonempty and each summand is positive (`λ > αₕ` on `S`, `βₕ > 0`). -/
lemma activeSet_denom_pos (hβ : ∀ i, 0 < β i)
    (hadm : IsAdmissibleSupport α β kappa S lam) :
    0 < ∑ h ∈ S, (lam - α h) / β h := by
  rcases hadm with ⟨hS, -, hactive, -⟩
  exact Finset.sum_pos
    (fun h hh => div_pos (sub_pos.mpr (hactive h hh)) (hβ h)) hS

/-- The active-set point has support exactly `S`: on `S` its coordinate is positive,
off `S` it is `0`. -/
lemma activeSetPoint_pos_iff (hM : 0 < M) (hβ : ∀ i, 0 < β i)
    (hadm : IsAdmissibleSupport α β kappa S lam) (i : Fin 3) :
    0 < activeSetPoint M α β S lam i ↔ i ∈ S := by
  constructor
  · intro hpos
    by_contra hi
    simp [activeSetPoint, hi] at hpos
  · intro hi
    simp [activeSetPoint, hi]
    exact div_pos
      (mul_pos hM (div_pos (sub_pos.mpr (hadm.2.2.1 i hi)) (hβ i)))
      (activeSet_denom_pos α β kappa S lam hβ hadm)

/-- The active-set point lies in the simplex `Δ_M`. -/
lemma activeSetPoint_mem (hM : 0 < M) (hβ : ∀ i, 0 < β i)
    (hadm : IsAdmissibleSupport α β kappa S lam) :
    InSimplex M (activeSetPoint M α β S lam) := by
  constructor
  · intro i
    by_cases hi : i ∈ S
    · exact le_of_lt ((activeSetPoint_pos_iff M α β kappa S lam hM hβ hadm i).2 hi)
    · simp [activeSetPoint, hi]
  · let D := ∑ h ∈ S, (lam - α h) / β h
    have hD : D ≠ 0 := ne_of_gt (activeSet_denom_pos α β kappa S lam hβ hadm)
    calc
      (∑ i, activeSetPoint M α β S lam i)
          = ∑ i ∈ S, M * ((lam - α i) / β i) / D := by
            simp [activeSetPoint, D]
      _ = M / D * (∑ i ∈ S, (lam - α i) / β i) := by
            rw [Finset.mul_sum]
            simp [D, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
      _ = M := by
            rw [show (∑ i ∈ S, (lam - α i) / β i) = D by rfl]
            field_simp [hD]

/-- Weighted squared norm of the active-set point: `Σ βᵢ tᵢ² = (Mκ)² / D²`, using the
admissibility identity `Σ_{i∈S}(λ−αᵢ)²/βᵢ = κ²`. -/
lemma activeSetPoint_normSq (hβ : ∀ i, 0 < β i)
    (hadm : IsAdmissibleSupport α β kappa S lam) :
    (∑ i, β i * activeSetPoint M α β S lam i ^ 2)
      = (M * kappa) ^ 2 / (∑ h ∈ S, (lam - α h) / β h) ^ 2 := by
  let D := ∑ h ∈ S, (lam - α h) / β h
  have hD : D ≠ 0 := ne_of_gt (activeSet_denom_pos α β kappa S lam hβ hadm)
  have hsq : (∑ i ∈ S, (lam - α i) ^ 2 / β i) = kappa ^ 2 := hadm.2.1
  calc
    (∑ i, β i * activeSetPoint M α β S lam i ^ 2)
        = ∑ i ∈ S, β i * (M * ((lam - α i) / β i) / D) ^ 2 := by
          simp [activeSetPoint, D]
    _ = ∑ i ∈ S, (M ^ 2 / D ^ 2) * ((lam - α i) ^ 2 / β i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hb : β i ≠ 0 := ne_of_gt (hβ i)
          field_simp [hb, hD]
    _ = (M ^ 2 / D ^ 2) * (∑ i ∈ S, (lam - α i) ^ 2 / β i) := by
          rw [Finset.mul_sum]
    _ = (M * kappa) ^ 2 / D ^ 2 := by
          rw [hsq]
          ring

/-- Objective value of the active-set point is the closed form `M·λ`. Multiplying
active stationarity `(λ−αᵢ) = κ βᵢ tᵢ / N` by `tᵢ` and summing gives
`Σ αᵢ tᵢ + κ N = λ Σ tᵢ = M λ`. -/
lemma activeSetPoint_value (hM : 0 < M) (hβ : ∀ i, 0 < β i) (hk : 0 < kappa)
    (hadm : IsAdmissibleSupport α β kappa S lam) :
    wsObj α β kappa (activeSetPoint M α β S lam) = M * lam := by
  let D := ∑ h ∈ S, (lam - α h) / β h
  have hDpos : 0 < D := activeSet_denom_pos α β kappa S lam hβ hadm
  have hD : D ≠ 0 := ne_of_gt hDpos
  have hsq : (∑ i ∈ S, (lam - α i) ^ 2 / β i) = kappa ^ 2 := hadm.2.1
  have hnorm :
      (∑ i, β i * activeSetPoint M α β S lam i ^ 2) = (M * kappa) ^ 2 / D ^ 2 := by
    simpa [D] using activeSetPoint_normSq M α β kappa S lam hβ hadm
  have hsqrt :
      Real.sqrt (∑ i, β i * activeSetPoint M α β S lam i ^ 2) = M * kappa / D := by
    rw [hnorm]
    rw [div_eq_mul_inv]
    rw [show (M * kappa) ^ 2 * (D ^ 2)⁻¹ = (M * kappa / D) ^ 2 by
      field_simp [hD]]
    exact Real.sqrt_sq (le_of_lt (div_pos (mul_pos hM hk) hDpos))
  have hlin :
      (∑ i, α i * activeSetPoint M α β S lam i) = M * lam - M * kappa ^ 2 / D := by
    have hcore :
        (∑ i ∈ S, α i * ((lam - α i) / β i)) = lam * D - kappa ^ 2 := by
      calc
        (∑ i ∈ S, α i * ((lam - α i) / β i))
            = ∑ i ∈ S,
                (lam * ((lam - α i) / β i) - (lam - α i) ^ 2 / β i) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hb : β i ≠ 0 := ne_of_gt (hβ i)
              field_simp [hb]
              ring
        _ = lam * D - kappa ^ 2 := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              rw [show (∑ x ∈ S, (lam - α x) / β x) = D by rfl, hsq]
    calc
      (∑ i, α i * activeSetPoint M α β S lam i)
          = ∑ i ∈ S, α i * (M * ((lam - α i) / β i) / D) := by
            simp [activeSetPoint, D]
      _ = M / D * (∑ i ∈ S, α i * ((lam - α i) / β i)) := by
            rw [Finset.mul_sum]
            simp [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
      _ = M * lam - M * kappa ^ 2 / D := by
            rw [hcore]
            field_simp [hD]
  calc
    wsObj α β kappa (activeSetPoint M α β S lam)
        = (∑ i, α i * activeSetPoint M α β S lam i) +
            kappa * Real.sqrt (∑ i, β i * activeSetPoint M α β S lam i ^ 2) := rfl
    _ = M * lam := by
          rw [hlin, hsqrt]
          field_simp [hD]
          ring

/-- **Strict minimality of the active-set point (κ > 0).** For every other simplex
point `s` the objective is strictly larger.
Proof plan (writing `t⋆ = activeSetPoint M α β S lam`, `N = √(Σ βᵢ t⋆ᵢ²) = Mκ/D > 0`):
* `wsObj s − wsObj t⋆ = Σ αᵢ(sᵢ − t⋆ᵢ) + κ(N(s) − N)`.
* Strict Cauchy–Schwarz (`weighted_cs_simplex_strict`, using `s ≠ t⋆`, `Σsᵢ = Σt⋆ᵢ = M`):
  `Σ βᵢ t⋆ᵢ sᵢ < N(s)·N`, so `κ(N(s) − N) > (κ/N) Σ βᵢ t⋆ᵢ (sᵢ − t⋆ᵢ)`.
* On `S`, `κ βᵢ t⋆ᵢ / N = λ − αᵢ`; off `S`, `t⋆ᵢ = 0`. Hence the RHS of the strict
  inequality is `Σ_{i∈S} (λ − αᵢ)(sᵢ − t⋆ᵢ)`.
* Adding `Σ αᵢ(sᵢ − t⋆ᵢ)` and regrouping gives
  `Σ_{i∈S} λ sᵢ + Σ_{i∉S} αᵢ sᵢ − λ M ≥ Σ λ sᵢ − λ M = λ(M − M) = 0`
  (using `αⱼ ≥ λ`, `sⱼ ≥ 0` off `S`). Therefore `wsObj s − wsObj t⋆ > 0`. -/
lemma activeSetPoint_strict_min (hM : 0 < M) (hβ : ∀ i, 0 < β i) (hk : 0 < kappa)
    (hadm : IsAdmissibleSupport α β kappa S lam) :
    ∀ s : Fin 3 → ℝ, InSimplex M s → s ≠ activeSetPoint M α β S lam →
      wsObj α β kappa (activeSetPoint M α β S lam) < wsObj α β kappa s := by
  intro s hs hne
  let t := activeSetPoint M α β S lam
  let D := ∑ h ∈ S, (lam - α h) / β h
  let Q := ∑ i, β i * t i ^ 2
  let N := Real.sqrt Q
  let Ns := Real.sqrt (∑ i, β i * s i ^ 2)
  let R := ∑ i, β i * (t i * s i)
  have htmem : InSimplex M t := by
    simpa [t] using activeSetPoint_mem M α β kappa S lam hM hβ hadm
  have ht_sum : ∑ i, t i = M := htmem.2
  have hDpos : 0 < D := activeSet_denom_pos α β kappa S lam hβ hadm
  have hD : D ≠ 0 := ne_of_gt hDpos
  have hQnorm : Q = (M * kappa) ^ 2 / D ^ 2 := by
    simpa [Q, t, D] using activeSetPoint_normSq M α β kappa S lam hβ hadm
  have hQnonneg : 0 ≤ Q := by
    rw [hQnorm]
    exact div_nonneg (sq_nonneg (M * kappa)) (sq_nonneg D)
  have hQeq : Q = N ^ 2 := by
    rw [Real.sq_sqrt hQnonneg]
  have hNval : N = M * kappa / D := by
    dsimp [N]
    rw [hQnorm]
    rw [div_eq_mul_inv]
    rw [show (M * kappa) ^ 2 * (D ^ 2)⁻¹ = (M * kappa / D) ^ 2 by
      field_simp [hD]]
    exact Real.sqrt_sq (le_of_lt (div_pos (mul_pos hM hk) hDpos))
  have hNpos : 0 < N := by
    rw [hNval]
    exact div_pos (mul_pos hM hk) hDpos
  have hcs : R < N * Ns := by
    simpa [R, N, Ns, t] using
      weighted_cs_simplex_strict M hM β t s hβ ht_sum hs.2 (Ne.symm hne)
  have hRdiff :
      (∑ i, β i * (t i * (s i - t i))) = R - Q := by
    simp [R, Q]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hnorm_strict :
      (kappa / N) * (∑ i, β i * (t i * (s i - t i))) <
        kappa * (Ns - N) := by
    rw [hRdiff, hQeq]
    field_simp [ne_of_gt hNpos]
    nlinarith [mul_pos hk hNpos]
  have hstationary :
      (kappa / N) * (∑ i, β i * (t i * (s i - t i))) =
        ∑ i ∈ S, (lam - α i) * (s i - t i) := by
    subst t
    calc
      (kappa / N) *
          (∑ i,
            β i * (activeSetPoint M α β S lam i * (s i - activeSetPoint M α β S lam i)))
          = ∑ i ∈ S,
              (kappa / N) *
                (β i * (M * ((lam - α i) / β i) / D *
                  (s i - activeSetPoint M α β S lam i))) := by
            rw [Finset.mul_sum]
            simp [activeSetPoint, D]
      _ = ∑ i ∈ S, (lam - α i) * (s i - activeSetPoint M α β S lam i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [activeSetPoint, hi, D]
            rw [hNval]
            rw [show (∑ h ∈ S, (lam - α h) / β h) = D by rfl]
            field_simp [ne_of_gt hM, ne_of_gt hk, hD, ne_of_gt (hβ i)]
  have hgap_formula :
      wsObj α β kappa s - wsObj α β kappa t =
        (∑ i, α i * (s i - t i)) + kappa * (Ns - N) := by
    subst t
    dsimp [wsObj, Ns, N, Q]
    have hsumdiff :
        (∑ i, α i * (s i - activeSetPoint M α β S lam i)) =
          (∑ i, α i * s i) - ∑ i, α i * activeSetPoint M α β S lam i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsumdiff]
    ring
  have hremainder_eq :
      (∑ i, α i * (s i - t i)) +
          (∑ i ∈ S, (lam - α i) * (s i - t i))
        = (∑ i, (if i ∈ S then lam else α i) * s i) - lam * M := by
    subst t
    have hcoeff :
        (∑ i, α i * (s i - activeSetPoint M α β S lam i)) +
            (∑ i ∈ S, (lam - α i) * (s i - activeSetPoint M α β S lam i))
          = ∑ i, (if i ∈ S then lam else α i) *
              (s i - activeSetPoint M α β S lam i) := by
      rw [show (∑ i ∈ S, (lam - α i) * (s i - activeSetPoint M α β S lam i)) =
          ∑ i, if i ∈ S then
            (lam - α i) * (s i - activeSetPoint M α β S lam i) else 0 by
        simp]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases his : i ∈ S
      · simp [his]
        ring
      · simp [his]
    have hmass :
        (∑ i, (if i ∈ S then lam else α i) * activeSetPoint M α β S lam i) =
          lam * M := by
      calc
        (∑ i, (if i ∈ S then lam else α i) * activeSetPoint M α β S lam i)
            = ∑ i, lam * activeSetPoint M α β S lam i := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases his : i ∈ S
              · simp [his]
              · simp [activeSetPoint, his]
        _ = lam * M := by
              rw [← Finset.mul_sum, ht_sum]
    rw [hcoeff]
    rw [show (∑ i, (if i ∈ S then lam else α i) *
        (s i - activeSetPoint M α β S lam i)) =
        (∑ i, (if i ∈ S then lam else α i) * s i) -
          ∑ i, (if i ∈ S then lam else α i) * activeSetPoint M α β S lam i by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [hmass]
  have hremainder_nonneg :
      0 ≤ (∑ i, α i * (s i - t i)) +
          (∑ i ∈ S, (lam - α i) * (s i - t i)) := by
    rw [hremainder_eq]
    have hpoint : ∀ i, lam * s i ≤ (if i ∈ S then lam else α i) * s i := by
      intro i
      by_cases hi : i ∈ S
      · simp [hi]
      · exact mul_le_mul_of_nonneg_right (by simpa [hi] using hadm.2.2.2 i hi) (hs.1 i)
    have hsum :
        (∑ i, lam * s i) ≤ ∑ i, (if i ∈ S then lam else α i) * s i := by
      exact Finset.sum_le_sum (fun i hi => hpoint i)
    rw [← Finset.mul_sum, hs.2] at hsum
    linarith
  have hgap_pos : 0 < wsObj α β kappa s - wsObj α β kappa t := by
    have hstrict :
        (∑ i, α i * (s i - t i)) + (∑ i ∈ S, (lam - α i) * (s i - t i)) <
          wsObj α β kappa s - wsObj α β kappa t := by
      rw [hgap_formula]
      rw [hstationary] at hnorm_strict
      linarith
    linarith
  have ht_value : wsObj α β kappa t = M * lam := by
    simpa [t] using activeSetPoint_value M α β kappa S lam hM hβ hk hadm
  linarith

end Causalean.Mathlib.Optimization
