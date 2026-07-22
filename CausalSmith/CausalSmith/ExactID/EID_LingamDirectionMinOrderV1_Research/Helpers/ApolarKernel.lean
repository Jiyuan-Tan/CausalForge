/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Apolar-kernel substrate for the generic arrow-recovery flagship

Support-annihilator algebra (nonvanishing, fixed-axis divisibility) and the
apolar evaluation-map / common-contraction-kernel identity `ker = ⟨Q_D⟩`,
reproved from Vandermonde minors (no general symmetric-tensor apolarity theory).
These leaves feed `TApolar.generic_apolar_arrow_recovery`.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarDefs
import Causalean.Stat.Nonparametric.LocalPoly.DesignMatrixPosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

private lemma eval₂_prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin 2) ℂ)
    (v : Fin 2 → ℂ) :
    MvPolynomial.eval₂ (RingHom.id ℂ) v (∏ j ∈ s, p j) =
      ∏ j ∈ s, MvPolynomial.eval₂ (RingHom.id ℂ) v (p j) := by
  change (MvPolynomial.eval₂Hom (RingHom.id ℂ) v) (∏ j ∈ s, p j) = _
  exact map_prod (MvPolynomial.eval₂Hom (RingHom.id ℂ) v) p s

/-- Each linear factor `C b * X0 - C a * X1` is nonzero when `(a,b) ≠ (0,0)`. -/
lemma supportAnnihilator_ne_zero {m : ℕ} (dirs : Fin (m + 2) → ℂ × ℂ)
    (h : ∀ j, (dirs j).1 ≠ 0 ∨ (dirs j).2 ≠ 0) : supportAnnihilator dirs ≠ 0 := by
  rw [supportAnnihilator]
  apply (Finset.prod_ne_zero_iff).2
  intro j _
  rcases h j with ha | hb
  · intro hj
    have he := congrArg
      (MvPolynomial.eval₂ (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then 0 else 1)) hj
    apply ha
    simpa using he
  · intro hj
    have he := congrArg
      (MvPolynomial.eval₂ (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then 1 else 0)) hj
    apply hb
    simpa using he

/-- For the forward loading family, the index-`(m+1)` factor equals `X 0`, so `X 0 ∣ Q_D`. -/
lemma X0_dvd_supportAnnihilator_forward {m : ℕ} (γ : ℂ) (ρ : Fin m → ℂ) :
    (MvPolynomial.X (0 : Fin 2)) ∣ supportAnnihilator (forwardLoading m γ ρ) := by
  rw [supportAnnihilator]
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _
    (Finset.mem_univ (⟨m + 1, by omega⟩ : Fin (m + 2))))
  simp [forwardLoading]

/-- `X 1 ∤ Q_D` for the forward loading when its finite slopes are nonzero. -/
lemma not_X1_dvd_supportAnnihilator_forward {m : ℕ} (γ : ℂ) (ρ : Fin m → ℂ)
    (hγ : γ ≠ 0) (hρ : ∀ i, ρ i ≠ 0) :
    ¬ (MvPolynomial.X (1 : Fin 2)) ∣ supportAnnihilator (forwardLoading m γ ρ) := by
  intro hd
  obtain ⟨p, hp⟩ := hd
  have hne : MvPolynomial.eval₂ (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then 1 else 0)
      (supportAnnihilator (forwardLoading m γ ρ)) ≠ 0 := by
    rw [supportAnnihilator]
    rw [eval₂_prod]
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, RingHom.id_apply]
    apply (Finset.prod_ne_zero_iff).2
    intro j _
    by_cases hj0 : j.val = 0
    · simp [forwardLoading, hj0, hγ]
    by_cases hjlast : j.val = m + 1
    · simp [forwardLoading, hjlast]
    have hjzero : j ≠ 0 := by
      intro h
      apply hj0
      simp [h]
    simpa [forwardLoading, hjzero, hjlast] using hρ ⟨j.val - 1, by omega⟩
  apply hne
  rw [hp]
  simp

/-- Mirror fixed-axis divisibility for the reverse loading family. -/
lemma X1_dvd_supportAnnihilator_reverse {m : ℕ} (δ : ℂ) (σ : Fin m → ℂ) :
    (MvPolynomial.X (1 : Fin 2)) ∣ supportAnnihilator (reverseLoading m δ σ) := by
  rw [supportAnnihilator]
  refine dvd_trans ?_ (Finset.dvd_prod_of_mem _
    (Finset.mem_univ (⟨0, by omega⟩ : Fin (m + 2))))
  simp [reverseLoading]

/-- Mirror nondivisibility for the reverse loading family. -/
lemma not_X0_dvd_supportAnnihilator_reverse {m : ℕ} (δ : ℂ) (σ : Fin m → ℂ)
    (hδ : δ ≠ 0) (hσ : ∀ i, σ i ≠ 0) :
    ¬ (MvPolynomial.X (0 : Fin 2)) ∣ supportAnnihilator (reverseLoading m δ σ) := by
  intro hd
  obtain ⟨p, hp⟩ := hd
  have hne : MvPolynomial.eval₂ (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then 0 else 1)
      (supportAnnihilator (reverseLoading m δ σ)) ≠ 0 := by
    rw [supportAnnihilator]
    rw [eval₂_prod]
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, RingHom.id_apply]
    apply (Finset.prod_ne_zero_iff).2
    intro j _
    by_cases hj0 : j.val = 0
    · simp [reverseLoading, hj0]
    by_cases hjlast : j.val = m + 1
    · simpa [reverseLoading, hj0, hjlast] using neg_ne_zero.mpr hδ
    simpa [reverseLoading, hj0, hjlast] using neg_ne_zero.mpr
      (hσ ⟨j.val - 1, by omega⟩)
  apply hne
  rw [hp]
  simp

/-- The support annihilator vanishes at every listed direction.  This is the
easy inclusion of the support-annihilator line in the apolar evaluation kernel. -/
lemma supportAnnihilator_eval_zero {m : ℕ} (dirs : Fin (m + 2) → ℂ × ℂ)
    (j : Fin (m + 2)) :
    MvPolynomial.eval₂ (RingHom.id ℂ)
        (fun i : Fin 2 => if i = 0 then (dirs j).1 else (dirs j).2)
        (supportAnnihilator dirs) = 0 := by
  rw [supportAnnihilator, eval₂_prod]
  rw [Finset.prod_eq_zero_iff]
  refine ⟨j, Finset.mem_univ _, ?_⟩
  simp [MvPolynomial.eval₂_sub, mul_comm]

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
