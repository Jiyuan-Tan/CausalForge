/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Reverse apolar kernel and its polynomial rank witness
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarRankBridge
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernelAux

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- The genuine weighted contraction map for the reverse loading family. -/
noncomputable def reverseWeightedContraction (m : ℕ) (η : ParamSpace ℂ m)
    (e : Fin (m + 2) → ℂ) : Fin (m + 1) → MvPolynomial (Fin 2) ℂ :=
  fun k => ∑ j : Fin (m + 2),
    MvPolynomial.C (η.2.2 j (m + 2 + k.1)) * MvPolynomial.C (e j) *
      linForm (reverseLoading m η.1 η.2.1 j) ^ k.1

private lemma reverse_pderiv_iterate_sum (i : Fin 2) (n : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    (fun g => MvPolynomial.pderiv i g)^[n] (∑ j ∈ s, f j) =
      ∑ j ∈ s, (fun g => MvPolynomial.pderiv i g)^[n] (f j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih]

private lemma reverse_pderiv_iterate_C_mul (i : Fin 2) (n : ℕ)
    (a : ℂ) (f : MvPolynomial (Fin 2) ℂ) :
    (fun g => MvPolynomial.pderiv i g)^[n] (MvPolynomial.C a * f) =
      MvPolynomial.C a * (fun g => MvPolynomial.pderiv i g)^[n] f := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih]

private lemma reverse_diffApply_sum (q : MvPolynomial (Fin 2) ℂ) {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    diffApply q (∑ i ∈ s, f i) = ∑ i ∈ s, diffApply q (f i) := by
  classical
  unfold diffApply
  simp_rw [reverse_pderiv_iterate_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.smul_sum]

private lemma reverse_diffApply_C_mul (q f : MvPolynomial (Fin 2) ℂ) (a : ℂ) :
    diffApply q (MvPolynomial.C a * f) = MvPolynomial.C a * diffApply q f := by
  classical
  unfold diffApply
  simp_rw [reverse_pderiv_iterate_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

/-- Common reverse contractions force all directional evaluations to vanish. -/
lemma evalAtDir_zero_of_reverse_contractions (m : ℕ) (η : ParamSpace ℂ m)
    (q : MvPolynomial (Fin 2) ℂ) (hq : q.IsHomogeneous (m + 2))
    (hrank : Function.Injective (reverseWeightedContraction m η))
    (hcon : ∀ k, k ≤ m → diffApply q
      (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0) :
    ∀ j, evalAtDir q (reverseLoading m η.1 η.2.1 j) = 0 := by
  let e : Fin (m + 2) → ℂ := fun j => evalAtDir q (reverseLoading m η.1 η.2.1 j)
  have hB : reverseWeightedContraction m η e = reverseWeightedContraction m η 0 := by
    funext k
    have hk : k.1 ≤ m := Nat.lt_succ_iff.mp k.2
    have h := hcon k.1 hk
    rw [dividedPowerBlock_reverse_eq_sum_linForm_pow m (2 * m + 2) (m + 2 + k.1) η
      (by omega) (by omega), reverse_diffApply_sum] at h
    simp_rw [reverse_diffApply_C_mul, diffApply_linForm_pow q hq] at h
    have hfac : (Nat.descFactorial (m + 2 + k.1) (m + 2) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt
        (Nat.descFactorial_pos.mpr (by omega : m + 2 ≤ m + 2 + k.1))
    rw [reverseWeightedContraction]
    change (∑ j : Fin (m + 2),
      MvPolynomial.C (η.2.2 j (m + 2 + k.1)) * MvPolynomial.C (e j) *
        linForm (reverseLoading m η.1 η.2.1 j) ^ k.1) =
      ∑ j : Fin (m + 2),
        MvPolynomial.C (η.2.2 j (m + 2 + k.1)) *
          MvPolynomial.C ((0 : Fin (m + 2) → ℂ) j) *
          linForm (reverseLoading m η.1 η.2.1 j) ^ k.1
    simp only [Pi.zero_apply, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    apply (mul_eq_zero.mp ?_).resolve_left (MvPolynomial.C_ne_zero.mpr hfac)
    calc
      MvPolynomial.C (Nat.descFactorial (m + 2 + k.1) (m + 2) : ℂ) *
          ∑ j : Fin (m + 2), MvPolynomial.C (η.2.2 j (m + 2 + k.1)) *
            MvPolynomial.C (e j) * linForm (reverseLoading m η.1 η.2.1 j) ^ k.1 =
          ∑ j : Fin (m + 2),
            MvPolynomial.C (Nat.descFactorial (m + 2 + k.1) (m + 2) : ℂ) *
              (MvPolynomial.C (η.2.2 j (m + 2 + k.1)) * MvPolynomial.C (e j) *
                linForm (reverseLoading m η.1 η.2.1 j) ^ k.1) := by rw [Finset.mul_sum]
      _ = 0 := by
        convert h using 1
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [e]
        ring
  have he : e = 0 := hrank hB
  intro j
  exact congrFun he j

private noncomputable def reverseDehom :
    MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => if i = 0 then Polynomial.X else 1)

private lemma reverseDehom_eval (p : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    (reverseDehom p).eval z = evalAtDir p (z, 1) := by
  change (Polynomial.evalRingHom z).comp reverseDehom p = _
  change (Polynomial.evalRingHom z).comp reverseDehom p =
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun i => if i = 0 then z else 1)) p
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [reverseDehom]
  · intro i
    fin_cases i <;> simp [reverseDehom]

private lemma reverseDehom_eq (p : MvPolynomial (Fin 2) ℂ) :
    reverseDehom p = Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => 1))
      (MvPolynomial.finSuccEquiv ℂ 1 p) := by
  have h : reverseDehom =
      (Polynomial.mapRingHom (MvPolynomial.eval (fun _ : Fin 1 => 1))).comp
        (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [reverseDehom, MvPolynomial.finSuccEquiv_apply]
    · intro i
      fin_cases i
      · simp [reverseDehom, MvPolynomial.finSuccEquiv_apply, RingHom.comp_apply]
      · change reverseDehom (MvPolynomial.X (Fin.succ (0 : Fin 1))) =
          ((Polynomial.mapRingHom (MvPolynomial.eval fun _ : Fin 1 => 1)).comp
            (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom)
            (MvPolynomial.X (Fin.succ (0 : Fin 1)))
        simp only [RingHom.comp_apply]
        change reverseDehom (MvPolynomial.X (Fin.succ (0 : Fin 1))) =
          Polynomial.map (MvPolynomial.eval fun _ : Fin 1 => 1)
            (MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X (Fin.succ (0 : Fin 1))))
        rw [MvPolynomial.finSuccEquiv_X_succ]
        simp [reverseDehom, RingHom.comp_apply]
  exact RingHom.congr_fun h p

private lemma reverse_homogeneous_fin_one_eq (p : MvPolynomial (Fin 1) ℂ) (n : ℕ)
    (hp : p.IsHomogeneous n) :
    p = MvPolynomial.C (MvPolynomial.eval (fun _ => 1) p) *
      MvPolynomial.X (0 : Fin 1) ^ n := by
  have hpform : p = MvPolynomial.monomial (Finsupp.single (0 : Fin 1) n)
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) n) p) := by
    apply MvPolynomial.ext
    intro d
    by_cases hd : d.degree = n
    · have hds : d = Finsupp.single (0 : Fin 1) n := by
        apply Finsupp.ext
        intro i
        fin_cases i
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at hd
        simpa using hd
      subst d
      simp
    · rw [hp.coeff_eq_zero hd]
      simp only [MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst d
        simp at hd
      · rfl
  rw [hpform]
  simp [MvPolynomial.monomial_eq]

private lemma reverseDehom_injective_on_homogeneous
    {p : MvPolynomial (Fin 2) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) (hzero : reverseDehom p = 0) : p = 0 := by
  apply (MvPolynomial.finSuccEquiv ℂ 1).injective
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ n
  · have hh := hp.finSuccEquiv_coeff_isHomogeneous i (n - i) (Nat.add_sub_of_le hi)
    rw [reverse_homogeneous_fin_one_eq _ _ hh]
    have heval : MvPolynomial.eval (fun _ : Fin 1 => 1)
        ((MvPolynomial.finSuccEquiv ℂ 1 p).coeff i) = 0 := by
      have hc := congrArg (fun f : Polynomial ℂ => f.coeff i) hzero
      rw [reverseDehom_eq] at hc
      simpa using hc
    simp [heval]
  · have hlt : (MvPolynomial.finSuccEquiv ℂ 1 p).natDegree < i := by
      have hdeg : (MvPolynomial.finSuccEquiv ℂ 1 p).natDegree ≤ n := by
        rw [MvPolynomial.natDegree_finSuccEquiv]
        exact (MvPolynomial.degreeOf_le_totalDegree p 0).trans hp.totalDegree_le
      exact lt_of_le_of_lt hdeg (lt_of_not_ge hi)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp

private lemma reverseDehom_natDegree_le_of_homogeneous
    {p : MvPolynomial (Fin 2) ℂ} {n : ℕ} (hp : p.IsHomogeneous n) :
    (reverseDehom p).natDegree ≤ n := by
  rw [reverseDehom_eq]
  calc
    (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => 1))
        (MvPolynomial.finSuccEquiv ℂ 1 p)).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1 p).natDegree := Polynomial.natDegree_map_le
    _ = p.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv p
    _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
    _ ≤ n := hp.totalDegree_le

private lemma reverse_homogeneous_eval_scale {p : MvPolynomial (Fin 2) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) (a : ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval (fun i => a * v i) p = a ^ n * MvPolynomial.eval v p := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d r hd =>
      simp only [MvPolynomial.eval_monomial, mul_pow, Finsupp.prod_mul]
      have ha : d.prod (fun _ e => a ^ e) = a ^ n := by
        change (∏ i ∈ d.support, a ^ d i) = a ^ n
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        have hd' : d.degree = n := by
          rw [Finsupp.degree_eq_weight_one]
          exact hd
        simpa [Finsupp.degree_apply] using hd'
      rw [ha]
      ring

private lemma reverse_succ_second (m : ℕ) (η : ParamSpace ℂ m) (j : Fin (m + 1)) :
    (reverseLoading m η.1 η.2.1 j.succ).2 = 1 := by
  rw [reverseLoading]
  split
  · rename_i h
    simp at h
  · split <;> rfl

private lemma reverse_axis_eval_gives_top_coeff (m : ℕ) (η : ParamSpace ℂ m)
    (p : MvPolynomial (Fin 2) ℂ)
    (hpHom : p.IsHomogeneous (m + 2))
    (hp : evalAtDir p (reverseLoading m η.1 η.2.1 0) = 0) :
    (reverseDehom p).coeff (m + 2) = 0 := by
  let F := MvPolynomial.finSuccEquiv ℂ 1 p
  have hpoly : Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => 0)) F =
      Polynomial.monomial (m + 2) ((reverseDehom p).coeff (m + 2)) := by
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_map, Polynomial.coeff_monomial]
    by_cases hi : i = m + 2
    · subst i
      simp only [if_pos rfl]
      have hh := hpHom.finSuccEquiv_coeff_isHomogeneous (m + 2) 0 (by omega)
      have hf := reverse_homogeneous_fin_one_eq (F.coeff (m + 2)) 0 hh
      rw [hf]
      simp [F, reverseDehom_eq, MvPolynomial.coeff_eval_eq_eval_coeff]
    · have hi' : m + 2 ≠ i := Ne.symm hi
      rw [if_neg hi']
      by_cases hil : i ≤ m + 2
      · have hpos : 0 < m + 2 - i := Nat.sub_pos_of_lt (lt_of_le_of_ne hil hi)
        have hh := hpHom.finSuccEquiv_coeff_isHomogeneous i (m + 2 - i)
          (Nat.add_sub_of_le hil)
        rw [reverse_homogeneous_fin_one_eq _ _ hh]
        simp [hpos.ne']
      · have hlt : F.natDegree < i := by
          have hdeg : F.natDegree ≤ m + 2 := by
            dsimp [F]
            rw [MvPolynomial.natDegree_finSuccEquiv]
            exact (MvPolynomial.degreeOf_le_totalDegree p 0).trans hpHom.totalDegree_le
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
        simp
  have hp' : Polynomial.eval 1
      (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => 0)) F) = 0 := by
    rw [← MvPolynomial.eval_eq_eval_mv_eval']
    have hfun : Fin.cons (1 : ℂ) (fun _ : Fin 1 => (0 : ℂ)) =
        fun i : Fin 2 => if i = 0 then (1 : ℂ) else (0 : ℂ) := by
      funext i
      fin_cases i <;> simp
    rw [hfun]
    simpa [F, evalAtDir, reverseLoading] using hp
  rw [hpoly] at hp'
  simpa using hp'

private lemma reverseDehom_support (m : ℕ) (η : ParamSpace ℂ m) :
    reverseDehom (supportAnnihilator (reverseLoading m η.1 η.2.1)) =
      -∏ j : Fin (m + 1),
        (Polynomial.X - Polynomial.C
          (reverseLoading m η.1 η.2.1 j.succ).1) := by
  rw [supportAnnihilator, map_prod, Fin.prod_univ_succ]
  simp [reverseDehom, reverseLoading]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hlast : j.val = m
  · simp [hlast]
  · simp [hlast]

private lemma reverseDehom_support_coeff (m : ℕ) (η : ParamSpace ℂ m) :
    (reverseDehom (supportAnnihilator (reverseLoading m η.1 η.2.1))).coeff
      (m + 1) = -1 := by
  rw [reverseDehom_support]
  let f : Fin (m + 1) → Polynomial ℂ := fun j =>
    Polynomial.X - Polynomial.C (reverseLoading m η.1 η.2.1 j.succ).1
  have hfmonic : ∀ j, (f j).Monic := fun j => Polynomial.monic_X_sub_C _
  have hprodMonic : (∏ j, f j).Monic := by
    exact Polynomial.monic_prod_of_monic Finset.univ f (fun j _ => hfmonic j)
  have hprodDeg : (∏ j, f j).natDegree = m + 1 := by
    change (∏ j ∈ Finset.univ, f j).natDegree = m + 1
    rw [Polynomial.natDegree_prod_of_monic
      (s := Finset.univ) (f := f) (fun j _ => hfmonic j)]
    simp [f]
  let g : Polynomial ℂ := ∏ j, f j
  have hgdeg : g.natDegree = m + 1 := hprodDeg
  have hgmonic : g.Monic := hprodMonic
  change -g.coeff (m + 1) = -1
  calc
    -g.coeff (m + 1) = -g.coeff g.natDegree := by rw [hgdeg]
    _ = -g.leadingCoeff := by rw [Polynomial.coeff_natDegree]
    _ = -1 := by rw [hgmonic.leadingCoeff]

/-- Reverse interpolation in the affine chart `X₁ = 1`, with the omitted
axis direction supplying the vanishing top coefficient. -/
lemma reverse_points_imply_supportAnnihilator_multiple (m : ℕ)
    (η : ParamSpace ℂ m) (q : MvPolynomial (Fin 2) ℂ)
    (hq : q.IsHomogeneous (m + 2))
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) =>
        (reverseLoading m η.1 η.2.1 j.succ).1))
    (_hnonzero : ∀ j : Fin (m + 1),
      (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0)
    (hzero : ∀ j, evalAtDir q (reverseLoading m η.1 η.2.1 j) = 0) :
    ∃ c : ℂ, q = c • supportAnnihilator (reverseLoading m η.1 η.2.1) := by
  let dirs : Fin (m + 2) → ℂ × ℂ := reverseLoading m η.1 η.2.1
  let Q := supportAnnihilator dirs
  have hQhom : Q.IsHomogeneous (m + 2) := supportAnnihilator_isHomogeneous dirs
  have hQcoeff : (reverseDehom Q).coeff (m + 1) = -1 := by
    simpa [Q, dirs] using reverseDehom_support_coeff m η
  let c : ℂ := (reverseDehom q).coeff (m + 1) / (reverseDehom Q).coeff (m + 1)
  let r : MvPolynomial (Fin 2) ℂ := q - MvPolynomial.C c * Q
  have hrhom : r.IsHomogeneous (m + 2) := by
    apply (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (m + 2)).sub_mem hq
    exact hQhom.C_mul c
  have hrtop : (reverseDehom r).coeff (m + 2) = 0 := by
    dsimp [r]
    rw [map_sub, map_mul]
    simp only [reverseDehom, MvPolynomial.eval₂Hom_C, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    have hqtop : (reverseDehom q).coeff (m + 2) = 0 :=
      reverse_axis_eval_gives_top_coeff m η q hq (hzero 0)
    have hQtop : (reverseDehom Q).coeff (m + 2) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [reverseDehom_support]
      have hdeg : (∏ j : Fin (m + 1),
          (Polynomial.X - Polynomial.C
            (reverseLoading m η.1 η.2.1 j.succ).1)).natDegree = m + 1 := by
        rw [Polynomial.natDegree_prod]
        · simp
        · intro j hj hz
          exact (Polynomial.monic_X_sub_C _).ne_zero hz
      rw [Polynomial.natDegree_neg, hdeg]
      omega
    change (reverseDehom q).coeff (m + 2) -
      c * (reverseDehom Q).coeff (m + 2) = 0
    rw [hqtop, hQtop]
    ring
  have hrnext : (reverseDehom r).coeff (m + 1) = 0 := by
    dsimp [r, c]
    rw [map_sub, map_mul]
    simp only [reverseDehom, MvPolynomial.eval₂Hom_C, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    have hQne : (reverseDehom Q).coeff (m + 1) ≠ 0 := by
      rw [hQcoeff]
      exact neg_ne_zero.mpr one_ne_zero
    change (reverseDehom q).coeff (m + 1) -
      ((reverseDehom q).coeff (m + 1) / (reverseDehom Q).coeff (m + 1)) *
        (reverseDehom Q).coeff (m + 1) = 0
    rw [div_mul_cancel₀ _ hQne, sub_self]
  have hrroot : ∀ j : Fin (m + 1),
      Polynomial.IsRoot (reverseDehom r) (dirs j.succ).1 := by
    intro j
    have hQzero : evalAtDir Q (dirs j.succ) = 0 :=
      evalAtDir_supportAnnihilator_eq_zero dirs j.succ
    have hqzero : evalAtDir q (dirs j.succ) = 0 := by
      simpa [dirs] using hzero j.succ
    have hrorig : evalAtDir r (dirs j.succ) = 0 := by
      change evalAtDir (q - MvPolynomial.C c * Q) (dirs j.succ) = 0
      simp only [evalAtDir, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
        MvPolynomial.eval_C] at hqzero hQzero ⊢
      rw [hqzero, hQzero]
      ring
    change (reverseDehom r).eval (dirs j.succ).1 = 0
    rw [reverseDehom_eval]
    have hsnd : (dirs j.succ).2 = 1 := by
      exact reverse_succ_second m η j
    change evalAtDir r ((dirs j.succ).1, 1) = 0
    rw [← hsnd]
    exact hrorig
  have hrdehom : reverseDehom r = 0 := by
    by_contra hne
    have hdeg_le : (reverseDehom r).natDegree ≤ m + 2 :=
      reverseDehom_natDegree_le_of_homogeneous hrhom
    have hdeg_lt : (reverseDehom r).natDegree < m + 1 := by
      by_contra hnot
      have hge : m + 1 ≤ (reverseDehom r).natDegree := Nat.le_of_not_gt hnot
      have hcases : (reverseDehom r).natDegree = m + 1 ∨
          (reverseDehom r).natDegree = m + 2 := by omega
      rcases hcases with hd | hd
      · exact (Polynomial.leadingCoeff_ne_zero.mpr hne)
          (by rw [← Polynomial.coeff_natDegree, hd, hrnext])
      · exact (Polynomial.leadingCoeff_ne_zero.mpr hne)
          (by rw [← Polynomial.coeff_natDegree, hd, hrtop])
    have hsub : Finset.image (fun j : Fin (m + 1) => (dirs j.succ).1)
        Finset.univ ⊆ (reverseDehom r).roots.toFinset := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨j, hj, rfl⟩ := hz
      simp only [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hrroot j
    have hmany : m + 1 ≤ (reverseDehom r).natDegree := by
      calc
        m + 1 = (Finset.image (fun j : Fin (m + 1) => (dirs j.succ).1)
            Finset.univ).card := by
              rw [Finset.card_image_iff.mpr (by simpa [dirs] using hslopes)]
              simp
        _ ≤ (reverseDehom r).roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ (reverseDehom r).roots.card := Multiset.toFinset_card_le _
        _ ≤ (reverseDehom r).natDegree := Polynomial.card_roots' _
    omega
  have hrzero : r = 0 := reverseDehom_injective_on_homogeneous hrhom hrdehom
  refine ⟨c, ?_⟩
  have heq : q = MvPolynomial.C c * Q := sub_eq_zero.mp hrzero
  simpa [Q, dirs, MvPolynomial.smul_eq_C_mul] using heq

/-- The common reverse apolar kernel is the reverse support-annihilator line. -/
theorem reverse_apolar_kernel_identity (m : ℕ) (η : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) =>
        (reverseLoading m η.1 η.2.1 j.succ).1))
    (hnonzero : ∀ j : Fin (m + 1),
      (reverseLoading m η.1 η.2.1 j.succ).1 ≠ 0)
    (hrank : Function.Injective (reverseWeightedContraction m η)) :
    ∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
      ((∀ k, k ≤ m → diffApply q
          (dividedPowerBlock (reverseCumulantMap m (2 * m + 2) η) (m + 2 + k)) = 0)
        ↔ ∃ c : ℂ, q = c • supportAnnihilator (reverseLoading m η.1 η.2.1)) := by
  intro q hq
  constructor
  · intro hcon
    apply reverse_points_imply_supportAnnihilator_multiple m η q hq hslopes hnonzero
    exact evalAtDir_zero_of_reverse_contractions m η q hq hrank hcon
  · exact reverse_supportAnnihilator_in_contraction_kernel m η q hq

private def reverseSlopePolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) ℂ :=
  if h0 : j.1 = 0 then 1
  else if ha : j.1 = m + 1 then MvPolynomial.X (Sum.inl ())
  else MvPolynomial.X (Sum.inr (Sum.inl ⟨j.1 - 1, by omega⟩))

private def reverseSecondPolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) ℂ :=
  if j.1 = 0 then 0 else 1

private def reverseWeightPolynomial (m : ℕ) (j : Fin (m + 2)) (r : ℕ) :
    MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.X (Sum.inr (Sum.inr (j, r)))

/-- The reverse coefficient minor: row zero uses the degree-zero block and
the other rows use all coefficients of the degree-`m` block. -/
private def reverseContractionMinorPolynomial (m : ℕ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial (ParamCoord m) ℂ) :=
  fun i j => Fin.cases
    (reverseWeightPolynomial m j (m + 2))
    (fun r => reverseWeightPolynomial m j (2 * m + 2) *
      MvPolynomial.C (m.choose r.1 : ℂ) *
      reverseSlopePolynomial m j ^ r.1 * reverseSecondPolynomial m j ^ (m - r.1)) i

private def reverseContractionMinor (m : ℕ) (η : ParamSpace ℂ m) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  (reverseContractionMinorPolynomial m).map (MvPolynomial.eval (paramEval η))

private lemma eval_reverseSlopePolynomial (m : ℕ) (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval η) (reverseSlopePolynomial m j) =
      (reverseLoading m η.1 η.2.1 j).1 := by
  simp [reverseSlopePolynomial, reverseLoading]
  split_ifs <;> simp [paramEval]

private lemma eval_reverseSecondPolynomial (m : ℕ) (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval η) (reverseSecondPolynomial m j) =
      (reverseLoading m η.1 η.2.1 j).2 := by
  simp [reverseSecondPolynomial, reverseLoading]
  split_ifs <;> simp_all

private lemma reverseContractionMinor_apply (m : ℕ) (η : ParamSpace ℂ m)
    (i j : Fin (m + 2)) :
    reverseContractionMinor m η i j = Fin.cases
      (η.2.2 j (m + 2))
      (fun r => η.2.2 j (2 * m + 2) * (m.choose r.1 : ℂ) *
        (reverseLoading m η.1 η.2.1 j).1 ^ r.1 *
        (reverseLoading m η.1 η.2.1 j).2 ^ (m - r.1)) i := by
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [reverseContractionMinor, reverseContractionMinorPolynomial,
      reverseWeightPolynomial, paramEval]
  · simp [reverseContractionMinor, reverseContractionMinorPolynomial,
      reverseWeightPolynomial, paramEval, eval_reverseSlopePolynomial,
      eval_reverseSecondPolynomial]

@[simp] private lemma reverseDehom_C (c : ℂ) :
    reverseDehom (MvPolynomial.C c) = Polynomial.C c := by
  simp [reverseDehom]

private lemma coeff_reverseDehom_linForm_pow (u : ℂ × ℂ) (m r : ℕ) :
    (reverseDehom (linForm u) ^ m).coeff r =
      (m.choose r : ℂ) * u.1 ^ r * u.2 ^ (m - r) := by
  have hlin : reverseDehom (linForm u) =
      Polynomial.C u.1 * Polynomial.X + Polynomial.C u.2 := by
    simp [reverseDehom, linForm]
  rw [hlin, Commute.add_pow (Commute.all _ _)]
  simp only [Polynomial.finset_sum_coeff]
  have hterm (x : ℕ) :
      (Polynomial.C u.1 * Polynomial.X) ^ x * Polynomial.C u.2 ^ (m - x) =
        Polynomial.C (u.1 ^ x * u.2 ^ (m - x)) * Polynomial.X ^ x := by
    rw [mul_pow, ← map_pow, ← map_pow, map_mul]
    ring
  simp only [hterm, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul_X_pow]
  by_cases hr : r < m + 1
  · rw [Finset.sum_eq_single r]
    · simp
      ring
    · intro b hb hbr
      simp [Ne.symm hbr]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hr))
  · have hmr : m < r := by omega
    have hchoose : m.choose r = 0 := Nat.choose_eq_zero_of_lt hmr
    rw [show (m.choose r : ℂ) = 0 by simp [hchoose]]
    simp only [zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    have hbr : r ≠ b := by
      have := Finset.mem_range.mp hb
      omega
    simp [hbr]

private lemma reverse_minor_mulVec_eq_zero_of_contraction_eq_zero (m : ℕ)
    (η : ParamSpace ℂ m) (e : Fin (m + 2) → ℂ)
    (he : reverseWeightedContraction m η e = 0) :
    (reverseContractionMinor m η).mulVec e = 0 := by
  funext i
  refine Fin.cases ?_ (fun r => ?_) i
  · have hzero := congrFun he (0 : Fin (m + 1))
    have h := congrArg (fun p => (reverseDehom p).coeff 0) hzero
    simp [reverseWeightedContraction, reverseContractionMinor_apply, Matrix.mulVec,
      dotProduct, reverseDehom] at h ⊢
    simpa [mul_assoc] using h
  · have htop := congrFun he ⟨m, by omega⟩
    have h := congrArg (fun p => (reverseDehom p).coeff r.1) htop
    simp only [reverseWeightedContraction, map_sum, map_mul, map_pow,
      Polynomial.finset_sum_coeff, map_zero, Polynomial.coeff_zero, Pi.zero_apply,
      reverseDehom_C] at h
    have hindex : m + 2 + m = 2 * m + 2 := by omega
    rw [hindex] at h
    simp only [reverseContractionMinor_apply, Fin.cases_succ, Matrix.mulVec, dotProduct]
    calc
      _ = ∑ x, e x * (η.2.2 x (2 * m + 2) *
          (reverseDehom (linForm (reverseLoading m η.1 η.2.1 x)) ^ m).coeff r.1) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [coeff_reverseDehom_linForm_pow]
        ring
      _ = ∑ x, (Polynomial.C (η.2.2 x (2 * m + 2)) * Polynomial.C (e x) *
          reverseDehom (linForm (reverseLoading m η.1 η.2.1 x)) ^ m).coeff r.1 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← map_mul, Polynomial.coeff_C_mul]
        ring
      _ = 0 := h

private lemma reverse_contraction_injective_of_minor_det_ne_zero (m : ℕ)
    (η : ParamSpace ℂ m) (hdet : (reverseContractionMinor m η).det ≠ 0) :
    Function.Injective (reverseWeightedContraction m η) := by
  intro e e' he
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  apply reverse_minor_mulVec_eq_zero_of_contraction_eq_zero
  funext k
  calc
    reverseWeightedContraction m η (e - e') k =
        reverseWeightedContraction m η e k - reverseWeightedContraction m η e' k := by
      simp only [reverseWeightedContraction, Pi.sub_apply, map_sub]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := sub_eq_zero.mpr (congrFun he k)

private def reverseWitnessParameter (m : ℕ) : ParamSpace ℂ m :=
  (((m + 1 : ℕ) : ℂ), (fun i => ((i.1 + 1 : ℕ) : ℂ)), fun j r =>
    if r = m + 2 then if j.1 = 0 then 1 else 0
    else if r = 2 * m + 2 then if j.1 = 0 then 0 else 1
    else 0)

private lemma reverse_witness_loading_succ (m : ℕ) (j : Fin (m + 1)) :
    reverseLoading m (reverseWitnessParameter m).1
      (reverseWitnessParameter m).2.1 j.succ =
      ((((j.1 + 1 : ℕ) : ℂ)), (1 : ℂ)) := by
  rcases j with ⟨j, hj⟩
  simp only [reverseLoading, reverseWitnessParameter, Fin.succ_mk, Fin.val_mk]
  have hzero : j + 1 ≠ 0 := by omega
  simp only [hzero, ↓reduceDIte]
  by_cases hlast : j + 1 = m + 1
  · simp [hlast]
  · simp [hlast]
    norm_cast
    omega

private lemma reverseWitnessSlope_injective (m : ℕ) :
    Function.Injective (fun j : Fin (m + 1) => ((j.1 + 1 : ℕ) : ℂ)) := by
  intro i j h
  apply Fin.ext
  have hnat : i.1 + 1 = j.1 + 1 := by
    apply Nat.cast_injective (R := ℂ)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  omega

private lemma reverse_witness_minor_zero_axis (m : ℕ) :
    reverseContractionMinor m (reverseWitnessParameter m) 0 0 = 1 := by
  simp [reverseContractionMinor_apply, reverseWitnessParameter]

private lemma reverse_witness_minor_zero_succ (m : ℕ) (j : Fin (m + 1)) :
    reverseContractionMinor m (reverseWitnessParameter m) 0 j.succ = 0 := by
  simp [reverseContractionMinor_apply, reverseWitnessParameter]

private lemma reverse_witness_minor_succ_axis (m : ℕ) (hm : 1 ≤ m)
    (r : Fin (m + 1)) :
    reverseContractionMinor m (reverseWitnessParameter m) r.succ 0 = 0 := by
  rw [reverseContractionMinor_apply]
  simp [reverseWitnessParameter, reverseLoading, show 2 * m ≠ m by omega]

private lemma reverse_witness_minor_succ_succ (m : ℕ) (hm : 1 ≤ m)
    (r j : Fin (m + 1)) :
    reverseContractionMinor m (reverseWitnessParameter m) r.succ j.succ =
      (m.choose r.1 : ℂ) * (((j.1 + 1 : ℕ) : ℂ) ^ r.1) := by
  rw [reverseContractionMinor_apply]
  simp only [Fin.cases_succ, reverseWitnessParameter]
  have hload := reverse_witness_loading_succ m j
  change reverseLoading m (((m + 1 : ℕ) : ℂ))
      (fun i => ((i.1 + 1 : ℕ) : ℂ)) j.succ = _ at hload
  rw [hload]
  simp [show 2 * m ≠ m by omega]

private lemma reverse_witness_minor_det_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    (reverseContractionMinor m (reverseWitnessParameter m)).det ≠ 0 := by
  have hinj : Function.Injective
      (reverseContractionMinor m (reverseWitnessParameter m)).mulVec := by
    intro e e' he
    have haxis : e 0 = e' 0 := by
      have h := congrFun he (0 : Fin (m + 2))
      change (∑ j : Fin (m + 2),
          reverseContractionMinor m (reverseWitnessParameter m) 0 j * e j) =
        ∑ j : Fin (m + 2),
          reverseContractionMinor m (reverseWitnessParameter m) 0 j * e' j at h
      conv_lhs at h => rw [Fin.sum_univ_succ]
      conv_rhs at h => rw [Fin.sum_univ_succ]
      simpa only [reverse_witness_minor_zero_axis, reverse_witness_minor_zero_succ,
        one_mul, zero_mul, Finset.sum_const_zero, add_zero] using h
    have hfinite : (fun j : Fin (m + 1) => e j.succ) = fun j => e' j.succ := by
      have hsum : ∀ r : Fin (m + 1),
          ∑ j : Fin (m + 1), (e j.succ - e' j.succ) *
            (((j.1 + 1 : ℕ) : ℂ) ^ r.1) = 0 := by
        intro r
        have h := congrFun he r.succ
        have hchoose : (m.choose r.1 : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.mp r.2)).ne'
        change (∑ j : Fin (m + 2),
            reverseContractionMinor m (reverseWitnessParameter m) r.succ j * e j) =
          ∑ j : Fin (m + 2),
            reverseContractionMinor m (reverseWitnessParameter m) r.succ j * e' j at h
        conv_lhs at h => rw [Fin.sum_univ_succ]
        conv_rhs at h => rw [Fin.sum_univ_succ]
        simp only [reverse_witness_minor_succ_axis m hm,
          reverse_witness_minor_succ_succ m hm, zero_mul, zero_add] at h
        apply (mul_eq_zero.mp ?_).resolve_left hchoose
        calc
          (m.choose r.1 : ℂ) * (∑ j : Fin (m + 1),
              (e j.succ - e' j.succ) * (((j.1 + 1 : ℕ) : ℂ) ^ r.1)) =
              (∑ j : Fin (m + 1), (m.choose r.1 : ℂ) *
                (((j.1 + 1 : ℕ) : ℂ) ^ r.1) * e j.succ) -
              ∑ j : Fin (m + 1), (m.choose r.1 : ℂ) *
                (((j.1 + 1 : ℕ) : ℂ) ^ r.1) * e' j.succ := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = 0 := sub_eq_zero.mpr h
      have hv : (fun j : Fin (m + 1) => e j.succ - e' j.succ) = 0 := by
        apply Matrix.eq_zero_of_vecMul_eq_zero
          (Matrix.det_vandermonde_ne_zero_iff.mpr (reverseWitnessSlope_injective m))
        funext r
        exact hsum r
      funext j
      exact sub_eq_zero.mp (congrFun hv j)
    funext j
    refine Fin.cases haxis (fun i => ?_) j
    exact congrFun hfinite i
  have hu : IsUnit (reverseContractionMinor m (reverseWitnessParameter m)) :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit (reverseContractionMinor m (reverseWitnessParameter m)).det := by
    have h := hu.map (Matrix.detMonoidHom (n := Fin (m + 2)) (R := ℂ))
    simpa only [Matrix.coe_detMonoidHom] using h
  exact isUnit_iff_ne_zero.mp hdet

/-- Reverse contraction injectivity holds on the principal open set cut out
by a genuine coefficient-minor determinant. The polynomial is nonzero at an explicit witness whose
weights vanish outside the pinned degree band. -/
theorem reverse_contraction_injective_of_generic_and_minor (m : ℕ) (hm : 1 ≤ m) :
    ∃ P : MvPolynomial (ParamCoord m) ℂ, P ≠ 0 ∧
      (∃ θ₀ : ParamSpace ℂ m,
        (∀ (j : Fin (m + 2)) (r : ℕ), (r < 2 ∨ 2 * m + 2 < r) → θ₀.2.2 j r = 0) ∧
        MvPolynomial.eval (paramEval θ₀) P ≠ 0) ∧
      ∀ η : ParamSpace ℂ m, MvPolynomial.eval (paramEval η) P ≠ 0 →
        Function.Injective (reverseWeightedContraction m η) := by
  refine ⟨(reverseContractionMinorPolynomial m).det, ?_, ?_, ?_⟩
  · intro hzero
    apply reverse_witness_minor_det_ne_zero m hm
    change Matrix.det
      ((MvPolynomial.eval (paramEval (reverseWitnessParameter m))).mapMatrix
        (reverseContractionMinorPolynomial m)) = 0
    rw [← RingHom.map_det, hzero, map_zero]
  · refine ⟨reverseWitnessParameter m, ?_, ?_⟩
    · intro j r hr
      simp only [reverseWitnessParameter]
      rcases hr with hr | hr
      · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]
    · intro hzero
      apply reverse_witness_minor_det_ne_zero m hm
      change Matrix.det
        ((MvPolynomial.eval (paramEval (reverseWitnessParameter m))).mapMatrix
          (reverseContractionMinorPolynomial m)) = 0
      rw [← RingHom.map_det]
      exact hzero
  · intro η hη
    apply reverse_contraction_injective_of_minor_det_ne_zero m η
    change Matrix.det ((MvPolynomial.eval (paramEval η)).mapMatrix
      (reverseContractionMinorPolynomial m)) ≠ 0
    rw [← RingHom.map_det]
    exact hη

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
