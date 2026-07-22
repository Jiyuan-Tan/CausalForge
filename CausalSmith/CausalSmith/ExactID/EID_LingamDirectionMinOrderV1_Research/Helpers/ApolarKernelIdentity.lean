/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The common contraction kernel is the support-annihilator line `ker = ⟨Q_D⟩`

Assembles the differentiation identity, the divided-power binomial bridge, the
support-annihilator vanishing, and the generic stacked block-Vandermonde rank
into the apolar kernel identity used by the arrow-recovery flagship.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernelDiff
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernelRank

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators


/-- Evaluation at a direction is the `eval₂` used by the support-annihilator
lemma, so the latter can be used directly in apolar calculations. -/
lemma evalAtDir_supportAnnihilator_eq_zero {m : ℕ}
    (dirs : Fin (m + 2) → ℂ × ℂ) (j : Fin (m + 2)) :
    evalAtDir (supportAnnihilator dirs) (dirs j) = 0 := by
  exact supportAnnihilator_eval_zero dirs j

private lemma pderiv_iterate_sum (i : Fin 2) (n : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    (fun g => MvPolynomial.pderiv i g)^[n] (∑ j ∈ s, f j) =
      ∑ j ∈ s, (fun g => MvPolynomial.pderiv i g)^[n] (f j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih]

private lemma pderiv_iterate_C_mul (i : Fin 2) (n : ℕ)
    (a : ℂ) (f : MvPolynomial (Fin 2) ℂ) :
    (fun g => MvPolynomial.pderiv i g)^[n] (MvPolynomial.C a * f) =
      MvPolynomial.C a * (fun g => MvPolynomial.pderiv i g)^[n] f := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih]

/-- Proves the stated mathematical property of diff Apply sum. -/
lemma diffApply_sum (q : MvPolynomial (Fin 2) ℂ) {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin 2) ℂ) :
    diffApply q (∑ i ∈ s, f i) = ∑ i ∈ s, diffApply q (f i) := by
  classical
  unfold diffApply
  simp_rw [pderiv_iterate_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.smul_sum]

/-- Proves the stated mathematical property of diff Apply C mul. -/
lemma diffApply_C_mul (q f : MvPolynomial (Fin 2) ℂ) (a : ℂ) :
    diffApply q (MvPolynomial.C a * f) = MvPolynomial.C a * diffApply q f := by
  classical
  unfold diffApply
  simp_rw [pderiv_iterate_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.smul_eq_C_mul]
  ring

/-- The easy half of the apolar kernel calculation: a homogeneous form that
vanishes on every loading direction annihilates every retained contraction. -/
lemma forward_contractions_vanish_of_evalAtDir_zero (m : ℕ)
    (θ : ParamSpace ℂ m) (q : MvPolynomial (Fin 2) ℂ)
    (hq : q.IsHomogeneous (m + 2))
    (hzero : ∀ j, evalAtDir q (forwardLoading m θ.1 θ.2.1 j) = 0)
    (k : ℕ) (hk : k ≤ m) :
    diffApply q
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0 := by
  rw [dividedPowerBlock_forward_eq_sum_linForm_pow m (2 * m + 2) (m + 2 + k) θ]
  · rw [diffApply_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [diffApply_C_mul, diffApply_linForm_pow q hq]
    rw [hzero j]
    simp
  · omega
  · omega

/-- The support-annihilator line is contained in the common contraction
kernel.  This is the backwards implication of the desired `ker = ⟨Q_D⟩`.
-/
lemma forward_supportAnnihilator_in_contraction_kernel (m : ℕ)
    (θ : ParamSpace ℂ m) (q : MvPolynomial (Fin 2) ℂ)
    (hq : q.IsHomogeneous (m + 2))
    (hqD : ∃ c : ℂ, q = c • supportAnnihilator (forwardLoading m θ.1 θ.2.1)) :
    ∀ k, k ≤ m → diffApply q
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0 := by
  rintro k hk
  apply forward_contractions_vanish_of_evalAtDir_zero m θ q hq _ k hk
  intro j
  rcases hqD with ⟨c, rfl⟩
  simp only [MvPolynomial.smul_eq_C_mul]
  have hQ : evalAtDir (supportAnnihilator (forwardLoading m θ.1 θ.2.1))
      (forwardLoading m θ.1 θ.2.1 j) = 0 :=
    evalAtDir_supportAnnihilator_eq_zero _ j
  simp only [evalAtDir] at hQ ⊢
  rw [MvPolynomial.eval_mul, hQ, mul_zero]

/-- The genuine (un-charted) weighted block-contraction map.  Its injectivity
is exactly the rank-open condition needed in the forward implication. -/
noncomputable def forwardWeightedContraction (m : ℕ) (θ : ParamSpace ℂ m)
    (e : Fin (m + 2) → ℂ) : Fin (m + 1) → MvPolynomial (Fin 2) ℂ :=
  fun k => ∑ j : Fin (m + 2),
    MvPolynomial.C (θ.2.2 j (m + 2 + k.1)) * MvPolynomial.C (e j) *
      linForm (forwardLoading m θ.1 θ.2.1 j) ^ k.1

/-- Under injectivity of the actual weighted contraction map, the common
contraction equations force every directional evaluation to vanish. -/
lemma evalAtDir_zero_of_forward_contractions (m : ℕ) (θ : ParamSpace ℂ m)
    (q : MvPolynomial (Fin 2) ℂ) (hq : q.IsHomogeneous (m + 2))
    (hrank : Function.Injective (forwardWeightedContraction m θ))
    (hcon : ∀ k, k ≤ m → diffApply q
      (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0) :
    ∀ j, evalAtDir q (forwardLoading m θ.1 θ.2.1 j) = 0 := by
  let e : Fin (m + 2) → ℂ := fun j => evalAtDir q (forwardLoading m θ.1 θ.2.1 j)
  have hB : forwardWeightedContraction m θ e = forwardWeightedContraction m θ 0 := by
    funext k
    have hk : k.1 ≤ m := Nat.lt_succ_iff.mp k.2
    have h := hcon k.1 hk
    rw [dividedPowerBlock_forward_eq_sum_linForm_pow m (2 * m + 2) (m + 2 + k.1) θ
      (by omega) (by omega), diffApply_sum] at h
    simp_rw [diffApply_C_mul, diffApply_linForm_pow q hq] at h
    -- The nonzero descending-factorial scalar is common to all summands.
    have hfac : (Nat.descFactorial (m + 2 + k.1) (m + 2) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt
        (Nat.descFactorial_pos.mpr (by omega : m + 2 ≤ m + 2 + k.1))
    rw [forwardWeightedContraction]
    change (∑ j : Fin (m + 2),
      MvPolynomial.C (θ.2.2 j (m + 2 + k.1)) * MvPolynomial.C (e j) *
        linForm (forwardLoading m θ.1 θ.2.1 j) ^ k.1) =
      ∑ j : Fin (m + 2),
        MvPolynomial.C (θ.2.2 j (m + 2 + k.1)) * MvPolynomial.C ((0 : Fin (m + 2) → ℂ) j) *
          linForm (forwardLoading m θ.1 θ.2.1 j) ^ k.1
    simp only [Pi.zero_apply, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    apply (mul_eq_zero.mp ?_).resolve_left (MvPolynomial.C_ne_zero.mpr hfac)
    calc
      MvPolynomial.C (Nat.descFactorial (m + 2 + k.1) (m + 2) : ℂ) *
          ∑ j : Fin (m + 2),
            MvPolynomial.C (θ.2.2 j (m + 2 + k.1)) * MvPolynomial.C (e j) *
              linForm (forwardLoading m θ.1 θ.2.1 j) ^ k.1 =
          ∑ j : Fin (m + 2),
            MvPolynomial.C (Nat.descFactorial (m + 2 + k.1) (m + 2) : ℂ) *
              (MvPolynomial.C (θ.2.2 j (m + 2 + k.1)) * MvPolynomial.C (e j) *
                linForm (forwardLoading m θ.1 θ.2.1 j) ^ k.1) := by
            rw [Finset.mul_sum]
      _ = 0 := by
        convert h using 1
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [e]
        ring
  have he : e = 0 := hrank hB
  intro j
  exact congrFun he j

private noncomputable def dehomInf :
    MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => if i = 0 then Polynomial.X else 1)

private lemma dehomInf_eval (p : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    (dehomInf p).eval z = evalAtDir p (z, 1) := by
  change (Polynomial.evalRingHom z).comp dehomInf p = _
  change (Polynomial.evalRingHom z).comp dehomInf p =
    (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun i => if i = 0 then z else 1)) p
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [dehomInf]
  · intro i
    fin_cases i <;> simp [dehomInf]

private lemma dehomInf_eq (p : MvPolynomial (Fin 2) ℂ) :
    dehomInf p =
      Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => 1))
        (MvPolynomial.finSuccEquiv ℂ 1 p) := by
  have h : dehomInf =
      (Polynomial.mapRingHom (MvPolynomial.eval (fun _ : Fin 1 => 1))).comp
        (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [dehomInf, MvPolynomial.finSuccEquiv_apply]
    · intro i
      fin_cases i
      · simp [dehomInf, MvPolynomial.finSuccEquiv_apply, RingHom.comp_apply]
      · change dehomInf (MvPolynomial.X (Fin.succ (0 : Fin 1))) =
          ((Polynomial.mapRingHom (MvPolynomial.eval fun _ : Fin 1 => 1)).comp
            (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom)
            (MvPolynomial.X (Fin.succ (0 : Fin 1)))
        simp only [RingHom.comp_apply]
        change dehomInf (MvPolynomial.X (Fin.succ (0 : Fin 1))) =
          Polynomial.map (MvPolynomial.eval fun _ : Fin 1 => 1)
            (MvPolynomial.finSuccEquiv ℂ 1
              (MvPolynomial.X (Fin.succ (0 : Fin 1))))
        rw [MvPolynomial.finSuccEquiv_X_succ]
        simp [dehomInf, RingHom.comp_apply]
  exact RingHom.congr_fun h p

private lemma homogeneous_fin_one_eq (p : MvPolynomial (Fin 1) ℂ) (n : ℕ)
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

private lemma dehomInf_injective_on_homogeneous
    {p : MvPolynomial (Fin 2) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) (hzero : dehomInf p = 0) : p = 0 := by
  apply (MvPolynomial.finSuccEquiv ℂ 1).injective
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ n
  · have hh := hp.finSuccEquiv_coeff_isHomogeneous i (n - i) (Nat.add_sub_of_le hi)
    rw [homogeneous_fin_one_eq _ _ hh]
    have heval : MvPolynomial.eval (fun _ : Fin 1 => 1)
        ((MvPolynomial.finSuccEquiv ℂ 1 p).coeff i) = 0 := by
      have hc := congrArg (fun f : Polynomial ℂ => f.coeff i) hzero
      rw [dehomInf_eq] at hc
      simpa using hc
    simp [heval]
  · have hlt : (MvPolynomial.finSuccEquiv ℂ 1 p).natDegree < i := by
      have hdeg : (MvPolynomial.finSuccEquiv ℂ 1 p).natDegree ≤ n := by
        rw [MvPolynomial.natDegree_finSuccEquiv]
        exact (MvPolynomial.degreeOf_le_totalDegree p 0).trans hp.totalDegree_le
      exact lt_of_le_of_lt hdeg (lt_of_not_ge hi)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    simp

private lemma dehomInf_natDegree_le_of_homogeneous
    {p : MvPolynomial (Fin 2) ℂ} {n : ℕ} (hp : p.IsHomogeneous n) :
    (dehomInf p).natDegree ≤ n := by
  rw [dehomInf_eq]
  calc
    (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 => 1))
        (MvPolynomial.finSuccEquiv ℂ 1 p)).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1 p).natDegree := Polynomial.natDegree_map_le
    _ = p.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv p
    _ ≤ p.totalDegree := MvPolynomial.degreeOf_le_totalDegree p 0
    _ ≤ n := hp.totalDegree_le

private lemma homogeneous_eval_scale {p : MvPolynomial (Fin 2) ℂ} {n : ℕ}
    (hp : p.IsHomogeneous n) (a : ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval (fun i => a * v i) p =
      a ^ n * MvPolynomial.eval v p := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add]
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

private lemma supportAnnihilator_isHomogeneous (m : ℕ)
    (dirs : Fin (m + 2) → ℂ × ℂ) :
    (supportAnnihilator dirs).IsHomogeneous (m + 2) := by
  rw [supportAnnihilator]
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun j : Fin (m + 2) =>
      MvPolynomial.C (dirs j).2 * MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.C (dirs j).1 * MvPolynomial.X (1 : Fin 2))
    (fun _ => 1) ?_ using 1
  · simp
  · intro j hj
    apply (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 1).sub_mem
    · exact MvPolynomial.isHomogeneous_C_mul_X _ _
    · exact MvPolynomial.isHomogeneous_C_mul_X _ _

private lemma dehomInf_support (m : ℕ) (dirs : Fin (m + 2) → ℂ × ℂ) :
    dehomInf (supportAnnihilator dirs) =
      ∏ j : Fin (m + 2),
        (Polynomial.C (dirs j).2 * Polynomial.X - Polynomial.C (dirs j).1) := by
  simp [supportAnnihilator, dehomInf]

private lemma dehomInf_support_natDegree (m : ℕ)
    (dirs : Fin (m + 2) → ℂ × ℂ) (hb : ∀ j, (dirs j).2 ≠ 0) :
    (dehomInf (supportAnnihilator dirs)).natDegree = m + 2 := by
  rw [dehomInf_support]
  rw [Polynomial.natDegree_prod]
  · calc
      (∑ j : Fin (m + 2),
          (Polynomial.C (dirs j).2 * Polynomial.X -
            Polynomial.C (dirs j).1).natDegree) =
          ∑ _j : Fin (m + 2), 1 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
            · simp [Polynomial.natDegree_C_mul_X, hb j]
            · simp [Polynomial.natDegree_C_mul_X, hb j]
      _ = m + 2 := by simp
  · intro j hj hz
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) hz
    simpa [hb j] using hc

private lemma dehomInf_support_coeff_top_ne (m : ℕ)
    (dirs : Fin (m + 2) → ℂ × ℂ) (hb : ∀ j, (dirs j).2 ≠ 0) :
    (dehomInf (supportAnnihilator dirs)).coeff (m + 2) ≠ 0 := by
  rw [← dehomInf_support_natDegree m dirs hb, Polynomial.coeff_natDegree,
    dehomInf_support, Polynomial.leadingCoeff_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hfac : Polynomial.C (dirs j).2 * Polynomial.X - Polynomial.C (dirs j).1 ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) hz
    simpa [hb j] using hc
  exact Polynomial.leadingCoeff_ne_zero.mpr hfac

private lemma forward_castSucc_first (m : ℕ) (θ : ParamSpace ℂ m)
    (k : Fin (m + 1)) :
    (forwardLoading m θ.1 θ.2.1 (Fin.castSucc k)).1 = 1 := by
  by_cases hk : k = 0
  · simp [forwardLoading, hk]
  · have hlast : k.val ≠ m + 1 := by omega
    simp [forwardLoading, hk, hlast]

private lemma forward_ratio_injective (m : ℕ) (θ : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) =>
        (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2))
    (hb : ∀ j : Fin (m + 2), (forwardLoading m θ.1 θ.2.1 j).2 ≠ 0) :
    Function.Injective (fun j : Fin (m + 2) =>
      (forwardLoading m θ.1 θ.2.1 j).1 /
        (forwardLoading m θ.1 θ.2.1 j).2) := by
  intro i j hij
  by_cases hi : i.val = m + 1
  · have hilast : i = (⟨m + 1, by omega⟩ : Fin (m + 2)) := Fin.ext hi
    by_cases hj : j.val = m + 1
    · exact Fin.ext (hi.trans hj.symm)
    · let k : Fin (m + 1) := ⟨j.val, by omega⟩
      have hjcast : Fin.castSucc k = j := Fin.ext rfl
      have hfirst : (forwardLoading m θ.1 θ.2.1 j).1 = 1 := by
        rw [← hjcast]
        exact forward_castSucc_first m θ k
      have hratio_ne :
          (forwardLoading m θ.1 θ.2.1 j).1 /
            (forwardLoading m θ.1 θ.2.1 j).2 ≠ 0 :=
        div_ne_zero (hfirst.symm ▸ one_ne_zero) (hb j)
      have hiratio : (forwardLoading m θ.1 θ.2.1 i).1 /
          (forwardLoading m θ.1 θ.2.1 i).2 = 0 := by
        rw [hilast]
        simp [forwardLoading]
      change (forwardLoading m θ.1 θ.2.1 i).1 /
          (forwardLoading m θ.1 θ.2.1 i).2 =
        (forwardLoading m θ.1 θ.2.1 j).1 /
          (forwardLoading m θ.1 θ.2.1 j).2 at hij
      rw [hiratio] at hij
      exact (hratio_ne hij.symm).elim
  · by_cases hj : j.val = m + 1
    · let k : Fin (m + 1) := ⟨i.val, by omega⟩
      have hicast : Fin.castSucc k = i := Fin.ext rfl
      have hfirst : (forwardLoading m θ.1 θ.2.1 i).1 = 1 := by
        rw [← hicast]
        exact forward_castSucc_first m θ k
      have hratio_ne :
          (forwardLoading m θ.1 θ.2.1 i).1 /
            (forwardLoading m θ.1 θ.2.1 i).2 ≠ 0 :=
        div_ne_zero (hfirst.symm ▸ one_ne_zero) (hb i)
      have hjlast : j = (⟨m + 1, by omega⟩ : Fin (m + 2)) := Fin.ext hj
      have hjratio : (forwardLoading m θ.1 θ.2.1 j).1 /
          (forwardLoading m θ.1 θ.2.1 j).2 = 0 := by
        rw [hjlast]
        simp [forwardLoading]
      change (forwardLoading m θ.1 θ.2.1 i).1 /
          (forwardLoading m θ.1 θ.2.1 i).2 =
        (forwardLoading m θ.1 θ.2.1 j).1 /
          (forwardLoading m θ.1 θ.2.1 j).2 at hij
      rw [hjratio] at hij
      exact (hratio_ne hij).elim
    · let ki : Fin (m + 1) := ⟨i.val, by omega⟩
      let kj : Fin (m + 1) := ⟨j.val, by omega⟩
      have hicast : Fin.castSucc ki = i := Fin.ext rfl
      have hjcast : Fin.castSucc kj = j := Fin.ext rfl
      have hfi : (forwardLoading m θ.1 θ.2.1 i).1 = 1 := by
        rw [← hicast]
        exact forward_castSucc_first m θ ki
      have hfj : (forwardLoading m θ.1 θ.2.1 j).1 = 1 := by
        rw [← hjcast]
        exact forward_castSucc_first m θ kj
      change (forwardLoading m θ.1 θ.2.1 i).1 /
          (forwardLoading m θ.1 θ.2.1 i).2 =
        (forwardLoading m θ.1 θ.2.1 j).1 /
          (forwardLoading m θ.1 θ.2.1 j).2 at hij
      rw [hfi, hfj, one_div, one_div] at hij
      have hk : ki = kj := hslopes (inv_injective hij)
      apply Fin.ext
      simpa [ki, kj] using congrArg Fin.val hk

/-- The binary interpolation step: a degree-`m+2` homogeneous binary form
vanishing on the `m+1` finite forward directions and on the direction at
infinity is a multiple of their support annihilator.

The hypotheses say precisely that the affine slopes are distinct and nonzero.
The nonzero condition is used by the dehomogenization at `X₀ = 1` (the roots
there are the reciprocal slopes); the final direction `(0,1)` supplies the
remaining root at zero. -/
lemma forward_points_imply_supportAnnihilator_multiple (m : ℕ)
    (θ : ParamSpace ℂ m) (q : MvPolynomial (Fin 2) ℂ)
    (hq : q.IsHomogeneous (m + 2))
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) =>
        (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2))
    (hnonzero : ∀ j : Fin (m + 1),
      (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2 ≠ 0)
    (hzero : ∀ j, evalAtDir q (forwardLoading m θ.1 θ.2.1 j) = 0) :
    ∃ c : ℂ, q = c • supportAnnihilator (forwardLoading m θ.1 θ.2.1) := by
  let dirs : Fin (m + 2) → ℂ × ℂ := forwardLoading m θ.1 θ.2.1
  let Q := supportAnnihilator dirs
  have hb : ∀ j, (dirs j).2 ≠ 0 := by
    intro j
    by_cases hj : j.val = m + 1
    · have hjlast : j = (⟨m + 1, by omega⟩ : Fin (m + 2)) := Fin.ext hj
      simp [dirs, hjlast, forwardLoading]
    · let k : Fin (m + 1) := ⟨j.val, by omega⟩
      have hjcast : Fin.castSucc k = j := Fin.ext rfl
      rw [← hjcast]
      exact hnonzero k
  have hQhom : Q.IsHomogeneous (m + 2) := supportAnnihilator_isHomogeneous m dirs
  have hQtop : (dehomInf Q).coeff (m + 2) ≠ 0 :=
    dehomInf_support_coeff_top_ne m dirs hb
  let c : ℂ := (dehomInf q).coeff (m + 2) / (dehomInf Q).coeff (m + 2)
  let r : MvPolynomial (Fin 2) ℂ := q - MvPolynomial.C c * Q
  have hrhom : r.IsHomogeneous (m + 2) := by
    apply (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (m + 2)).sub_mem hq
    exact hQhom.C_mul c
  have hrtop : (dehomInf r).coeff (m + 2) = 0 := by
    dsimp [r, c]
    rw [map_sub, map_mul]
    rw [show dehomInf (MvPolynomial.C
        ((dehomInf q).coeff (m + 2) / (dehomInf Q).coeff (m + 2))) =
        Polynomial.C ((dehomInf q).coeff (m + 2) /
          (dehomInf Q).coeff (m + 2)) by simp [dehomInf]]
    change (dehomInf q - Polynomial.C
      ((dehomInf q).coeff (m + 2) / (dehomInf Q).coeff (m + 2)) *
        dehomInf Q).coeff (m + 2) = 0
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rw [div_mul_cancel₀ _ hQtop, sub_self]
  have hratio : Function.Injective (fun j : Fin (m + 2) =>
      (dirs j).1 / (dirs j).2) := by
    exact forward_ratio_injective m θ hslopes hb
  have hrroot : ∀ j : Fin (m + 2),
      Polynomial.IsRoot (dehomInf r) ((dirs j).1 / (dirs j).2) := by
    intro j
    have hQzero : evalAtDir Q (dirs j) = 0 := by
      exact evalAtDir_supportAnnihilator_eq_zero dirs j
    have hqzero : evalAtDir q (dirs j) = 0 := by
      simpa [dirs] using hzero j
    have hrorig : evalAtDir r (dirs j) = 0 := by
      change evalAtDir (q - MvPolynomial.C c * Q) (dirs j) = 0
      simp only [evalAtDir, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
        MvPolynomial.eval_C] at hqzero hQzero ⊢
      rw [hqzero, hQzero]
      ring
    have hs := homogeneous_eval_scale hrhom (dirs j).2
      (fun i : Fin 2 => if i = 0 then (dirs j).1 / (dirs j).2 else 1)
    have hleft :
        MvPolynomial.eval
          (fun i : Fin 2 => (dirs j).2 *
            (if i = 0 then (dirs j).1 / (dirs j).2 else 1)) r =
          evalAtDir r (dirs j) := by
      unfold evalAtDir
      apply congrArg (fun f : Fin 2 → ℂ => MvPolynomial.eval f r)
      funext i
      fin_cases i
      · change (dirs j).2 * ((dirs j).1 / (dirs j).2) = (dirs j).1
        rw [mul_comm, div_mul_cancel₀ _ (hb j)]
      · change (dirs j).2 * 1 = (dirs j).2
        simp
    rw [hleft, hrorig] at hs
    change (dehomInf r).eval ((dirs j).1 / (dirs j).2) = 0
    rw [dehomInf_eval]
    apply (mul_eq_zero.mp hs.symm).resolve_left
    exact pow_ne_zero _ (hb j)
  have hrdehom : dehomInf r = 0 := by
    by_contra hne
    have hdeg_le : (dehomInf r).natDegree ≤ m + 2 :=
      dehomInf_natDegree_le_of_homogeneous hrhom
    have hdeg_ne : (dehomInf r).natDegree ≠ m + 2 := by
      intro heq
      have hlc : (dehomInf r).leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr hne
      apply hlc
      rw [← Polynomial.coeff_natDegree, heq, hrtop]
    have hdeg_lt : (dehomInf r).natDegree < m + 2 := by omega
    have hsub : Finset.image (fun j : Fin (m + 2) =>
        (dirs j).1 / (dirs j).2) Finset.univ ⊆ (dehomInf r).roots.toFinset := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨j, hj, rfl⟩ := hz
      simp only [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hrroot j
    have hmany : m + 2 ≤ (dehomInf r).natDegree := by
      calc
        m + 2 = (Finset.image (fun j : Fin (m + 2) =>
            (dirs j).1 / (dirs j).2) Finset.univ).card := by
              rw [Finset.card_image_iff.mpr hratio.injOn]
              simp
        _ ≤ (dehomInf r).roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ (dehomInf r).roots.card := Multiset.toFinset_card_le _
        _ ≤ (dehomInf r).natDegree := Polynomial.card_roots' _
    omega
  have hrzero : r = 0 := dehomInf_injective_on_homogeneous hrhom hrdehom
  refine ⟨c, ?_⟩
  have heq : q = MvPolynomial.C c * Q := sub_eq_zero.mp hrzero
  simpa [Q, dirs, MvPolynomial.smul_eq_C_mul] using heq

/-- **Forward apolar kernel identity.**  This is the actual common-kernel
statement used by the flagship: among homogeneous degree-`m+2` binary forms,
the simultaneous contractions with orders `m+2,…,2m+2` have exactly the
support-annihilator line as their kernel.

`hrank` is the real-polynomial form of the block-Vandermonde rank-open
condition.  The remaining charted bridge identifies it with injectivity of
`stackedContraction` after nonzero binomial/leading-coordinate rescaling. -/
theorem forward_apolar_kernel_identity (m : ℕ) (θ : ParamSpace ℂ m)
    (hslopes : Function.Injective
      (fun j : Fin (m + 1) =>
        (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2))
    (hnonzero : ∀ j : Fin (m + 1),
      (forwardLoading m θ.1 θ.2.1 (Fin.castSucc j)).2 ≠ 0)
    (hrank : Function.Injective (forwardWeightedContraction m θ)) :
    ∀ q : MvPolynomial (Fin 2) ℂ, q.IsHomogeneous (m + 2) →
      ((∀ k, k ≤ m → diffApply q
          (dividedPowerBlock (forwardCumulantMap m (2 * m + 2) θ) (m + 2 + k)) = 0)
        ↔ ∃ c : ℂ, q = c • supportAnnihilator (forwardLoading m θ.1 θ.2.1)) := by
  intro q hq
  constructor
  · intro hcon
    apply forward_points_imply_supportAnnihilator_multiple m θ q hq hslopes hnonzero
    exact evalAtDir_zero_of_forward_contractions m θ q hq hrank hcon
  · exact forward_supportAnnihilator_in_contraction_kernel m θ q hq

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
