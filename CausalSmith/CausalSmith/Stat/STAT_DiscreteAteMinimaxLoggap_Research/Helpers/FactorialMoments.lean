import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Estimator
import Causalean.Stat.UStatistic.OrderM.Basic
import Mathlib.RingTheory.Binomial

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

open Finset Polynomial

/-- Linearization of the product of two falling-factorial basis polynomials.
This is the polynomial form of classifying two ordered selections by the size
of their overlap. -/
private lemma descPochhammer_mul_linearization (a b : ℕ) :
    descPochhammer ℤ a * descPochhammer ℤ b =
      ∑ h ∈ range (min a b + 1),
        C (Nat.choose a h * Nat.choose b h * h.factorial : ℤ) *
          descPochhammer ℤ (a + b - h) := by
  classical
  wlog hab : a ≤ b generalizing a b
  · rw [mul_comm]
    simpa [Nat.min_comm, mul_comm, Nat.add_comm] using this b a (le_of_not_ge hab)
  rw [Nat.min_eq_left hab]
  have hadd := Ring.descPochhammer_smeval_add (R := ℤ[X]) b
    (Commute.all (X - C (a : ℤ)) (C (a : ℤ)))
  simp only [sub_add_cancel] at hadd
  have hsX (p : ℤ[X]) : p.smeval X = p := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    simpa using Polynomial.eval₂_C_X p
  have hscomp (p : ℤ[X]) : p.smeval (X - C (a : ℤ)) =
      p.comp (X - C (a : ℤ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    have hhom : (RingHom.smulOneHom : ℤ →+* ℤ[X]) = C := by
      ext z
      simp
    rw [hhom]
    rfl
  have hsC (p : ℤ[X]) : p.smeval (C (a : ℤ)) = C (p.eval (a : ℤ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    simpa using Polynomial.eval₂_at_apply C (a : ℤ) (p := p)
  simp only [hsX, hscomp, hsC] at hadd
  rw [← Finset.Nat.sum_antidiagonal_swap] at hadd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hadd
  simp only [Prod.swap, Prod.fst, Prod.snd, Nat.succ_eq_add_one] at hadd
  have heval (h : ℕ) : (descPochhammer ℤ h).eval (a : ℤ) =
      (a.descFactorial h : ℤ) := by
    simpa [Polynomial.eval_eq_smeval] using
      (Polynomial.descPochhammer_smeval_eq_descFactorial (R := ℤ) a h)
  have hbform : descPochhammer ℤ b =
      ∑ h ∈ range (b + 1),
        C ((b.choose h : ℤ) * (a.descFactorial h : ℤ)) *
          (descPochhammer ℤ (b - h)).comp (X - C (a : ℤ)) := by
    rw [hadd]
    apply Finset.sum_congr rfl
    intro h hh
    rw [heval]
    have hh' : h ≤ b := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hh)
    rw [Nat.choose_symm hh']
    simp
    ring
  calc
    descPochhammer ℤ a * descPochhammer ℤ b =
        descPochhammer ℤ a *
          (∑ h ∈ range (b + 1),
            C ((b.choose h : ℤ) * (a.descFactorial h : ℤ)) *
              (descPochhammer ℤ (b - h)).comp (X - C (a : ℤ))) := by rw [hbform]
    _ = ∑ h ∈ range (b + 1),
          C ((b.choose h : ℤ) * (a.descFactorial h : ℤ)) *
            descPochhammer ℤ (a + (b - h)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      calc
        descPochhammer ℤ a *
            (C ((b.choose h : ℤ) * (a.descFactorial h : ℤ)) *
              (descPochhammer ℤ (b - h)).comp (X - C (a : ℤ))) =
            C ((b.choose h : ℤ) * (a.descFactorial h : ℤ)) *
              (descPochhammer ℤ a *
                (descPochhammer ℤ (b - h)).comp (X - C (a : ℤ))) := by ring
        _ = _ := by
          rw [show C (a : ℤ) = (a : ℤ[X]) by simp]
          rw [descPochhammer_mul]
    _ = ∑ h ∈ range (a + 1),
          C ((b.choose h : ℤ) * (a.descFactorial h : ℤ)) *
            descPochhammer ℤ (a + (b - h)) := by
      symm
      apply Finset.sum_subset
      · intro h hh
        exact Finset.mem_range.mpr ((Finset.mem_range.mp hh).trans_le (Nat.succ_le_succ hab))
      · intro h hhBig hhSmall
        have ha_lt : a < h := by
          have := Finset.mem_range.mp hhBig
          simpa [Finset.mem_range] using hhSmall
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr ha_lt]
        simp
    _ = ∑ h ∈ range (a + 1),
          C (Nat.choose a h * Nat.choose b h * h.factorial : ℤ) *
            descPochhammer ℤ (a + b - h) := by
      apply Finset.sum_congr rfl
      intro h hh
      have hh' : h ≤ a := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hh)
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      congr 1
      · push_cast
        ring
      · rw [Nat.add_sub_assoc (le_trans hh' hab) a]

/-- Falling-factorial product identity used for within-cell moments. -/
lemma descFactorial_mul_identity (z a b : ℕ) :
    (z.descFactorial a) * (z.descFactorial b) =
      ∑ h ∈ Finset.range (min a b + 1),
        Nat.choose a h * Nat.choose b h * h.factorial *
          z.descFactorial (a + b - h) := by
  have hp := congrArg (Polynomial.eval (z : ℤ))
    (descPochhammer_mul_linearization a b)
  simp only [Polynomial.eval_mul, Polynomial.eval_finset_sum, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial] at hp
  exact_mod_cast hp

/-- The ordered injective tuple count is the normalizing falling factorial. -/
-- @node: factorial_normalization
lemma factorial_normalization (m r : ℕ) :
    Causalean.Stat.injectiveTupleCount r m = m.descFactorial r := by
  exact Causalean.Stat.injectiveTupleCount_eq_descFactorial r m

/-- Ratio estimate for two normalized ordered selections. -/
lemma factorial_ratio_bound {m r s H : ℕ} (hdeg : r ≤ s) (hM : 4 * s ^ 2 ≤ m)
    (hH : H ≤ s) :
    (m.descFactorial (r + s - H) : ℝ) /
        ((m.descFactorial r : ℝ) * m.descFactorial s) ≤
      Real.exp 1 / m ^ H := by
  by_cases hs0 : s = 0
  · subst s
    have hr0 : r = 0 := by omega
    have hH0 : H = 0 := by omega
    subst r
    subst H
    norm_num
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity : 0 < 4 * s ^ 2) hM
  have hsm : s ≤ m := by nlinarith [sq_nonneg (s : ℝ)]
  have hsubpos : 0 < m - s := by
    have : s < m := by nlinarith
    omega
  let u : ℕ := m - s
  have hu_pos : 0 < u := by simpa [u] using hsubpos
  have hnumNat : m.descFactorial (r + s - H) ≤ m ^ (r + s - H) :=
    Nat.descFactorial_le_pow m _
  have hlowS : u ^ s ≤ m.descFactorial s := by
    calc
      u ^ s ≤ (m + 1 - s) ^ s := Nat.pow_le_pow_left (by simp [u]; omega) s
      _ ≤ m.descFactorial s := Nat.pow_sub_le_descFactorial m s
  have hur : u ≤ m + 1 - r := by
    simp only [u]
    omega
  have hlowR : u ^ r ≤ m.descFactorial r := by
    calc
      u ^ r ≤ (m + 1 - r) ^ r := Nat.pow_le_pow_left hur r
      _ ≤ m.descFactorial r := Nat.pow_sub_le_descFactorial m r
  have hdenNat : u ^ (r + s) ≤ m.descFactorial r * m.descFactorial s := by
    rw [pow_add]
    exact Nat.mul_le_mul hlowR hlowS
  have hN : r + s ≤ 2 * s := by omega
  have hratio_exp : ((m : ℝ) / u) ^ (r + s) ≤ Real.exp 1 := by
    have huR : (0 : ℝ) < u := by exact_mod_cast hu_pos
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hratio_pos : (0 : ℝ) < (m : ℝ) / u := div_pos hmR huR
    have hratio_eq : (m : ℝ) / u = 1 + (s : ℝ) / u := by
      have hmu : m = u + s := by simp [u, Nat.sub_add_cancel hsm]
      rw [hmu, Nat.cast_add, add_div]
      simp [huR.ne']
    have hlog : Real.log ((m : ℝ) / u) ≤ (s : ℝ) / u := by
      calc
        Real.log ((m : ℝ) / u) ≤ (m : ℝ) / u - 1 :=
          Real.log_le_sub_one_of_pos hratio_pos
        _ = (s : ℝ) / u := by rw [hratio_eq]; ring
    have hfrac : ((r + s : ℕ) : ℝ) * ((s : ℝ) / u) ≤ 1 := by
      have huLowerNat : 2 * s ^ 2 ≤ u := by
        have hs_sq : s ≤ 2 * s ^ 2 := by
          calc
            s = s * 1 := by omega
            _ ≤ s * s := Nat.mul_le_mul_left s (Nat.succ_le_iff.mpr hspos)
            _ ≤ 2 * s ^ 2 := by nlinarith
        dsimp [u]
        omega
      have hNR : ((r + s : ℕ) : ℝ) ≤ 2 * s := by exact_mod_cast hN
      have hsR : (0 : ℝ) ≤ s := by positivity
      have huR' : (0 : ℝ) < u := by exact_mod_cast hu_pos
      calc
        ((r + s : ℕ) : ℝ) * ((s : ℝ) / u) =
            (((r + s : ℕ) : ℝ) * s) / u := by ring
        _ ≤ 1 := (div_le_one huR').2 (by
          calc
            ((r + s : ℕ) : ℝ) * s ≤ (2 * s : ℝ) * s :=
              mul_le_mul_of_nonneg_right hNR hsR
            _ ≤ u := by
              norm_cast
              convert huLowerNat using 1 <;> simp [pow_two, mul_assoc])
    have hlogN : ((r + s : ℕ) : ℝ) * Real.log ((m : ℝ) / u) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hfrac
    calc
      ((m : ℝ) / u) ^ (r + s) =
          Real.exp (((r + s : ℕ) : ℝ) * Real.log ((m : ℝ) / u)) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hratio_pos _)]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hlogN
  have hpow_ratio : (m : ℝ) ^ (r + s) / (u : ℝ) ^ (r + s) ≤ Real.exp 1 := by
    simpa [div_pow] using hratio_exp
  have hdenpos : (0 : ℝ) < (m.descFactorial r : ℝ) * m.descFactorial s := by
    have hrm : r ≤ m := hdeg.trans hsm
    have hrp : (0 : ℝ) < m.descFactorial r := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hrm)
    have hsp : (0 : ℝ) < m.descFactorial s := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hsm)
    exact mul_pos hrp hsp
  have huPowPos : (0 : ℝ) < (u : ℝ) ^ (r + s) := by positivity
  have hmPowPos : (0 : ℝ) < (m : ℝ) ^ H := by positivity
  have hnum : (m.descFactorial (r + s - H) : ℝ) ≤
      (m : ℝ) ^ (r + s - H) := by exact_mod_cast hnumNat
  have hden : (u : ℝ) ^ (r + s) ≤
      (m.descFactorial r : ℝ) * m.descFactorial s := by exact_mod_cast hdenNat
  calc
    (m.descFactorial (r + s - H) : ℝ) /
        ((m.descFactorial r : ℝ) * m.descFactorial s) ≤
        (m : ℝ) ^ (r + s - H) / (u : ℝ) ^ (r + s) := by
      calc
        (m.descFactorial (r + s - H) : ℝ) /
            ((m.descFactorial r : ℝ) * m.descFactorial s) ≤
            (m : ℝ) ^ (r + s - H) /
              ((m.descFactorial r : ℝ) * m.descFactorial s) :=
          div_le_div_of_nonneg_right hnum hdenpos.le
        _ ≤ (m : ℝ) ^ (r + s - H) / (u : ℝ) ^ (r + s) :=
          div_le_div_of_nonneg_left (by positivity) huPowPos hden
    _ = ((m : ℝ) ^ (r + s) / (u : ℝ) ^ (r + s)) / (m : ℝ) ^ H := by
      have hHsum : H ≤ r + s := hH.trans (Nat.le_add_left s r)
      rw [← pow_sub_mul_pow (m : ℝ) hHsum]
      field_simp
    _ ≤ Real.exp 1 / (m : ℝ) ^ H :=
      div_le_div_of_nonneg_right hpow_ratio hmPowPos.le

/-- Sharp disjoint-selection normalization.  This is the covariance factor for
two monomials attached to distinct multinomial categories: the two ordered
selections cannot share observations, so their joint moment differs from the
product of their means only through this falling-factorial ratio. -/
lemma factorial_cross_ratio_bound {m r s : ℕ} (hdeg : r ≤ s)
    (hM : 4 * s ^ 2 ≤ m) :
    |(m.descFactorial (r + s) : ℝ) /
        ((m.descFactorial r : ℝ) * m.descFactorial s) - 1| ≤
      2 * (s : ℝ) ^ 2 / m := by
  by_cases hs0 : s = 0
  · subst s
    have hr0 : r = 0 := by omega
    subst r
    norm_num
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity : 0 < 4 * s ^ 2) hM
  have hsm : s ≤ m := by nlinarith [sq_nonneg (s : ℝ)]
  have h2sm : 2 * s ≤ m := by
    have hs_sq' : s ≤ s ^ 2 := by
      calc
        s = s * 1 := by omega
        _ ≤ s * s := Nat.mul_le_mul_left s (Nat.succ_le_iff.mpr hspos)
        _ = s ^ 2 := by ring
    omega
  have hrm : r ≤ m := hdeg.trans hsm
  have hfac : (m - r).descFactorial s * m.descFactorial r =
      m.descFactorial (r + s) := by
    simpa using Nat.descFactorial_mul_descFactorial (n := m)
      (k := r) (m := r + s) (Nat.le_add_right r s)
  have hfrpos : (0 : ℝ) < m.descFactorial r := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hrm)
  have hfspos : (0 : ℝ) < m.descFactorial s := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hsm)
  have hratio_eq : (m.descFactorial (r + s) : ℝ) /
        ((m.descFactorial r : ℝ) * m.descFactorial s) =
      (m - r).descFactorial s / (m.descFactorial s : ℝ) := by
    rw [← hfac]
    push_cast
    field_simp
  have hratio_le_one : (m.descFactorial (r + s) : ℝ) /
        ((m.descFactorial r : ℝ) * m.descFactorial s) ≤ 1 := by
    rw [hratio_eq]
    apply (div_le_one hfspos).2
    exact_mod_cast Nat.descFactorial_le s (Nat.sub_le m r)
  have hbaseNat : m - 2 * s ≤ m - r + 1 - s := by omega
  have hlowNumNat : (m - 2 * s) ^ s ≤ (m - r).descFactorial s := by
    calc
      (m - 2 * s) ^ s ≤ (m - r + 1 - s) ^ s := Nat.pow_le_pow_left hbaseNat s
      _ ≤ (m - r).descFactorial s := Nat.pow_sub_le_descFactorial (m - r) s
  have hdenUpperNat : m.descFactorial s ≤ m ^ s := Nat.descFactorial_le_pow m s
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hratio_lower : ((m : ℝ) - 2 * s) ^ s / (m : ℝ) ^ s ≤
      (m.descFactorial (r + s) : ℝ) /
        ((m.descFactorial r : ℝ) * m.descFactorial s) := by
    rw [hratio_eq]
    have hnumR : ((m : ℝ) - 2 * s) ^ s ≤ ((m - r).descFactorial s : ℝ) := by
      have hcast : ((m - 2 * s : ℕ) : ℝ) = (m : ℝ) - 2 * s := by
        rw [Nat.cast_sub h2sm]
        push_cast
        ring
      rw [← hcast]
      exact_mod_cast hlowNumNat
    have hdenR : (m.descFactorial s : ℝ) ≤ (m : ℝ) ^ s := by
      exact_mod_cast hdenUpperNat
    calc
      ((m : ℝ) - 2 * s) ^ s / (m : ℝ) ^ s ≤
          ((m - r).descFactorial s : ℝ) / (m : ℝ) ^ s :=
        div_le_div_of_nonneg_right hnumR (by positivity)
      _ ≤ ((m - r).descFactorial s : ℝ) / m.descFactorial s :=
        div_le_div_of_nonneg_left (by positivity) hfspos hdenR
  have hbern : 1 - 2 * (s : ℝ) ^ 2 / m ≤
      ((m : ℝ) - 2 * s) ^ s / (m : ℝ) ^ s := by
    have hx : (-1 : ℝ) ≤ -2 * (s : ℝ) / m := by
      apply (le_div_iff₀ hmR).2
      have h2smR : (2 : ℝ) * s ≤ m := by exact_mod_cast h2sm
      nlinarith
    have hb := one_add_mul_le_pow ((by norm_num : (-2 : ℝ) ≤ -1).trans hx) s
    have heq : (1 + (-2 * (s : ℝ) / m)) ^ s =
        ((m : ℝ) - 2 * s) ^ s / (m : ℝ) ^ s := by
      rw [← div_pow]
      congr 1
      field_simp
      ring
    rw [← heq]
    convert hb using 1 <;> ring
  rw [abs_of_nonpos (sub_nonpos.mpr hratio_le_one)]
  linarith [hbern.trans hratio_lower]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
