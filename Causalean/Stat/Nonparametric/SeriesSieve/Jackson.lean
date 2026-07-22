/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.Approximation.HolderTaylor

/-!
# Jackson-type approximation for the piecewise-polynomial sieve

Jackson-type approximation bounds for piecewise-polynomial sieves on one-dimensional Hölder
classes.

This file proves a **from-scratch Jackson theorem** for a concrete one-dimensional sieve:
the *piecewise-Taylor* approximant on a uniform `J`-cell partition of a window `[lo, hi]`.
Splitting `[lo, hi]` into `J` cells of width `δ = (hi − lo)/J` and replacing `f` on each cell
by its degree-`p` Taylor polynomial, where `p = holderDerivOrder β`, expanded at
the cell's left endpoint yields a
piecewise polynomial whose uniform (sup-norm) approximation error obeys

`sup_{x ∈ [lo,hi]} |f x − g x| ≤ (M / p!) · ((hi − lo)/J)^β = C · J^{−β}`

under the standard Hölder convention used here: `f` has `p` continuous
derivatives and its `p`-th derivative satisfies the displayed Hölder-type bound
with exponent `β − p`. For positive integer `β = m`, this means `p = m - 1`
and exponent `1`.

The result is the deterministic *approximation-error* half of the series least-squares prediction
analysis. It feeds the empirical projection reduction in `SeriesSieve/Prediction.lean`, where a
sup-norm approximation bound can control a weighted empirical least-squares objective via
projection optimality (`lstsq_objective_le_of_orthogonal`).
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators

/-- The width `δ = (hi − lo)/J` of a uniform `J`-cell partition of `[lo, hi]`. -/
noncomputable def cellWidth (lo hi : ℝ) (J : ℕ) : ℝ := (hi - lo) / (J : ℝ)

/-- The cell index of `x` in a uniform `J`-cell partition of `[lo, hi]`: the floor
`⌊(x − lo)/δ⌋`, clamped to the last cell `J − 1` (so the right endpoint `hi` lands in the
final cell). -/
noncomputable def cellIdx (lo hi : ℝ) (J : ℕ) (x : ℝ) : ℕ :=
  min (J - 1) ⌊(x - lo) / cellWidth lo hi J⌋₊

/-- The left endpoint `lo + (cellIdx x)·δ` of the cell containing `x`. The piecewise-Taylor
approximant expands `f` around this base point. -/
noncomputable def cellBase (lo hi : ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  lo + (cellIdx lo hi J x : ℝ) * cellWidth lo hi J

/-- The **piecewise-Taylor sieve approximant**: on the cell containing `x`, the value of the
degree-`p` Taylor polynomial of `f` expanded at the cell's left endpoint. This is a piecewise
polynomial of degree `≤ p` on the uniform `J`-cell partition of `[lo, hi]`. -/
noncomputable def piecewiseTaylorApprox (p : ℕ) (f : ℝ → ℝ) (lo hi : ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  taylorPoly p f (cellBase lo hi J x) x

/-- The cell width is positive on a nondegenerate window. -/
lemma cellWidth_pos {lo hi : ℝ} {J : ℕ} (hlohi : lo < hi) (hJ : 0 < J) :
    0 < cellWidth lo hi J := by
  unfold cellWidth
  have h1 : 0 < hi - lo := by linarith
  have h2 : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  exact div_pos h1 h2

/-- The cell base point lies inside the window `[lo, hi]`. -/
lemma cellBase_mem {lo hi : ℝ} {J : ℕ} (hlohi : lo < hi) (hJ : 0 < J)
    {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    cellBase lo hi J x ∈ Set.Icc lo hi := by
  let δ := cellWidth lo hi J
  have hδ : 0 < δ := cellWidth_pos hlohi hJ
  constructor
  · unfold cellBase
    have hnonneg : 0 ≤ (cellIdx lo hi J x : ℝ) * δ :=
      mul_nonneg (Nat.cast_nonneg _) hδ.le
    dsimp [δ] at hnonneg ⊢
    linarith [hx.1]
  · unfold cellBase
    change lo + (cellIdx lo hi J x : ℝ) * δ ≤ hi
    have hJone : 1 ≤ J := Nat.succ_le_of_lt hJ
    have hidx_nat : cellIdx lo hi J x ≤ J - 1 := by
      unfold cellIdx
      exact min_le_left _ _
    have hidx_cast : (cellIdx lo hi J x : ℝ) ≤ (J : ℝ) - 1 := by
      have hcast : (cellIdx lo hi J x : ℝ) ≤ (J - 1 : ℕ) := by
        exact_mod_cast hidx_nat
      have hsub : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
        rw [Nat.cast_sub hJone, Nat.cast_one]
      linarith
    have hmul : (cellIdx lo hi J x : ℝ) * δ ≤ ((J : ℝ) - 1) * δ :=
      mul_le_mul_of_nonneg_right hidx_cast hδ.le
    have hJnz : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
    have hJδ : (J : ℝ) * δ = hi - lo := by
      dsimp [δ]
      unfold cellWidth
      field_simp [hJnz]
    nlinarith [hmul, hδ]

/-- `x` is within one cell width to the right of its base point: `0 ≤ x − base ≤ δ`. -/
lemma cellBase_dist {lo hi : ℝ} {J : ℕ} (hlohi : lo < hi) (hJ : 0 < J)
    {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    0 ≤ x - cellBase lo hi J x ∧ x - cellBase lo hi J x ≤ cellWidth lo hi J := by
  let δ := cellWidth lo hi J
  have hδ : 0 < δ := cellWidth_pos hlohi hJ
  let q := (x - lo) / δ
  let m : ℕ := ⌊q⌋₊
  let i : ℕ := min (J - 1) m
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by linarith [hx.1]) hδ.le
  have hJnz : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  have hJδ : (J : ℝ) * δ = hi - lo := by
    dsimp [δ]
    unfold cellWidth
    field_simp [hJnz]
  have hqJ : q ≤ (J : ℝ) := by
    have hxq' : q * δ = x - lo := by
      dsimp [q]
      field_simp [hδ.ne']
    have hmul : q * δ ≤ (J : ℝ) * δ := by
      linarith [hx.2, hJδ, hxq']
    exact le_of_mul_le_mul_right hmul hδ
  have hmq : (m : ℝ) ≤ q := by
    exact Nat.floor_le hq0
  have hqm : q < (m : ℝ) + 1 := by
    exact Nat.lt_floor_add_one q
  have him : (i : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (min_le_right (J - 1) m)
  have hcellidx : cellIdx lo hi J x = i := by
    unfold cellIdx
    dsimp [δ, q, m, i]
  have hxq : δ * q = x - lo := by
    dsimp [q]
    field_simp [hδ.ne']
  have hrepr : x - cellBase lo hi J x = δ * (q - (i : ℝ)) := by
    unfold cellBase
    rw [hcellidx]
    nlinarith [hxq]
  constructor
  · rw [hrepr]
    exact mul_nonneg hδ.le (by linarith [him, hmq])
  · rw [hrepr]
    have hqi : q ≤ (i : ℝ) + 1 := by
      by_cases hmle : m ≤ J - 1
      · have hi_eq_m : i = m := by
          dsimp [i]
          exact min_eq_right hmle
        rw [hi_eq_m]
        linarith [hqm]
      · have hlt : J - 1 < m := Nat.lt_of_not_ge hmle
        have hle : J - 1 ≤ m := le_of_lt hlt
        have hi_eq_j : i = J - 1 := by
          dsimp [i]
          exact min_eq_left hle
        rw [hi_eq_j]
        have hJone : 1 ≤ J := Nat.succ_le_of_lt hJ
        have hcast : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
          rw [Nat.cast_sub hJone, Nat.cast_one]
          linarith
        rw [hcast]
        exact hqJ
    have hle1 : q - (i : ℝ) ≤ 1 := by linarith
    calc
      δ * (q - (i : ℝ)) ≤ δ * 1 := mul_le_mul_of_nonneg_left hle1 hδ.le
      _ = cellWidth lo hi J := by simp [δ]

/-- **Piecewise-Taylor approximation bound under the standard Hölder convention.**
If `f` has `p = holderDerivOrder β` continuous derivatives and its `p`-th
derivative obeys a Hölder bound with exponent `β - p` on the window, then the
corresponding piecewise-Taylor approximant on a uniform `J`-cell partition has
pointwise error at most `(M / p!)·((hi − lo)/J)^β`. For positive integer
`β = m`, this uses derivative order `m - 1` and Hölder exponent `1`. -/
theorem piecewiseTaylor_sup_approx {f : ℝ → ℝ} {M β lo hi : ℝ} {J : ℕ}
    (hβ : 0 < β) (hM : 0 ≤ M) (hlohi : lo < hi) (hJ : 0 < J)
    (hf : ContDiff ℝ ((holderDerivOrder β)) f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ)))
    {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    |f x - piecewiseTaylorApprox (holderDerivOrder β) f lo hi J x|
      ≤ M / ((holderDerivOrder β)).factorial * ((hi - lo) / (J : ℝ)) ^ β := by
  have hbase_mem := cellBase_mem hlohi hJ hx
  have hdist := cellBase_dist hlohi hJ hx
  have hwpos := cellWidth_pos hlohi hJ
  -- Hölder–Taylor remainder at base point `cellBase`.
  have hrem := holder_taylor_remainder (f := f) (M := M) (β := β) (lo := lo) (hi := hi)
    (t := cellBase lo hi J x) (a := x) hβ hM hbase_mem hx hf hb
  refine hrem.trans ?_
  -- `|x − base|^β ≤ δ^β` since `0 ≤ x − base ≤ δ`.
  have habs : |x - cellBase lo hi J x| = x - cellBase lo hi J x := abs_of_nonneg hdist.1
  have hpow : |x - cellBase lo hi J x| ^ β ≤ (cellWidth lo hi J) ^ β := by
    rw [habs]
    exact Real.rpow_le_rpow hdist.1 hdist.2 hβ.le
  have hcoef : 0 ≤ M / (((holderDerivOrder β)).factorial : ℝ) :=
    div_nonneg hM (by positivity)
  calc
    M / (((holderDerivOrder β)).factorial : ℝ) * |x - cellBase lo hi J x| ^ β
        ≤ M / (((holderDerivOrder β)).factorial : ℝ) * (cellWidth lo hi J) ^ β :=
          mul_le_mul_of_nonneg_left hpow hcoef
    _ = M / (((holderDerivOrder β)).factorial : ℝ) * ((hi - lo) / (J : ℝ)) ^ β := by
          rw [cellWidth]

/-- **Jackson rate, `J^{−β}` form.** The same bound rewritten with the explicit rate factor:
`|f x − g x| ≤ C · J^{−β}` with constant
`C = (M / (holderDerivOrder β)!)·(hi − lo)^β` independent of `J`. -/
theorem piecewiseTaylor_sup_approx_rate {f : ℝ → ℝ} {M β lo hi : ℝ} {J : ℕ}
    (hβ : 0 < β) (hM : 0 ≤ M) (hlohi : lo < hi) (hJ : 0 < J)
    (hf : ContDiff ℝ ((holderDerivOrder β)) f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ)))
    {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    |f x - piecewiseTaylorApprox (holderDerivOrder β) f lo hi J x|
      ≤ (M / ((holderDerivOrder β)).factorial * (hi - lo) ^ β) * (J : ℝ) ^ (-β) := by
  have h := piecewiseTaylor_sup_approx hβ hM hlohi hJ hf hb hx
  refine h.trans_eq ?_
  have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hlo : (0 : ℝ) ≤ hi - lo := by linarith
  rw [Real.div_rpow hlo hJpos.le, Real.rpow_neg hJpos.le]
  ring

end Causalean.Stat.Nonparametric
