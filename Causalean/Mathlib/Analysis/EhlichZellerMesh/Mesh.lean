/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.EhlichZellerMesh.Bernstein

/-!
# The Ehlich–Zeller Chebyshev–Lobatto mesh (norming) inequality

A real polynomial of degree `≤ β` is uniformly controlled on `[-1, 1]` by its
values on the `k+1` Chebyshev–Lobatto nodes `x_j = -cos(π j / k)` (`j = 0..k`)
as soon as the mesh is oversampled (`β < k`), with a norming constant of the form
`sec(π β / (2k))` depending only on the oversampling ratio.

Main declarations:

* `czNode k j` — the `j`-th Chebyshev–Lobatto node `-cos(π j / k)` (for positive
  `k`, the endpoints are `x_0 = -1` and `x_k = 1`).
* `ehlichZeller_mesh_bound` — the mesh inequality
  `sup_{x∈[-1,1]} |R x| ≤ sec(π β / (2k)) · max_{0≤j≤k} |R(x_j)|` for
  `R.natDegree ≤ β` and `β < k`.
* `oversampled_norming` — the oversampling-ratio corollary: for `c > 1`, `β ≥ 1`
  and `k ≥ c·β`, the constant `K(c) = sec(π / (2c))` works uniformly in `β`.

Everything is stated for a *general* real polynomial `R` and *general* `(β, k)`,
so the module is reusable (Mathlib-shaped) and not gerrymandered to any
downstream object.  The analytic heart (Bernstein/Szegő) lives in
`Causalean.Mathlib.Analysis.EhlichZellerMesh.Bernstein`.

## Standard reference
Ehlich, H. & Zeller, K. (1964), *Schwankung von Polynomen zwischen
Gitterpunkten*, Math. Z. 86, 41–44.
-/

open Real Polynomial

namespace Causalean.Mathlib.Analysis.EhlichZellerMesh

/-- The `j`-th Chebyshev–Lobatto (extrema) node on `[-1, 1]` for a mesh of order
`k`: `czNode k j = -cos(π j / k)`.  When `0 < k`, the indices `j = 0..k` give
`k+1` points with endpoints `czNode k 0 = -1` and `czNode k k = 1`. -/
noncomputable def czNode (k : ℕ) (j : ℕ) : ℝ := - Real.cos (Real.pi * j / k)

/-- The mesh maximum: `max_{0 ≤ j ≤ k} |R(x_j)|`, written as a bounded supremum
over `Finset.range (k+1)`.  Since each summand is `≥ 0` and the index set is
finite and nonempty, this is the ordinary finite maximum. -/
noncomputable def czMeshMax (R : Polynomial ℝ) (k : ℕ) : ℝ :=
  ⨆ j ∈ Finset.range (k + 1), |R.eval (czNode k j)|

/-- The trigonometric transform evaluated at the mesh parameter `t = π j / k`
recovers the node value: `czTrig R (π j / k) = R(czNode k j)`. -/
theorem czTrig_at_meshParam (R : Polynomial ℝ) (k j : ℕ) :
    czTrig R (Real.pi * j / k) = R.eval (czNode k j) := by
  simp only [czTrig, czNode]

/-- **Node-selection lemma.**  For `k ≥ 1` and any `t₀ ∈ [0, π]` there is a mesh
index `j ≤ k` whose parameter `π j / k` is within `π / (2k)` of `t₀`:
`|t₀ − π j / k| ≤ π / (2k)`.  (The `k` mesh parameters partition `[0, π]` into
subintervals of length `π / k`, so every point is within a half-step of a node.) -/
theorem exists_meshParam_close (k : ℕ) (hk : 0 < k) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) Real.pi) :
    ∃ j ∈ Finset.range (k + 1), |t₀ - Real.pi * j / k| ≤ Real.pi / (2 * k) := by
  let x : ℝ := t₀ * k / Real.pi
  let n : ℤ := round x
  let j : ℕ := n.toNat
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hπpos : 0 < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := ne_of_gt hπpos
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkℝ
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (mul_nonneg ht₀.1 hkℝ.le) hπpos.le
  have hx_le : x ≤ k := by
    dsimp [x]
    calc
      t₀ * (k : ℝ) / Real.pi ≤ Real.pi * (k : ℝ) / Real.pi := by
        gcongr
        exact ht₀.2
      _ = k := by field_simp [hπne]
  have hn_nonneg : (0 : ℤ) ≤ n := by
    change (0 : ℤ) ≤ round x
    rw [round_eq]
    exact (Int.floor_nonneg).2 (by linarith)
  have hn_le : n ≤ (k : ℤ) := by
    change round x ≤ (k : ℤ)
    rw [round_eq, Int.floor_le_iff]
    change x + 1 / 2 < (k : ℝ) + 1
    linarith
  have hj_le : j ≤ k := by
    dsimp [j]
    omega
  have hj_mem : j ∈ Finset.range (k + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hj_le
  refine ⟨j, hj_mem, ?_⟩
  have hj_cast : (j : ℝ) = (n : ℝ) := by
    dsimp [j]
    exact_mod_cast (Int.toNat_of_nonneg hn_nonneg)
  have hround : |x - (j : ℝ)| ≤ (1 : ℝ) / 2 := by
    simpa [hj_cast] using (abs_sub_round x)
  have hscale : t₀ - Real.pi * (j : ℝ) / k =
      (Real.pi / k) * (x - (j : ℝ)) := by
    dsimp [x]
    field_simp [hπne, hkne]
  calc
    |t₀ - Real.pi * (j : ℝ) / k|
        = |Real.pi / k| * |x - (j : ℝ)| := by
          rw [hscale, abs_mul]
    _ = (Real.pi / k) * |x - (j : ℝ)| := by
          rw [abs_of_nonneg (div_nonneg hπpos.le hkℝ.le)]
    _ ≤ (Real.pi / k) * ((1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left hround (div_nonneg hπpos.le hkℝ.le)
    _ = Real.pi / (2 * k) := by
          field_simp [hkne]

/-- **Sup transfer.**  The `[-1, 1]` sup-norm of `R` equals the sup-norm of its
trigonometric transform on `[0, π]`: since `t ↦ -cos t` maps `[0, π]` *onto*
`[-1, 1]`, `sup_{x∈[-1,1]} |R x| ≤ czSup R` (in fact with equality). -/
theorem czMeshLHS_le_czSup (R : Polynomial ℝ) :
    sSup ((fun x => |R.eval x|) '' Set.Icc (-1 : ℝ) 1) ≤ czSup R := by
  refine Real.sSup_le ?_ (czSup_nonneg R)
  rintro y ⟨x, hx, rfl⟩
  let t := Real.arccos (-x)
  have ht : t ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg (-x), Real.arccos_le_pi (-x)⟩
  have hcos : -Real.cos t = x := by
    have hx₁ : -1 ≤ -x := by linarith [hx.2]
    have hx₂ : -x ≤ 1 := by linarith [hx.1]
    simp [t, Real.cos_arccos hx₁ hx₂]
  simpa [czTrig, hcos] using abs_czTrig_le_czSup R ht

/-- The mesh maximum lower-bounds every node value it ranges over. -/
theorem eval_node_le_czMeshMax (R : Polynomial ℝ) (k : ℕ) {j : ℕ}
    (hj : j ∈ Finset.range (k + 1)) :
    |R.eval (czNode k j)| ≤ czMeshMax R k := by
  let s := Finset.range (k + 1)
  let f : ℕ → ℝ := fun j => |R.eval (czNode k j)|
  have hsne : s.Nonempty := ⟨0, by simp [s]⟩
  let M : ℝ := max 0 (s.sup' hsne f)
  have hM_nonneg : 0 ≤ M := le_max_left _ _
  have hval_le_M {i : ℕ} (hi : i ∈ s) : f i ≤ M := by
    exact (Finset.le_sup' f hi).trans (le_max_right _ _)
  have hinner_bound (i : ℕ) : (⨆ (_ : i ∈ s), f i) ≤ M := by
    exact Real.iSup_le (fun hi => hval_le_M hi) hM_nonneg
  have houter_bdd : BddAbove (Set.range (fun i => ⨆ (_ : i ∈ s), f i)) :=
    ⟨M, by rintro _ ⟨i, rfl⟩; exact hinner_bound i⟩
  have hinner_bdd : BddAbove (Set.range (fun _ : j ∈ s => f j)) :=
    ⟨f j, by rintro _ ⟨hj, rfl⟩; rfl⟩
  have hinner : f j ≤ ⨆ (_ : j ∈ s), f j := le_ciSup hinner_bdd hj
  have houter : f j ≤ ⨆ i, ⨆ (_ : i ∈ s), f i :=
    le_ciSup_of_le houter_bdd j hinner
  simpa [czMeshMax, s, f] using houter

private lemma czMeshMax_nonneg (R : Polynomial ℝ) (k : ℕ) :
    0 ≤ czMeshMax R k := by
  have hmem : 0 ∈ Finset.range (k + 1) := by simp
  exact (abs_nonneg (R.eval (czNode k 0))).trans (eval_node_le_czMeshMax R k hmem)

private lemma czTrig_neg (R : Polynomial ℝ) (t : ℝ) :
    czTrig (-R) t = -czTrig R t := by
  simp [czTrig, Polynomial.eval_neg]

private lemma czSup_neg (R : Polynomial ℝ) :
    czSup (-R) = czSup R := by
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp [czTrig_neg]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp [czTrig_neg]⟩

private lemma czMeshMax_neg (R : Polynomial ℝ) (k : ℕ) :
    czMeshMax (-R) k = czMeshMax R k := by
  simp [czMeshMax, Polynomial.eval_neg]

private lemma meshParam_mem_Icc (k : ℕ) (hk : 0 < k) {j : ℕ}
    (hj : j ∈ Finset.range (k + 1)) :
    Real.pi * j / k ∈ Set.Icc (0 : ℝ) Real.pi := by
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkℝ
  have hj_le : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  constructor
  · positivity
  · calc
      Real.pi * (j : ℝ) / k ≤ Real.pi * (k : ℝ) / k := by
        gcongr
      _ = Real.pi := by
        field_simp [hkne]

private lemma mesh_cos_pos {β k : ℕ} (hk : β < k) :
    0 < Real.cos (Real.pi * β / (2 * k)) := by
  have hk_nat : 0 < k := by omega
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk_nat
  have hβk : (β : ℝ) < k := by exact_mod_cast hk
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · have hnonneg : 0 ≤ Real.pi * (β : ℝ) / (2 * k) := by positivity
    linarith [Real.pi_pos]
  · field_simp [ne_of_gt hkℝ]
    nlinarith [Real.pi_pos, hβk]

private theorem ehlichZeller_mesh_bound_of_pos_max (R : Polynomial ℝ) (β k : ℕ)
    (hβ : R.natDegree ≤ β) (hk : β < k) (hM : 0 < czSup R) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) Real.pi) (hmax : czTrig R t₀ = czSup R) :
    czSup R ≤ (1 / Real.cos (Real.pi * β / (2 * k))) * czMeshMax R k := by
  have hk_nat : 0 < k := by omega
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk_nat
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkℝ
  obtain ⟨j, hj, hclose⟩ := exists_meshParam_close k hk_nat ht₀
  let s : ℝ := Real.pi * j / k
  have hs : s ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa [s] using meshParam_mem_Icc k hk_nat hj
  have hdist : |t₀ - s| ≤ Real.pi / (2 * k) := by
    simpa [s] using hclose
  have hdelta_le_angle :
      (β : ℝ) * |t₀ - s| ≤ Real.pi * β / (2 * k) := by
    calc
      (β : ℝ) * |t₀ - s| ≤ (β : ℝ) * (Real.pi / (2 * k)) := by
        exact mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = Real.pi * β / (2 * k) := by ring
  have hangle_le_half : Real.pi * β / (2 * k) ≤ Real.pi / 2 := by
    have hβk : (β : ℝ) ≤ k := by exact_mod_cast hk.le
    field_simp [hkne]
    nlinarith [Real.pi_pos, hβk]
  have hdelta_le_half :
      (β : ℝ) * |t₀ - s| ≤ Real.pi / 2 :=
    hdelta_le_angle.trans hangle_le_half
  have hbern :
      czSup R * Real.cos ((β : ℝ) * |t₀ - s|) ≤ czTrig R s :=
    czTrig_maximizer_bound R β hβ hM ht₀ hs hmax hdelta_le_half
  have hdelta_nonneg : 0 ≤ (β : ℝ) * |t₀ - s| := by positivity
  have hangle_le_pi : Real.pi * β / (2 * k) ≤ Real.pi := by
    linarith [hangle_le_half, Real.pi_pos]
  have hcos_mono :
      Real.cos (Real.pi * β / (2 * k)) ≤
        Real.cos ((β : ℝ) * |t₀ - s|) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hdelta_nonneg hangle_le_pi hdelta_le_angle
  have h_abs_eval : |czTrig R s| = |R.eval (czNode k j)| := by
    change |czTrig R (Real.pi * j / k)| = |R.eval (czNode k j)|
    rw [czTrig_at_meshParam]
  have hprod :
      czSup R * Real.cos (Real.pi * β / (2 * k)) ≤ czMeshMax R k := by
    calc
      czSup R * Real.cos (Real.pi * β / (2 * k))
          ≤ czSup R * Real.cos ((β : ℝ) * |t₀ - s|) := by
            exact mul_le_mul_of_nonneg_left hcos_mono (czSup_nonneg R)
      _ ≤ czTrig R s := hbern
      _ ≤ |czTrig R s| := le_abs_self _
      _ = |R.eval (czNode k j)| := h_abs_eval
      _ ≤ czMeshMax R k := eval_node_le_czMeshMax R k hj
  have hcospos : 0 < Real.cos (Real.pi * β / (2 * k)) := mesh_cos_pos hk
  have hdiv :
      czSup R ≤ czMeshMax R k / Real.cos (Real.pi * β / (2 * k)) :=
    (le_div_iff₀ hcospos).2 hprod
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- **Ehlich–Zeller mesh (norming) inequality.**  Let `R` be a real polynomial of
degree `≤ β` and let `k` be an integer with `β < k`.  With Chebyshev–Lobatto nodes
`x_j = -cos(π j / k)` (`j = 0..k`),
`sup_{x∈[-1,1]} |R x| ≤ (1 / cos(π β / (2k))) · max_{0≤j≤k} |R(x_j)|`.

The norming constant `sec(π β / (2k))` is finite because `β < k` forces
`π β / (2k) < π / 2`.  The proof reduces (via `czMeshLHS_le_czSup`) to bounding the
trigonometric sup-norm `M = czSup R`: choose a maximizer `t₀` (`czSup_attained`)
and, replacing `R` by `-R` if necessary so that `czTrig R t₀ = M`, pick a nearby
mesh parameter `π j / k` (`exists_meshParam_close`); then `czTrig_maximizer_bound`
gives `M · cos(π β / (2k)) ≤ |R(x_j)| ≤ max_j |R(x_j)|`. -/
theorem ehlichZeller_mesh_bound (R : Polynomial ℝ) (β k : ℕ)
    (hβ : R.natDegree ≤ β) (hk : β < k) :
    sSup ((fun x => |R.eval x|) '' Set.Icc (-1 : ℝ) 1)
      ≤ (1 / Real.cos (Real.pi * β / (2 * k))) * czMeshMax R k := by
  refine (czMeshLHS_le_czSup R).trans ?_
  by_cases hzero : czSup R = 0
  · rw [hzero]
    exact mul_nonneg (one_div_nonneg.mpr (mesh_cos_pos hk).le) (czMeshMax_nonneg R k)
  · have hM : 0 < czSup R :=
      lt_of_le_of_ne (czSup_nonneg R) (by exact fun h => hzero h.symm)
    obtain ⟨t₀, ht₀, habs⟩ := czSup_attained R
    rcases abs_choice (czTrig R t₀) with hpos | hneg
    · have hmax : czTrig R t₀ = czSup R := by linarith
      exact ehlichZeller_mesh_bound_of_pos_max R β k hβ hk hM ht₀ hmax
    · have hmax_neg : czTrig (-R) t₀ = czSup (-R) := by
        rw [czTrig_neg, czSup_neg]
        linarith
      have hβneg : (-R).natDegree ≤ β := by
        simpa [Polynomial.natDegree_neg] using hβ
      have hMneg : 0 < czSup (-R) := by
        simpa [czSup_neg] using hM
      have hbound :=
        ehlichZeller_mesh_bound_of_pos_max (-R) β k hβneg hk hMneg ht₀ hmax_neg
      simpa [czSup_neg, czMeshMax_neg] using hbound

/-- **Oversampled Chebyshev–Lobatto norming (constant depending only on the
oversampling ratio).**  Let `c > 1`, let `R` have degree `≤ β` with `β ≥ 1`, and
let `k` be a mesh order with `c·β ≤ k`.  Then
`sup_{x∈[-1,1]} |R x| ≤ (1 / cos(π / (2c))) · max_{0≤j≤k} |R(x_j)|`,
i.e. the norming constant `K(c) = sec(π / (2c))` works uniformly in `β`.

This specializes `ehlichZeller_mesh_bound`: from `c·β ≤ k` and `c > 1`, `β ≥ 1`
one gets `β < k` and `β / k ≤ 1 / c`, hence `π β / (2k) ≤ π / (2c) < π / 2`; since
`cos` is positive and antitone on `[0, π/2)`, `cos(π / (2c)) ≤ cos(π β / (2k))`,
so `sec(π β / (2k)) ≤ sec(π / (2c))`. -/
theorem oversampled_norming (R : Polynomial ℝ) (β k : ℕ) (c : ℝ)
    (hc : 1 < c) (hβ : 1 ≤ β) (hβR : R.natDegree ≤ β) (hk : (c * β) ≤ k) :
    sSup ((fun x => |R.eval x|) '' Set.Icc (-1 : ℝ) 1)
      ≤ (1 / Real.cos (Real.pi / (2 * c))) * czMeshMax R k := by
  have hβposℝ : 0 < (β : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hβ)
  have hβ_lt_cβ : (β : ℝ) < c * β := by
    nlinarith [hc, hβposℝ]
  have hβ_lt_kℝ : (β : ℝ) < k := hβ_lt_cβ.trans_le hk
  have hk' : β < k := by exact_mod_cast hβ_lt_kℝ
  refine (ehlichZeller_mesh_bound R β k hβR hk').trans ?_
  have hk_nat : 0 < k := by omega
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk_nat
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hangle_le :
      Real.pi * β / (2 * k) ≤ Real.pi / (2 * c) := by
    field_simp [ne_of_gt hkℝ, ne_of_gt hcpos]
    nlinarith [Real.pi_pos, hk]
  have hsmall_lt : Real.pi / (2 * c) < Real.pi / 2 := by
    field_simp [ne_of_gt hcpos]
    nlinarith [Real.pi_pos, hc]
  have hsmall_nonneg : 0 ≤ Real.pi / (2 * c) := by positivity
  have hsmall_le_pi : Real.pi / (2 * c) ≤ Real.pi := by
    linarith [hsmall_lt, Real.pi_pos]
  have hangle_nonneg : 0 ≤ Real.pi * β / (2 * k) := by positivity
  have hcos_order :
      Real.cos (Real.pi / (2 * c)) ≤ Real.cos (Real.pi * β / (2 * k)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hangle_nonneg hsmall_le_pi hangle_le
  have hcos_small_pos : 0 < Real.cos (Real.pi / (2 * c)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hsmall_nonneg, Real.pi_pos], hsmall_lt⟩
  have hcoef :
      1 / Real.cos (Real.pi * β / (2 * k)) ≤
        1 / Real.cos (Real.pi / (2 * c)) :=
    one_div_le_one_div_of_le hcos_small_pos hcos_order
  exact mul_le_mul_of_nonneg_right hcoef (czMeshMax_nonneg R k)

end Causalean.Mathlib.Analysis.EhlichZellerMesh
