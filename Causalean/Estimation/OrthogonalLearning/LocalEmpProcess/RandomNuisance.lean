/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Rademacher
import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.RandomParam

/-!
# Random-nuisance empirical-process modulus (cross-fitting lift)

The fixed-nuisance bridge `localEmpProcessModulus_of_bounded_rademacher`
(`OrthogonalLearning/LocalEmpProcess/Rademacher.lean`) controls the centred
excess-risk process for a *fixed* nuisance `g : G`.  Cross-fitting feeds a
*random*, fold-A-measurable nuisance
`ĥ : ℕ → Ω → G` into the fold-B evaluation, so the high-probability modulus
event becomes a random object: at sample `n` and sample point `ω` the bad set is
selected by `ĥ n ω`.

`LocalEmpProcessModulusRandom` is the random-`g` analogue of
`LocalEmpProcessModulus` — exactly the `hMod` hypothesis of
`oracle_inequality_drLearner_random_nuisance`.

The proof structure factors the fixed-nuisance Rademacher argument into
`g`-parametric lemmas, then lifts them with the cross-fit conditioning keystone
`randomParam_event_le`:

* `foldBCoord` / `foldBCoord_law` — the fold-B coordinate map `Y : Ω → (Fin m → Z)`
  with law `Measure.pi P_Z` (independent of `g`);
* `badDataSet g` — despite the historical name, this is the product-sample
  **bad event** for nuisance `g`, not an observed data set. Its
  `Measure.pi P_Z`-mass is `≤ δ` (`badDataSet_mass_le`, using McDiarmid and
  symmetrization);
* `modulus_of_not_badData g` — on the complement, the modulus inequality holds
  uniformly over `Θ_set`;
* `randomParam_event_le` — conditions on fold A, integrates the per-`ĥ n ω`
  mass bound against the fold-A marginal, with no loss in the probability budget.

The fold-A-measurability of `ĥ n` and the joint measurability of
`(ω, s) ↦ s ∈ badDataSet (ĥ n ω)` enter as named regularity hypotheses, in the
same spirit as `RademacherBound` / `LossContinuousOnΘset`.
-/


namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Causalean.Stat
  Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-! ## The random-nuisance modulus predicate -/

/-- **Random-nuisance local empirical-process modulus.**  The `hMod` shape: for
each `n` there is a high-probability event on which the centred excess risk at
the *random* nuisance `ĥ n ω` obeys the modulus inequality uniformly in `θ`. -/
def LocalEmpProcessModulusRandom
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (ρ : ℕ → ℝ) (δ : ℝ) (ĥ : ℕ → Ω → G) : Prop :=
  ∀ n : ℕ, ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
    ∀ ω ∈ E, ∀ θ ∈ S.Θ_set,
      (S.L θ (ĥ n ω) - S.L S.θ₀ (ĥ n ω))
        - (empRiskFoldB S S_iid split n ω θ (ĥ n ω)
            - empRiskFoldB S S_iid split n ω S.θ₀ (ĥ n ω))
        ≤ ρ n * ‖θ - S.θ₀‖ + (ρ n) ^ 2

/-! ## `g`-parametric pieces of the fixed-nuisance bridge -/

/-- The fold-B coordinate map `Y : Ω → (Fin m → Z)`, `m = card (foldB n)`,
reindexing the fold-B subsample by the canonical order isomorphism. -/
noncomputable def foldBCoord
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (n : ℕ) : Ω → Fin (split.foldB n).card → Z :=
  fun ω j => S_iid.Z (((split.foldB n).orderIsoOfFin rfl) j).val ω

/-- The product-sample bad event for nuisance `g`.

Although the declaration is named `badDataSet`, it denotes the subset of
fold-B product samples on which the centred-loss uniform deviation is too large;
it is an event in sample space, not a stored data set.  The McDiarmid deviation
radius is `ε = 2b·√(2 log(1/δ)/m)`. -/
noncomputable def badDataSet
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (n : ℕ) (b δ : ℝ) (_R : ℕ → ℝ) (g : G) :
    Set (Fin (split.foldB n).card → Z) :=
  {s | 2 • rademacherComplexity (split.foldB n).card
          (fun (θ : S.Θ_set) z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g) P_Z id
        + 2 * b * Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)
      ≤ uniformDeviation (split.foldB n).card
          (fun (θ : S.Θ_set) z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g) P_Z id (id ∘ s)}

/-- The deterministic modulus radius `ρ n`. -/
noncomputable def modulusRadius
    {S_iid : IIDSample Ω Z μ P_Z}
    (split : OneShotSplit S_iid) (b δ : ℝ) (R : ℕ → ℝ) : ℕ → ℝ :=
  fun n => Real.sqrt
    (if (split.foldB n).card = 0 then 2 * b
     else 2 * R n + 2 * b *
       Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))

/-- **Fold-B coordinate law.**  `μ.map (foldBCoord n) = Measure.pi P_Z`.
This identifies the validation-fold coordinates as an i.i.d. product sample. -/
theorem foldBCoord_law
    {S_iid : IIDSample Ω Z μ P_Z}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (split : OneShotSplit S_iid) (n : ℕ) :
    μ.map (foldBCoord S_iid split n) = Measure.pi (fun _ : Fin (split.foldB n).card => P_Z) := by
  set m := (split.foldB n).card with hm
  let e : Fin m ≃o split.foldB n := (split.foldB n).orderIsoOfFin rfl
  let YB : Ω → split.foldB n → Z := fun ω i => S_iid.Z i.val ω
  let T : (split.foldB n → Z) ≃ᵐ (Fin m → Z) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin m => Z) e.symm.toEquiv
  have hY_eq : foldBCoord S_iid split n = T ∘ YB := by
    funext ω j
    simpa [foldBCoord, YB, T, e] using
      (MeasurableEquiv.piCongrLeft_apply_apply (e := e.symm.toEquiv)
        (β := fun _ : Fin m => Z)
        (x := fun i : split.foldB n => S_iid.Z i.val ω) (i := e j)).symm
  rw [hY_eq, ← Measure.map_map T.measurable
    (measurable_pi_lambda YB fun i => S_iid.meas i.val)]
  rw [foldB_pi_law S_iid split n]
  simpa [T] using Measure.pi_map_piCongrLeft (e := e.symm.toEquiv)
    (β := fun _ : Fin m => Z) (μ := fun _ : Fin m => P_Z)

/-- **Mass bound.**  The product-space bad set has `Measure.pi P_Z`-mass `≤ δ`.
The proof uses the deterministic fixed-nuisance construction from
`Rademacher.lean`: McDiarmid concentration, symmetrization, and separable
lifting. -/
theorem badDataSet_mass_le
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb_pos : 0 < b) (g : G)
    (hg_bdd : UniformlyBoundedLoss S g b)
    (hg_cont : LossContinuousOnΘset S g)
    (idx : ℕ → S.Θ_set) (idx_dense : DenseRange idx)
    (R : ℕ → ℝ) (_hR : RademacherBound S S_iid split g idx R)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) (n : ℕ)
    (hm_pos : 0 < (split.foldB n).card) :
    Measure.pi (fun _ : Fin (split.foldB n).card => P_Z)
        (badDataSet S S_iid split n b δ R g) ≤ ENNReal.ofReal δ := by
  simp only [badDataSet]
  let m : ℕ := (split.foldB n).card
  let fθ : S.Θ_set → Z → ℝ := fun θ z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g
  haveI : Nonempty Z := nonempty_of_isProbabilityMeasure P_Z
  haveI : Nonempty S.Θ_set := ⟨⟨S.θ₀, S.θ₀_mem⟩⟩
  haveI : SeparableSpace S.Θ_set := by
    exact ⟨⟨Set.range idx, Set.countable_range idx, idx_dense⟩⟩
  have hf_meas : ∀ θ : S.Θ_set, Measurable (fθ θ) := by
    intro θ
    exact (S.ℓ_meas θ.val g).sub (S.ℓ_meas S.θ₀ g)
  have hf_bdd : ∀ θ : S.Θ_set, ∀ z : Z, |fθ θ z| ≤ 2 * b := by
    intro θ z
    have h1 : |S.ℓ z θ.val g| ≤ b := hg_bdd z θ.val θ.property
    have h2 : |S.ℓ z S.θ₀ g| ≤ b := hg_bdd z S.θ₀ S.θ₀_mem
    have h := abs_sub (S.ℓ z θ.val g) (S.ℓ z S.θ₀ g)
    dsimp [fθ]
    linarith
  have hf_cont : ∀ z : Z, Continuous fun θ : S.Θ_set => fθ θ z := by
    intro z
    exact (hg_cont z).sub continuous_const
  let ε : ℝ := 2 * b * Real.sqrt (2 * Real.log (1 / δ) / m)
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hm_pos' : 0 < m := hm_pos
  have htail := uniform_deviation_tail_bound_separable_of_pos
    (μ := P_Z) (n := m) (f := fθ) hf_meas (X := id) measurable_id
    (b := 2 * b) (by linarith) hf_bdd hf_cont (ε := ε) hε_nonneg
  change Measure.pi (fun _ : Fin m => P_Z)
      {s | 2 • rademacherComplexity m fθ P_Z id + ε ≤
        uniformDeviation m fθ P_Z id (id ∘ s)} ≤ ENNReal.ofReal δ
  have hbad_toReal : (Measure.pi (fun _ : Fin m => P_Z)
      {s | 2 • rademacherComplexity m fθ P_Z id + ε ≤
        uniformDeviation m fθ P_Z id (id ∘ s)}).toReal ≤ δ := by
    have hle_exp := htail
    have hexp_le : Real.exp (-ε ^ 2 * m / (2 * (2 * b) ^ 2)) ≤ δ := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
      have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ 1 / δ := by
          rw [le_div_iff₀ hδ]
          simpa using hδ'
        exact this
      have hsqrt_sq : (Real.sqrt (2 * Real.log (1 / δ) / m)) ^ 2 =
          2 * Real.log (1 / δ) / m := by
        rw [Real.sq_sqrt]
        positivity
      have hcalc : -ε ^ 2 * m / (2 * (2 * b) ^ 2) = Real.log δ := by
        have hεsq : ε ^ 2 = 4 * b ^ 2 * (2 * Real.log (1 / δ) / m) := by
          dsimp [ε]
          rw [mul_pow, hsqrt_sq]
          ring
        have hloginv : Real.log (1 / δ) = -Real.log δ := by
          rw [one_div, Real.log_inv]
        rw [hεsq, hloginv]
        have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos'.ne'
        have hbne : (b : ℝ) ≠ 0 := hb_pos.ne'
        field_simp
        ring
      rw [hcalc, Real.exp_log hδ]
    exact hle_exp.trans hexp_le
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (le_of_lt hδ)]
  exact hbad_toReal

/-- **On-event modulus.**  Off the bad set, the modulus inequality holds
uniformly over `Θ_set` for a fixed nuisance `g`, using the same bounded-loss
Rademacher radius as the deterministic bridge in `Rademacher.lean`. -/
theorem modulus_of_not_badData
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure μ]
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb_pos : 0 < b) (g : G)
    (hg_bdd : UniformlyBoundedLoss S g b)
    (hg_cont : LossContinuousOnΘset S g)
    (idx : ℕ → S.Θ_set) (idx_dense : DenseRange idx)
    (R : ℕ → ℝ) (hR : RademacherBound S S_iid split g idx R)
    {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ ≤ 1) (n : ℕ) (ω : Ω)
    (hm_pos : 0 < (split.foldB n).card)
    (hoff : foldBCoord S_iid split n ω ∉ badDataSet S S_iid split n b δ R g)
    (θ : Θ) (hθ : θ ∈ S.Θ_set) :
    (S.L θ g - S.L S.θ₀ g)
        - (empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g)
      ≤ modulusRadius split b δ R n * ‖θ - S.θ₀‖
        + (modulusRadius split b δ R n) ^ 2 := by
  classical
  haveI : IsProbabilityMeasure P_Z := by
    rw [← S_iid.law]
    exact Measure.isProbabilityMeasure_map (S_iid.meas 0).aemeasurable
  have hR_nonneg : 0 ≤ R n := (hR n).1
  have hm0 : (split.foldB n).card ≠ 0 := hm_pos.ne'
  have hm_pos' : 0 < ((split.foldB n).card : ℝ) := Nat.cast_pos.mpr hm_pos
  set m : ℕ := (split.foldB n).card with hm_def
  let fθ : S.Θ_set → Z → ℝ := fun θ z => S.ℓ z θ.val g - S.ℓ z S.θ₀ g
  haveI : Nonempty Z := nonempty_of_isProbabilityMeasure P_Z
  haveI : Nonempty S.Θ_set := ⟨⟨S.θ₀, S.θ₀_mem⟩⟩
  haveI : SeparableSpace S.Θ_set := by
    exact ⟨⟨Set.range idx, Set.countable_range idx, idx_dense⟩⟩
  have hf_meas : ∀ θ : S.Θ_set, Measurable (fθ θ) := by
    intro θ
    exact (S.ℓ_meas θ.val g).sub (S.ℓ_meas S.θ₀ g)
  have hf_bdd : ∀ θ : S.Θ_set, ∀ z : Z, |fθ θ z| ≤ 2 * b := by
    intro θ z
    have h1 : |S.ℓ z θ.val g| ≤ b := hg_bdd z θ.val θ.property
    have h2 : |S.ℓ z S.θ₀ g| ≤ b := hg_bdd z S.θ₀ S.θ₀_mem
    have h := abs_sub (S.ℓ z θ.val g) (S.ℓ z S.θ₀ g)
    dsimp [fθ]
    linarith
  have hf_cont : ∀ z : Z, Continuous fun θ : S.Θ_set => fθ θ z := by
    intro z
    exact (hg_cont z).sub continuous_const
  let ε : ℝ := 2 * b * Real.sqrt (2 * Real.log (1 / δ) / m)
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hsep_sup : ∀ {f : S.Θ_set → ℝ}, Continuous f →
      ⨆ x : S.Θ_set, f x = ⨆ k : ℕ, f (idx k) := by
    intro f hf
    have hclosure :
        closure (Set.range f) = closure (Set.range (f ∘ idx)) := by
      rw [Set.range_comp f idx]
      apply Set.Subset.antisymm
      · have hsub : Set.range f ⊆ closure (f '' Set.range idx) :=
          hf.range_subset_closure_image_dense idx_dense
        exact closure_minimal hsub isClosed_closure
      · apply closure_mono
        exact Set.image_subset_range f (Set.range idx)
    by_cases hbdd : BddAbove (Set.range f)
    · calc
        ⨆ x : S.Θ_set, f x = sSup (closure (Set.range f)) := by
          exact sSup_eq_closure_sSup (Set.range_nonempty f) hbdd
        _ = sSup (closure (Set.range (f ∘ idx))) := by
          rw [hclosure]
        _ = ⨆ k : ℕ, f (idx k) := by
          have hbdd_idx : BddAbove (Set.range (f ∘ idx)) := by
            rw [Set.range_comp f idx]
            exact BddAbove.mono (Set.image_subset_range f (Set.range idx)) hbdd
          exact (sSup_eq_closure_sSup (Set.range_nonempty (f ∘ idx)) hbdd_idx).symm
    · have hbdd_idx : ¬ BddAbove (Set.range (f ∘ idx)) := by
        intro h
        have hclosure_bdd : BddAbove (closure (Set.range (f ∘ idx))) :=
          bddAbove_closure.mpr h
        rw [← hclosure] at hclosure_bdd
        exact hbdd (bddAbove_closure.mp hclosure_bdd)
      calc
        ⨆ x : S.Θ_set, f x = 0 := Real.iSup_of_not_bddAbove hbdd
        _ = ⨆ k : ℕ, f (idx k) := (Real.iSup_of_not_bddAbove hbdd_idx).symm
  have hemp_dense : ∀ sample : Fin m → Z,
      empiricalRademacherComplexity m fθ sample =
        empiricalRademacherComplexity m (fθ ∘ idx) sample := by
    intro sample
    dsimp [empiricalRademacherComplexity]
    congr
    ext σ
    exact hsep_sup (by
      apply Continuous.abs
      apply Continuous.const_mul
      exact continuous_finset_sum Finset.univ fun k _ =>
        continuous_const.mul (hf_cont (sample k)))
  have hrad_full_le : rademacherComplexity m fθ P_Z id ≤ R n := by
    have hfull_dense :
        rademacherComplexity m fθ P_Z id =
          rademacherComplexity m (fθ ∘ idx) P_Z id := by
      dsimp [rademacherComplexity]
      congr
      ext ω'
      exact hemp_dense (id ∘ ω')
    have hmap :
        rademacherComplexity m (fθ ∘ idx) P_Z id =
          rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) := by
      have hmap' :
          rademacherComplexity m (fθ ∘ idx) (μ.map (S_iid.Z 0)) id =
            rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) := by
        dsimp [rademacherComplexity]
        let Φ : (Fin m → Ω) → (Fin m → Z) := fun ω' i => S_iid.Z 0 (ω' i)
        have hmapΦ :
            Measure.map Φ (Measure.pi fun _ : Fin m => μ) =
              Measure.pi fun _ : Fin m => μ.map (S_iid.Z 0) := by
          dsimp [Φ]
          rw [Measure.pi_map_pi]
          intro _
          exact (S_iid.meas 0).aemeasurable
        rw [← hmapΦ]
        rw [integral_map]
        · rfl
        · exact (measurable_pi_lambda Φ
              (fun i => (S_iid.meas 0).comp (measurable_pi_apply i))).aemeasurable
        · apply Measurable.aestronglyMeasurable
          apply measurable_const.mul
          apply Finset.univ.measurable_sum
          intro σ _
          apply Measurable.iSup
          intro i
          apply Measurable.abs
          apply measurable_const.mul
          apply Finset.univ.measurable_sum
          intro k _
          apply measurable_const.mul
          exact (hf_meas (idx i)).comp (measurable_pi_apply k)
      simpa [S_iid.law] using hmap'
    calc
      rademacherComplexity m fθ P_Z id
          = rademacherComplexity m (fθ ∘ idx) P_Z id := hfull_dense
      _ = rademacherComplexity m (fθ ∘ idx) μ (S_iid.Z 0) := hmap
      _ ≤ R n := by simpa [m, fθ] using (hR n).2
  let e : Fin m ≃o split.foldB n := (split.foldB n).orderIsoOfFin rfl
  let Y : Ω → Fin m → Z := fun ω j => S_iid.Z (e j).val ω
  have hgood : ¬ (2 • rademacherComplexity m fθ P_Z id + ε ≤
      uniformDeviation m fθ P_Z id (id ∘ Y ω)) := by
    have hoff' := hoff
    simp only [badDataSet, Set.mem_setOf_eq] at hoff'
    exact hoff'
  let θs : S.Θ_set := ⟨θ, hθ⟩
  have hdev_lt : uniformDeviation m fθ P_Z id (Y ω) < 2 * R n + ε := by
    have hnot : uniformDeviation m fθ P_Z id (Y ω) <
        2 • rademacherComplexity m fθ P_Z id + ε := by
      rw [not_le] at hgood
      simpa using hgood
    have hrad_two : 2 • rademacherComplexity m fθ P_Z id + ε ≤ 2 * R n + ε := by
      simpa [two_nsmul] using
        add_le_add_right
          (mul_le_mul_of_nonneg_left hrad_full_le (by norm_num : (0 : ℝ) ≤ 2)) ε
    exact hnot.trans_le hrad_two
  have hpoint_le_dev :
      |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k))
        - P_Z[fun z => fθ θs (id z)]|
        ≤ uniformDeviation m fθ P_Z id (Y ω) := by
    dsimp [uniformDeviation]
    apply le_ciSup (f := fun i : S.Θ_set =>
      |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ i (Y ω k))
        - P_Z[fun z => fθ i (id z)]|)
    rw [bddAbove_def]
    use 4 * b
    intro y hy
    rcases hy with ⟨θ', rfl⟩
    have hsample :
        |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))| ≤
          2 * b := by
      calc
        _ = (m : ℝ)⁻¹ * |Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k)| := by
          rw [abs_mul, abs_of_nonneg]
          exact inv_nonneg.mpr (Nat.cast_nonneg _)
        _ ≤ (m : ℝ)⁻¹ * (Finset.univ.sum fun _ : Fin m => 2 * b) := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
              (Finset.sum_le_sum fun k _ => hf_bdd θ' (Y ω k))
          · positivity
        _ = 2 * b := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, inv_mul_cancel₀ hm_pos'.ne', one_mul]
    have hmean : |P_Z[fun z => fθ θ' (id z)]| ≤ 2 * b := by
      calc
        _ ≤ ∫ z, |fθ θ' z| ∂P_Z := abs_integral_le_integral_abs
        _ ≤ ∫ _z, 2 * b ∂P_Z := by
          apply integral_mono
          · exact Integrable.of_bound ((hf_meas θ').abs.aestronglyMeasurable) (2 * b)
              (by
                filter_upwards with z
                simpa [Real.norm_eq_abs] using hf_bdd θ' z)
          · exact integrable_const (2 * b)
          · intro z
            exact hf_bdd θ' z
        _ = 2 * b := by simp
    calc
      |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))
          - P_Z[fun z => fθ θ' (id z)]|
          ≤ |(m : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin m => fθ θ' (Y ω k))|
              + |P_Z[fun z => fθ θ' (id z)]| := abs_sub _ _
      _ ≤ 4 * b := by linarith
  have hcenter_abs :
      |(empRiskFoldB S S_iid split n ω θ g
          - empRiskFoldB S S_iid split n ω S.θ₀ g)
        - (S.L θ g - S.L S.θ₀ g)| ≤ 2 * R n + ε := by
    have hsum_reindex :
        (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k)) =
          ∑ i ∈ split.foldB n,
            (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
      have hsum_subtype :
          (Finset.univ.sum fun k : Fin m => fθ θs (Y ω k)) =
            ∑ i : split.foldB n,
              (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g) :=
        Fintype.sum_equiv e.toEquiv (fun k => fθ θs (Y ω k))
          (fun i : split.foldB n =>
            S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)
          (by intro k; rfl)
      have hsum_attach :
          (∑ i : split.foldB n,
              (S.ℓ (S_iid.Z i.val ω) θ g - S.ℓ (S_iid.Z i.val ω) S.θ₀ g)) =
            ∑ i ∈ split.foldB n,
              (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g) := by
        simpa using Finset.sum_attach (s := split.foldB n)
          (f := fun i =>
            S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g)
      exact hsum_subtype.trans hsum_attach
    have hmean_eq : (∫ z, fθ θs z ∂P_Z) = S.L θ g - S.L S.θ₀ g := by
      have hintθ : Integrable (fun z => S.ℓ z θ g) P_Z :=
        Integrable.of_bound (S.ℓ_meas θ g).aestronglyMeasurable b
          (by
            filter_upwards with z
            simpa [Real.norm_eq_abs] using hg_bdd z θ hθ)
      have hint0 : Integrable (fun z => S.ℓ z S.θ₀ g) P_Z :=
        Integrable.of_bound (S.ℓ_meas S.θ₀ g).aestronglyMeasurable b
          (by
            filter_upwards with z
            simpa [Real.norm_eq_abs] using hg_bdd z S.θ₀ S.θ₀_mem)
      change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
        S.L θ g - S.L S.θ₀ g
      change (∫ z, S.ℓ z θ g - S.ℓ z S.θ₀ g ∂P_Z) =
        (∫ z, S.ℓ z θ g ∂P_Z) - (∫ z, S.ℓ z S.θ₀ g ∂P_Z)
      exact integral_sub hintθ hint0
    have hpoint := hpoint_le_dev.trans (le_of_lt hdev_lt)
    have hpoint' :
        |(m : ℝ)⁻¹ *
              (∑ i ∈ split.foldB n,
                (S.ℓ (S_iid.Z i ω) θ g - S.ℓ (S_iid.Z i ω) S.θ₀ g))
            - (S.L θ g - S.L S.θ₀ g)| ≤ 2 * R n + ε := by
      simpa [hmean_eq, hsum_reindex] using hpoint
    convert hpoint' using 1
    simp [empRiskFoldB, m]
    ring_nf
  have hmain :
      (S.L θ g - S.L S.θ₀ g)
        - (empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g)
        ≤ 2 * R n + ε := by
    have := neg_le_abs ((empRiskFoldB S S_iid split n ω θ g
          - empRiskFoldB S S_iid split n ω S.θ₀ g)
        - (S.L θ g - S.L S.θ₀ g))
    linarith
  have hρsq_eq :
      (Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 =
        2 * R n + ε := by
    have hradicand :
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
           Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))
          = 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card) := by
      rw [if_neg hm0]
    have hnonneg :
        0 ≤ (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
           Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) := by
      have : 0 ≤ 2 * R n + ε := by
        nlinarith [hε_nonneg, hR_nonneg]
      rw [hradicand]
      simpa [ε, m] using this
    rw [Real.sq_sqrt hnonneg]
    rw [hradicand]
  have hρ_nonneg :
      0 ≤ Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
    Real.sqrt_nonneg _
  have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
  change (S.L θ g - S.L S.θ₀ g)
        - (empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g)
      ≤ modulusRadius split b δ R n * ‖θ - S.θ₀‖
        + (modulusRadius split b δ R n) ^ 2
  unfold modulusRadius
  calc
    (S.L θ g - S.L S.θ₀ g)
        - (empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g)
        ≤ 2 * R n + ε := hmain
    _ = (Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq_eq.symm
    _ ≤ Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
        + (Real.sqrt
        (if (split.foldB n).card = 0 then 2 * b
         else 2 * R n + 2 * b *
          Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
      nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]

/-! ## Main theorem: cross-fit lift to a random nuisance -/

/-- The fold-B coordinate map is measurable. -/
theorem foldBCoord_meas
    {S_iid : IIDSample Ω Z μ P_Z}
    (split : OneShotSplit S_iid) (n : ℕ) :
    Measurable (foldBCoord S_iid split n) := by
  apply measurable_pi_lambda
  intro j
  exact S_iid.meas _

/-- **Cross-fit lift of the empirical-process modulus to a random nuisance.**

Given a fold-A-measurable random nuisance `ĥ : ℕ → Ω → G` for which the centred
loss is uniformly bounded (`b`), continuous in `θ`, and Rademacher-controlled
(`R`) *at every realisation* `ĥ n ω`, together with the cross-fit structural
facts

* `hindep n` — fold A is independent of the fold-B coordinate block, and
* `hbad_joint n` — the bad set `badDataSet … (ĥ n ω)` depends jointly
  measurably on `(ω, s)` w.r.t. `m_A n ⊗ σ(fold-B coords)`,

the deterministic-`ρ` empirical-process modulus inequality holds with
probability `≥ 1 - δ` *at the random nuisance* `ĥ n ω`.  Proof: condition on
fold A and apply `randomParam_event_le` with the per-`g` mass bound
`badDataSet_mass_le`; on the complementary good event invoke
`modulus_of_not_badData`. -/
theorem localEmpProcessModulus_random_of_bounded_rademacher
    (S : LearningSystem Ω μ Z P_Z Θ G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P_Z]
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    {b : ℝ} (hb_pos : 0 < b)
    (ĥ : ℕ → Ω → G)
    (hg_bdd : ∀ n ω, UniformlyBoundedLoss S (ĥ n ω) b)
    (hg_cont : ∀ n ω, LossContinuousOnΘset S (ĥ n ω))
    (idx : ℕ → S.Θ_set) (idx_dense : DenseRange idx)
    (R : ℕ → ℝ) (hR : ∀ n ω, RademacherBound S S_iid split (ĥ n ω) idx R)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (m_A : ℕ → MeasurableSpace Ω)
    (hm_A_le : ∀ n, m_A n ≤ (inferInstance : MeasurableSpace Ω))
    (hindep : ∀ n, @Indep Ω (m_A n)
        (MeasurableSpace.comap (foldBCoord S_iid split n) inferInstance)
        (inferInstance : MeasurableSpace Ω) μ)
    (hbad_joint : ∀ n, @MeasurableSet (Ω × (Fin (split.foldB n).card → Z))
        ((m_A n).prod inferInstance)
        {p | p.2 ∈ badDataSet S S_iid split n b δ R (ĥ n p.1)}) :
    LocalEmpProcessModulusRandom S S_iid split (modulusRadius split b δ R) δ ĥ := by
  intro n
  classical
  by_cases hm0 : (split.foldB n).card = 0
  · -- Empty fold-B: trivial event Set.univ.
    refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ θ hθ
      have hfold_empty : split.foldB n = ∅ := Finset.card_eq_zero.mp hm0
      -- inline population bound  S.L θ ĥ - S.L θ₀ ĥ ≤ 2 b
      have habs : ∀ θ' ∈ S.Θ_set, |S.L θ' (ĥ n ω)| ≤ b := by
        intro θ' hθ'
        calc
          |S.L θ' (ĥ n ω)| = |∫ z, S.ℓ z θ' (ĥ n ω) ∂P_Z| := rfl
          _ ≤ ∫ z, |S.ℓ z θ' (ĥ n ω)| ∂P_Z := abs_integral_le_integral_abs
          _ ≤ ∫ _z, b ∂P_Z := by
            apply integral_mono
            · exact Integrable.of_bound (S.ℓ_meas θ' (ĥ n ω)).abs.aestronglyMeasurable b
                (by
                  filter_upwards with z
                  simpa [Real.norm_eq_abs] using hg_bdd n ω z θ' hθ')
            · exact integrable_const b
            · intro z
              exact hg_bdd n ω z θ' hθ'
          _ = b := by simp
      have hpop : S.L θ (ĥ n ω) - S.L S.θ₀ (ĥ n ω) ≤ 2 * b := by
        have hθ_abs := habs θ hθ
        have hθ₀_abs := habs S.θ₀ S.θ₀_mem
        have hθ_le : S.L θ (ĥ n ω) ≤ b := (le_abs_self _).trans hθ_abs
        have hθ₀_ge : -b ≤ S.L S.θ₀ (ĥ n ω) := (abs_le.mp hθ₀_abs).1
        linarith
      have hρsq :
          (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2
            = 2 * b := by
        rw [Real.sq_sqrt]
        · simp [hm0]
        · have : 0 ≤ 2 * b := by nlinarith
          simpa [hm0] using this
      have hρ_nonneg :
          0 ≤ Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) :=
        Real.sqrt_nonneg _
      have hnorm_nonneg : 0 ≤ ‖θ - S.θ₀‖ := norm_nonneg _
      change (S.L θ (ĥ n ω) - S.L S.θ₀ (ĥ n ω))
            - (empRiskFoldB S S_iid split n ω θ (ĥ n ω)
                - empRiskFoldB S S_iid split n ω S.θ₀ (ĥ n ω))
          ≤ modulusRadius split b δ R n * ‖θ - S.θ₀‖
            + (modulusRadius split b δ R n) ^ 2
      unfold modulusRadius
      calc
        (S.L θ (ĥ n ω) - S.L S.θ₀ (ĥ n ω))
            - (empRiskFoldB S S_iid split n ω θ (ĥ n ω)
                - empRiskFoldB S S_iid split n ω S.θ₀ (ĥ n ω))
            = S.L θ (ĥ n ω) - S.L S.θ₀ (ĥ n ω) := by
                simp [empRiskFoldB, hfold_empty]
        _ ≤ 2 * b := hpop
        _ = (Real.sqrt
            (if (split.foldB n).card = 0 then 2 * b
             else 2 * R n + 2 * b *
              Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := hρsq.symm
        _ ≤ Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card)) * ‖θ - S.θ₀‖
              + (Real.sqrt
              (if (split.foldB n).card = 0 then 2 * b
               else 2 * R n + 2 * b *
                Real.sqrt (2 * Real.log (1 / δ) / (split.foldB n).card))) ^ 2 := by
            nlinarith [mul_nonneg hρ_nonneg hnorm_nonneg]
  · -- Nonempty fold-B: cross-fit conditioning via randomParam_event_le.
    have hm_pos : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hm0
    set Bad : Ω → Set (Fin (split.foldB n).card → Z) :=
      fun ω => badDataSet S S_iid split n b δ R (ĥ n ω) with hBad_def
    haveI : IsProbabilityMeasure (Measure.pi (fun _ : Fin (split.foldB n).card => P_Z)) := by
      infer_instance
    have hsec : ∀ ω, Measure.pi (fun _ : Fin (split.foldB n).card => P_Z) (Bad ω)
        ≤ ENNReal.ofReal δ :=
      fun ω => badDataSet_mass_le S S_iid split hb_pos (ĥ n ω) (hg_bdd n ω) (hg_cont n ω)
        idx idx_dense R (hR n ω) hδ hδ' n hm_pos
    have hkey : μ {ω | foldBCoord S_iid split n ω ∈ Bad ω} ≤ ENNReal.ofReal δ :=
      randomParam_event_le (foldBCoord_meas split n) (foldBCoord_law split n)
        (m_A n) (hm_A_le n) (hindep n) Bad (hbad_joint n) hsec
    -- measurability of the bad event
    have hmeas_bad : MeasurableSet {ω | foldBCoord S_iid split n ω ∈ Bad ω} := by
      have hset_eq :
          {ω | foldBCoord S_iid split n ω ∈ Bad ω}
            = (fun ω => (ω, foldBCoord S_iid split n ω)) ⁻¹'
                {p : Ω × (Fin (split.foldB n).card → Z) | p.2 ∈ Bad p.1} := rfl
      rw [hset_eq]
      have hms : MeasurableSet[(inferInstance : MeasurableSpace Ω).prod inferInstance]
          {p : Ω × (Fin (split.foldB n).card → Z) | p.2 ∈ Bad p.1} := by
        have hle : (m_A n).prod (inferInstance : MeasurableSpace (Fin (split.foldB n).card → Z))
            ≤ (inferInstance : MeasurableSpace Ω).prod inferInstance := by
          unfold MeasurableSpace.prod
          exact sup_le_sup_right (MeasurableSpace.comap_mono (hm_A_le n)) _
        exact hle _ (hbad_joint n)
      exact (measurable_id.prodMk (foldBCoord_meas split n)) hms
    refine ⟨{ω | foldBCoord S_iid split n ω ∉ Bad ω},
      hmeas_bad.compl, ?_, ?_⟩
    · -- μ E ≥ 1 - ofReal δ
      have hEc : {ω | foldBCoord S_iid split n ω ∉ Bad ω}
          = {ω | foldBCoord S_iid split n ω ∈ Bad ω}ᶜ := rfl
      rw [hEc, measure_compl hmeas_bad (measure_ne_top μ _), measure_univ]
      rw [ge_iff_le]
      exact tsub_le_tsub_left hkey 1
    · -- on-event modulus bound
      intro ω hω θ hθ
      have hoff : foldBCoord S_iid split n ω ∉ badDataSet S S_iid split n b δ R (ĥ n ω) := hω
      exact modulus_of_not_badData S S_iid split hb_pos (ĥ n ω) (hg_bdd n ω) (hg_cont n ω)
        idx idx_dense R (hR n ω) hδ hδ' n ω hm_pos hoff θ hθ

end OrthogonalLearning
end Estimation
end Causalean
