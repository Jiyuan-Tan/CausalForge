/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan, Dhruv Gupta
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Metrizable.Basic

/-!
# Choquet capacities on Polish spaces

This file isolates the small piece of Choquet capacity theory needed to prove universal
measurability of analytic sets.  A capacity is represented directly as a set function, with
continuity from below, finite values on compact sets, and right-continuity through open
neighborhoods of compact sets.  The main theorem is the Choquet capacitability theorem specialized
to Mathlib's topological `MeasureTheory.AnalyticSet`.

The formulation deliberately avoids introducing a second notion of analytic set or a general
paving library.  It follows the hypotheses used in Kechris, *Classical Descriptive Set Theory*,
Theorem 30.13, and is sufficient for the outer measure of a finite Borel measure.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω]

/-- A Choquet capacity on a topological sample space bundles [an extended-real-valued set
function](hyp:toFun) that is [monotone under set inclusion](hyp:mono'), [continuous from below
along increasing sequences of sets](hyp:iUnion_of_monotone'), [finite on every compact
set](hyp:isCompact_lt_top'), and [right-continuous at compact sets: any strict upper bound on a
compact set's value is already an upper bound on some open neighborhood of that compact
set](hyp:exists_isOpen_superset_lt'). -/
structure ChoquetCapacity (Ω : Type*) [TopologicalSpace Ω] where
  /-- The value of the capacity on an arbitrary set. -/
  toFun : Set Ω → ℝ≥0∞
  /-- A capacity is monotone under inclusion. -/
  mono' : ∀ ⦃s t : Set Ω⦄, s ⊆ t → toFun s ≤ toFun t
  /-- A capacity is continuous along increasing sequences. -/
  iUnion_of_monotone' : ∀ (s : ℕ → Set Ω), Monotone s →
    toFun (⋃ n, s n) = ⨆ n, toFun (s n)
  /-- A capacity is finite on compact sets. -/
  isCompact_lt_top' : ∀ ⦃K : Set Ω⦄, IsCompact K → toFun K < ⊤
  /-- A capacity is right-continuous on compact sets: every strict upper bound at a compact set
  remains an upper bound on some open neighborhood. -/
  exists_isOpen_superset_lt' : ∀ ⦃K : Set Ω⦄, IsCompact K → ∀ ⦃a : ℝ≥0∞⦄,
    toFun K < a → ∃ U, K ⊆ U ∧ IsOpen U ∧ toFun U < a

/-- A Choquet capacity coerces to its underlying extended-nonnegative set function. -/
instance : CoeFun (ChoquetCapacity Ω) fun _ ↦ Set Ω → ℝ≥0∞ :=
  ⟨ChoquetCapacity.toFun⟩

namespace ChoquetCapacity

/-- Capacity values are monotone under inclusion. -/
theorem mono (c : ChoquetCapacity Ω) {s t : Set Ω} (hst : s ⊆ t) : c s ≤ c t :=
  c.mono' hst

/-- Capacity values on compact sets are finite. -/
theorem isCompact_lt_top (c : ChoquetCapacity Ω) {K : Set Ω} (hK : IsCompact K) :
    c K < ⊤ :=
  c.isCompact_lt_top' hK

/-- A strict upper bound for the capacity of a compact set also bounds some open neighborhood. -/
theorem exists_isOpen_superset_lt (c : ChoquetCapacity Ω) {K : Set Ω} (hK : IsCompact K)
    {a : ℝ≥0∞} (ha : c K < a) : ∃ U, K ⊆ U ∧ IsOpen U ∧ c U < a :=
  c.exists_isOpen_superset_lt' hK ha

/-- A set is capacitable when its capacity is the supremum of the capacities of its compact
subsets. -/
def IsCapacitable (c : ChoquetCapacity Ω) (s : Set Ω) : Prop :=
  c s = ⨆ (K : Set Ω) (_ : K ⊆ s) (_ : IsCompact K), c K

/-! ### Baire-space cylinders -/

/-- The cylinder of sequences bounded by `N` through coordinate `n`. -/
private abbrev Cyl (N : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, i ≤ n → g i ≤ N i}

/-- The compact set of sequences bounded by `N` in every coordinate. -/
private abbrev Bnd (N : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, g i ≤ N i}

private lemma isCompact_bnd (N : ℕ → ℕ) : IsCompact (Bnd N) := by
  have : Bnd N = Set.pi Set.univ (fun i => Set.Iic (N i)) := by
    ext g
    simp only [Bnd, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
  rw [this]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (N i)).isCompact

private lemma bnd_subset_cyl (N : ℕ → ℕ) (n : ℕ) : Bnd N ⊆ Cyl N n :=
  fun _ hg i _ => hg i

private lemma cyl_succ_eq (N : ℕ → ℕ) (n : ℕ) :
    Cyl N n = ⋃ k : ℕ, (Cyl N n ∩ {g | g (n + 1) ≤ k}) := by
  ext g
  simp only [Cyl, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  exact ⟨fun h => ⟨g (n + 1), h, le_refl _⟩, fun ⟨_, h, _⟩ => h⟩

private lemma monotone_cyl_split (N : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k}) := by
  intro a b hab x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, hx₂.trans hab⟩

private lemma cyl_inter_eq_cyl_update (N : ℕ → ℕ) (n k : ℕ) :
    Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k} =
      Cyl (Function.update N (n + 1) k) (n + 1) := by
  ext g
  simp only [Cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Function.update]
  constructor
  · rintro ⟨hg, hgk⟩ i hi
    by_cases heq : i = n + 1
    · subst heq
      simp [hgk]
    · have : i ≤ n := by omega
      simp [heq, hg i this]
  · intro hg
    constructor
    · intro i hi
      specialize hg i (by omega)
      simp [show i ≠ n + 1 by omega] at hg
      exact hg
    · specialize hg (n + 1) (le_refl _)
      simpa using hg

private lemma cyl_ext (N N' : ℕ → ℕ) (n : ℕ) (h : ∀ i, i ≤ n → N i = N' i) :
    Cyl N n = Cyl N' n := by
  ext g
  simp only [Cyl, Set.mem_setOf_eq]
  exact ⟨fun hg i hi => h i hi ▸ hg i hi, fun hg i hi => (h i hi).symm ▸ hg i hi⟩

/-- Truncate a sequence coordinatewise into `Bnd N`. -/
private noncomputable def truncate (N : ℕ → ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
  fun i => min (g i) (N i)

private lemma truncate_mem_bnd (N : ℕ → ℕ) (g : ℕ → ℕ) : truncate N g ∈ Bnd N :=
  fun _ => min_le_right _ _

private lemma truncate_agree_on_cyl (N : ℕ → ℕ) (n : ℕ) (g : ℕ → ℕ)
    (hg : g ∈ Cyl N n) : ∀ i, i ≤ n → truncate N g i = g i := by
  intro i hi
  simp only [truncate, min_eq_left (hg i hi)]

/-- The decreasing closures of the images of bounded cylinders eventually enter every open
neighborhood of the image of the fully bounded sequences. -/
private lemma exists_closure_image_cyl_subset
    {α : Type*} [TopologicalSpace α] [PolishSpace α]
    {f : (ℕ → ℕ) → α} (hf : Continuous f) (N : ℕ → ℕ)
    {U : Set α} (hU : IsOpen U) (hsub : f '' Bnd N ⊆ U) :
    ∃ n, closure (f '' Cyl N n) ⊆ U := by
  haveI : T2Space α := inferInstance
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
  by_contra h
  push_neg at h
  have h' : ∀ n, ∃ y, y ∈ closure (f '' Cyl N n) ∧ y ∉ U :=
    fun n => Set.not_subset.mp (h n)
  choose y hy_mem hy_not_mem using h'
  have happrox : ∀ n, ∃ g ∈ Cyl N n, dist (f g) (y n) < 1 / (↑n + 1) := by
    intro n
    have hyn : y n ∈ closure (f '' Cyl N n) := hy_mem n
    rw [Metric.mem_closure_iff] at hyn
    obtain ⟨z, hz, hdist⟩ := hyn (1 / (↑n + 1)) (by positivity)
    obtain ⟨g, hg, rfl⟩ := hz
    exact ⟨g, hg, by simpa only [dist_comm] using hdist⟩
  choose g hg_cyl hg_dist using happrox
  let g' : ℕ → (ℕ → ℕ) := fun n => truncate N (g n)
  have hg'_bnd : ∀ n, g' n ∈ Bnd N := fun n => truncate_mem_bnd N (g n)
  have hg'_agree : ∀ n i, i ≤ n → g' n i = g n i :=
    fun n => truncate_agree_on_cyl N n (g n) (hg_cyl n)
  obtain ⟨gstar, hgstar_bnd, φ, hφ, hg'_conv⟩ :=
    (isCompact_bnd N).isSeqCompact (fun n => hg'_bnd n)
  have hg_conv : Tendsto (fun n => g (φ n)) atTop (𝓝 gstar) := by
    rw [tendsto_pi_nhds]
    intro i
    simp only [nhds_discrete, Filter.tendsto_pure]
    have hg'_ev : ∀ᶠ n in atTop, g' (φ n) i = gstar i := by
      rw [tendsto_pi_nhds] at hg'_conv
      simpa only [nhds_discrete, Filter.tendsto_pure, Function.comp_def] using hg'_conv i
    have hφ_ev : ∀ᶠ n in atTop, i ≤ φ n :=
      hφ.tendsto_atTop.eventually (Filter.eventually_ge_atTop i)
    filter_upwards [hg'_ev, hφ_ev] with n h₁ h₂
    rw [← h₁, hg'_agree (φ n) i h₂]
  have hfg_conv : Tendsto (fun n => f (g (φ n))) atTop (𝓝 (f gstar)) :=
    hf.continuousAt.tendsto.comp hg_conv
  have hbound_zero : Tendsto (fun n => (1 : ℝ) / (↑(φ n) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hdist_zero :
      Tendsto (fun n => dist (f (g (φ n))) (y (φ n))) atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hbound_zero
    exact Filter.Eventually.of_forall fun n => (hg_dist (φ n)).le
  have hy_conv : Tendsto (fun n => y (φ n)) atTop (𝓝 (f gstar)) :=
    hfg_conv.congr_dist hdist_zero
  have : ∀ᶠ n in atTop, y (φ n) ∈ U := hy_conv.eventually (hU.mem_nhds (hsub ⟨gstar,
    hgstar_bnd, rfl⟩))
  obtain ⟨n, hn⟩ := this.exists
  exact hy_not_mem (φ n) hn

/-- **Choquet's capacitability theorem.** On a Polish sample space, if [a set `s` is
analytic — the continuous image of a Polish space, or empty](hyp:hs), then [`s` is capacitable
for every Choquet capacity `c`: the capacity of `s` equals the supremum, over the compact
subsets of `s`, of their capacities](goal). -/
theorem _root_.MeasureTheory.AnalyticSet.isCapacitable [PolishSpace Ω]
    {c : ChoquetCapacity Ω} {s : Set Ω} (hs : AnalyticSet s) : c.IsCapacitable s := by
  apply le_antisymm
  · rw [AnalyticSet] at hs
    rcases hs with rfl | ⟨f, hf, hfs⟩
    · exact le_iSup_of_le ∅ (le_iSup_of_le (Set.empty_subset _) (le_iSup_of_le
        isCompact_empty le_rfl))
    · subst hfs
      apply le_of_forall_lt_imp_le_of_dense
      intro t ht
      have hrange_union : range f = ⋃ k, f '' {g : ℕ → ℕ | g 0 ≤ k} := by
        rw [← Set.image_univ,
          show (Set.univ : Set (ℕ → ℕ)) = ⋃ k, {g : ℕ → ℕ | g 0 ≤ k} from by
            ext g
            simp [Set.mem_iUnion]
            exact ⟨g 0, le_refl _⟩,
          Set.image_iUnion]
      have hmono_base : Monotone (fun k => f '' {g : ℕ → ℕ | g 0 ≤ k}) := by
        intro a b hab
        exact Set.image_mono fun _ hx => hx.trans hab
      rw [hrange_union, c.iUnion_of_monotone' _ hmono_base] at ht
      obtain ⟨k₀, hk₀⟩ := lt_iSup_iff.mp ht
      have hcyl0 : f '' {g : ℕ → ℕ | g 0 ≤ k₀} = f '' Cyl (fun _ => k₀) 0 := by
        congr 1
        ext g
        simp [Cyl]
      have rec_step : ∀ (M : ℕ → ℕ) (n : ℕ), t < c (f '' Cyl M n) →
          ∃ k, t < c (f '' Cyl (Function.update M (n + 1) k) (n + 1)) := by
        intro M n hlt
        have hsplit : c (f '' Cyl M n) =
            ⨆ k, c (f '' (Cyl M n ∩ {g | g (n + 1) ≤ k})) := by
          conv_lhs => rw [cyl_succ_eq M n, Set.image_iUnion]
          exact c.iUnion_of_monotone' _
            (fun _ _ h => Set.image_mono (monotone_cyl_split M n h))
        rw [hsplit] at hlt
        obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
        exact ⟨k, by rwa [cyl_inter_eq_cyl_update] at hk⟩
      let build : (n : ℕ) → {M : ℕ → ℕ // t < c (f '' Cyl M n)} :=
        fun n => Nat.rec
          ⟨fun _ => k₀, hcyl0 ▸ hk₀⟩
          (fun m ⟨M, hM⟩ =>
            ⟨Function.update M (m + 1) (Classical.choose (rec_step M m hM)),
              Classical.choose_spec (rec_step M m hM)⟩)
          n
      let Nseq : ℕ → (ℕ → ℕ) := fun n => (build n).val
      have hNseq_prop : ∀ n, t < c (f '' Cyl (Nseq n) n) := fun n => (build n).property
      have hNseq_consistent : ∀ n i, i ≤ n → Nseq (n + 1) i = Nseq n i := by
        intro n i hi
        show (Function.update (Nseq n) (n + 1) _) i = Nseq n i
        exact Function.update_of_ne (by omega) ..
      let N : ℕ → ℕ := fun i => Nseq i i
      have hN_agree : ∀ n i, i ≤ n → N i = Nseq n i := by
        intro n
        induction n with
        | zero =>
            intro i hi
            simp only [Nat.le_zero] at hi
            subst hi
            rfl
        | succ m ih =>
            intro i hi
            by_cases heq : i = m + 1
            · subst heq
              rfl
            · have him : i ≤ m := by omega
              show Nseq i i = Nseq (m + 1) i
              rw [hNseq_consistent m i him]
              exact ih i him
      have hcyl_eq : ∀ n, Cyl N n = Cyl (Nseq n) n :=
        fun n => cyl_ext N (Nseq n) n (hN_agree n)
      have hcap_bound : ∀ n, t < c (f '' Cyl N n) :=
        fun n => hcyl_eq n ▸ hNseq_prop n
      let K := f '' Bnd N
      have hK_compact : IsCompact K := (isCompact_bnd N).image hf
      have hK_sub : K ⊆ range f := Set.image_subset_range f _
      have htK : t ≤ c K := by
        by_contra hnot
        have hcKt : c K < t := lt_of_not_ge hnot
        obtain ⟨U, hKU, hU, hcUt⟩ := c.exists_isOpen_superset_lt hK_compact hcKt
        obtain ⟨n, hn⟩ := exists_closure_image_cyl_subset hf N hU hKU
        have := (hcap_bound n).trans_le (c.mono subset_closure)
        exact (not_lt_of_ge hcUt.le) (this.trans_le (c.mono hn))
      exact htK.trans (le_iSup_of_le K (le_iSup_of_le hK_sub
        (le_iSup_of_le hK_compact le_rfl)))
  · exact iSup_le fun K => iSup_le fun hKs => iSup_le fun _ => c.mono hKs

end ChoquetCapacity

/-- The outer-measure set function associated with a finite Borel measure on a Polish space is a
Choquet capacity. -/
noncomputable def Measure.toChoquetCapacity [PolishSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] : ChoquetCapacity Ω where
  toFun := μ
  mono' := fun {_ _} hst ↦ μ.mono hst
  iUnion_of_monotone' := fun _ hs ↦ hs.measure_iUnion
  isCompact_lt_top' := fun {_} hK ↦ hK.measure_lt_top
  exists_isOpen_superset_lt' := fun {_} hK {_} ha ↦ hK.exists_isOpen_lt_of_lt _ ha

/-- The capacity induced by a finite measure assigns every event exactly that measure's outer
mass. -/
@[simp]
theorem Measure.toChoquetCapacity_apply [PolishSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) :
    μ.toChoquetCapacity s = μ s := rfl

end MeasureTheory

