import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.Fin.Tuple
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

/-! # Measurable lexicographic argmin on a compact finite-dimensional set

For a fixed nonempty compact subset of a finite Euclidean space, this file
constructs the lexicographically first minimizer of a Carathéodory objective.
The construction requires no countable-generation or standard-Borel
assumption on the sample space.  Countability enters only through a dense
sequence in the compact parameter set.
-/

open scoped Topology
open Set Function Filter TopologicalSpace

namespace CausalSmith.Substrate.MeasurableFiniteLinearERM

/-- Strict lexicographic order on finite real-coordinate vectors, using the
canonical order on `Fin d`. -/
def FinLexLT {d : ℕ} (x y : Fin d → ℝ) : Prop :=
  Pi.Lex (· < ·) (· < ·) x y

/-- A point is the lexicographically first objective minimizer on `K`. -/
def IsLexArgmin {d : ℕ} (K : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Prop :=
  x ∈ K ∧
    (∀ y ∈ K, f x ≤ f y) ∧
    ∀ y ∈ K, f y = f x → ¬ FinLexLT y x

private noncomputable def compactDenseSeq {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty) : ℕ → K := by
  letI : Nonempty K := hKne.to_subtype
  letI : SeparableSpace K := hK.isSeparable.separableSpace
  exact denseSeq K

private theorem denseRange_compactDenseSeq {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty) :
    DenseRange (compactDenseSeq K hK hKne) := by
  letI : Nonempty K := hKne.to_subtype
  letI : SeparableSpace K := hK.isSeparable.separableSpace
  exact denseRange_denseSeq K

/-- The minimum-value functional computed from a countable dense sequence in
the fixed compact feasible set. -/
private noncomputable def compactMinimum {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty)
    (G : Ω → E → ℝ) (ω : Ω) : ℝ :=
  ⨅ n : ℕ, G ω (compactDenseSeq K hK hKne n)

private theorem measurable_compactMinimum {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty)
    (G : Ω → E → ℝ) (hGm : ∀ x, Measurable fun ω => G ω x) :
    Measurable (compactMinimum K hK hKne G) := by
  apply Measurable.iInf
  intro n
  exact hGm _

private theorem compactMinimum_spec {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] (K : Set E) (hK : IsCompact K) (hKne : K.Nonempty)
    (G : Ω → E → ℝ) (hGc : ∀ ω, Continuous fun x => G ω x) (ω : Ω) :
    ∃ x ∈ K, G ω x = compactMinimum K hK hKne G ω ∧
      ∀ y ∈ K, compactMinimum K hK hKne G ω ≤ G ω y := by
  obtain ⟨x, hxK, hx⟩ :=
    hK.exists_isMinOn hKne (hGc ω).continuousOn
  have hle_dense :
      ∀ n, G ω x ≤ G ω (compactDenseSeq K hK hKne n) :=
    fun n => hx (compactDenseSeq K hK hKne n).property
  have hbdd : BddBelow
      (range fun n : ℕ => G ω (compactDenseSeq K hK hKne n)) :=
    ⟨G ω x, by rintro _ ⟨n, rfl⟩; exact hle_dense n⟩
  have hx_le : G ω x ≤ compactMinimum K hK hKne G ω := by
    exact le_ciInf hle_dense
  have hmin_le_x :
      compactMinimum K hK hKne G ω ≤ G ω x := by
    let q := compactDenseSeq K hK hKne
    have hq : DenseRange q := denseRange_compactDenseSeq K hK hKne
    have hrange :
        range q ⊆ {z : K | compactMinimum K hK hKne G ω ≤ G ω z} := by
      rintro _ ⟨n, rfl⟩
      exact ciInf_le hbdd n
    have hclosed :
        IsClosed {z : K | compactMinimum K hK hKne G ω ≤ G ω z} :=
      isClosed_le continuous_const ((hGc ω).comp continuous_subtype_val)
    have hall : (univ : Set K) ⊆
        {z | compactMinimum K hK hKne G ω ≤ G ω z} := by
      rw [← hq.closure_range]
      exact closure_minimal hrange hclosed
    exact hall (mem_univ ⟨x, hxK⟩)
  refine ⟨x, hxK, le_antisymm hx_le hmin_le_x, ?_⟩
  intro y hyK
  rw [← le_antisymm hx_le hmin_le_x]
  exact hx hyK

private theorem exists_lex_least_compact :
    ∀ {d : ℕ} (S : Set (Fin d → ℝ)), IsCompact S → S.Nonempty →
      ∃ x ∈ S, ∀ y ∈ S, ¬ FinLexLT y x := by
  intro d
  induction d with
  | zero =>
      intro S _ hS
      obtain ⟨x, hx⟩ := hS
      refine ⟨x, hx, fun y hy hlt => ?_⟩
      have hxy : y = x := Subsingleton.elim _ _
      simp [hxy, FinLexLT, Pi.Lex] at hlt
  | succ d ih =>
      intro S hS hSne
      obtain ⟨x₀, hx₀S, hx₀min⟩ :=
        hS.exists_isMinOn hSne (continuous_apply 0).continuousOn
      let S₀ : Set (Fin (d + 1) → ℝ) := {x ∈ S | x 0 = x₀ 0}
      have hS₀c : IsCompact S₀ := by
        exact hS.inter_right (isClosed_eq (continuous_apply 0) continuous_const)
      have hS₀ne : S₀.Nonempty := ⟨x₀, hx₀S, rfl⟩
      let T : Set (Fin d → ℝ) := Fin.tail '' S₀
      have hTc : IsCompact T :=
        hS₀c.image (continuous_pi fun i => continuous_apply i.succ)
      have hTne : T.Nonempty := hS₀ne.image _
      obtain ⟨t, htT, htmin⟩ := ih T hTc hTne
      obtain ⟨x, hxS₀, hxt⟩ := htT
      refine ⟨x, hxS₀.1, fun y hyS hyx => ?_⟩
      have hxhead : x 0 = x₀ 0 := hxS₀.2
      rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail x,
        FinLexLT, Fin.pi_lex_lt_cons_cons] at hyx
      rcases hyx with hyhead | ⟨hyhead, hytail⟩
      · exact (not_lt_of_ge (hx₀min hyS)) (hxhead ▸ hyhead)
      · apply htmin (Fin.tail y)
        · refine ⟨y, ⟨hyS, ?_⟩, rfl⟩
          exact hyhead.trans hxhead
        · rw [← hxt]
          exact hytail

private theorem exists_isLexArgmin {d : ℕ} (K : Set (Fin d → ℝ))
    (hK : IsCompact K) (hKne : K.Nonempty)
    (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    ∃ x, IsLexArgmin K f x := by
  let A : Set (Fin d → ℝ) := {x ∈ K | ∀ y ∈ K, f x ≤ f y}
  obtain ⟨x₀, hx₀K, hx₀min⟩ :=
    hK.exists_isMinOn hKne hf.continuousOn
  have hAc : IsCompact A := by
    refine hK.inter_right ?_
    change IsClosed ({x | ∀ y ∈ K, f x ≤ f y} : Set (Fin d → ℝ))
    rw [show ({x | ∀ y ∈ K, f x ≤ f y} : Set (Fin d → ℝ)) =
        ⋂ y ∈ K, {x | f x ≤ f y} by ext x; simp]
    exact isClosed_biInter fun y _ => isClosed_le hf continuous_const
  have hAne : A.Nonempty := ⟨x₀, hx₀K, hx₀min⟩
  obtain ⟨x, hxA, hxlex⟩ := exists_lex_least_compact A hAc hAne
  refine ⟨x, hxA.1, hxA.2, ?_⟩
  intro y hyK hyf
  apply hxlex y
  exact ⟨hyK, fun z hz => hyf ▸ hxA.2 z hz⟩

private theorem isLexArgmin_unique {d : ℕ} {K : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ}
    (hx : IsLexArgmin K f x) (hy : IsLexArgmin K f y) : x = y := by
  have hfx : f x = f y := le_antisymm (hx.2.1 y hy.1) (hy.2.1 x hx.1)
  apply (Pi.trichotomous_lex (β := fun _ : Fin d => ℝ)
      (r := (· < ·)) (s := (· < ·)) wellFounded_lt).trichotomous
  · exact fun h => hy.2.2 x hx.1 hfx h
  · exact fun h => hx.2.2 y hy.1 hfx.symm h

/-- The lexicographically first minimizer of a continuous objective on a fixed
nonempty compact feasible set. -/
noncomputable def lexArgmin {Ω : Type*} {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (F : Ω → (Fin d → ℝ) → ℝ)
    (hFc : ∀ ω, Continuous fun θ => F ω θ) :
    Ω → (Fin d → ℝ) :=
  fun ω => Classical.choose (exists_isLexArgmin K hK hKne (F ω) (hFc ω))

private theorem lexArgmin_spec {Ω : Type*} {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (F : Ω → (Fin d → ℝ) → ℝ)
    (hFc : ∀ ω, Continuous fun θ => F ω θ) (ω : Ω) :
    IsLexArgmin K (F ω) (lexArgmin K hK hKne F hFc ω) :=
  Classical.choose_spec (exists_isLexArgmin K hK hKne (F ω) (hFc ω))

private theorem measurable_lexArgmin {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (F : Ω → (Fin d → ℝ) → ℝ)
    (hFm : ∀ θ, Measurable fun ω => F ω θ)
    (hFc : ∀ ω, Continuous fun θ => F ω θ) :
    Measurable (lexArgmin K hK hKne F hFc) := by
  rw [measurable_pi_iff]
  intro i
  have hcoord : ∀ n : ℕ, ∀ hn : n < d,
      Measurable fun ω => lexArgmin K hK hKne F hFc ω ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let i : Fin d := ⟨n, hn⟩
      apply measurable_of_Iio
      intro a
      let v : Ω → ℝ := compactMinimum K hK hKne F
      have hv : Measurable v := measurable_compactMinimum K hK hKne F hFm
      have hv_eq (ω : Ω) :
          v ω = F ω (lexArgmin K hK hKne F hFc ω) := by
        obtain ⟨z, hzK, hz, hzmin⟩ :=
          compactMinimum_spec K hK hKne F hFc ω
        apply le_antisymm
        · exact hzmin _ (lexArgmin_spec K hK hKne F hFc ω).1
        · exact ((lexArgmin_spec K hK hKne F hFc ω).2.1 z hzK).trans_eq hz
      let R : ℕ → Ω → (Fin d → ℝ) → ℝ := fun k ω θ =>
        |F ω θ - v ω| +
          (∑ j ∈ Finset.Iio i,
            |θ j - lexArgmin K hK hKne F hFc ω j|) +
          max (θ i - (a - 1 / (k + 1 : ℝ))) 0
      have hprevious (j : Fin d) (hji : j < i) :
          Measurable fun ω => lexArgmin K hK hKne F hFc ω j := by
        exact ih j.val hji (j.isLt)
      have hRm : ∀ k θ, Measurable fun ω => R k ω θ := by
        intro k θ
        dsimp [R]
        have hfirst : Measurable fun ω => |F ω θ - v ω| := by
          exact ((hFm θ).sub hv).abs
        have hsum : Measurable fun ω =>
            ∑ j ∈ Finset.Iio i,
              |θ j - lexArgmin K hK hKne F hFc ω j| := by
          apply Finset.measurable_sum
          intro j hj
          exact (measurable_const.sub
            (hprevious j (Finset.mem_Iio.mp hj))).abs
        exact (hfirst.add hsum).add measurable_const
      have hRc : ∀ k ω, Continuous fun θ => R k ω θ := by
        intro k ω
        dsimp [R]
        fun_prop
      have hminR : ∀ k, Measurable
          (compactMinimum K hK hKne (R k)) :=
        fun k => measurable_compactMinimum K hK hKne (R k) (hRm k)
      have hevent :
          (fun ω => lexArgmin K hK hKne F hFc ω i) ⁻¹' Iio a =
            ⋃ k : ℕ, {ω | compactMinimum K hK hKne (R k) ω = 0} := by
        ext ω
        constructor
        · intro hω
          have hgap : 0 < a - lexArgmin K hK hKne F hFc ω i := sub_pos.2 hω
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
          refine mem_iUnion.2 ⟨k, ?_⟩
          obtain ⟨z, hzK, hz, -⟩ :=
            compactMinimum_spec K hK hKne (R k) (hRc k) ω
          have hnonneg : 0 ≤ compactMinimum K hK hKne (R k) ω := by
            rw [← hz]
            dsimp [R]
            exact add_nonneg
              (add_nonneg (abs_nonneg _)
                (Finset.sum_nonneg fun _ _ => abs_nonneg _))
              (le_max_right _ _)
          apply le_antisymm
          · calc
              compactMinimum K hK hKne (R k) ω ≤
                  R k ω (lexArgmin K hK hKne F hFc ω) :=
                (compactMinimum_spec K hK hKne (R k) (hRc k) ω).choose_spec.2.2
                  _ (lexArgmin_spec K hK hKne F hFc ω).1
              _ = 0 := by
                dsimp [R]
                rw [← hv_eq ω]
                simp only [sub_self, abs_zero]
                have hi :
                    lexArgmin K hK hKne F hFc ω i -
                        (a - 1 / (k + 1 : ℝ)) ≤ 0 := by
                  rw [sub_nonpos]
                  rw [le_sub_iff_add_le]
                  have hk' := hk.le
                  rw [le_sub_iff_add_le] at hk'
                  simpa [add_comm] using hk'
                rw [max_eq_right hi]
                simp
          · exact hnonneg
        · intro hω
          obtain ⟨k, hk⟩ := mem_iUnion.1 hω
          obtain ⟨θ, hθK, hθR, -⟩ :=
            compactMinimum_spec K hK hKne (R k) (hRc k) ω
          have hRzero : R k ω θ = 0 := hθR.trans hk
          have hparts :
              F ω θ = v ω ∧
              (∀ j ∈ Finset.Iio i,
                θ j = lexArgmin K hK hKne F hFc ω j) ∧
              θ i ≤ a - 1 / (k + 1 : ℝ) := by
            dsimp [R] at hRzero
            have h1nonneg : 0 ≤ |F ω θ - v ω| := abs_nonneg _
            have h2nonneg : 0 ≤ ∑ j ∈ Finset.Iio i,
                |θ j - lexArgmin K hK hKne F hFc ω j| :=
              Finset.sum_nonneg fun _ _ => abs_nonneg _
            have h3nonneg :
                0 ≤ max (θ i - (a - 1 / (k + 1 : ℝ))) 0 :=
              le_max_right _ _
            have h1 : |F ω θ - v ω| = 0 := by linarith
            have h2 : (∑ j ∈ Finset.Iio i,
                |θ j - lexArgmin K hK hKne F hFc ω j|) = 0 := by
              linarith
            have h3 : max (θ i - (a - 1 / (k + 1 : ℝ))) 0 = 0 := by
              linarith
            refine ⟨sub_eq_zero.mp (abs_eq_zero.mp h1), ?_, ?_⟩
            · intro j hj
              have hjzero := (Finset.sum_eq_zero_iff_of_nonneg
                (fun _ _ => abs_nonneg _)).mp h2 j hj
              exact sub_eq_zero.mp (abs_eq_zero.mp hjzero)
            · have := le_max_left (θ i - (a - 1 / (k + 1 : ℝ))) 0
              linarith
          have hobj :
              F ω θ = F ω (lexArgmin K hK hKne F hFc ω) :=
            hparts.1.trans (hv_eq ω)
          have hcoord_le :
              lexArgmin K hK hKne F hFc ω i ≤ θ i := by
            by_contra hlt
            apply (lexArgmin_spec K hK hKne F hFc ω).2.2 θ hθK hobj
            refine ⟨i, ?_, lt_of_not_ge hlt⟩
            intro j hji
            exact hparts.2.1 j (Finset.mem_Iio.mpr hji)
          have hkpos : 0 < 1 / (k + 1 : ℝ) := by positivity
          exact hcoord_le.trans_lt (hparts.2.2.trans_lt (sub_lt_self a hkpos))
      rw [hevent]
      exact MeasurableSet.iUnion fun k =>
        (hminR k) (measurableSet_singleton 0)
  exact hcoord i.val i.isLt

/-- The measurable lexicographic argmin selector.  It belongs to `K`, minimizes
the objective, and no other objective minimizer is lexicographically smaller.
No hypothesis beyond an arbitrary measurable space on `Ω` is needed. -/
theorem measurable_lex_argmin {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (F : Ω → (Fin d → ℝ) → ℝ)
    (hFm : ∀ θ, Measurable fun ω => F ω θ)
    (hFc : ∀ ω, Continuous fun θ => F ω θ) :
    ∃ θhat : Ω → (Fin d → ℝ),
      Measurable θhat ∧
      (∀ ω, θhat ω ∈ K) ∧
      (∀ ω θ, θ ∈ K → F ω (θhat ω) ≤ F ω θ) ∧
      (∀ ω θ, θ ∈ K → F ω θ = F ω (θhat ω) →
        ¬ FinLexLT θ (θhat ω)) ∧
      ∀ g : Ω → (Fin d → ℝ),
        (∀ ω, IsLexArgmin K (F ω) (g ω)) → g = θhat := by
  refine ⟨lexArgmin K hK hKne F hFc,
    measurable_lexArgmin K hK hKne F hFm hFc, ?_, ?_, ?_, ?_⟩
  · exact fun ω => (lexArgmin_spec K hK hKne F hFc ω).1
  · exact fun ω => (lexArgmin_spec K hK hKne F hFc ω).2.1
  · exact fun ω => (lexArgmin_spec K hK hKne F hFc ω).2.2
  · intro g hg
    funext ω
    exact isLexArgmin_unique (hg ω) (lexArgmin_spec K hK hKne F hFc ω)

/-- Any independently defined selector satisfying the same membership,
optimality, and lexicographic-minimality properties equals `lexArgmin`.  This
is suitable for identifying a selector introduced with `Classical.choose`. -/
theorem eq_lexArgmin_of_isLexArgmin {Ω : Type*} {d : ℕ}
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (F : Ω → (Fin d → ℝ) → ℝ)
    (hFc : ∀ ω, Continuous fun θ => F ω θ)
    (g : Ω → (Fin d → ℝ))
    (hg : ∀ ω, IsLexArgmin K (F ω) (g ω)) :
    g = lexArgmin K hK hKne F hFc := by
  funext ω
  exact isLexArgmin_unique (hg ω) (lexArgmin_spec K hK hKne F hFc ω)

end CausalSmith.Substrate.MeasurableFiniteLinearERM
