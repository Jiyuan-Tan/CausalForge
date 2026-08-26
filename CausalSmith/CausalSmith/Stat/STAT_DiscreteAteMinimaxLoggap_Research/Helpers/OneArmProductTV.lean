import Causalean.Stat.Minimax.MaximalCoupling
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Total-variation tensorization for finite iid products

This file derives the linear product bound from coordinatewise maximal
couplings.  It is used to pass a one-cell predictive comparison to the full
collection of active cells.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open scoped ENNReal symmDiff

/-- Any coupling bounds total variation by its probability of unequal
coordinates. -/
lemma tvDist_le_coupling_ne
    {X Ω : Type*} [MeasurableSpace X] [MeasurableEq X] [MeasurableSpace Ω]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (gamma : Measure Ω) [IsProbabilityMeasure gamma]
    (f g : Ω → X) (hf : Measurable f) (hg : Measurable g)
    (hfst : gamma.map f = mu) (hsnd : gamma.map g = nu) :
    tvDist mu nu ≤ gamma.real {z | f z ≠ g z} := by
  unfold tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  let S : Set Ω := f ⁻¹' A
  let T : Set Ω := g ⁻¹' A
  have hS : MeasurableSet S := hA.preimage hf
  have hT : MeasurableSet T := hA.preimage hg
  have hmu : mu.real A = gamma.real S := by
    rw [← hfst, map_measureReal_apply hf hA]
  have hnu : nu.real A = gamma.real T := by
    rw [← hsnd, map_measureReal_apply hg hA]
  rw [hmu, hnu]
  refine (abs_measureReal_sub_le_measureReal_symmDiff hS.nullMeasurableSet
    hT.nullMeasurableSet).trans ?_
  apply measureReal_mono
  intro z hz
  simp only [Set.mem_symmDiff, Set.mem_preimage, S, T] at hz
  change f z ≠ g z
  rintro hfg
  rcases hz with ⟨hfA, hgA⟩ | ⟨hgA, hfA⟩
  · exact hgA (hfg ▸ hfA)
  · exact hfA (hfg.symm ▸ hgA)
  exact measure_ne_top gamma _

/-- The mismatch probability of the maximal coupling is at most total
variation. -/
lemma maximalCoupling_ne_mass_le
    {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (Causalean.Stat.maximalCoupling mu nu).real {z | z.1 ≠ z.2} ≤
      tvDist mu nu := by
  let gamma := Causalean.Stat.maximalCoupling mu nu
  let D : Set (X × X) := {z | z.1 = z.2}
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  have htv0 : 0 ≤ tvDist mu nu := tvDist_nonneg
  have hdiagENN := Causalean.Stat.maximalCoupling_eq_mass_ge mu nu
  have hdiag : 1 - tvDist mu nu ≤ gamma.real D := by
    have hfinite : gamma D ≠ ∞ := measure_ne_top gamma D
    have hreal := ENNReal.toReal_mono (by simp) hdiagENN
    change 1 - tvDist mu nu ≤ (gamma D).toReal
    simpa [gamma, D, ENNReal.toReal_ofReal (sub_nonneg.mpr
      (tvDist_le_one (μ := mu) (ν := nu)))] using hreal
  have hcompl : gamma.real Dᶜ = 1 - gamma.real D := by
    rw [measureReal_compl hD, probReal_univ]
  have hne : {z : X × X | z.1 ≠ z.2} = Dᶜ := by
    ext z
    simp [D]
  rw [hne, hcompl]
  linarith

/-- Total variation of finite, not necessarily iid, products is bounded by
the sum of the coordinatewise total-variation distances. -/
theorem tvDist_pi_le_sum
    {X : Type*} [MeasurableSpace X] [MeasurableEq X] [Countable X]
    {m : ℕ} (mu nu : Fin m → Measure X)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)] :
    tvDist (Measure.pi mu) (Measure.pi nu) ≤
      ∑ i, tvDist (mu i) (nu i) := by
  let gamma : Fin m → Measure (X × X) :=
    fun i => Causalean.Stat.maximalCoupling (mu i) (nu i)
  let Gamma : Measure (Fin m → X × X) := Measure.pi gamma
  let left : (Fin m → X × X) → (Fin m → X) := fun z i => (z i).1
  let right : (Fin m → X × X) → (Fin m → X) := fun z i => (z i).2
  let E : Fin m → Set (Fin m → X × X) := fun i => {z | (z i).1 ≠ (z i).2}
  let bad : Set (Fin m → X × X) := {z | ∃ i, (z i).1 ≠ (z i).2}
  have hleft : Gamma.map left = Measure.pi mu := by
    rw [show left = fun z i => Prod.fst (z i) by rfl, Measure.pi_map_pi]
    congr 1
    funext i
    exact Causalean.Stat.maximalCoupling_map_fst (mu i) (nu i)
    intro i
    exact measurable_fst.aemeasurable
  have hright : Gamma.map right = Measure.pi nu := by
    rw [show right = fun z i => Prod.snd (z i) by rfl, Measure.pi_map_pi]
    congr 1
    funext i
    exact Causalean.Stat.maximalCoupling_map_snd (mu i) (nu i)
    intro i
    exact measurable_snd.aemeasurable
  have htv : tvDist (Measure.pi mu) (Measure.pi nu) ≤ Gamma.real bad := by
    have hbadLR : {z | left z ≠ right z} = bad := by
      ext z
      simp [bad, left, right, Function.ne_iff]
    rw [← hbadLR]
    apply tvDist_le_coupling_ne _ _ Gamma left right
    · dsimp [left]
      fun_prop
    · dsimp [right]
      fun_prop
    · exact hleft
    · exact hright
  have hbad : bad = ⋃ i, E i := by
    ext z
    simp [bad, E]
  have hcoord (i : Fin m) :
      Gamma.real (E i) ≤ tvDist (mu i) (nu i) := by
    have hEval : Gamma.map (Function.eval i) = gamma i := by
      rw [Measure.pi_map_eval]
      simp
    have hmap : Gamma.real (E i) =
        (gamma i).real {z | z.1 ≠ z.2} := by
      rw [← hEval, map_measureReal_apply (measurable_pi_apply i)]
      · rfl
      · exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [hmap]
    exact maximalCoupling_ne_mass_le (mu i) (nu i)
  calc
    tvDist (Measure.pi mu) (Measure.pi nu) ≤ Gamma.real bad := htv
    _ = Gamma.real (⋃ i, E i) := by rw [hbad]
    _ ≤ ∑ i, Gamma.real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ i, tvDist (mu i) (nu i) :=
      Finset.sum_le_sum fun i _ => hcoord i

/-- Total variation between `m`-fold iid product measures is at most `m`
times the one-coordinate total variation. -/
theorem tvDist_pi_le_card_mul
    {X : Type*} [MeasurableSpace X] [MeasurableEq X] [Countable X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (m : ℕ) :
    tvDist (Measure.pi fun _ : Fin m => mu) (Measure.pi fun _ : Fin m => nu) ≤
      (m : ℝ) * tvDist mu nu := by
  let gamma := Causalean.Stat.maximalCoupling mu nu
  let Gamma : Measure (Fin m → X × X) := Measure.pi fun _ : Fin m => gamma
  let left : (Fin m → X × X) → (Fin m → X) := fun z i => (z i).1
  let right : (Fin m → X × X) → (Fin m → X) := fun z i => (z i).2
  let E : Fin m → Set (Fin m → X × X) := fun i => {z | (z i).1 ≠ (z i).2}
  let bad : Set (Fin m → X × X) := {z | ∃ i, (z i).1 ≠ (z i).2}
  have hleft : Gamma.map left = Measure.pi fun _ : Fin m => mu := by
    rw [show left = fun z i => Prod.fst (z i) by rfl, Measure.pi_map_pi]
    congr 1
    funext i
    exact Causalean.Stat.maximalCoupling_map_fst mu nu
    intro i
    exact measurable_fst.aemeasurable
  have hright : Gamma.map right = Measure.pi fun _ : Fin m => nu := by
    rw [show right = fun z i => Prod.snd (z i) by rfl, Measure.pi_map_pi]
    congr 1
    funext i
    exact Causalean.Stat.maximalCoupling_map_snd mu nu
    intro i
    exact measurable_snd.aemeasurable
  have htv : tvDist (Measure.pi fun _ : Fin m => mu)
      (Measure.pi fun _ : Fin m => nu) ≤ Gamma.real bad := by
    have hbadLR : {z | left z ≠ right z} = bad := by
      ext z
      simp [bad, left, right, Function.ne_iff]
    rw [← hbadLR]
    apply tvDist_le_coupling_ne _ _ Gamma left right
    · dsimp [left]
      fun_prop
    · dsimp [right]
      fun_prop
    · exact hleft
    · exact hright
  have hbad : bad = ⋃ i, E i := by
    ext z
    simp [bad, E]
  have hcoord (i : Fin m) : Gamma.real (E i) ≤ tvDist mu nu := by
    have hEval : Gamma.map (Function.eval i) = gamma := by
      rw [Measure.pi_map_eval]
      simp
    have hmap : Gamma.real (E i) = gamma.real {z | z.1 ≠ z.2} := by
      rw [← hEval, map_measureReal_apply (measurable_pi_apply i)]
      · rfl
      · exact (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [hmap]
    exact maximalCoupling_ne_mass_le mu nu
  calc
    tvDist (Measure.pi fun _ : Fin m => mu) (Measure.pi fun _ : Fin m => nu)
        ≤ Gamma.real bad := htv
    _ = Gamma.real (⋃ i, E i) := by rw [hbad]
    _ ≤ ∑ i, Gamma.real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _i : Fin m, tvDist mu nu := Finset.sum_le_sum fun i _ => hcoord i
    _ = (m : ℝ) * tvDist mu nu := by simp

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
