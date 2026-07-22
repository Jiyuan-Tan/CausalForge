-- Adapted from auto-res/lean-rademacher FoML/PseudoMetric.lean (commit 72d28921dc960f47691640fb973303a1be9d13ca, MIT (c) 2025 AutoRes)
import Causalean.Stat.Concentration.Covering.CoveringNumber
import Causalean.Stat.Concentration.Rademacher.Rademacher

/-!
Defines the empirical L² pseudometric on function classes used by Dudley
entropy bounds.

The file provides `empiricalNorm`, `empiricalDist`, the pseudometric
`empiricalPMet`, and the indexed `EmpiricalFunctionSpace` wrapper.  It also
records the coordinate projection bound `empiricalDist_proj`, which converts an
empirical-norm bound into pointwise control on the fixed sample.

UPSTREAM-DELTA: declarations are placed in the
`Causalean.Stat.Concentration` namespace. The proofs are otherwise kept close
to upstream, with only Mathlib API-drift adjustments for Lean 4.29.
-/

namespace Causalean.Stat.Concentration

universe v
open scoped BigOperators
variable {𝒳 : Type v}
variable {n : ℕ}

/-- The empirical norm is the root mean square value of a function on a fixed
sample. -/
noncomputable def empiricalNorm (S : Fin n → 𝒳) (f : 𝒳 → ℝ) : ℝ :=
  Real.sqrt ((1 / n) * ∑ i : Fin n, (f (S i)^2))

/-- The empirical norm unfolds to the square root of the average squared sample
values. -/
lemma empiricalNorm_def (S : Fin n → 𝒳) (f : 𝒳 → ℝ) :
    empiricalNorm S f = Real.sqrt ((1 / n) * ∑ i : Fin n, (f (S i))^2) :=
  rfl

/-- The empirical distance between two functions is the empirical norm of their
difference on the fixed sample. -/
noncomputable def empiricalDist (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) : ℝ :=
  empiricalNorm S (f - g)

/-- The empirical distance unfolds to the empirical norm of the pointwise
difference. -/
@[simp]
lemma empiricalDist_def (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) :
    empiricalDist S f g = empiricalNorm S (f - g) :=
  rfl

/-- The empirical distance defines a pseudometric on functions evaluated on the
fixed sample. -/
noncomputable def empiricalPMet (S : Fin n → 𝒳) :
    PseudoMetricSpace (𝒳 → ℝ) where
  dist := fun f g => empiricalDist S f g
  dist_self := by
    intro x; dsimp[empiricalDist]
    simp only [sub_self]; dsimp [empiricalNorm]; simp
  dist_comm := by
    intro x y
    dsimp[empiricalDist, empiricalNorm]
    grind
  dist_triangle := by
    intro x y z
    dsimp[empiricalDist,empiricalNorm]
    suffices
        Real.sqrt (∑ i, (x (S i) - z (S i)) ^ 2) ≤
          Real.sqrt (∑ i, (x (S i) - y (S i)) ^ 2) +
            Real.sqrt (∑ i, (y (S i) - z (S i)) ^ 2) from by
      calc
      _ = √(1 / ↑n) * √(∑ i, (x (S i) - z (S i)) ^ 2) := by simp
      _ ≤ √(1 / ↑n) * (√(∑ i, (x (S i) - y (S i)) ^ 2) + √(∑ i, (y (S i) - z (S i)) ^ 2)) := by
        apply mul_le_mul
        · simp
        · exact this
        · apply Real.sqrt_nonneg
        simp
      _ = √(1 / ↑n) * √(∑ i, (x (S i) - y (S i)) ^ 2) +
          √(1 / ↑n) * √(∑ i, (y (S i) - z (S i)) ^ 2) := by
        apply LeftDistribClass.left_distrib
      _ = _ := by simp
    let xS : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ x (S i))
    let yS : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ y (S i))
    let zS : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i ↦ z (S i))
    calc
    _ = √(∑ i, (xS i - zS i) ^ 2) := by rfl
    _ = √(∑ i, ‖xS i - zS i‖ ^ 2) := by simp
    _ = ‖xS - zS‖ := Eq.symm (EuclideanSpace.norm_eq (xS - zS))
    _ ≤ ‖xS - yS‖ + ‖yS - zS‖ := norm_sub_le_norm_sub_add_norm_sub xS yS zS
    _ = _ := by
      apply Mathlib.Tactic.LinearCombination.add_eq_eq
      · calc
        _ = √(∑ i, ‖xS i - yS i‖ ^ 2) := EuclideanSpace.norm_eq (xS - yS)
        _ = √(∑ i, (xS i - yS i) ^ 2) := by simp
      · calc
        _ = √(∑ i, ‖yS i - zS i‖ ^ 2) := EuclideanSpace.norm_eq (yS - zS)
        _ = √(∑ i, (yS i - zS i) ^ 2) := by simp

/-- The empirical distance between two functions is their empirical norm
difference. -/
@[simp]
lemma empiricalDist_app (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) :
    empiricalDist S f g = empiricalNorm S (f - g) :=
  rfl

/-- The empirical distance is symmetric. -/
@[simp] lemma empiricalDist_comm (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) :
    empiricalDist S f g = empiricalDist S g f := by
  letI := empiricalPMet S
  simpa [empiricalDist] using (dist_comm (x := f) (y := g))

/-- A single sample coordinate is bounded by the empirical norm up to the
sample-size scaling. -/
lemma empiricalDist_proj (S : Fin n → 𝒳) (f : 𝒳 → ℝ) (i : Fin n) :
    |f (S i)|/√n ≤ empiricalNorm S f := by
  calc
  _ = √(f (S i)^2)/√n := by
    have : √(f (S i)^2) = |f (S i)| := by exact Real.sqrt_sq_eq_abs (f (S i))
    rw [this]
  _ = √((f (S i)^2)/n) := by
    simp
  _ ≤ _ := by
    dsimp [empiricalNorm]
    apply Real.sqrt_le_sqrt
    rw [one_div_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ ?_
    · have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ (f (S j))^2 := by
        intro j hj; exact sq_nonneg _
      have hi : i ∈ Finset.univ := by simp
      simpa using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun j => (f (S j))^2)
          hnonneg hi)
    · simp

section

universe u
variable {ι : Type u} {F : ι → 𝒳 → ℝ}
variable {S : Fin n → 𝒳}

/-- The empirical function space is the indexed class of functions equipped
with the empirical pseudometric induced by a fixed sample. -/
structure EmpiricalFunctionSpace (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) where
  /-- The index selecting a function from the class. -/
  index : ι

/-- An empirical function-space element evaluates as the function selected by
its index. -/
instance : CoeFun (EmpiricalFunctionSpace F S) (fun _ ↦ 𝒳 → ℝ) where
  coe f := F f.index

/-- Coercing an empirical function-space element gives the indexed function it
stores. -/
@[simp] lemma EmpiricalFunctionSpace.coe_apply
    (q : EmpiricalFunctionSpace F S) :
    (q : 𝒳 → ℝ) = F q.index := rfl

/-- The empirical function space inherits the empirical distance on the selected
functions. -/
@[simps!]
noncomputable instance : Dist (EmpiricalFunctionSpace F S) where
  dist f g := empiricalDist S f g

/-- The empirical function space is a pseudometric space under sample empirical
distance. -/
noncomputable instance : PseudoMetricSpace (EmpiricalFunctionSpace F S) :=
  PseudoMetricSpace.induced (fun f ↦ F f.index) (empiricalPMet S)

end

end Causalean.Stat.Concentration
