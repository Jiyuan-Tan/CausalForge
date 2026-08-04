import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Basic
import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Bernoulli block score and the two Riesz programs

All objects here live on the finite assignment space `Fin d → Bool`.  The
bilinear form is the expectation of Causalean's finite Bernoulli design, so no
measure-theoretic `L²` wrapper is needed.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

/-- A Boolean coordinate viewed as a real treatment indicator. -/
def blockInd {d : ℕ} (z : Fin d → Bool) (j : Fin d) : ℝ :=
  if z j then 1 else 0

/-- The centered contrast score on a complete `d`-block. -/
noncomputable def blockScore (β : ℕ) (p : ℝ) (d : ℕ) (z : Fin d → Bool) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (effBeta β d),
    (bernoulliContrast p r / (p * (1 - p)) ^ r) *
      ∑ S ∈ (Finset.univ.powerset.filter (fun S : Finset (Fin d) => S.card = r)),
        ∏ j ∈ S, (blockInd z j - p)
-- @realizes g_d(block centered contrast score)

/-- The exact squared norm of the block score. -/
noncomputable def blockEnergy (β : ℕ) (p : ℝ) (d : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (effBeta β d),
    (Nat.choose d r : ℝ) * (bernoulliContrast p r) ^ 2 /
      (p * (1 - p)) ^ r
-- @realizes A_d(exact block score energy)

/-- The normalized representer, with the degree-zero convention imposed
without ever forming `0 / 0`. -/
noncomputable def blockRepresenter
    (β : ℕ) (p : ℝ) (d : ℕ) (z : Fin d → Bool) : ℝ :=
  if d = 0 then 0 else blockScore β p d z / blockEnergy β p d
-- @realizes h_d(g_d/A_d for d≥1 and zero at d=0)

/-- The raw-monomial coefficient of the normalized representer. -/
noncomputable def blockRawCoef
    (β : ℕ) (p : ℝ) (d : ℕ)
    (T : Finset (Fin d)) : ℝ := -- @realizes T(block-coordinate subset T : Finset (Fin d))
  if d = 0 then 0 else
    (blockEnergy β p d)⁻¹ *
      ∑ r ∈ Finset.Icc 1 (effBeta β d),
        ∑ S ∈ (Finset.univ.powerset.filter (fun S : Finset (Fin d) => S.card = r)),
          if T ⊆ S then
            (bernoulliContrast p r / (p * (1 - p)) ^ r) *
              (-p) ^ (S.card - T.card)
          else 0
-- @realizes h_{d,T}(raw-monomial coefficient of h_d)

/-- The four objects jointly introduced by the block score/energy definition:
`g_d`, `A_d`, the normalized representer `h_d`, and all raw coefficients
`h_{d,T}`. -/
-- @node: def:block-score-energy
noncomputable def blockScoreEnergyBundle (β : ℕ) (p : ℝ) (d : ℕ) :
    ((Fin d → Bool) → ℝ) × ℝ ×
      ((Fin d → Bool) → ℝ) × (Finset (Fin d) → ℝ) :=
  (blockScore β p d, blockEnergy β p d,
    blockRepresenter β p d, blockRawCoef β p d)

/-- A raw block monomial. -/
-- @env: S5
noncomputable def rawMonomial {d : ℕ} (S : Finset (Fin d)) :
    (Fin d → Bool) → ℝ :=
  fun z => ∏ j ∈ S, blockInd z j

/-- The span of raw monomials through effective order. -/
noncomputable def polySpace (β d : ℕ) :
    Submodule ℝ ((Fin d → Bool) → ℝ) :=
  Submodule.span ℝ
    {f | ∃ S : Finset (Fin d),
      S.card ≤ effBeta β d ∧ f = rawMonomial S}
-- @realizes \mathcal P_d(span of raw monomials of degree ≤ min β d)
-- @realizes f(candidate polynomial in \mathcal P_d)
-- @realizes h(candidate perturbation in \mathcal P_d)

/-- The all-one versus all-zero functional. -/
def contrastFunctional {d : ℕ} (f : (Fin d → Bool) → ℝ) : ℝ :=
  f (fun _ => true) - f (fun _ => false)
-- @realizes L_d(f ↦ f(1)-f(0))

/-- The common-probability Bernoulli design on a block. -/
noncomputable def blockDesign
    (d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteDesign (Fin d → Bool) :=
  bernoulliDesign (fun _ => p) (fun _ => hp0) (fun _ => hp1)

/-- Feasibility for the normalized perturbation program. -/
def PerturbFeasible (β d : ℕ) (h : (Fin d → Bool) → ℝ) : Prop :=
  h ∈ polySpace β d ∧ contrastFunctional h = 1

/-- The normalized perturbation program. -/
-- @node: def:perturbation-program
noncomputable def perturbProg
    (β d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ℝ :=
  sInf {q : ℝ | ∃ h : (Fin d → Bool) → ℝ,
    PerturbFeasible β d h ∧
      q = (blockDesign d p hp0 hp1).E (fun z => h z ^ 2)}
-- @realizes \mathsf{PerturbProg}_{d,\beta,p}(minimum perturbation energy)

/-- Feasibility for a design-unbiased block weight. -/
def WeightFeasible
    (β d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : (Fin d → Bool) → ℝ) : Prop :=
  (blockDesign d p hp0 hp1).E w = 0 ∧
    ∀ S : Finset (Fin d), S.Nonempty → S.card ≤ effBeta β d →
      (blockDesign d p hp0 hp1).E
        (fun z => w z * rawMonomial S z) = 1
-- @realizes w(candidate block-local unbiased weight)

/-- The minimum-energy unbiased-weight program. -/
-- @node: def:weight-program
noncomputable def weightProg
    (β d : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ℝ :=
  sInf {q : ℝ | ∃ w : (Fin d → Bool) → ℝ,
    WeightFeasible β d p hp0 hp1 w ∧
      q = (blockDesign d p hp0 hp1).E (fun z => w z ^ 2)}
-- @realizes \mathsf{WeightProg}_{d,\beta,p}(minimum unbiased weight energy)

/-- The paper's degree-zero conventions, including the guarded normalized
representer and its raw coefficients. -/
-- @node: def:zero-degree-conventions
def ZeroDegreeConventions (β : ℕ) (p : ℝ) : Prop :=
  effBeta β 0 = 0 ∧
    kStar 0 β p = 0 ∧
    blockScore β p 0 = 0 ∧
    blockEnergy β p 0 = 0 ∧
    blockRepresenter β p 0 = 0 ∧
    blockRawCoef β p 0 = 0

/-- The degree-zero conventions follow from the finite empty sums and the
guard in `blockRepresenter`. -/
lemma zeroDegreeConventions_holds (β : ℕ) (p : ℝ) :
    ZeroDegreeConventions β p := by
  constructor
  · simp [effBeta]
  constructor
  · simp [kStar, effBeta]
  constructor
  · funext z
    simp [blockScore, effBeta]
  constructor
  · simp [blockEnergy, effBeta]
  constructor
  · funext z
    simp [blockRepresenter]
  · funext T
    simp [blockRawCoef]

end CausalSmith.Experimentation.SnipeDegreeFrontier
