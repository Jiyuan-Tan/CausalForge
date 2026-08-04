import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Gibbs.RegretIdentity
import Causalean.Stat.Minimax.Assouad
import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.Mixture
import Causalean.Stat.Minimax.TotalVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

-- @env: S3
variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

-- @node: def:hard-region
def hardRegion (d : ℕ) (eta : ℝ) : Set (ℝ × ℝ) :=
  {(C, D) | 1 < D ∧ D ≤ C ∧ C < Real.exp eta ∧
    2 * D - 1 < Real.exp eta ∧ 4 ≤ d}
  -- @realizes \mathfrak F_{\mathrm{hard}}^\circ(d,\eta)({1<D≤C<eη, 2D-1<eη, d≥4})

/-- Number of paired hard coordinates. -/
def hardCoordinateCount (d : ℕ) : ℕ := (d - 1) / 2
  -- @realizes k(k=floor((d-1)/2), positive for d≥4)

noncomputable def hardQ (C eta : ℝ) : ℝ :=
  (Real.exp eta / C - 1) / (Real.exp eta - 1)
  -- @realizes q((eη/C-1)/(eη-1), range (0,1) on hard region)

noncomputable def hardP (D : ℝ) : ℝ := (4 * D)⁻¹
  -- @realizes p((4D)^{-1}, range (0,1/4))

noncomputable def hardT (D eta gamma : ℝ) : ℝ :=
  D * (1 - 2 * hardP D) /
    (Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
  -- @realizes T_\gamma(D(1-2p)/(e^{ηγ}-2pD cosh(ηγ)), positive on admissible range)

noncomputable def hardBeta (D eta gamma : ℝ) : ℝ :=
  eta⁻¹ * Real.log (hardT D eta gamma)
  -- @realizes \beta(η^{-1}log Tγ, range [0,1] on admissible range)

noncomputable def hardScale (D eta : ℝ) : ℝ :=
  sSup {g : ℝ | 0 < g ∧ ∀ s ∈ Set.Icc (0 : ℝ) g,
    0 < Real.exp (eta * s) - 2 * hardP D * D * Real.cosh (eta * s) ∧
    s ≤ eta⁻¹ * Real.log (hardT D eta s) ∧
    eta⁻¹ * Real.log (hardT D eta s) ≤ 1 - s}
  -- @realizes g_0(D,\eta)(largest admissible hard perturbation scale)

noncomputable def hardPerturbation (eps eta : ℝ) : ℝ :=
  eta⁻¹ * Real.log
    (Real.exp (64 * eta * eps) +
      Real.sqrt (Real.exp (64 * eta * eps) ^ 2 - 1))
  -- @realizes \gamma(\epsilon,d,C,D,\eta)(η^{-1} arcosh(e^{64ηε}); independent of d,C)

-- @node: def:hard-accuracy-range
noncomputable def hardAccuracyRange (C D eta : ℝ) : ℝ :=
  (64 * eta)⁻¹ *
    Real.log (Real.cosh (eta * min (hardScale D eta) (1 / 4)))
  -- @realizes \epsilon_0(C,D,\eta)([64η]^{-1} log cosh(η min{g0,1/4}))

/-- A cell has the Bernoulli reward law with the prescribed conditional mean. -/
def ConditionalBernoulliCell (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) (x : 𝒳) (a : 𝒜) (mean : ℝ) : Prop :=
  (∀ᵐ z ∂P.dataMeasure,
    z.context = x → z.action = a → z.reward = 0 ∨ z.reward = 1) ∧
  (P.dataMeasure {z | z.context = x ∧ z.action = a ∧ z.reward = 1}).toReal =
    cellMass P x a * mean

/-- The action carrier consists of exactly the three displayed actions. -/
def ExactlyThreeActions (plus minus zero : 𝒜) : Prop :=
  plus ≠ minus ∧ plus ≠ zero ∧ minus ≠ zero ∧
    ∀ a : 𝒜, a = plus ∨ a = minus ∨ a = zero

/-- Exclusion of canonical one-cell-per-coordinate tabular features. -/
def NotCanonicalTabularFeature (E : CommonExperiment d 𝒳 𝒜) : Prop :=
  ¬ ∃ coord : 𝒳 → 𝒜 → Fin d,
    Function.Bijective (fun p : 𝒳 × 𝒜 => coord p.1 p.2) ∧
      ∀ x a i, E.feature x a i = if i = coord x a then 1 else 0

/-- Full finite blueprint of one sign-indexed paired-Bernoulli law. -/
def HardFamilyBlueprint (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (C D eps : ℝ) (v : Fin (hardCoordinateCount d) → Bool)
    (plus minus zero : 𝒜) (xC xA xZ : 𝒳)
    (xHard : Fin (hardCoordinateCount d) → 𝒳)
    (e0 z : Fin d → ℝ)
    (u w : Fin (hardCoordinateCount d) → Fin d → ℝ) : Prop :=
  ReferenceLogging E P ∧
  (C, D) ∈ hardRegion d E.eta ∧
  0 < eps ∧ eps ≤ hardAccuracyRange C D E.eta ∧
    ExactlyThreeActions plus minus zero ∧
    Function.Injective xHard ∧
    (∀ j, xHard j ≠ xC ∧ (C > D → xHard j ≠ xA) ∧
      (Even d → xHard j ≠ xZ)) ∧
    (C > D → xA ≠ xC) ∧ (Even d → xZ ≠ xC ∧ (C > D → xZ ≠ xA)) ∧
    (∀ x, x = xC ∨ (C > D ∧ x = xA) ∨
      (∃ j, x = xHard j) ∨ (Even d ∧ x = xZ)) ∧
    (∀ i, E.feature xC plus i = e0 i) ∧
    (∀ i, E.feature xC minus i = 0 ∧ E.feature xC zero i = 0) ∧
    E.reference xC plus = hardQ C E.eta ∧
    0 < E.reference xC minus ∧ 0 < E.reference xC zero ∧
    E.reference xC minus + E.reference xC zero = 1 - hardQ C E.eta ∧
    (∀ j i, E.feature (xHard j) plus i =
        (u j i + w j i) / Real.sqrt 2) ∧
    (∀ j i, E.feature (xHard j) minus i =
        (u j i - w j i) / Real.sqrt 2) ∧
    (∀ j i, E.feature (xHard j) zero i = 0) ∧
    (∀ j, E.reference (xHard j) plus = hardP D ∧
      E.reference (xHard j) minus = hardP D ∧
      E.reference (xHard j) zero = 1 - 2 * hardP D) ∧
    (∀ j, dotProduct e0 (u j) = 0 ∧ dotProduct e0 (w j) = 0 ∧
      dotProduct (u j) (u j) = 1 ∧ dotProduct (w j) (w j) = 1 ∧
      dotProduct (u j) (w j) = 0) ∧
    (∀ j l, j ≠ l →
      dotProduct (u j) (u l) = 0 ∧ dotProduct (u j) (w l) = 0 ∧
      dotProduct (w j) (u l) = 0 ∧ dotProduct (w j) (w l) = 0) ∧
    dotProduct e0 e0 = 1 ∧
    (Even d →
      dotProduct z z = 1 ∧ dotProduct e0 z = 0 ∧
        (∀ j, dotProduct (u j) z = 0 ∧ dotProduct (w j) z = 0) ∧
        (∀ a i, E.feature xZ a i = z i) ∧ dotProduct P.theta z = 0) ∧
    (∀ y : Fin d → ℝ, ∀ i,
      y i = dotProduct y e0 * e0 i +
        ∑ j, (dotProduct y (u j) * u j i + dotProduct y (w j) * w j i) +
        if Even d then dotProduct y z * z i else 0) ∧
    dotProduct P.theta e0 = 1 ∧
    (∀ j, dotProduct P.theta (u j) =
        Real.sqrt 2 * hardBeta D E.eta (hardPerturbation eps E.eta)) ∧
    (∀ j, dotProduct P.theta (w j) =
        Real.sqrt 2 * hardPerturbation eps E.eta *
          (if v j then 1 else -1)) ∧
    hardPerturbation eps E.eta ≤
      min (hardScale D E.eta)
        (min (1 / 4)
          (min (hardBeta D E.eta (hardPerturbation eps E.eta))
            (1 - hardBeta D E.eta (hardPerturbation eps E.eta)))) ∧
    (C > D → ∀ a i, E.feature xA a i = e0 i) ∧
    (∃ H tau anchor : ℝ,
      0 < H ∧ tau = (4 * (1 + anchor))⁻¹ ∧
      anchor = hardQ C E.eta * (C - D) / (D - 1) ∧
      H = 1 + tau + (if C > D then tau * anchor else 0) +
        (if Even d then 1 / 4 else 0) ∧
      contextMass P xC = tau / H ∧
      (C > D → contextMass P xA = tau * anchor / H) ∧
      (∀ j, contextMass P (xHard j) =
        (hardCoordinateCount d : ℝ)⁻¹ / H) ∧
      (Even d → contextMass P xZ = (1 / 4) / H)) ∧
    (∀ j,
      gibbsNormalizer E P (xHard j) =
        1 - 2 * hardP D +
          2 * hardP D * hardT D E.eta (hardPerturbation eps E.eta) *
            Real.cosh (E.eta * hardPerturbation eps E.eta)) ∧
    (∀ x a, ConditionalBernoulliCell E P x a (linearReward P x a))
  -- @realizes e_0,u_j,w_j,z(orthogonal hard-family coordinate vectors)
  -- @realizes x_C,x_A,x_j,x_z(calibration, anchor, hard, optional contexts)
  -- @realizes v(sign vector in {-1,1}^k)
  -- @realizes \pi_{\mathrm{ref}}(every hard-family law uses the specified logging kernel)

-- @node: def:explicit-hard-family
def explicitHardFamily (E : CommonExperiment d 𝒳 𝒜) (C D eps : ℝ)
    (plus minus zero : 𝒜) (xC xA xZ : 𝒳)
    (xHard : Fin (hardCoordinateCount d) → 𝒳)
    (e0 z : Fin d → ℝ)
    (u w : Fin (hardCoordinateCount d) → Fin d → ℝ)
    (family : (Fin (hardCoordinateCount d) → Bool) → BanditLaw E) :
    Set (BanditLaw E) :=
  {P | Function.Injective family ∧
    (∀ v, HardFamilyBlueprint E (family v) C D eps v
      plus minus zero xC xA xZ xHard e0 z u w) ∧
    ∃ v, P = family v}
  -- @realizes \mathcal H_{d,C,D,\eta,\epsilon}(2^k sign-indexed paired-Bernoulli family)
  -- @realizes Z(hard-context Gibbs normalizer induced by blueprint)

end CausalSmith.Stat.ReverseKLTwoCoverage
