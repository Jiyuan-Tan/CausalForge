/- Cited interfaces used by the real-outcome frontier development. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Basic
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

private abbrev BinLaw :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw
private abbrev BinObs :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

-- @env: S2
variable (binary_n binary_d : ℕ) (binary_epsilon : ℝ)
variable (binaryP : BinLaw binary_d)
  -- @realizes n(binary source sample size) @realizes d(binary source alphabet size)
  -- @realizes epsilon(binary source overlap)

/-- The uniform-mass, exactly homogeneous binary source class. -/
def BinaryExactHomogeneous {d : ℕ} (epsilon : ℝ) (P : BinLaw d) : Prop :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P ∧
  (∀ k, CausalSmith.Stat.DiscreteAteMinimaxLoggap.cellMass P k = 1 / (d : ℝ)) ∧
  (∀ k l,
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k =
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true l -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false l)

/-- Binary laws in the cited exact-homogeneity source experiment. -/
def BinaryExactLaw (_n d : ℕ) (epsilon : ℝ) :=
  {P : BinLaw d // BinaryExactHomogeneous epsilon P}

/-- Exact-homogeneity source minimax risk. -/
noncomputable def binaryExactMinimaxRisk (n d : ℕ) (epsilon : ℝ) : ℝ :=
  ⨅ est : {f : (Fin n → BinObs d) → ℝ // Measurable f},
    ⨆ P : BinaryExactLaw n d epsilon,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
        est.1 (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1)

/-- **Cited gate (Zeng, Balakrishnan, Han, and Kennedy, 2024, revised 2026).**
Source: arXiv:2405.00118v3, Theorem 4 and Appendix C.8.  The fixed-sample
uniform-mass exactly homogeneous binary experiment has minimax risk at least a
constant times `1/n+d/n^2` throughout its source range. -/
def ZengBinaryExactHomogeneityLower (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 / 2 →
    ∃ a_epsilon b_epsilon : ℝ, ∃ N_epsilon : ℕ,
      0 < a_epsilon ∧ 0 < b_epsilon ∧
      ∀ n d : ℕ, 0 < d → N_epsilon ≤ n →
        (d : ℝ) ≤ b_epsilon * (n : ℝ) ^ 2 →
        a_epsilon * (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) ≤
          binaryExactMinimaxRisk n d epsilon

/-- Re-export of the cited fixed-sample one-arm lower-bound interface from the
binary source development (Zeng et al., arXiv:2405.00118v3, Theorem 2,
Appendix C.5, Lemma 4, and Appendix D.2). -/
abbrev ZengOneArmMinimaxLower :=
  CausalSmith.Stat.DiscreteAteMinimaxLoggap.ZengOneArmMinimaxLower

/-- **Cited gate (Zeng, Balakrishnan, Han, and Kennedy, 2024, revised 2026).**
Source: arXiv:2405.00118v3, Lemma 1 and Appendix C.7, equation (26) and the
reciprocal-occupancy display.  The constants are quantified before the model
parameters and hence depend only on `epsilon`. -/
def ZengUsableOccupancyReciprocal (epsilon : ℝ) : Prop :=
  ∃ b_epsilon B_epsilon : ℝ,
    0 < b_epsilon ∧ 0 < B_epsilon ∧
    ∀ n d : ℕ, ∀ M sigma : ℝ, ∀ P : ModelClass d epsilon M sigma,
      realMass (productLaw n P.law) {s | usableTotal s = 0} ≤
          2 * Real.exp (-b_epsilon * (n : ℝ) ^ 2 / (max n d : ℕ)) ∧
      (∫ s, (if 0 < usableTotal s then (1 : ℝ) / usableTotal s else 0)
          ∂productLaw n P.law) ≤
        B_epsilon * ((max n d : ℕ) / (n : ℝ) ^ 2 +
          Real.exp (-b_epsilon * (n : ℝ) ^ 2 / (max n d : ℕ)))

private def binArmCount {n d : ℕ} (sample : Fin n → BinObs d)
    (a : Bool) (k : Fin d) : ℕ :=
  (Finset.univ.filter fun i => (sample i).1 = k ∧ (sample i).2.1 = a).card

private noncomputable def binArmMean {n d : ℕ} (sample : Fin n → BinObs d)
    (a : Bool) (k : Fin d) : ℝ :=
  if 0 < binArmCount sample a k then
    (∑ i : Fin n, if (sample i).1 = k ∧ (sample i).2.1 = a ∧ (sample i).2.2
      then (1 : ℝ) else 0) / binArmCount sample a k
  else 0

/-- The equation-(13) occupancy-weighted binary estimator, totalized at zero. -/
private noncomputable def sourceCollisionEstimator {n d : ℕ}
    (sample : Fin n → BinObs d) : ℝ :=
  let denom := ∑ k : Fin d,
    if 0 < binArmCount sample false k ∧ 0 < binArmCount sample true k then
      binArmCount sample false k + binArmCount sample true k else 0
  if 0 < denom then
    (∑ k : Fin d,
      if 0 < binArmCount sample false k ∧ 0 < binArmCount sample true k then
        (binArmCount sample false k + binArmCount sample true k : ℕ) *
          (binArmMean sample true k - binArmMean sample false k)
      else 0) / denom
  else 0

/-- `sigma_bin` is the actual maximal binary treatment-effect heterogeneity,
not merely an arbitrary envelope. -/
def BinaryMaximalHeterogeneity {d : ℕ} (P : BinLaw d)
    (sigma_bin : ℝ) : Prop :=
  0 ≤ sigma_bin ∧
  (∀ k,
    |(CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k) -
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P| ≤ sigma_bin) ∧
  ∃ k,
    |(CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k) -
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P| = sigma_bin

-- @node: lem:zeng-binary-collision-upper
/-- **Cited gate (Zeng, Balakrishnan, Han, and Kennedy, 2024, revised 2026).**
Source: arXiv:2405.00118v3, Theorem 3 on page 11 and Appendix C.7.  This is the
published bias/variance guarantee for their equation-(13) estimator. -/
def ZengBinaryCollisionUpper (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 / 2 →
  ∃ C_epsilon b_epsilon : ℝ, 0 < C_epsilon ∧ 0 < b_epsilon ∧
    ∀ n d : ℕ, 0 < d → ∀ P : BinLaw d, ∀ sigma_bin : ℝ,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P →
      BinaryMaximalHeterogeneity P sigma_bin →
      |(∫ s, sourceCollisionEstimator s
          ∂CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P n) -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P| ≤
          sigma_bin + 2 * Real.exp (-b_epsilon * (n : ℝ) ^ 2 / (max n d : ℕ)) ∧
      variance sourceCollisionEstimator
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P n) ≤
        C_epsilon * (sigma_bin ^ 2 + (d : ℝ) / (n : ℝ) ^ 2 + 1 / (n : ℝ))

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
