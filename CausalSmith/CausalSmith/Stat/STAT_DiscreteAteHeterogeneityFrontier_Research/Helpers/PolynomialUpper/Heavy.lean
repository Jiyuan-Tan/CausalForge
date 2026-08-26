/- Heavy-cell and fallback interfaces for the polynomial program. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.LightVariance
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCellMoments
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.PilotSandwich

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

/-- The cell aggregates available after the single pass through the sample.
No raw observation is retained by the post-aggregation evaluator. -/
structure PolynomialCellAggregate (d : ℕ) where
  pilot : Fin d → ℕ
  count : Bool → Fin d → ℕ
  outcomeSum : Bool → Fin d → ℝ

/-- The concrete aggregation pass used by the polynomial estimator. -/
noncomputable def aggregatePolynomialSample {n d : ℕ}
    (sample : Fin n → Obs d) : PolynomialCellAggregate d where
  pilot := pilotCount sample
  count := fun a k => estimationArmCount sample a k
  outcomeSum := fun a k => estimationArmSum sample a k

/-- A small executable arithmetic language over the aggregated cell table.
Its only inputs are counts and outcome sums; loops are represented explicitly
by finite sums, so their arithmetic cost is determined by syntax. -/
inductive AggregatedArithmeticProgram (d : ℕ) where
  | const (x : ℝ)
  | pilot (k : Fin d)
  | count (a : Bool) (k : Fin d)
  | outcomeSum (a : Bool) (k : Fin d)
  | add (p q : AggregatedArithmeticProgram d)
  | sub (p q : AggregatedArithmeticProgram d)
  | mul (p q : AggregatedArithmeticProgram d)
  | div (p q : AggregatedArithmeticProgram d)
  | minimum (p q : AggregatedArithmeticProgram d)
  | maximum (p q : AggregatedArithmeticProgram d)
  | iteLt (p q yes no : AggregatedArithmeticProgram d)
  | sumCells (body : Fin d → AggregatedArithmeticProgram d)
  | sumTerms (r : ℕ) (body : Fin r → AggregatedArithmeticProgram d)
  | armDescFactorial (a : Bool) (k : Fin d) (offset order : ℕ)
  | cellSub (k : Fin d) (offset : ℕ)

/-- Operational semantics of the post-aggregation arithmetic language. -/
noncomputable def AggregatedArithmeticProgram.eval {d : ℕ}
    (input : PolynomialCellAggregate d) : AggregatedArithmeticProgram d → ℝ
  | .const x => x
  | .pilot k => input.pilot k
  | .count a k => input.count a k
  | .outcomeSum a k => input.outcomeSum a k
  | .add p q => p.eval input + q.eval input
  | .sub p q => p.eval input - q.eval input
  | .mul p q => p.eval input * q.eval input
  | .div p q => p.eval input / q.eval input
  | .minimum p q => min (p.eval input) (q.eval input)
  | .maximum p q => max (p.eval input) (q.eval input)
  | .iteLt p q yes no => if p.eval input < q.eval input then yes.eval input else no.eval input
  | .sumCells body => ∑ k, (body k).eval input
  | .sumTerms _ body => ∑ j, (body j).eval input
  | .armDescFactorial a k offset order =>
      ((input.count a k - offset).descFactorial order : ℕ)
  | .cellSub k offset =>
      ((input.count false k + input.count true k - offset : ℕ) : ℝ)

/-- Structural arithmetic cost of an executable program.  Input reads and
constants are free; every arithmetic/comparison node and every finite-sum
accumulation is charged. -/
def AggregatedArithmeticProgram.operationCount {d : ℕ} :
    AggregatedArithmeticProgram d → ℕ
  | .const _ | .pilot _ | .count _ _ | .outcomeSum _ _ => 0
  | .add p q | .sub p q | .mul p q | .div p q | .minimum p q | .maximum p q =>
      1 + p.operationCount + q.operationCount
  | .iteLt p q yes no =>
      1 + p.operationCount + q.operationCount +
        max yes.operationCount no.operationCount
  | .sumCells body => d + ∑ k, (body k).operationCount
  | .sumTerms r body => r + ∑ j, (body j).operationCount
  | .armDescFactorial _ _ _ order => order
  | .cellSub _ _ => 1

/-- A genuine post-aggregation program certificate: executing its syntax on the
actual aggregate table computes the handle-indexed estimator for every sample. -/
structure AggregatedPolynomialProgram (n d : ℕ) (handle : PolynomialHandle) (M : ℝ) where
  code : AggregatedArithmeticProgram d
  computesEstimator : ∀ sample : Fin n → Obs d,
    code.eval (aggregatePolynomialSample sample) = polyEstimator handle M sample

/-- The proof-local numerical budget used to certify the concrete program. -/
noncomputable def polynomialOperationBudget (n d : ℕ) : ℕ :=
  128 * (d + 1) * (polynomialDegree n + 1) ^ 2

/-- Internal finite-sample strengthening with the proof's explicit numerical
constant.  This is not the public complexity claim. -/
def PolynomialExactComplexityCertificate (n d : ℕ)
    (handle : PolynomialHandle) (M : ℝ) : Prop :=
  ∃ program : AggregatedPolynomialProgram n d handle M,
    program.code.operationCount ≤ polynomialOperationBudget n d

/-- The estimator family has post-aggregation arithmetic complexity
`O(d K²)`, with one constant uniform in the sample size, alphabet size, and
outcome scale. -/
def PolynomialComplexityBound (handle : PolynomialHandle) : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ n d : ℕ, ∀ M : ℝ,
      ∃ program : AggregatedPolynomialProgram n d handle M,
        program.code.operationCount ≤
          C * (d + 1) * (polynomialDegree n + 1) ^ 2

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
