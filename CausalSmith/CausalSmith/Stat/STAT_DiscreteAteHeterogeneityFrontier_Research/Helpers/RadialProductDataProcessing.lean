import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.LowerTransfer
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmCountSufficiency
import Causalean.Stat.Minimax.MarkovKernelTransport

/-!
# Product total-variation contraction for the radial channel

This module lifts a one-record common Markov-kernel identity to the finite
product experiments and records the resulting data-processing inequality.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

-- @node: radialProduct_tvDist_le_of_kernel
/-- If [the first target law is produced by the channel](hyp:hQ0) and [the second target law is
  produced by the channel](hyp:hQ1), [a common one-record Markov channel contracts total variation
  after taking the finite i.i.d. product experiment](goal). -/
lemma radialProduct_tvDist_le_of_kernel {n m d : ℕ}
    (P0 P1 : CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw m)
    (Q0 Q1 : RealLaw d)
    (K : Kernel (CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs m) (Obs d))
    [IsMarkovKernel K]
    (hQ0 : Q0.observedLaw = K ∘ₘ
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P0)
    (hQ1 : Q1.observedLaw = K ∘ₘ
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P1) :
    Causalean.Stat.tvDist (productLaw n Q0) (productLaw n Q1) ≤
      Causalean.Stat.tvDist
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0 n)
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P1 n) := by
  let Kn := Causalean.Stat.finProductKernel n K
  have hprod (P : CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw m) :
      Kn ∘ₘ CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P n =
        Measure.pi (fun _ : Fin n =>
          K ∘ₘ CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P) := by
    exact Causalean.Stat.finProductKernel_comp_pi n
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P) K
  change Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n => Q0.observedLaw))
      (Measure.pi (fun _ : Fin n => Q1.observedLaw)) ≤
    Causalean.Stat.tvDist
      (Measure.pi (fun _ : Fin n =>
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P0))
      (Measure.pi (fun _ : Fin n =>
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P1))
  rw [hQ0, hQ1, ← hprod P0, ← hprod P1]
  exact
    CausalSmith.Stat.DiscreteAteMinimaxLoggap.tvDist_bind_common_kernel_le
      _ _ Kn Kn.measurable (fun _ => inferInstance)

-- @node: radialDataProcessingCertificate_of_kernel
/-- If [the target law is the specified transported law](hyp:hQ), [the pointwise observed-law
  identity for a common radial kernel packages directly as the handle's product data-processing
  certificate](goal). -/
lemma radialDataProcessingCertificate_of_kernel {n d : ℕ}
    {epsilon M sigma : ℝ}
    (H : LeastFavorableHandle n d epsilon M sigma)
    (K : Kernel
      (CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs H.radialCap) (Obs d))
    [IsMarkovKernel K]
    (hQ : ∀ P ∈ H.radialSource,
      (H.radialEmbedding P).observedLaw =
        K ∘ₘ CausalSmith.Stat.DiscreteAteMinimaxLoggap.obsLaw P.1) :
    DataProcessingCertificate H := by
  intro P0 hP0 P1 hP1
  exact radialProduct_tvDist_le_of_kernel P0.1 P1.1
    (H.radialEmbedding P0) (H.radialEmbedding P1) K
    (hQ P0 hP0) (hQ P1 hP1)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
