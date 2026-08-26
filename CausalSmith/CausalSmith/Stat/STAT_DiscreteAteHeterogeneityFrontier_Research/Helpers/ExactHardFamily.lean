/- Extracting an estimator-wise hard family from exact binary minimax risk. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.ExactHomogeneityLower

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Set

private abbrev BinObs := CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs

/-- If [the sample is nonempty](hyp:_hn) and [the alphabet is nonempty](hyp:hd) and [the overlap
  constant is positive](hyp:he0) and [the overlap constant is below one half](hyp:he1) and [the
  logarithmic scale satisfies its stated bound](hyp:hL), [any level strictly below the exact
  binary minimax risk is attained as a lower bound against every measurable estimator by some
  exact source law](goal). -/
-- @node: binaryExactMinimaxRisk_hard_family_of_lt
lemma binaryExactMinimaxRisk_hard_family_of_lt {n d : ℕ} {epsilon L : ℝ}
    (_hn : 0 < n) (hd : 0 < d) (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hL : L < binaryExactMinimaxRisk n d epsilon) :
    ∀ est : (Fin n → BinObs d) → ℝ, Measurable est →
      ∃ P : BinaryExactLaw n d epsilon,
        L ≤ CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨P0, _htau0, _hv0, _hP0⟩ :=
    endpoint_null_exact (n := n) hd he0 he1
  letI : Nonempty (BinaryExactLaw n d epsilon) := ⟨P0⟩
  intro est hest
  let est' : {f : (Fin n → BinObs d) → ℝ // Measurable f} := ⟨est, hest⟩
  have hb : BddAbove (Set.range (fun P : BinaryExactLaw n d epsilon ↦
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
        est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1))) := by
    refine ⟨((∑ sample : Fin n → BinObs d, |est sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_le_estimator_abs_sum_bound
      P.1 P.2.1 est
  have hbelow : BddBelow (Set.range (fun e : {f : (Fin n → BinObs d) → ℝ //
      Measurable f} ↦ ⨆ P : BinaryExactLaw n d epsilon,
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          e.1 (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨e, rfl⟩
    have hbe : BddAbove (Set.range (fun P : BinaryExactLaw n d epsilon ↦
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          e.1 (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1))) := by
      refine ⟨((∑ sample : Fin n → BinObs d, |e.1 sample|) + 1) ^ 2, ?_⟩
      rintro _ ⟨P, rfl⟩
      exact CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse_le_estimator_abs_sum_bound
        P.1 P.2.1 e.1
    have hmse0 : 0 ≤ CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P0.1 n)
        e.1 (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P0.1) := by
      unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
      exact integral_nonneg fun _ => sq_nonneg _
    exact hmse0.trans (le_ciSup hbe P0)
  have hinf : binaryExactMinimaxRisk n d epsilon ≤
      ⨆ P : BinaryExactLaw n d epsilon,
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
          (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
          est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) := by
    unfold binaryExactMinimaxRisk
    exact ciInf_le hbelow est'
  have hsup : L < ⨆ P : BinaryExactLaw n d epsilon,
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.mse
        (CausalSmith.Stat.DiscreteAteMinimaxLoggap.productLaw P.1 n)
        est (CausalSmith.Stat.DiscreteAteMinimaxLoggap.ateFunctional P.1) :=
    hL.trans_le hinf
  obtain ⟨P, hLP⟩ := (lt_ciSup_iff hb).mp hsup
  exact ⟨P, hLP.le⟩

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
