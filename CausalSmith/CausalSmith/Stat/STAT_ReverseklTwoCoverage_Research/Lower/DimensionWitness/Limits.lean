import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitnessDefs
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitness.Risk

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped Topology

lemma dw_dimensionIndex_coe_tendsto :
    Filter.Tendsto (fun k : DimensionIndex => k.1)
      Filter.atTop Filter.atTop := by
  have hmap :
      Filter.map ((↑) : DimensionIndex → ℕ) Filter.atTop =
        Filter.atTop :=
    Filter.map_val_atTop_of_Ici_subset (a := 4) (by
      intro n hn
      exact hn)
  exact hmap.le

lemma dw_inverse_dimension_limit :
    Filter.Tendsto (fun k : DimensionIndex => ((k.1 : ℝ)⁻¹))
      Filter.atTop (nhds 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp dw_dimensionIndex_coe_tendsto)

lemma dw_linear_dimension_limit :
    Filter.Tendsto
      (fun k : DimensionIndex =>
        (k.1 : ℝ) * dimensionWitnessD / (k.1 ^ 2 : ℕ))
      Filter.atTop (nhds 0) := by
  have h :=
    (tendsto_const_nhds.mul dw_inverse_dimension_limit :
      Filter.Tendsto
        (fun k : DimensionIndex => dimensionWitnessD * ((k.1 : ℝ)⁻¹))
        Filter.atTop (nhds (dimensionWitnessD * 0)))
  simp only [mul_zero] at h
  convert h using 1
  funext k
  have hk0 : (k.1 : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : k.1 ≠ 0)
  simp only [dimensionWitnessD]
  push_cast
  field_simp

lemma dw_sqrt_dimension_limit :
    Filter.Tendsto
      (fun k : DimensionIndex =>
        Real.sqrt ((k.1 : ℝ) * dimensionWitnessD / (k.1 ^ 2 : ℕ)))
      Filter.atTop (nhds 0) := by
  convert Real.continuous_sqrt.continuousAt.tendsto.comp
    dw_linear_dimension_limit using 1
  simp only [Real.sqrt_zero]

end CausalSmith.Stat.ReverseKLTwoCoverage
