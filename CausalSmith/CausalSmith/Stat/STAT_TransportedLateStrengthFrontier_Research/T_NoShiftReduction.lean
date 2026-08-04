/-
# No-shift reduction
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_CompactCausalRange
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_FixedGeometryFrontier
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_OracleScoreInversionAttainment

set_option linter.style.longLine false

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory
open scoped Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: prop:no-shift-reduction
/-- If the transport weight is one, the target and source covariate laws agree,
Kish dispersion is one, and effective strength reduces to `n μ_n²`.  The
conditional frontier is therefore the compact single-population weak-ratio
frontier. -/
theorem no_shift_reduction
    (N k : ℕ → ℕ) (c epsilon alpha : ℝ) (g : Geometry 𝒳)
    (hc : 0 < c)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1)
      -- @realizes \alpha(noncoverage in (0,1))
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
      -- @realizes N_n(N_n/n→c)
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ =>
      (k n : ℝ) / Real.sqrt n) atTop (𝓝 0))
      -- @realizes k_n(positive, diverging, and o(√n))
    (hg : AdmissibleGeometry g k epsilon)
    (hw : ∀ n, g.weight n =ᵐ[g.sourceX n] fun _ => 1) :
    (∀ n, geometryKish g n = 1 ∧ g.targetX n = g.sourceX n) ∧
    (∀ (P : TransportedArray 𝒳) n,
      fixedGeometrySlice P g N k c epsilon n →
      effectiveStrength P n =
        (n : ℝ) * transportedFirstStage P n ^ 2) ∧
    (∀ (t0 : ℝ) (ht0 : 0 < t0), -- @realizes t_0(positive frontier threshold)
      let Lalpha := Real.sqrt (8 / (alpha * epsilon ^ 2))
      let calpha := 3 * (1 - alpha) ^ 2 / 16
      let Calpha := max 2 (4 * Lalpha + 8 / epsilon ^ 2)
      calpha * min 1 (t0 ^ (-1 / 2 : ℝ)) ≤
        fixedGeometryValue N k c epsilon alpha ⟨g, hg⟩ ⟨t0, ht0⟩ ∧
      fixedGeometryValue N k c epsilon alpha ⟨g, hg⟩ ⟨t0, ht0⟩ ≤
        Calpha * min 1 (t0 ^ (-1 / 2 : ℝ))) := by
  have hg' := hg
  rcases hg' with ⟨hSourceProb, hTargetProb, heps0, heps1, hprop,
    hweight, hweightMean, hweightSecond, hchange⟩
  have hGeom :
      ∀ n, geometryKish g n = 1 ∧ g.targetX n = g.sourceX n := by
    intro n
    letI := hSourceProb n
    constructor
    · rw [geometryKish]
      calc
        ∫ x, g.weight n x ^ 2 ∂g.sourceX n =
            ∫ _x, (1 : ℝ) ∂g.sourceX n := by
              apply integral_congr_ae
              filter_upwards [hw n] with x hx
              simp [hx]
        _ = 1 := by simp
    · ext A hA
      rw [hchange n A hA]
      have hrestr :
          g.weight n =ᵐ[(g.sourceX n).restrict A] fun _ => 1 :=
        ae_restrict_of_ae (hw n)
      rw [integral_congr_ae hrestr]
      simp [measureReal_def]
  refine ⟨hGeom, ?_, ?_⟩
  · intro P n hslice
    have hkish : kishDispersion P n = geometryKish g n := by
      have hwP := hslice.2.2.2.1
      rw [hslice.2.1] at hwP
      rw [kishDispersion, geometryKish, hslice.2.1]
      apply integral_congr_ae
      filter_upwards [hwP] with x hx
      rw [hx]
    rw [effectiveStrength, hkish, (hGeom n).1]
    ring
  · intro t0 ht0
    apply fixed_geometry_frontier N k c epsilon alpha g hc hN hkPos
      hkInf hkRoot hepsilon hg
    · intro n P hP
      exact hP.1.twoSampleArray
    · intro n P hP
      exact hP.1.instrumentOverlap
    · intro n P hP
      exact hP.1.weightEnvelope
    · intro n P hP
      exact hP.1.weightSecondMoment
    · intro n P hP
      exact hP.1.degradingArray
    · exact halpha

end CausalSmith.Stat.TransportedLateStrengthFrontier
