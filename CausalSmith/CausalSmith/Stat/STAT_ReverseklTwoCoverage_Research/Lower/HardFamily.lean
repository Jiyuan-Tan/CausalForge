import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.HardFamilyCore
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Terminal

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

-- @node: thm:same-shell-lower
theorem same_shell_lower :
    ∀ eta C D : ℝ, 0 < eta → 1 < D → D ≤ C →
      C < Real.exp eta → 2 * D - 1 < Real.exp eta →
      ∃ eps1 c : ℝ, 0 < eps1 ∧ 0 < c ∧
        ∀ d : ℕ, 4 ≤ d →
          ∃ (mX mA : ℕ) (E : CommonExperiment d (Fin mX) (Fin mA)),
            E.eta = eta ∧
            0 < hardScale D eta ∧
            eps1 ≤ hardAccuracyRange C D eta ∧
            ∃ (plus minus zero : Fin mA) (xC xA xZ : Fin mX)
              (xHard : Fin (hardCoordinateCount d) → Fin mX)
              (e0 z : Fin d → ℝ)
              (u w : Fin (hardCoordinateCount d) → Fin d → ℝ),
              ∀ eps, ∀ heps : 0 < eps, ∀ heps_one : eps < 1, eps ≤ eps1 →
                ∃ family :
                    (Fin (hardCoordinateCount d) → Bool) → BanditLaw E,
                  (explicitHardFamily E C D eps plus minus zero xC xA xZ
                    xHard e0 z u w family).Nonempty ∧
                  explicitHardFamily E C D eps plus minus zero xC xA xZ
                    xHard e0 z u w family ⊆ exactShellSet E C D ∧
                  (↑⌈c * (d : ℝ) * D * eta / eps⌉₊ : WithTop ℕ) ≤
                    sampleComplexity E eps C D heps heps_one :=
  same_shell_lower_disposable_proof

/-- Shared-feature, non-tabular property of the five-dimensional blueprint. -/
def SharedFeatureWitness5
    (E : CommonExperiment 5 𝒳 𝒜) (P : BanditLaw E)
    (C D eps : ℝ) : Prop :=
  ∃ (plus minus zero : 𝒜) (xC xA xZ : 𝒳)
      (xHard : Fin 2 → 𝒳) (e0 z : Fin 5 → ℝ)
      (basisU basisW : Fin 2 → Fin 5 → ℝ) (v : Fin 2 → Bool),
    HardFamilyBlueprint E P C D eps v plus minus zero xC xA xZ
      xHard e0 z basisU basisW ∧
    NotCanonicalTabularFeature E ∧
    ∀ j : Fin 2,
      ∃ (plus minus : 𝒜) (x : 𝒳) (u w : Fin 5 → ℝ),
        plus ≠ minus ∧
        dotProduct u u = 1 ∧ dotProduct w w = 1 ∧ dotProduct u w = 0 ∧
        (∀ i, E.feature x plus i = (u i + w i) / Real.sqrt 2) ∧
        (∀ i, E.feature x minus i = (u i - w i) / Real.sqrt 2) ∧
        dotProduct P.theta u =
          Real.sqrt 2 * hardBeta D E.eta (hardPerturbation eps E.eta) ∧
        dotProduct P.theta w =
          Real.sqrt 2 * hardPerturbation eps E.eta *
            (if v j then 1 else -1)

-- @node: prop:shared-feature-witness
theorem shared_feature_witness
    (E : CommonExperiment 5 𝒳 𝒜) (C D eps : ℝ)
    (plus minus zero : 𝒜) (xC xA xZ : 𝒳)
    (xHard : Fin 2 → 𝒳) (e0 z : Fin 5 → ℝ)
    (u w : Fin 2 → Fin 5 → ℝ)
    (family : (Fin 2 → Bool) → BanditLaw E)
    (hregion : (C, D) ∈ hardRegion 5 E.eta)
    (heps : 0 < eps ∧ eps ≤ hardAccuracyRange C D E.eta) :
    ∀ P ∈ explicitHardFamily E C D eps plus minus zero xC xA xZ
        xHard e0 z u w family,
      SharedFeatureWitness5 E P C D eps := by
  intro P hP
  rcases hP with ⟨hfamily_inj, hblue_all, v, rfl⟩
  have hblue := hblue_all v
  unfold HardFamilyBlueprint at hblue
  obtain ⟨href, hr, hepos, hele, hthree, hxinj, hxdist, hCA, hZ, hctx,
    hfeatCplus, hfeatCminus, hrefCplus, hrefminus, hrefzero, hrefsum,
    hfeatplus, hfeatminus, hfeatzero, hrefhard, horth, hcross, he0norm,
    heven, hdecomp, hthetae0, hthetau, hthetaw, hpert, hfeatureA,
    hmass, hnorm, hbern⟩ := hblue
  refine ⟨plus, minus, zero, xC, xA, xZ, xHard, e0, z, u, w, v, ?_, ?_, ?_⟩
  · exact hblue_all v
  · intro htab
    rcases htab with ⟨coord, hcoord, hcoord_feat⟩
    have hcard : Fintype.card (𝒳 × 𝒜) = 5 := by
      calc
        Fintype.card (𝒳 × 𝒜) = Fintype.card (Fin 5) :=
          Fintype.card_congr (Equiv.ofBijective _ hcoord)
        _ = 5 := Fintype.card_fin 5
    have hA : 3 ≤ Fintype.card 𝒜 := by
      have hsub : ({plus, minus, zero} : Finset 𝒜) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hc : ({plus, minus, zero} : Finset 𝒜).card = 3 := by
        rcases hthree with ⟨hpm, hpz, hmz, _⟩
        simp [hpm, hpz, hmz]
      rw [← hc]
      simpa using Finset.card_le_card hsub
    have hX : 3 ≤ Fintype.card 𝒳 := by
      have hxinj2 : Function.Injective xHard := by
        simpa [hardCoordinateCount] using hxinj
      have hxdist2 : ∀ j : Fin 2, xHard j ≠ xC := by
        simpa [hardCoordinateCount] using fun j => (hxdist j).1
      have h0 : xHard 0 ≠ xC := hxdist2 0
      have h1 : xHard 1 ≠ xC := hxdist2 1
      have h01 : xHard 0 ≠ xHard 1 := by
        exact fun h => Fin.zero_ne_one (hxinj2 h)
      have hsub : ({xC, xHard 0, xHard 1} : Finset 𝒳) ⊆ Finset.univ :=
        Finset.subset_univ _
      have hc : ({xC, xHard 0, xHard 1} : Finset 𝒳).card = 3 := by
        simp [h01, Ne.symm h0, Ne.symm h1]
      rw [← hc]
      simpa using Finset.card_le_card hsub
    have hprod : Fintype.card 𝒳 * Fintype.card 𝒜 = 5 := by
      simpa only [Fintype.card_prod] using hcard
    have hnine : 9 ≤ Fintype.card 𝒳 * Fintype.card 𝒜 := by
      calc
        9 = 3 * 3 := by norm_num
        _ ≤ Fintype.card 𝒳 * Fintype.card 𝒜 := Nat.mul_le_mul hX hA
    omega
  · intro j
    have horth2 : ∀ j : Fin 2,
        dotProduct e0 (u j) = 0 ∧ dotProduct e0 (w j) = 0 ∧
        dotProduct (u j) (u j) = 1 ∧ dotProduct (w j) (w j) = 1 ∧
        dotProduct (u j) (w j) = 0 := by
      simpa [hardCoordinateCount] using horth
    have hfeatplus2 : ∀ j : Fin 2, ∀ i,
        E.feature (xHard j) plus i = (u j i + w j i) / Real.sqrt 2 := by
      simpa [hardCoordinateCount] using hfeatplus
    have hfeatminus2 : ∀ j : Fin 2, ∀ i,
        E.feature (xHard j) minus i = (u j i - w j i) / Real.sqrt 2 := by
      simpa [hardCoordinateCount] using hfeatminus
    have hthetau2 : ∀ j : Fin 2, dotProduct (family v).theta (u j) =
        Real.sqrt 2 * hardBeta D E.eta (hardPerturbation eps E.eta) := by
      simpa [hardCoordinateCount] using hthetau
    have hthetaw2 : ∀ j : Fin 2, dotProduct (family v).theta (w j) =
        Real.sqrt 2 * hardPerturbation eps E.eta *
          (if v j then 1 else -1) := by
      simpa [hardCoordinateCount] using hthetaw
    refine ⟨plus, minus, xHard j, u j, w j, hthree.1,
      (horth2 j).2.2.1, (horth2 j).2.2.2.1, (horth2 j).2.2.2.2,
      hfeatplus2 j, hfeatminus2 j, hthetau2 j, hthetaw2 j⟩

end CausalSmith.Stat.ReverseKLTwoCoverage
