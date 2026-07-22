/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP CATE minimax: the certified (non-matching) bracket and the β=γ sharp corollary

Stage-2 scaffold. Assembly of the causal lower endpoint
(`lem:causal_oracle_private_lower_bound`) and the private local-polynomial upper
endpoint (`lem:private_local_polynomial_upper_bound`) into the certified two-sided
bracket `lem:certified_private_cate_bracket`
(`c{n^{-γ/(2γ+d)} ∨ (n ε_n)^{-γ/(γ+d)}} ≤ R_n^{DP} ≤ C{n^{-β/(2β+d)} ∨ (n ε_n)^{-β/(β+d)}}`).
The bracket is NON-MATCHING in general and sharp only at `β = γ`.

At `β = γ` the endpoints coincide: `lem:equal_smoothness_sharp_private_rate`
(co-located here, SYNC-BACK from the plan's `RateAlgebra.lean` to avoid an import
cycle with `certified_private_cate_bracket`), and `lem:equal_smoothness_regression_inheritance`
records that this sharp rate is INHERITED from one-server private pointwise
regression, not a new causal exponent.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateUpperEndpoint
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CausalLowerBound
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RateAlgebra
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.EqualSmoothnessAlgebra
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RegressionEmbedding

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat

-- @node: lem:certified-private-cate-bracket
/-- **Certified (non-matching) private CATE bracket (crux).** For constants
`0 < c < C` and all sufficiently large `n`,
`c{n^{-γ/(2γ+d)} ∨ (n ε_n)^{-γ/(γ+d)}} ≤ R_n^{DP} ≤ C{n^{-β/(2β+d)} ∨ (n ε_n)^{-β/(β+d)}}`.
The endpoints are NON-MATCHING in general (γ-branch lower vs β-branch upper); they
coincide only at `β = γ`. -/
lemma certified_private_cate_bracket {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hne : ModelNonempty d alpha beta gamma L e0 f0 f1 r0 x0)
    (hd : 0 < d) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
      ∀ᶠ n : ℕ in Filter.atTop,
      c * max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
            (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ)))))
          ≤ dpMinimaxRisk n (eps n) (del n)
              (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
        ∧ dpMinimaxRisk n (eps n) (del n)
              (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
          ≤ C * max ((n : ℝ) ^ (-(beta / (2 * beta + (d : ℝ)))))
              (((n : ℝ) * eps n) ^ (-(beta / (beta + (d : ℝ))))) := by
  obtain ⟨c, cB, B, P0, hc, hcB, hP0, hiidP0, hrangeP0, hBdiff, hBzero,
      hBbounds, hBsupp, hmu0, hmu1, hpi, hlower⟩ :=
    causal_oracle_private_lower_bound alpha beta gamma L e0 f0 f1 r0 x0 hreg hne
  obtain ⟨C, hC, hupper⟩ :=
    private_local_polynomial_upper_bound alpha beta gamma L e0 f0 f1 r0 x0 hreg hd
  refine ⟨c, C + c, hc, ?_, ?_⟩
  · linarith
  · intro eps del hbudget
    filter_upwards [hlower eps del hbudget, hupper eps del hbudget] with n hnlow hnup
    refine ⟨hnlow.2, hnup.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc.le)
      ((Real.rpow_nonneg (Nat.cast_nonneg n) _).trans (le_max_left _ _))

-- @node: lem:equal-smoothness-sharp-private-rate
/-- **β = γ sharp private rate (crux).** If `β = γ`, the bracket endpoints coincide,
so over the full frozen class
`R_n^{DP} ≍ n^{-γ/(2γ+d)} ∨ (n ε_n)^{-γ/(γ+d)} ≍ r_n^{regDP}`, and the KBRW exponent
simplifies to `κ = γ/(2γ+d)`, i.e. `r_n^{CATE} = n^{-γ/(2γ+d)}`.

**Proved crossing boundary (added clauses).** In addition, the privacy budget
`ε_* = n^{-γ/(2γ+d)}` is EXACTLY the order at which the non-private branch
`n^{-γ/(2γ+d)}` and the private branch `(n·e)^{-γ/(γ+d)}` coincide:
`n^{-γ/(2γ+d)} = (n·e)^{-γ/(γ+d)} ⟺ e = n^{-γ/(2γ+d)}`; above that order (`e` larger)
the non-private term is leading (the private term is `≤` it), and below that order
(`e` smaller) the private term is leading (`≥` the non-private term). (SYNC-BACK: the
plan placed this in `RateAlgebra.lean`; it is co-located here with the bracket it
depends on to avoid an import cycle.) -/
lemma equal_smoothness_sharp_private_rate {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hne : ModelNonempty d alpha beta gamma L e0 f0 f1 r0 x0)
    (hbg : beta = gamma)
    (hd : 0 < d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
      ∀ᶠ n : ℕ in Filter.atTop,
      (c * privateRegressionCalibration n r0 gamma d (eps n)
          ≤ dpMinimaxRisk n (eps n) (del n)
              (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
        ∧ dpMinimaxRisk n (eps n) (del n)
              (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
          ≤ C * privateRegressionCalibration n r0 gamma d (eps n))
      ∧ nonprivateCateRate n alpha beta gamma d
          = (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
      -- proved crossing boundary: ε_* = n^{-γ/(2γ+d)} is exactly where the two
      --   branches coincide (n^{-γ/(2γ+d)} = (n·e)^{-γ/(γ+d)} ⟺ e = n^{-γ/(2γ+d)})
      ∧ (∀ e : ℝ, 0 < e →
          ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
              = ((n : ℝ) * e) ^ (-(gamma / (gamma + (d : ℝ))))
            ↔ e = (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))))
      -- above the boundary (e larger): the non-private term is leading (private ≤ it)
      ∧ (∀ e : ℝ, (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))) < e →
          ((n : ℝ) * e) ^ (-(gamma / (gamma + (d : ℝ))))
            ≤ (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
      -- below the boundary (e smaller): the private term is leading (≥ non-private)
      ∧ (∀ e : ℝ, 0 < e → e < (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))) →
          (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
            ≤ ((n : ℝ) * e) ^ (-(gamma / (gamma + (d : ℝ))))) := by
  rcases hreg with ⟨halpha, hbeta, hgamma, hL, he0, hf0, hf01, hr0, hx0⟩
  obtain ⟨cb, Cb, hcb, hcbCb, hbracket⟩ :=
    certified_private_cate_bracket alpha beta gamma L e0 f0 f1 r0 x0
      ⟨halpha, hbeta, hgamma, hL, he0, hf0, hf01, hr0, hx0⟩ hne
      hd
  obtain ⟨cr, Cr, hcr, hCr, hcalibration⟩ :=
    private_regression_calibration_algebra r0 gamma hgamma hr0.1
  have hCb : 0 < Cb := hcb.trans hcbCb
  refine ⟨cb / Cr, Cb / cr, div_pos hcb hCr, div_pos hCb hcr, ?_⟩
  intro eps del hbudget
  filter_upwards [hbracket eps del hbudget, hcalibration eps del hbudget,
      Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hnbr hncal hn
  let R := max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
    (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ)))))
  have hscaleLower :
      (cb / Cr) * privateRegressionCalibration n r0 gamma d (eps n) ≤ cb * R := by
    calc
      (cb / Cr) * privateRegressionCalibration n r0 gamma d (eps n)
          ≤ (cb / Cr) * (Cr * R) :=
            mul_le_mul_of_nonneg_left hncal.2 (div_nonneg hcb.le hCr.le)
      _ = cb * R := by field_simp
  have hscaleUpper : Cb * R ≤
      (Cb / cr) * privateRegressionCalibration n r0 gamma d (eps n) := by
    calc
      Cb * R = (Cb / cr) * (cr * R) := by field_simp
      _ ≤ (Cb / cr) * privateRegressionCalibration n r0 gamma d (eps n) :=
        mul_le_mul_of_nonneg_left hncal.1 (div_nonneg hCb.le hcr.le)
  have hnbrUpper :
      dpMinimaxRisk n (eps n) (del n)
          (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0 ≤ Cb * R := by
    simpa [R, hbg] using hnbr.2
  have hrate := nonprivateCateRate_equal_smoothness (d := d) n alpha beta gamma
    halpha hgamma hbg
  have hboundary := equal_smoothness_rate_boundary (d := d) n gamma hgamma hn
  refine ⟨⟨hscaleLower.trans hnbr.1, hnbrUpper.trans hscaleUpper⟩, hrate,
    hboundary.1, hboundary.2.1, hboundary.2.2⟩

-- @node: lem:equal-smoothness-regression-inheritance
/-- **β = γ regression inheritance (crux, interpretive).** When `β = γ`, the sharp
full-class central-DP CATE rate is inherited, AT THE LEVEL OF RATES, from one-server
private pointwise regression: `R_n^{DP} ≍ r_n^{regDP}` with comparison constants
`c, C` depending ONLY on the fixed regularity parameters — hence quantified
OUTERMOST, before the budget sequences `ε_n, δ_n`. The inheritance is witnessed
EXPLICITLY: (upper) an armwise clipped-regression mechanism `M` — a central-DP
probability kernel whose worst-case risk is the differenced armwise private
regressions — and (lower) a causal potential-outcome embedding, a two-point family
with `μ₀ = 0`, `μ₁ = bump`, and constant propensity `e₀`, whose CATE at
`x₀` is the full bump. Overlap and the two-arm structure
affect only constants; this is not a new causal exponent beyond private pointwise
regression. The lower construction fixes its smooth `[0,1]`-valued bump `B`, scale
`cB`, and null law `P0` uniformly before the privacy budgets and sample size. It also
exhibits both the non-private and private alternatives as measurable
regression-to-treated-observation embeddings with the same reduction map and the
same shared control-arm law, so only the treated regression component changes on
either branch; the map also preserves replacement adjacency coordinatewise. -/
lemma equal_smoothness_regression_inheritance {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hne : ModelNonempty d alpha beta gamma L e0 f0 f1 r0 x0)
    (hbg : beta = gamma)
    (hd : 0 < d) :
    ∃ (c C cB : ℝ) (B : (Fin d → ℝ) → ℝ) (P0 : CateLaw d),
      0 < c ∧ 0 < C ∧ 0 < cB ∧
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B ∧
      (∀ u, 0 ≤ B u ∧ B u ≤ 1) ∧ B 0 = 1 ∧
      (∀ u : Fin d → ℝ, (∃ j, 1 < |u j|) → B u = 0) ∧
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P0 ∧
      IidSampling P0 ∧ |P0.mu1 x0 - P0.mu0 x0| ≤ 2 ∧
      (∀ x, P0.mu0 x = 0) ∧ (∀ x, P0.mu1 x = 0) ∧ (∀ x, P0.pi x = e0) ∧
      ∀ (eps del : ℕ → ℝ), PrivacyBudget eps del →
      ∀ᶠ n : ℕ in Filter.atTop,
        -- (upper) armwise clipped-regression mechanism witness: the mechanism is
        -- IDENTIFIED as the clipped DIFFERENCE OF TWO ARMWISE PRIVATE LOCAL-POLY
        -- REGRESSIONS (`IsArmwisePrivatizedLocalPoly`), not an arbitrary clipped
        -- central-DP kernel meeting the rate bound
        (∃ M : (Fin n → CateObs d) → Measure ℝ,
            IsArmwisePrivatizedLocalPoly n beta r0 (eps n) x0 M ∧
            CentralDP n (eps n) (del n) M ∧
            (∀ s, (M s) (Set.Icc (-2 : ℝ) 2)ᶜ = 0) ∧
            (⨆ P : {P : CateLaw d //
                  HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P
                    ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2},
                ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(M s))
                  ∂(Measure.pi fun _ : Fin n => (P.1).dataMeasure))
              ≤ C * privateRegressionCalibration n r0 gamma d (eps n)) ∧
        -- (lower) single-regression causal embedding witness: a SHARED causal null `P0`
        -- and SEPARATE non-private / private alternatives `P1np`, `P1priv` (as in
        -- `causal_oracle_private_lower_bound`). The single pair is SPLIT because no one
        -- alternative can carry BOTH the full regression-calibration separation and the
        -- DP-TV budget (inconsistent at `ε_n = 1`, where the calibration has non-private
        -- order `n^{-γ/(2γ+d)}` while overlap/Hölder interpolation forces the product-TV to
        -- grow): the NON-PRIVATE branch uses product-TV closeness with non-private
        -- separation `≍ n^{-γ/(2γ+d)}`, the PRIVATE branch uses the DP TV-contraction budget
        -- with private separation `≍ (n ε_n)^{-γ/(γ+d)}`. Each alternative is a localized
        -- causal two-point family with SHARED covariate design and a localized γ-Hölder
        -- bump on μ₁ ONLY (μ₀ = 0), so estimating the CATE embeds ONE pointwise-regression
        -- subproblem
        (∃ (hnp hpriv : ℝ) (P1np P1priv : CateLaw d),
            HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P1np ∧
            HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P1priv ∧
            -- GENUINE i.i.d. probability laws with in-range estimand (so the embedded
            -- pairs sit in `dpMinimaxRisk`'s sup domain)
            IidSampling P1np ∧ IidSampling P1priv ∧
            |P1np.mu1 x0 - P1np.mu0 x0| ≤ 2 ∧ |P1priv.mu1 x0 - P1priv.mu0 x0| ≤ 2 ∧
            -- alternatives keep μ₀ = 0, propensity and covariate design unchanged
            (∀ x, P1np.mu0 x = 0) ∧
            (∀ x, P1np.pi x = e0) ∧
            P1np.PX = P0.PX ∧ (∀ x, P1np.px x = P0.px x) ∧
            (∀ x, P1priv.mu0 x = 0) ∧
            (∀ x, P1priv.pi x = e0) ∧
            P1priv.PX = P0.PX ∧ (∀ x, P1priv.px x = P0.px x) ∧
            -- explicit localized γ-Hölder μ₁ bumps (ONLY μ₁ is perturbed)
            0 < hnp ∧ hnp ≤ r0 ∧ 0 < hpriv ∧ hpriv ≤ r0 ∧
            (∀ x, P1np.mu1 x =
              cB * hnp ^ gamma * B (fun j => (x j - x0 j) / hnp)) ∧
            (∀ x, P1priv.mu1 x =
              cB * hpriv ^ gamma * B (fun j => (x j - x0 j) / hpriv)) ∧
            -- the CATE is the full localized bump
            P1np.mu1 x0 - P1np.mu0 x0 =
              cB * hnp ^ gamma * B (fun j => (x0 j - x0 j) / hnp) ∧
            P1priv.mu1 x0 - P1priv.mu0 x0 =
              cB * hpriv ^ gamma * B (fun j => (x0 j - x0 j) / hpriv) ∧
            -- NON-PRIVATE branch: product-TV closeness (`TV(P0^n, P1np^n) ≤ 1/2`) + non-private
            -- separation `≍ n^{-γ/(2γ+d)}` (the non-private endpoint of `r_n^regDP`)
            tvDist (Measure.pi fun _ : Fin n => P0.dataMeasure)
                (Measure.pi fun _ : Fin n => P1np.dataMeasure) ≤ 1 / 2 ∧
            c * (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
                ≤ |(P1np.mu1 x0 - P1np.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| ∧
            -- PRIVATE branch: DP TV-contraction budget (`n{exp ε−1+δ}·TV(P0,P1priv) ≤ 1/2`) +
            -- private separation `≍ (n ε_n)^{-γ/(γ+d)}` (the private endpoint of `r_n^regDP`);
            -- this is the reduction that links the embedded private subproblem to `dpMinimaxRisk`
            (n : ℝ) * (Real.exp (eps n) - 1 + del n)
                * tvDist P0.dataMeasure P1priv.dataMeasure ≤ 1 / 2 ∧
            c * ((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ))))
                ≤ |(P1priv.mu1 x0 - P1priv.mu0 x0) - (P0.mu1 x0 - P0.mu0 x0)| ∧
            -- (EMBEDDING) the causal lower family IS a one-server pointwise-regression experiment
            -- pushed into the TREATED arm. Explicitly: a measurable regression-to-treated-observation
            -- map `Phi`, sending a regression datum `(x, z)` to the treated causal record
            -- `(Y = z, A = 1, X = x)`; regression laws `rho0` (null), `rhonp` (non-private
            -- alternative), and `rho1` (private alternative) sharing the causal covariate design
            -- `P0.PX`, whose pointwise regression functions `E[Z ∣ X]` are respectively the null's
            -- `μ₁ ≡ 0` and the alternatives' localized γ-Hölder bumps `P1np.mu1` and
            -- `P1priv.mu1`; and a SHARED control law `Lctrl` supported on `{A = 0}`.
            -- The three mixture identities exhibit `P0`, `P1np`, and `P1priv` using the SAME
            -- reduction map `Phi` and the SAME `Lctrl` — so ONLY the treated regression component
            -- changes on EITHER branch: estimating the CATE CONTAINS exactly one pointwise-regression
            -- subproblem, and the constant propensity `e₀` only thins the informative observations
            -- by a fixed factor (a constant, not a rate).
            -- Finally `Phi` acts COORDINATEWISE on samples, so it PRESERVES replacement adjacency —
            -- hence a central-DP mechanism for the causal problem induces a central-DP mechanism for
            -- the embedded regression problem, and the privacy exponent transfers unchanged.
            (∃ (Phi : (Fin d → ℝ) × ℝ → CateObs d) (Lctrl : Measure (CateObs d))
                (rho0 rhonp rho1 : Measure ((Fin d → ℝ) × ℝ)),
              Measurable Phi ∧
              (∀ p : (Fin d → ℝ) × ℝ,
                  (Phi p).Y = p.2 ∧ (Phi p).A = 1 ∧ (Phi p).X = p.1) ∧
              (∀ (m : ℕ) (D D' : Fin m → (Fin d → ℝ) × ℝ), ReplacementAdjacent D D' →
                  ReplacementAdjacent (fun i => Phi (D i)) (fun i => Phi (D' i))) ∧
              IsProbabilityMeasure Lctrl ∧
              Lctrl {O : CateObs d | O.A = 0}ᶜ = 0 ∧
              IsProbabilityMeasure rho0 ∧ IsProbabilityMeasure rhonp ∧
              IsProbabilityMeasure rho1 ∧
              rho0.map Prod.fst = P0.PX ∧ rhonp.map Prod.fst = P0.PX ∧
              rho1.map Prod.fst = P0.PX ∧
              IsRegressionFn rho0 P0.mu1 ∧ IsRegressionFn rhonp P1np.mu1 ∧
              IsRegressionFn rho1 P1priv.mu1 ∧
              P0.dataMeasure
                  = ENNReal.ofReal e0 • rho0.map Phi
                    + ENNReal.ofReal (1 - e0) • Lctrl ∧
              P1np.dataMeasure
                  = ENNReal.ofReal e0 • rhonp.map Phi
                    + ENNReal.ofReal (1 - e0) • Lctrl ∧
              P1priv.dataMeasure
                  = ENNReal.ofReal e0 • rho1.map Phi
                    + ENNReal.ofReal (1 - e0) • Lctrl)) ∧
        -- rate comparability R_n^DP ≍ r_n^regDP
        (c * privateRegressionCalibration n r0 gamma d (eps n)
            ≤ dpMinimaxRisk n (eps n) (del n)
                (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
          ∧ dpMinimaxRisk n (eps n) (del n)
                (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0
              ≤ C * privateRegressionCalibration n r0 gamma d (eps n)) := by
  rcases hreg with ⟨halpha, hbeta, hgamma, hL, he0, hf0, hf01, hr0, hx0⟩
  obtain ⟨c0, cB, B, Q, hc0, hcB, hQPX, hP0, hiidP0, hBdiff, hBzero,
      hBbounds, hBsupp, hlower⟩ :=
    causal_oracle_private_lower_bound_witness alpha beta gamma L e0 f0 f1 r0 x0
      ⟨halpha, hbeta, hgamma, hL, he0, hf0, hf01, hr0, hx0⟩ hne
  haveI : IsProbabilityMeasure Q.PX := hQPX
  obtain ⟨C0, hC0, hupper⟩ :=
    private_local_polynomial_upper_bound alpha beta gamma L e0 f0 f1 r0 x0
      ⟨halpha, hbeta, hgamma, hL, he0, hf0, hf01, hr0, hx0⟩
      hd
  obtain ⟨cr, Cr, hcr, hCr, hcalibration⟩ :=
    private_regression_calibration_algebra r0 gamma hgamma hr0.1
  let c := min c0 (c0 / Cr)
  let C := C0 / cr
  have hc : 0 < c := lt_min hc0 (div_pos hc0 hCr)
  have hC : 0 < C := div_pos hC0 hcr
  refine ⟨c, C, cB, B, cateWitnessLaw Q e0 (fun _ => 0), hc, hC, hcB,
    hBdiff, hBbounds, hBzero, hBsupp, hP0, hiidP0, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply, sub_self, abs_zero]
    norm_num
  · intro x
    exact cateWitnessLaw_mu0_apply Q e0 (fun _ => 0) x
  · intro x
    exact cateWitnessLaw_mu1_apply Q e0 (fun _ => 0) x
  · intro x
    exact cateWitnessLaw_pi_apply Q e0 (fun _ => 0) x
  intro eps del hbudget
  filter_upwards [hlower eps del hbudget, hupper eps del hbudget,
      hcalibration eps del hbudget, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hnlow hnup hncal hnNat
  let R := max ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))
    (((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ)))))
  have hR : 0 ≤ R :=
    (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans (le_max_left _ _)
  have hcalNonneg : 0 ≤ privateRegressionCalibration n r0 gamma d (eps n) :=
    (mul_nonneg hcr.le hR).trans hncal.1
  obtain ⟨M, hMpoly, hMdp, hMsupp, hMrisk⟩ := hnup.1
  have hMriskR :
      (⨆ P : {P : CateLaw d //
            HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P
              ∧ IidSampling P ∧ |P.mu1 x0 - P.mu0 x0| ≤ 2},
          ∫ s, (∫ z, |z - (P.1.mu1 x0 - P.1.mu0 x0)| ∂(M s))
            ∂(Measure.pi fun _ : Fin n => (P.1).dataMeasure)) ≤ C0 * R := by
    simpa [R, hbg] using hMrisk
  have hupperCal : C0 * R ≤ C * privateRegressionCalibration n r0 gamma d (eps n) := by
    calc
      C0 * R = (C0 / cr) * (cr * R) := by field_simp
      _ ≤ (C0 / cr) * privateRegressionCalibration n r0 gamma d (eps n) :=
        mul_le_mul_of_nonneg_left hncal.1 (div_nonneg hC0.le hcr.le)
      _ = C * privateRegressionCalibration n r0 gamma d (eps n) := by rfl
  obtain ⟨hnp, hpriv, bnp, bp, hhnp, hhnpr0, hhpriv, hhprivr0,
      hbnpmeas, hbpmeas, hbnpbound, hbpbound, hbumpnp, hbumppriv,
      hP1np, hP1priv, hiidnp, hiidpriv, hsepnp, htvnp, hseppriv, htvpriv⟩ := hnlow.1
  have hsepnp' :
      c * (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
        ≤ |((cateWitnessLaw Q e0 bnp).mu1 x0 - (cateWitnessLaw Q e0 bnp).mu0 x0) -
          ((cateWitnessLaw Q e0 (fun _ => 0)).mu1 x0 -
            (cateWitnessLaw Q e0 (fun _ => 0)).mu0 x0)| := by
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans (by
        simpa only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply, sub_zero,
          sub_self] using hsepnp)
  have hseppriv' :
      c * ((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ))))
        ≤ |((cateWitnessLaw Q e0 bp).mu1 x0 - (cateWitnessLaw Q e0 bp).mu0 x0) -
          ((cateWitnessLaw Q e0 (fun _ => 0)).mu1 x0 -
            (cateWitnessLaw Q e0 (fun _ => 0)).mu0 x0)| := by
    have heps : 0 ≤ eps n :=
      (inv_nonneg.mpr (Nat.cast_nonneg n)).trans (hbudget n hnNat).1
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg n) heps) _)).trans
        (by simpa only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply, sub_zero,
          sub_self] using hseppriv)
  have hlowerCal :
      c * privateRegressionCalibration n r0 gamma d (eps n)
        ≤ c0 * R := by
    calc
      c * privateRegressionCalibration n r0 gamma d (eps n)
          ≤ (c0 / Cr) * privateRegressionCalibration n r0 gamma d (eps n) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hcalNonneg
      _ ≤ (c0 / Cr) * (Cr * R) :=
        mul_le_mul_of_nonneg_left hncal.2 (div_nonneg hc0.le hCr.le)
      _ = c0 * R := by field_simp
  have hnupRiskR :
      dpMinimaxRisk n (eps n) (del n)
          (HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0) x0 ≤ C0 * R := by
    simpa [R, hbg] using hnup.2
  refine ⟨⟨M, hMpoly, hMdp, hMsupp, hMriskR.trans hupperCal⟩,
    ⟨hnp, hpriv, cateWitnessLaw Q e0 bnp, cateWitnessLaw Q e0 bp,
      hP1np, hP1priv, hiidnp, hiidpriv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hhnp, hhnpr0, hhpriv, hhprivr0, ?_, ?_, ?_, ?_, htvnp, hsepnp',
      htvpriv, hseppriv', ?_⟩,
    hlowerCal.trans hnlow.2, hnupRiskR.trans hupperCal⟩
  · simpa only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply, sub_zero]
      using (hbnpbound x0).trans (by norm_num : (1 : ℝ) ≤ 2)
  · simpa only [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply, sub_zero]
      using (hbpbound x0).trans (by norm_num : (1 : ℝ) ≤ 2)
  · intro x
    exact cateWitnessLaw_mu0_apply Q e0 bnp x
  · intro x
    exact cateWitnessLaw_pi_apply Q e0 bnp x
  · exact (cateWitnessLaw_PX_eq Q e0 bnp).trans
      (cateWitnessLaw_PX_eq Q e0 (fun _ => 0)).symm
  · intro x
    rw [cateWitnessLaw_px_apply, cateWitnessLaw_px_apply]
  · intro x
    exact cateWitnessLaw_mu0_apply Q e0 bp x
  · intro x
    exact cateWitnessLaw_pi_apply Q e0 bp x
  · exact (cateWitnessLaw_PX_eq Q e0 bp).trans
      (cateWitnessLaw_PX_eq Q e0 (fun _ => 0)).symm
  · intro x
    rw [cateWitnessLaw_px_apply, cateWitnessLaw_px_apply]
  · intro x
    exact (cateWitnessLaw_mu1_apply Q e0 bnp x).trans (hbumpnp x)
  · intro x
    exact (cateWitnessLaw_mu1_apply Q e0 bp x).trans (hbumppriv x)
  · rw [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply, hbumpnp x0]
    ring
  · rw [cateWitnessLaw_mu1_apply, cateWitnessLaw_mu0_apply, hbumppriv x0]
    ring
  · refine ⟨regToTreated, cateWitnessControlLaw Q,
      cateWitnessRegressionLaw Q (fun _ => 0), cateWitnessRegressionLaw Q bnp,
      cateWitnessRegressionLaw Q bp,
      measurable_regToTreated, ?_, ?_,
      cateWitnessControlLaw_isProbabilityMeasure Q, cateWitnessControlLaw_support Q,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      exact ⟨regToTreated_Y p, regToTreated_A p, regToTreated_X p⟩
    · intro m D D' hDD'
      exact regToTreated_replacementAdjacent hDD'
    · exact cateWitnessRegressionLaw_isProbabilityMeasure Q measurable_const (by simp)
    · exact cateWitnessRegressionLaw_isProbabilityMeasure Q hbnpmeas hbnpbound
    · exact cateWitnessRegressionLaw_isProbabilityMeasure Q hbpmeas hbpbound
    · rw [cateWitnessRegressionLaw_map_fst Q measurable_const (by simp),
        cateWitnessLaw_PX_eq]
    · rw [cateWitnessRegressionLaw_map_fst Q hbnpmeas hbnpbound,
        cateWitnessLaw_PX_eq]
    · rw [cateWitnessRegressionLaw_map_fst Q hbpmeas hbpbound,
        cateWitnessLaw_PX_eq]
    · simpa only [cateWitnessLaw_mu1_eq] using
        (cateWitnessRegressionLaw_isRegressionFn Q measurable_const (by simp))
    · simpa only [cateWitnessLaw_mu1_eq] using
        (cateWitnessRegressionLaw_isRegressionFn Q hbnpmeas hbnpbound)
    · simpa only [cateWitnessLaw_mu1_eq] using
        (cateWitnessRegressionLaw_isRegressionFn Q hbpmeas hbpbound)
    · exact cateWitnessLaw_dataMeasure_mixture Q e0 measurable_const (by simp)
        he0.1.le (by linarith [he0.2])
    · exact cateWitnessLaw_dataMeasure_mixture Q e0 hbnpmeas hbnpbound
        he0.1.le (by linarith [he0.2])
    · exact cateWitnessLaw_dataMeasure_mixture Q e0 hbpmeas hbpbound
        he0.1.le (by linarith [he0.2])

end CausalSmith.Stat.DpCateMinimax
