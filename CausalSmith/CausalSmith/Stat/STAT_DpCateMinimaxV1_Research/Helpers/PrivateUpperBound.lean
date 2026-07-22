/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP CATE minimax: the private local-polynomial upper endpoint

Stage-2 scaffold. The heaviest crux `lem:private_local_polynomial_upper_bound`: an
explicit armwise privatized local-polynomial estimator (Laplace-mechanism pure-DP
release via `ℓ¹`-sensitivity `Δ_h = C/(n h^d)`, Gram-matrix spectral projection,
Hölder–Taylor bias, variance + Laplace-noise decomposition, bandwidth
optimization) attaining
`R_n^{DP} ≤ C{n^{-β/(2β+d)} ∨ (n ε_n)^{-β/(β+d)}}` uniformly over the frozen class.
No DP substrate exists in Causalean/CausalSmith, so the Laplace mechanism /
sensitivity bound is build-inline but constructive. The remaining construction
gap is isolated immediately above the endpoint theorem.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import Causalean.Mathlib.Analysis.ConvexProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace CausalSmith.Stat.DpCateMinimax

open Causalean.Mathlib.Analysis (frobDist)

open MeasureTheory
open scoped BigOperators

/-- Laplace noise kernel of scale `b`: the measure on `ℝ` with Laplace density
`w ↦ (2b)⁻¹ exp(-|w|/b)`. Models the pure-`ε_n`-DP additive Laplace release. -/
noncomputable def laplaceKernel (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun w => ENNReal.ofReal ((2 * b)⁻¹ * Real.exp (-(|w| / b))))

/-- Joint (product) Laplace noise kernel of dimension `Nq` and per-coordinate scale
`b`: the `Nq`-fold product of `laplaceKernel b`, modeling independent Laplace noise
added to each coordinate of the JOINT Gram/moment query. -/
noncomputable def laplaceVecKernel (Nq : ℕ) (b : ℝ) : Measure (Fin Nq → ℝ) :=
  Measure.pi (fun _ : Fin Nq => laplaceKernel b)

/-- **Armwise privatized local-polynomial Laplace mechanism (witness identifier).**
Structural `Prop` that IDENTIFIES the upper-endpoint witness `M` as the paper's
EXPLICIT armwise local-polynomial construction rather than an anonymous `∃ M`, at the
level of structure the paper states it. For SOME admissible bandwidth `h ∈ (0, r₀]`
in the regularity neighborhood and local-polynomial degree `m = ⌈β⌉ - 1`, the FULL
degree-`m` multivariate MONOMIAL feature basis is used: coordinates of `feat` are
indexed by exponent multi-indices `expo k : Fin d → ℕ` with total degree `≤ m`,
`feat u k = ∏ⱼ (uⱼ)^{expo k j}`, EVERY degree-`≤ m` monomial occurs
(`∀ r, ∑ r ≤ m → ∃ k, expo k = r`), and the intercept coordinate `icpt` is the
constant monomial (`expo icpt = 0`, `feat _ icpt = 1`). The kernel `K` is nonnegative,
bounded above by `Kmax`, supported on the unit `∞`-norm cube, AND BOUNDED BELOW by
`Kmin > 0` on an inner cube `‖u‖_∞ ≤ rinner` (the paper's kernel lower bound).

The paper releases the NOISY JOINT Gram/moment query, then spectrally projects:

* `Gram a s` is the ARM-SELECTED (`1(A_i = a)`) kernel-weighted degree-`m` Gram
  matrix `n⁻¹ Σ_i 1(A_i=a) h^{-d} K((X_i-x₀)/h) v_i v_iᵀ`, `v_i = feat((X_i-x₀)/h)`;
* `moment a s` is the matching kernel-weighted moment vector
  `n⁻¹ Σ_i 1(A_i=a) h^{-d} K((X_i-x₀)/h) v_i clip_{[-1,1]}(Y_i)`, where the outcome is
  CLIPPED to its declared range `[-1,1]` INSIDE the query (`max (-1) (min 1 Y_i)`); this
  is a no-op on every in-range law of the class but makes the `ℓ¹`-sensitivity bound below
  hold over ALL `CateObs` datasets — including adversarial records with unbounded raw
  `CateObs.Y` — so the query has genuinely finite global sensitivity `Δ_h`;
* the JOINT query `(Gram 0, Gram 1, moment 0, moment 1)` is flattened into the
  `Fin Nq → ℝ` coordinate layout via injective, disjoint index maps `gramIdx, momIdx`,
  and has `ℓ¹`-sensitivity `Δ_h = C_s/(n h^d)` (a single-record change moves the joint
  query by at most `Δ_h` in `ℓ¹`), which pins the joint Laplace noise scale;
* `M` adds independent Laplace(`Δ_h/ε_n`) noise to EACH query coordinate
  (`laplaceVecKernel Nq (Δ_h/ε_n)`), then post-processes: each noisy Gram is
  SPECTRALLY PROJECTED by `proj` into the well-conditioned Loewner set
  `{G : c_⋆ I ≤ G ≤ C_⋆ I}` (so it is invertible), the projected normal equations are
  solved, the two arm intercept coordinates are differenced, and the scalar is clipped
  to `[-2,2]`.

The joint DP release is pure `ε_n`-DP by `ℓ¹`-sensitivity calibration, and the
spectral projection + solve + difference + clip is post-processing. All construction
parameters are existentially bound so the in-proof construction obviously satisfies
this shape. -/
def IsArmwisePrivatizedLocalPoly {d : ℕ} (n : ℕ) (beta r0 epsN : ℝ)
    (x0 : Fin d → ℝ) (M : (Fin n → CateObs d) → Measure ℝ) : Prop :=
  ∃ (h Cs Kmax Kmin rinner cstar Cstar : ℝ) (m p Nq : ℕ) (icpt : Fin p)
      (expo : Fin p → (Fin d → ℕ))
      (K : (Fin d → ℝ) → ℝ)
      (feat : (Fin d → ℝ) → (Fin p → ℝ))
      (gramIdx : Fin 2 → Fin p → Fin p → Fin Nq)
      (momIdx : Fin 2 → Fin p → Fin Nq)
      (Gram : Fin 2 → (Fin n → CateObs d) → Matrix (Fin p) (Fin p) ℝ)
      (moment : Fin 2 → (Fin n → CateObs d) → (Fin p → ℝ))
      (proj : Matrix (Fin p) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ)
      (release : (Fin n → CateObs d) → (Fin Nq → ℝ) → ℝ),
    0 < h ∧ h ≤ r0 ∧ 0 < Cs ∧ 0 < Kmin ∧ Kmin ≤ Kmax ∧
      0 < rinner ∧ rinner < 1 ∧ 0 < cstar ∧ cstar ≤ Cstar ∧
    -- local-polynomial degree m = ⌈β⌉ - 1; FULL degree-≤ m multivariate monomial basis
    m + 1 = ⌈beta⌉₊ ∧ 0 < p ∧
    (∀ k : Fin p, (∑ j : Fin d, expo k j) ≤ m) ∧
    (∀ (u : Fin d → ℝ) (k : Fin p), feat u k = ∏ j : Fin d, (u j) ^ (expo k j)) ∧
    (∀ r : Fin d → ℕ, (∑ j : Fin d, r j) ≤ m → ∃ k : Fin p, expo k = r) ∧
    expo icpt = (fun _ => 0) ∧ (∀ u : Fin d → ℝ, feat u icpt = 1) ∧
    -- kernel: nonnegative, bounded above, supported on the unit ∞-norm cube, and
    --   BOUNDED BELOW by Kmin on the inner cube ‖u‖_∞ ≤ rinner
    (∀ u : Fin d → ℝ, 0 ≤ K u) ∧ (∀ u : Fin d → ℝ, K u ≤ Kmax) ∧
    (∀ u : Fin d → ℝ, (∃ j, 1 < |u j|) → K u = 0) ∧
    (∀ u : Fin d → ℝ, (∀ j, |u j| ≤ rinner) → Kmin ≤ K u) ∧
    -- armwise kernel-weighted degree-m local-polynomial Gram matrix and moment vector
    (∀ (a : Fin 2) (s : Fin n → CateObs d),
        Gram a s = Matrix.of (fun k l : Fin p =>
          (n : ℝ)⁻¹ * ∑ i : Fin n,
            (if (s i).A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0)
              * h ^ (-(d : ℝ)) * K (fun j => ((s i).X j - x0 j) / h)
              * feat (fun j => ((s i).X j - x0 j) / h) k
              * feat (fun j => ((s i).X j - x0 j) / h) l) ∧
        moment a s = (fun k : Fin p =>
          (n : ℝ)⁻¹ * ∑ i : Fin n,
            (if (s i).A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0)
              * h ^ (-(d : ℝ)) * K (fun j => ((s i).X j - x0 j) / h)
              * max (-1) (min 1 (s i).Y)
              * feat (fun j => ((s i).X j - x0 j) / h) k)) ∧
    -- injective, disjoint coordinate layout of the JOINT (Gram, moment) query
    Function.Injective (fun q : Fin 2 × Fin p × Fin p => gramIdx q.1 q.2.1 q.2.2) ∧
    Function.Injective (fun q : Fin 2 × Fin p => momIdx q.1 q.2) ∧
    (∀ (a : Fin 2) (k l : Fin p) (a' : Fin 2) (k' : Fin p),
        gramIdx a k l ≠ momIdx a' k') ∧
    -- ℓ¹-sensitivity Δ_h = Cs/(n h^d) of the JOINT Gram/moment query: a single-record
    --   change moves the flattened query by at most Δ_h in ℓ¹ (pins the noise scale)
    (∀ s s' : Fin n → CateObs d, (∃ i : Fin n, ∀ j : Fin n, j ≠ i → s j = s' j) →
        (∑ a : Fin 2, ∑ k : Fin p, ∑ l : Fin p, |Gram a s k l - Gram a s' k l|)
            + (∑ a : Fin 2, ∑ k : Fin p, |moment a s k - moment a s' k|)
          ≤ Cs / ((n : ℝ) * h ^ (d : ℝ))) ∧
    -- SPECTRAL PROJECTION: `proj` is the paper's FROBENIUS-NORM METRIC PROJECTION onto the
    --   well-conditioned Loewner set `𝒮 = {G : c_⋆ I ≤ G ≤ C_⋆ I}`. Three clauses, exactly the
    --   content the paper's argument uses:
    --   (i)   `proj` lands every matrix in `𝒮` (so the projected Gram is invertible);
    --   (ii)  `proj` FIXES every matrix already in `𝒮` (a projection is idempotent on its range);
    --   (iii) `proj` is NON-EXPANSIVE towards every point of `𝒮` — the variational inequality for
    --         the Euclidean/Frobenius projection onto a convex set, i.e. the paper's
    --         "the variational inequality for Euclidean projection gives ‖G^priv − EG‖_F no larger
    --         than the norm of the unprojected noisy error". Without (iii) the predicate would allow
    --         an arbitrary retraction onto `𝒮` rather than the paper's explicit estimator.
    --   `proj` is measurable, so the release is a genuine Markov kernel.
    Measurable proj ∧
    (∀ G : Matrix (Fin p) (Fin p) ℝ,
        (proj G - cstar • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef ∧
        (Cstar • (1 : Matrix (Fin p) (Fin p) ℝ) - proj G).PosSemidef) ∧
    (∀ G : Matrix (Fin p) (Fin p) ℝ,
        (G - cstar • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef →
        (Cstar • (1 : Matrix (Fin p) (Fin p) ℝ) - G).PosSemidef →
        proj G = G) ∧
    (∀ G S : Matrix (Fin p) (Fin p) ℝ,
        (S - cstar • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef →
        (Cstar • (1 : Matrix (Fin p) (Fin p) ℝ) - S).PosSemidef →
        frobDist (proj G) S ≤ frobDist G S) ∧
    -- release map: add joint Laplace noise to the (Gram, moment) query, spectrally
    --   project each noisy Gram, solve the projected normal equations, difference the
    --   two arm intercepts, clip to [-2,2] — post-processing of ONE joint DP release
    (∀ (s : Fin n → CateObs d) (w : Fin Nq → ℝ),
        release s w =
          max (-2) (min 2
            ( ((proj (Matrix.of
                    (fun k l : Fin p => Gram 1 s k l + w (gramIdx 1 k l))))⁻¹.mulVec
                  (fun k : Fin p => moment 1 s k + w (momIdx 1 k))) icpt
            - ((proj (Matrix.of
                    (fun k l : Fin p => Gram 0 s k l + w (gramIdx 0 k l))))⁻¹.mulVec
                  (fun k : Fin p => moment 0 s k + w (momIdx 0 k))) icpt ))) ∧
    (∀ s : Fin n → CateObs d,
      M s = (laplaceVecKernel Nq ((Cs / ((n : ℝ) * h ^ (d : ℝ))) / epsN)).map
        (release s))

/-- The algebraic inverse-perturbation identity.  Analytic bounds on a projected
Gram solve reduce to this identity plus operator-norm submultiplicativity. -/
private lemma matrix_inv_sub_inv {p : ℕ}
    (U V : Matrix (Fin p) (Fin p) ℝ)
    (hUleft : U⁻¹ * U = 1) (hVright : V * V⁻¹ = 1) :
    U⁻¹ - V⁻¹ = U⁻¹ * (V - U) * V⁻¹ := by
  calc
    U⁻¹ - V⁻¹ = U⁻¹ * V * V⁻¹ - U⁻¹ * U * V⁻¹ := by
      simp [mul_assoc, hUleft, hVright]
    _ = U⁻¹ * (V - U) * V⁻¹ := by noncomm_ring

end CausalSmith.Stat.DpCateMinimax
