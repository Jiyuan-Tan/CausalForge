# Substrate requirement: ate_eif_instance

## Goal
Instantiate the abstract pathwise-gradient / regular-submodel layer
(`Causalean.Estimation.Efficiency.PathwiseGradient`) on the genuine Hilbert space
`Lp ℝ 2 S.P_Z` for a backdoor ATE estimation system `S`, proving the **Hahn (1998)**
statement: the AIPW score `S.aipwLp` is a *pathwise gradient* of the ATE functional
along every regular submodel, and — as the canonical (projected) gradient lying in
the mean-zero nonparametric tangent space `S.Tfull` — the **efficient influence
function** for the ATE. This upgrades the existing
`Causalean.Estimation.Efficiency.ATETangent.aipw_score_meanZero_projection_eq`
(currently only "AIPW is mean-zero, so projection fixes it") into the full
"AIPW *is* the EIF of the ATE functional" statement, by tying the identification
to pathwise differentiability of the functional rather than to a pre-supplied
reference gradient.

## Provides (API contract)
- `inner_aipwLp_eq_integral (f : Lp ℝ 2 S.P_Z) : ⟪S.aipwLp …, f⟫_ℝ = ∫ z, S.ψ_AIPW z * f z ∂S.P_Z`
  — **bridge lemma**: the L² inner product of the AIPW score against any `f` equals
  the covariance integral. Turns the Hahn covariance form into the inner-product
  form required by `IsPathwiseGradient`.
- `aipw_isPathwiseGradient_ATE (ψ) (hHahn) : IsPathwiseGradient S.oneLp S.P_Z ψ (S.aipwLp …)`
  — the AIPW score is a pathwise gradient of the ATE functional `ψ`, given the Hahn
  pathwise-derivative identity `hHahn` (see § interface hypotheses).
- `aipw_is_efficientInfluenceFunction (ψ) (hHahn) (hdense) :`
  `IsPathwiseGradient S.oneLp S.P_Z ψ (S.aipwLp …) ∧ S.aipwLp … ∈ S.Tfull ∧`
  `∀ g, IsPathwiseGradient S.oneLp S.P_Z ψ g → efficientIF S.Tfull g = S.aipwLp …`
  — the **MAIN result**: AIPW is a pathwise gradient, lies in `Tfull`, and is the
  canonical gradient (= `efficientIF Tfull g` for every pathwise gradient `g`),
  hence the unique pathwise gradient in `Tfull` — the efficient influence function.

## Interface hypotheses (assumed, NOT derived — sanctioned)
These encode "the model is nonparametric" and "the standard Hahn pathwise
derivative holds"; they are threaded as explicit hypotheses on the theorems, so the
headline is a sorry-free CONDITIONAL on the sanctioned semiparametric interface.
They are NOT to be derived from a general Fréchet-differentiability theory of
statistical functionals (explicit non-goal).
- `hHahn : ∀ m : RegularSubmodel S.oneLp S.P_Z, HasDerivAt (fun t => ψ (m.path t)) (∫ z, S.ψ_AIPW z * (m.score z) ∂S.P_Z) 0`
  — Hahn's pathwise-derivative calculation `d/dt ψ(P_t)|₀ = ∫ ψ_AIPW · s dP_Z`.
- `hdense : S.Tfull ≤ tangentSpace S.oneLp S.P_Z`
  — `Tfull` is the nonparametric tangent space (contained in the closed span of
  the submodel scores). The reverse inclusion (`scores_mem`) is automatic from
  mean-zero-ness.

## Statement / milestones
1. **Bridge** `inner_aipwLp_eq_integral`: `Causalean.Panel.FWLInstanceL2.inner_eq_integral`
   gives `⟪aipwLp, f⟫ = ∫ aipwLp · f`, then rewrite `aipwLp =ᵐ ψ_AIPW` using
   `(S.aipw_memLp …).coeFn_toLp` to replace `aipwLp z` by `S.ψ_AIPW z` under the integral.
2. **Pathwise gradient** `aipw_isPathwiseGradient_ATE`: unfold `IsPathwiseGradient`; for
   each submodel `m`, rewrite the target derivative `⟪aipwLp, m.score⟫` to
   `∫ ψ_AIPW · m.score` via the bridge lemma, then apply `hHahn m`.
3. **Assembly** `aipw_is_efficientInfluenceFunction`: combine (2), the existing
   `S.aipwLp_mem_tangent` (AIPW ∈ Tfull), and `isTangentSpace_Tfull` (from `hdense`)
   through the abstract uniqueness lemma
   `Causalean.Estimation.Efficiency.isPathwiseGradient_eq_efficientIF_of_mem`.
   Also provide the trivial helpers `score_mem_Tfull` (scores are mean-zero, so lie
   in `(ℝ ∙ oneLp)ᗮ = Tfull` via `Submodule.mem_orthogonal_singleton_iff_inner_left`)
   and `isTangentSpace_Tfull`.

## Standard reference
Hahn (1998, Econometrica), "On the Role of the Propensity Score in Efficient
Semiparametric Estimation of Average Treatment Effects"; Bickel–Klaassen–Ritov–Wellner
(1993); Tsiatis (2006), Ch. 4; van der Vaart (1998), Ch. 25.

## Intended reuse
The canonical Causalean statement that AIPW is the efficient influence function for
the backdoor ATE — the semiparametric-efficiency headline for ATE estimation.
Consumed wherever the ATE efficiency bound / EIF is invoked (double-robust /
one-step / TMLE estimators). Coupled to `ATE.BackdoorEstimationSystem`, which is the
correct generality for this instance (the abstract reusable layer is already in
`PathwiseGradient`).

## May assume / must derive
May assume: the two interface hypotheses `hHahn`, `hdense` above (threaded explicitly).
Must derive: everything else — the bridge lemma from `FWLInstanceL2.inner_eq_integral`
+ `coeFn_toLp`, the pathwise-gradient conclusion from the bridge + `hHahn`, and the
canonical-gradient / EIF conclusion from the abstract Hilbert-projection uniqueness
lemma. Do NOT assume any of the three provided results. Zero `sorry`.

## Known building blocks
`Causalean.Estimation.Efficiency.PathwiseGradient` (`RegularSubmodel`, `IsPathwiseGradient`,
`IsTangentSpace`, `tangentSpace`, `isPathwiseGradient_eq_efficientIF_of_mem`);
`Causalean.Estimation.Efficiency.ATETangent` (`BackdoorEstimationSystem.aipwLp`,
`oneLp`, `Tfull`, `P_Z`, `ψ_AIPW`, `aipw_memLp`, `aipwLp_mem_tangent`);
`Causalean.Estimation.Efficiency.TangentProjection` (`efficientIF`);
`Causalean.Panel.FWLInstanceL2.inner_eq_integral`; `MemLp.coeFn_toLp`;
`Submodule.mem_orthogonal_singleton_iff_inner_left`.

## Target module
Causalean.Estimation.Efficiency.ATEEfficientIF
