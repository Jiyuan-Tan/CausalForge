# Substrate debt (disclosed gates)

**STATUS 2026-07-09: NO OPEN GATES.** Every top-level theorem is unconditional modulo its
standard modeling assumptions. Audited against the Lean source, not against this file's history.

All seven top-level theorems — `hetero_clt`, `postdesign_wald`, `heterogeneity_separation`,
`hetero_envelope`, `convex_design`, `homogeneous_reduction`, `surrogate_certificate` — are
`sorry`-free and axiom-clean on `{propext, Classical.choice, Quot.sound}` (checked with
`#print axioms` against freshly rebuilt oleans). The module declares no custom `axiom`. No theorem
carries a `…Input` or `…Data` gate hypothesis.

## CLOSED

- **thm:heterogeneity-separation / `EnvelopeLineC2Data`** — **RESOLVED (2026-07-09).** The
  one-dimensional calculus of the reciprocal-product envelope line
  `g(s) = V_env(p^hom + s·d)/4` along `d = e_b − e_a` is now DISCHARGED by
  `envelopeLineC2Data_holds` (`THeterogeneitySeparation.lean`); the `hdata` hypothesis was REMOVED
  from both `envelope_segment_descent_gap` and `heterogeneity_separation`, which are now
  unconditional. `EnvelopeLineC2Data` survives only as a named `Prop` bundle, supplied internally.

  Two pieces were missing, and the debt note over-estimated both:
  1. *Reciprocal-product second derivative.* `recipC` is a smooth cutoff times `x⁻¹`, so it is
     `C^∞`, not merely `C¹` — the old bound was an artifact of the lemma statement.
     `Causalean/Mathlib/Analysis/SmoothReciprocal.lean` now proves `recipC_contDiff_of` at
     arbitrary order `n : ℕ∞`, with `recipC_contDiff` / `recipC_contDiff_two` as `fun_prop`
     specializations. `varEnvelopeExt` lifts to `C²` mechanically.
  2. *`BddAbove` / `le_ciSup` for `dirModulus`.* Obtained from continuity of the directional
     curvature `envCurv` on the COMPACT `feasibleSet` (compactness already proved inside
     `convex_design`). `0 ≤ dirModulus` comes from convexity of `V_env`, also already proved
     there, via a new converse-direction lemma.

  New reusable substrate, both axiom-clean:
  - `Causalean/Mathlib/Analysis/LineSecondDeriv.lean` — `secondDirDeriv f d q` (Hessian quadratic
    form), `deriv_deriv_line` (second derivative of a line restriction = curvature at the moving
    base point), `continuous_secondDirDeriv`, and `convexOn_deriv2_nonneg` (convex `C²` ⇒
    `deriv² ≥ 0` at interior points — the converse of Mathlib's `convexOn_of_deriv2_nonneg`,
    which Mathlib does not have).
  - `.../EXP_BipartiteMinimaxDesign_Research/Helpers/EnvelopeCalculus.lean` — `C²` regularity of
    `varEnvelopeExt`, the `envCurv` modulus, singular↔floored transfer along a line (via an
    `ε/2`-ball `EventuallyEq`), `dirModulus_eq_ciSup_envCurv`, `bddAbove_envCurv_range`,
    `envCurv_le_dirModulus`.

  Supporting change: `deriv_varEnvelope_div_four_coord_line` in `TConvexDesign.lean` went from
  `private` to public (it already computed the coordinate partial as `envelopeGrad`).

- **input:hetero-clt-denominator-tightness** — **RESOLVED (2026-07-09).** The delta-method Hájek
  ratio-remainder `o_p` tightness envelope is DISCHARGED, not assumed. Built a reusable
  convergence-in-probability product-tightness layer in Causalean
  (`Causalean/Experimentation/DesignBased/InProb.lean`: `BoundedInProb`, `boundedInProb_of_var_bound`,
  `TendstoInProb.{mul_boundedInProb, const_mul, add, abs}`), the numerator/denominator moment +
  in-probability facts (`Helpers/{NumeratorMoment, DenominatorRatioInProb}.lean`), and the per-arm
  ratio-remainder identity + capped bound (`Helpers/RatioRemainder.lean`); assembled in
  `THeteroClt.lean` as `remainder_tendstoInProb_zero` → `heteroDenominatorTightness_discharged`.
  `HeteroDenominatorTightnessInput` survives only as a named `def`, supplied internally.

- **thm:hetero-clt / `HeteroLinScoreCLTInput`** — **RESOLVED.** The bounded-degree dependency-graph
  CLT for the linearized score is discharged by `hetero_linscore_clt_of_depgraph`
  (`THeteroClt.lean:167`), built on the `linScore-depgraph` construction and
  `bounded_degree_dependency_clt`. Supplied internally at `THeteroClt.lean:592`.

- **thm:hetero-clt / `HeteroStudentizedSlutskyInput`** — **RESOLVED.** The finite-design
  converging-together transfer is now the proved lemma `hetero_studentized_slutsky`
  (`THeteroClt.lean:297`). The identifier no longer exists.

- **thm:hetero-clt / `HeteroLinearizationInput`** — **RESOLVED.** Now the proved lemma
  `hetero_linearization_of_denominator_tightness` (`THeteroClt.lean:85`). The identifier no
  longer exists.

- **thm:hetero-clt** — REGULARITY added: `denominatorKernelBound/card(Ox)→0` (design non-degeneracy;
  `hetero_clt` was under-specified). With all four input gates above discharged, `hetero_clt` and
  `postdesign_wald` are UNCONDITIONAL modulo the standard modeling assumptions (bipartite
  interference, independent heterogeneous Bernoulli, positivity floor, budget balance, bounded
  outcomes, bounded outcome degree, bounded overlap dependency, variance nondegeneracy) and the
  disclosed tail condition `hcardEq`. An earlier verbatim-conclusion gate here was LAUNDERING — fixed.
