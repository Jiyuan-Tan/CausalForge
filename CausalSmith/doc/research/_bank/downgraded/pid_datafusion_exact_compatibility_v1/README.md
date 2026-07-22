---
qid: pid_datafusion_exact_compatibility
spec: v1
topic: "exact no-cancellation compatibility frontier for simultaneous NUC and study-exchangeability sensitivity: characterize K(P) by C_P(rho,gamma)=max_t E[(L_t-U_t)_+], and derive cross-fitted nuisance-robust contact-set inference uniformly over the two-parameter frontier including interval ties, with the verified two-stratum cancellation witness and the regular local separation boundary; fixes the average-overlap/fixed-nuisance incompatibility test used by Lanners et al. (NeurIPS 2025) in Project STAR"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  # NOTE: no conjecture collapsed. D0.5.G PASSED at tier=field, meets_floor=true.
  # This is an ORCHESTRATOR/USER-DIRECTED downgrade at the D0.5->F1 go/no-go,
  # taken on significance-and-completeness grounds, not correctness. The first
  # three entries are verbatim from the passing referee's own critique
  # (reviews/review_general.json); the last two are orchestrator findings.
  - "The sharp separation rate is proved only for the canonical Hölder tie subexperiment, not for the full primitive class or the entire two-parameter frontier, exactly as the framing acknowledges."
  - "Uniform coverage and level for the proposed numerical directional-delta procedure remain open, and the scalar-tangent nonfactorization lemma shows that the displayed multiplier input is not itself selector-complete at ties."
  - "The load-bearing regular-conditional-kernel lemma is stated without proof or a precise theorem-level citation, so the generic Kallenberg reference should be replaced with a pinpoint citation."
  - "Positioning gap (orchestrator): MastenPoirier2020 and LuedtkeVanderLaan2016 appear exactly once each in writeup.tex, inside \\bibitem, and are never engaged in the body. Both are same-genre prior art — breakdown-frontier inference under directional differentiability, and ties destroying regular sqrt(n) inference. If either subsumes the inference half, only contributions 1-2 survive."
  - "No empirical check (orchestrator): the paper's punch is a claim about LRVP's Project STAR analysis, but nobody tested whether signed-overlap cancellation actually bites in that dataset. LRVP's code is public; this is the cheapest available path to field tier."
reusable_artifacts:
  # Verified against the primary source — do NOT re-derive these.
  - "discovery/core.json :: prop:two-stratum-cancellation — the two-stratum witness (weights 4/5, 1/5; a=1/4, b=8; theta=(1,1); mu_00=4, mu_10=(1/2,4), mu_01=mu_11=1). Orchestrator re-checked the arithmetic BY HAND: with LRVP's own UN-CLIPPED v,w it gives H_0(x1)=-1, H_0(x2)=+4, G(0)=0 exactly, so their one-sided test does not reject while their Theorem's pointwise hypothesis fails on the 4/5-mass stratum. The witness does not depend on clipping; clipping only widens the gap 1 -> 9/8 (C_P=9/10)."
  - "VERIFIED SOURCE READ (2026-07-21): arXiv:2505.24296 e-print pulled and read. LRVP appendix incompatible.tex line 62 defines G(t)=E[min{v(x,t,gamma),w(x,t,rho)} - max{v(x,t,-gamma),w(x,t,-rho)}] and tests H_0: G(t)>=0. The note's characterization of their diagnostic is VERBATIM CORRECT. Do not re-verify."
  - "SHARPENED CRITIQUE (orchestrator, supersedes the note's framing): LRVP already KNOW the exact condition is pointwise (Theorem hypothesis is 'for each x and t'; Remark: bounds 'valid only when'; appendix line 59 calls the average a tractability concession). So 'they used an average' is not the finding. The actual error is the DIRECTION of their approximation: appendix line 76 claims the procedure is conservative ('inflated incompatible region ... we prefer to label (rho,gamma) pairs as incompatible that may, in fact, be compatible'), but that argument covers only the fixed-nuisance limitation. The averaging limitation biases the OPPOSITE way and its sign is never analyzed. Their stated safety posture is therefore unsupported."
  - "FALSE-DICHOTOMY POINT (orchestrator): LRVP frame the choice as pointwise (intractable) vs average (tractable). E[(max lower - min upper)_+] costs exactly the same to compute from the same fitted nuisances and is zero iff the pointwise condition holds a.s. The extra cost is statistical (boundary null, tie non-regularity), not computational — which is precisely what this run's minimax half characterizes."
  - "discovery/core.json :: def:selector-extension-handle + def:endpoint-kernel — the sufficiency construction (midpoint selector + two-point kernel nu_m realizing any mean in [a,b] on {a,b} + standard-Borel measurable selection). Generic recipe for turning a.s. pointwise interval intersection into one common latent law; reusable in any partial-ID compatibility argument where the joint law of (Y(0),Y(1)) is unconstrained beyond marginals."
  - "discovery/core.json :: lem:tie-subexperiment-minimax-boundary — the reduction C_{P_u}(0,0) = (b-a)*||u||_{L1} on a designed Hölder submodel, giving the classical n^{-2beta/(4beta+d)} separation rate. Reusable template for showing a positive-part partial-ID functional is not uniformly sqrt(n)-testable."
  - "discovery/core.json :: lem:scalar-face-tangent-nonfactorization — directions r_0=0 and r_1=x_1-1/2 give identical zero derivatives on all four integrated face coordinates but derivatives 0 vs 1/4 for C_P. Clean template for killing a finite-dimensional-tangent bootstrap at a kink."
  - "discovery/writeup.tex, discovery/writeup.pdf — full NL proofs (never Lean-verified; F-phase was not entered)."
seeds_burned: []
proof_attempt_summary: |
  Discovery completed through D0.5 and PASSED the general referee at tier=field
  (meets_floor=true, flagship_potential=false); F-phase was never entered, so nothing
  here is Lean-verified — pending_sorries is empty only because F1 never ran.
  Nine statements are NL-proved: an exact iff characterizing the compatibility region
  as the zero set K(P)={theta : C_P(theta)=0} (necessity plus an explicit measurable
  common-latent-law construction), a fully specified two-stratum witness defeating
  LRVP's signed-overlap diagnostic, a sharp n^{-2beta/(4beta+d)} minimax separation rate
  at positive-mass ties against a regular sqrt(n) constant-path Gaussian power formula,
  and a nonfactorization lemma showing the run's OWN proposed multiplier tangent is
  under-specified at ties. The tenth statement, oeq:uniform-contact-inference — does the
  proposed cross-fitted directional-delta procedure have uniform coverage and level? —
  is the paper's central practical question and is left open.
  Downgraded at the go/no-go rather than committed to formalization: the package
  diagnoses a real defect in a published NeurIPS 2025 procedure but supplies no working
  replacement, and its three constituent results are individually routine (a standard
  selection argument, a hand-checkable counterexample, a classical Ingster-type rate
  applied to a new functional). Formal verification would not have changed this — the
  objection is to significance and completeness, which Lean cannot adjudicate.
  Re-raise path is concrete and either branch alone likely reaches field: (a) close
  oeq:uniform-contact-inference by building a selector-complete covariate-indexed tangent
  (precedent: Chernozhukov-Lee-Rosen, Fang-Santos, Masten-Poirier all built uniformly
  valid procedures around this species of non-differentiability), or (b) run the
  cancellation check against Project STAR on LRVP's public code — far cheaper, and it
  converts a theoretical possibility into a demonstrated applied correction.
banked_on: "2026-07-22"
---

# pid_datafusion_exact_compatibility / v1 — Downgraded

**Topic.** exact no-cancellation compatibility frontier for simultaneous NUC and study-exchangeability sensitivity: characterize K(P) by C_P(rho,gamma)=max_t E[(L_t-U_t)_+], and derive cross-fitted nuisance-robust contact-set inference uniformly over the two-parameter frontier including interval ties, with the verified two-stratum cancellation witness and the regular local separation boundary; fixes the average-overlap/fixed-nuisance incompatibility test used by Lanners et al. (NeurIPS 2025) in Project STAR

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Sound math, over-framed novelty: the central inference question (uniform coverage/level of the proposed directional-delta procedure) is left open, and the two closest competitors (Masten-Poirier 2020 breakdown frontiers, Luedtke-van der Laan 2016 tie non-regularity) are cited in the bibliography but never engaged in the body.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

**This is not a referee-driven bank.** D0.5.G passed the note at `field` and flagged only a
missing pinpoint citation. The downgrade is an orchestrator/user call at the D0.5→F1 go/no-go,
recorded so a future reader does not mistake `downgraded` for "the reviewer rejected it."
`banked_novelty_tier: subfield` is set deliberately below the referee's `field` so that a
later `--upgrade` can target `field` on the strength of closing the open question.

**What survived verification.** The single highest-risk dependency — that LRVP really do use a
signed expectation as their operative compatibility test — was checked against the arXiv source
and holds verbatim. Anyone revisiting this entry can treat that as settled.

**What the note gets wrong about its own contribution.** It frames the finding as "LRVP used an
average instead of the pointwise condition." They knew; they say so. The defensible finding is
narrower and sharper: their claimed *error direction* is wrong, because they justify the
procedure on conservativeness grounds that only cover one of their two limitations. Any re-raise
should lead with that, not with the averaging observation.

**Honest scope carried over from the note.** No claim of uniform coverage or level for the
proposed procedure; no optimality outside the stated tie subexperiment; nothing beyond the frozen
binary-treatment, two-study sensitivity model. Clipping to `[a,b]` is an improvement available
under an *extra* assumption (known outcome support) rather than a correction — LRVP assume no
bounded support, so un-clipped endpoints are correct for them in general.
