---
qid: exp_crossworld_robust_controlvariate_design
spec: v1
topic: "Robust ex-ante Zhao control-variate bases under cross-world dependence uncertainty. Freeze a finite known network and assignment law, two mutually exclusive exposure events, iid bounded potential-outcome pairs, and an independent unpaired pilot identifying F1,F0 but not their copula. K1 derive sharp Fréchet covariance endpoints by rearrangement and prove fixed-basis loss is affine, so the adversary is an endpoint. K2 minimize the larger endpoint residual over normalized κ-regular block-separable projective bases, using certified interval branch-and-bound with ε-global guarantees and ε→0, while retaining the smaller endpoint gain as a secondary diagnostic; claim neither an SDP reduction nor a universal minimax equality. K3 prove strictly lower worst-copula residual variance than Zhao's c=0 surrogate on a relative-open lawful neighborhood. K4 prove plug-in robust-value and outer argmin-set consistency, with point convergence only for a singleton minimizer, then deliver a reproducible, explicitly unexecuted protocol for the Jiangxi PICC network experiment reanalyzed by Zhao that reconstructs the design, cross-fits robust and zero-covariance bases, deploys each held-out basis through the displayed observable ordinary-inverse control-variate estimator, and reports point estimates, design-randomization standard errors, endpoint and worst losses, minimum regularity, and a clearly heuristic optimization diagnostic, while distinguishing its internal split from the independent unpaired pilot model and asserting no numerical results absent authenticated replication data. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The triangle Bernoulli(1/3) witness gives the stated π and Ω; Bernoulli(1/2) margins admit observationally equivalent c=±1/4. Exact endpoint-mixture certificates give c=0 worst loss 521/1200 and robust constant loss 2613/8432, an absolute reduction 4912/39525 and a 28.62398% relative reduction. UNRESOLVED BOTTLENECK: Prove the certified global solver and uniform relative-open dominance/argmin correspondence for the full κ-regular class. EARLY KILL TEST: Recheck the certificate equality sets and run interval branch-and-bound on the triangle; stop if any c=0 optimizer has worst loss ≤2613/8432 or the claimed outer set convergence fails."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The stability price is only defined as b_n^st = min_{B in K_n^st} w+(B) - inf_{B in B_Z+} w+(B) >= 0, with no rate."
  - "The projector lemma supplies only fixed-n qualitative sequences and contains no modulus involving loss error, the positive spectral margin, the coordinate envelope, or n."
  - "Selector-wide observable improvement fails already at the center triangle instance: another lawful stable minimax tie representative reverses the observable gap."
  - "No faithful same-topic field-level repair exists without a new crux-encoding approximation or tie-selection premise."
reusable_artifacts:
  - "discovery/core.json — final sound subfield theorem network and exact stability-price formulation"
  - "discovery/writeup.tex — sharp endpoint reduction, rank-stratified CAD certificates, stable-carrier construction, and exact triangle witnesses"
  - "reviews/review_general.json — final field-floor assessment and novelty receipts"
  - "orchestrator/decision_log.jsonl — full repair, adjudication, maximality, counterexample, and terminal history"
seeds_burned: []
proof_attempt_summary: |
  The derivation proved the sharp Frechet endpoint reduction, rank-stratified certification,
  measurable and encoded-input selectors, directed-local observable bridges, and a stable
  all-rank selector with explicit deployment price. The attempted field-level closure failed
  because the current assumptions provide no triangular-sequence approximation rate for that
  stability price, while an exact lawful stable minimax tie representative reverses the desired
  selector-wide observable gap. The resulting mathematics is sound and reusable at subfield tier;
  a field-tier revival needs genuinely new approximation or tie-selection primitives.
token_usage:
  complete: false
  orchestrator_tokens: 2763925
  pipeline_codex_tokens: 127199637
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-01"
---

# exp_crossworld_robust_controlvariate_design / v1 — Downgraded

**Topic.** Robust ex-ante Zhao control-variate bases under cross-world dependence uncertainty. Freeze a finite known network and assignment law, two mutually exclusive exposure events, iid bounded potential-outcome pairs, and an independent unpaired pilot identifying F1,F0 but not their copula. K1 derive sharp Fréchet covariance endpoints by rearrangement and prove fixed-basis loss is affine, so the adversary is an endpoint. K2 minimize the larger endpoint residual over normalized κ-regular block-separable projective bases, using certified interval branch-and-bound with ε-global guarantees and ε→0, while retaining the smaller endpoint gain as a secondary diagnostic; claim neither an SDP reduction nor a universal minimax equality. K3 prove strictly lower worst-copula residual variance than Zhao's c=0 surrogate on a relative-open lawful neighborhood. K4 prove plug-in robust-value and outer argmin-set consistency, with point convergence only for a singleton minimizer, then deliver a reproducible, explicitly unexecuted protocol for the Jiangxi PICC network experiment reanalyzed by Zhao that reconstructs the design, cross-fits robust and zero-covariance bases, deploys each held-out basis through the displayed observable ordinary-inverse control-variate estimator, and reports point estimates, design-randomization standard errors, endpoint and worst losses, minimum regularity, and a clearly heuristic optimization diagnostic, while distinguishing its internal split from the independent unpaired pilot model and asserting no numerical results absent authenticated replication data. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The triangle Bernoulli(1/3) witness gives the stated π and Ω; Bernoulli(1/2) margins admit observationally equivalent c=±1/4. Exact endpoint-mixture certificates give c=0 worst loss 521/1200 and robust constant loss 2613/8432, an absolute reduction 4912/39525 and a 28.62398% relative reduction. UNRESOLVED BOTTLENECK: Prove the certified global solver and uniform relative-open dominance/argmin correspondence for the full κ-regular class. EARLY KILL TEST: Recheck the certificate equality sets and run interval branch-and-bound on the triangle; stop if any c=0 optimizer has worst loss ≤2613/8432 or the claimed outer set convergence fails.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** D0.5 delivered a mathematically sound subfield result below the required field floor; no faithful same-topic field-level repair remains under the current assumptions.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
