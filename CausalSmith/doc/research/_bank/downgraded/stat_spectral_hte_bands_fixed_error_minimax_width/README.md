---
qid: stat_spectral_hte_bands
spec: fixed_error_minimax_width
topic: "Honest minimax-width uniform confidence bands for a Hölder heterogeneous treatment-slope curve in a varying-coefficient partially linear model under fixed non-Gaussian treatment-noise separation, using the accepted contour-annihilator bank to remain valid with fixed nonzero conditional L1 treatment-code error and no outcome learner; prove primitive-condition simultaneous coverage and a matching all-band expected-width lower bound."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: solver_blocked
reraise_status: re-raise
gap_reasons:
  - "tier=subfield, paper_score_ceiling=6.8, meets_floor=false; required floor/target=field with ceiling_for_field=7."
  - "lem:uniform-bahadur-multiplier still lacks full derivations of selected-score entropy, same-sample plug-in empirical-L2 control, uniform studentization, o(r_n) fallback/bad-event rates, and the complementary-event critical-value moment bound; selector pilot-rate derivation is also abbreviated."
  - "A field-tier lift would require a genuinely new result—e.g. a sharp weak-separation phase diagram or a lower bound essentially driven by persistent code error—or a materially expanded learner model."
reusable_artifacts:
  - discovery/proto_core.json
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/d0_working.json
  - discovery/proof_archive/index.jsonl
  - reviews/review_general.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run constructed a total split-sample contour band and a matching all-band
  width lower-bound program at r_n=(log n/n)^(beta/(2 beta+1)), using the accepted
  contour-annihilator bank under a frozen externally certified treatment code.
  D0.5 accepted the mathematical interface but the cold review placed the result
  at subfield novelty and identified incomplete empirical-process derivations.
  Future work should reuse the contour bank and exact-code converse, while fully
  proving the score-class coupling and adding a genuinely new field-tier axis.
banked_on: "2026-08-23"
---

# stat_spectral_hte_bands / fixed_error_minimax_width — Downgraded

**Topic.** Honest minimax-width uniform confidence bands for a Hölder heterogeneous treatment-slope curve in a varying-coefficient partially linear model under fixed non-Gaussian treatment-noise separation, using the accepted contour-annihilator bank to remain valid with fixed nonzero conditional L1 treatment-code error and no outcome learner; prove primitive-condition simultaneous coverage and a matching all-band expected-width lower bound.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Cold D0.5 review assessed subfield at 6.8, below the field floor of 7; the in-scope empirical-process repair cannot reach field novelty, while the proposed learner-certificate repair is outside the frozen supplied-code model.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

This is a downgraded research artifact, not an accepted theorem. Reuse the
noise-only contour bank, reference-localized selector, and exact-code lower-bound
construction; re-derive the selected-score empirical-process and studentization
steps before presenting the confidence-band theorem as sound.
