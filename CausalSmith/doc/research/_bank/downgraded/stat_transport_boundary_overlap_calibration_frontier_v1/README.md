---
qid: stat_transport_boundary_overlap_calibration_frontier
spec: v1
topic: "K1 prove the transported-mean minimax LOWER root-risk phase diagram m^-1/2 plus n^-1/2 for a<1, sqrt(log n/n) at a=1, and n^{-(s+1)/(2s+a+1)} for a>1 when f_S~x^a and f_T stays positive at zero, together with the matching deterministic truncated-oracle bias-standard-deviation envelope. K2 construct an executable capped calibrated-OT plus boundary local-polynomial realized-design linear/Hoeffding certificate, without claiming a data-measurable minimax upper bound or frontier attainment. K3 give a finite-sample fixed-class observable-radius coverage certificate, without claiming frontier-order expected length. K4 prove the matching lower bounds and the explicit nonadaptation obstruction; leave executable self-similar adaptation open. Include the boundary-bump and critical multiscale witnesses and the RICOT cardiomyopathy consumer. The measurable same-class upper bound, stochastic held-out weight localization, and frontier-order interval length remain open research objects."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: subfield
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The note proves a substantive three-regime minimax lower bound, including the critical logarithm, but it proves no matching upper bound for any data-measurable estimator."
  - "Consequently the advertised frontier remains an impossibility phase diagram paired with an oracle benchmark, rather than a settled minimax frontier, which keeps the contribution below the field floor."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/proof_archive/index.jsonl
  - discovery/d0_escalation_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  D0 completed the three-regime minimax lower phase diagram, boundary-local-polynomial
  oracle envelope, finite jet-LP bias certificate, and realized-design RiCOT/Hoeffding
  coverage result. The field-tier claim did not survive because no data-measurable
  estimator received a matching same-class upper risk bound. A future upgrade must
  prove held-out localization for capped RiCOT weights and frontier-order bounds for
  both the observable bias radius and the squared coefficient norm.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 308772790
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-08-31"
---

# stat_transport_boundary_overlap_calibration_frontier / v1 — Downgraded

**Topic.** K1 prove the transported-mean minimax LOWER root-risk phase diagram m^-1/2 plus n^-1/2 for a<1, sqrt(log n/n) at a=1, and n^{-(s+1)/(2s+a+1)} for a>1 when f_S~x^a and f_T stays positive at zero, together with the matching deterministic truncated-oracle bias-standard-deviation envelope. K2 construct an executable capped calibrated-OT plus boundary local-polynomial realized-design linear/Hoeffding certificate, without claiming a data-measurable minimax upper bound or frontier attainment. K3 give a finite-sample fixed-class observable-radius coverage certificate, without claiming frontier-order expected length. K4 prove the matching lower bounds and the explicit nonadaptation obstruction; leave executable self-similar adaptation open. Include the boundary-bump and critical multiscale witnesses and the RICOT cardiomyopathy consumer. The measurable same-class upper bound, stochastic held-out weight localization, and frontier-order interval length remain open research objects.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** subfield — below the requested field floor

**Banking reason.** The note proves no matching upper bound for any data-measurable estimator, so the contribution remains below the field floor.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The lower-bound phase diagram and oracle/LP constructions are reusable. Do not
rerun the same field-tier derivation unchanged: the independently validated gap
is new held-out localization theory, not a remaining carrier or proof repair.
