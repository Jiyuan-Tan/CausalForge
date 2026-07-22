---
qid: pid_factorial_did_moderation_bounds
spec: v1
topic: "Flagship partial-identification upgrade for factorial difference-in-differences: characterize the sharp identified set for causal moderation in a finite 2x2 factorial DiD design when the standard FDID estimand identifies only effect modification, allowing a bounded imbalance budget between moderator strata in untreated trends. Recover the recent factorial-DID point-identification result at zero imbalance, give an exact finite-cell LP/dual interval for moderation under nonzero imbalance, and exhibit a concrete witness where effect modification and causal moderation have opposite signs."
novelty_target: flagship
tier_at_proposal: NONFLAGSHIP-KILL
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "Conjecture 1: N-mischar -- Rambachan-Roth, Balke-Pearl, and Demuynck are generic sensitivity/LP templates; current kernel is an FDID specialization, so tier=field below novelty_target=flagship."
  - "Conjecture 1: C-definitional-unfold -- the projection/lift equality follows directly by choosing latent untreated means and treatment increments; the remaining LP duality is routine."
  - "Theorem 2: C-definitional-unfold -- the support formula h_eta(d;rho)=min{rho_*,rho0+rho1} is just the defining inequalities plus matching two-point witnesses."
  - "Setup: prior C-wellposed/C-coherence flags were repaired by v3, but the repaired object became even more visibly a finite-cell sensitivity note rather than a flagship theorem."
reusable_artifacts:
  - path: "pid_factorial_did_moderation_bounds_v1_gaps.json"
    kind: literature_map
    one_line: "Useful FDID map: Xu-Zhao-Ding 2026, Bansak 2021, VanderWeele 2009, Rambachan-Roth 2023, Manski-Pepper 2018, Balke-Pearl 1997, Demuynck 2015."
  - path: "pid_factorial_did_moderation_bounds_v1_reviews/angle0_v3.json"
    kind: counterexample
    one_line: "Cleanest reviewer diagnosis: after setup repair, the flagship claim is still a field-tier definition unfold/support calculation."
  - path: "pid_factorial_did_moderation_bounds_v1_proposal.tex"
    kind: lp_setup
    one_line: "Reusable as a field-tier FDID causal-moderation sensitivity scaffold, not as a flagship candidate."
seeds_burned: []
proof_attempt_summary: |
  Attempted a new finite factorial-DiD partial-ID topic rather than an upgrade, targeting causal moderation when standard FDID identifies only effect modification. The literature gap was real and the pipeline worked, but the reviewer plateaued at field tier: once the observable/latent setup was repaired, the main sharpness and sign-frontier claims reduced to generic finite LP/support-function calculations. Treat this as a topic-strength failure, not a strict-reviewer failure; a future version would need a genuinely non-definitional FDID restriction class or an inference theorem, not just the finite-cell sensitivity interval.
banked_on: "2026-05-24"
---

# pid_factorial_did_moderation_bounds / v1 â€” Failed

**Topic.** Flagship partial-identification upgrade for factorial difference-in-differences: characterize the sharp identified set for causal moderation in a finite 2x2 factorial DiD design when the standard FDID estimand identifies only effect modification, allowing a bounded imbalance budget between moderator strata in untreated trends. Recover the recent factorial-DID point-identification result at zero imbalance, give an exact finite-cell LP/dual interval for moderation under nonzero imbalance, and exhibit a concrete witness where effect modification and causal moderation have opposite signs.

**Novelty target.** flagship

**Stage -0.5 verdict.** NONFLAGSHIP-KILL

**Stage 0.5 verdict.** NA

**Banking reason.** Interrupted during Stage -0.5 after three consecutive REVISE reviews at field tier: the finite FDID moderation-bounds topic had a real literature gap but the reviewer kept blocking flagship status on remaining novelty/correctness issues, so it was stopped before burning the full pivot budget.

## Key files

- `pid_factorial_did_moderation_bounds_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `pid_factorial_did_moderation_bounds_v1_proposal.tex` â€” final proposal version.
- `pid_factorial_did_moderation_bounds_v1.tex` â€” derivation note (if Stage 0 ran).
- `pid_factorial_did_moderation_bounds_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_factorial_did_moderation_bounds_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
