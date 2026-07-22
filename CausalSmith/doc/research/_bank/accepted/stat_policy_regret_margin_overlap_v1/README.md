---
qid: stat_policy_regret_margin_overlap
spec: v1
topic: "Matching minimax characterization of the offline policy-learning welfare-regret rate under one-sided overlap decay and a Tsybakov margin. Estimand: expected welfare regret E[R(pi_hat) - inf_pi R(pi)] of a learned treatment-assignment policy (a risk functional of P; point-identified under strict overlap, so this is an estimation-RATE problem, not identification). THEOREM TO PROVE, two directions: (T1 achievability) a trimmed/clipped-AIPW-score ERM, with propensity clipping threshold t_n tied to a one-sided polynomial overlap-decay exponent gamma (e(x) -> {0,1} like distance-to-boundary^gamma) and operating under a Tsybakov margin exponent alpha at the decision boundary tau(x)=0, attains E[R(pi_hat) - inf R(pi)] <= C n^{-r(alpha,gamma)} with r(alpha,gamma) in closed form; (T2 converse, THE CORE CONTRIBUTION) a localized fuzzy-hypothesis (Le Cam / many-hypothesis) construction with propensity shrinking pi_lambda ~ h^rho on local cubes, whose LOCAL OVERLAP-MARGIN CALIBRATION LEMMA (the Hellinger/KL-equalizing balance among the regret-separation height, the propensity-decay height, and the local cube geometry) is derived explicitly, giving a minimax lower bound n^{-r(alpha,gamma)} matching T1. The named focal object is this calibration lemma plus the matched exponent r(alpha,gamma); the (alpha,gamma) phase boundary (margin-driven branch vs overlap-limited branch) is READ OFF the closed calibration, not assumed. Differentiation: Athey-Wager Ecta'21 give n^{-1/2} under strict overlap with no margin; Luedtke-Chambaz give the margin-alpha fast rate under strict positivity (load-bearing only via influence-function boundedness); Bibaut et al. 2510.15483 treat ONLINE cumulative bandit regret, upper-bound only, with a constant overlap floor and no minimax converse. This proposal is FIXED offline one-sided overlap decay with a matching lower bound, explicitly distinct from adaptive diminishing-exploration policy-learning minimax results."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  # TODO: paste verbatim reviewer phrases identifying which Conjecture
  # collapsed and why. Source: stat_policy_regret_margin_overlap_v1_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.
banked_on: "2026-07-10"
paper_score: 6
paper_score_rationale: "The core lower-bound calibration appears correct and potentially useful, but the paper is still too narrow and too conditionally framed, with several claim-fidelity and presentation problems that prevent publication as written."
---

# stat_policy_regret_margin_overlap / v1 — Accepted

**Topic.** Matching minimax characterization of the offline policy-learning welfare-regret rate under one-sided overlap decay and a Tsybakov margin. Estimand: expected welfare regret E[R(pi_hat) - inf_pi R(pi)] of a learned treatment-assignment policy (a risk functional of P; point-identified under strict overlap, so this is an estimation-RATE problem, not identification). THEOREM TO PROVE, two directions: (T1 achievability) a trimmed/clipped-AIPW-score ERM, with propensity clipping threshold t_n tied to a one-sided polynomial overlap-decay exponent gamma (e(x) -> {0,1} like distance-to-boundary^gamma) and operating under a Tsybakov margin exponent alpha at the decision boundary tau(x)=0, attains E[R(pi_hat) - inf R(pi)] <= C n^{-r(alpha,gamma)} with r(alpha,gamma) in closed form; (T2 converse, THE CORE CONTRIBUTION) a localized fuzzy-hypothesis (Le Cam / many-hypothesis) construction with propensity shrinking pi_lambda ~ h^rho on local cubes, whose LOCAL OVERLAP-MARGIN CALIBRATION LEMMA (the Hellinger/KL-equalizing balance among the regret-separation height, the propensity-decay height, and the local cube geometry) is derived explicitly, giving a minimax lower bound n^{-r(alpha,gamma)} matching T1. The named focal object is this calibration lemma plus the matched exponent r(alpha,gamma); the (alpha,gamma) phase boundary (margin-driven branch vs overlap-limited branch) is READ OFF the closed calibration, not assumed. Differentiation: Athey-Wager Ecta'21 give n^{-1/2} under strict overlap with no margin; Luedtke-Chambaz give the margin-alpha fast rate under strict positivity (load-bearing only via influence-function boundedness); Bibaut et al. 2510.15483 treat ONLINE cumulative bandit regret, upper-bound only, with a constant overlap floor and no minimax converse. This proposal is FIXED offline one-sided overlap decay with a matching lower bound, explicitly distinct from adaptive diminishing-exploration policy-learning minimax results.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Auto-banked 2026-07-10; tier_at_proposal=ACCEPT, tier_at_derivation=NA, novelty_target=field.

## Key files

- `stat_policy_regret_margin_overlap_v1_state.json` — pipeline state at banking (`banked: true`).
- `stat_policy_regret_margin_overlap_v1_proposal.tex` — final proposal version.
- `stat_policy_regret_margin_overlap_v1.tex` — derivation note (if Stage 0 ran).
- `stat_policy_regret_margin_overlap_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `stat_policy_regret_margin_overlap_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
