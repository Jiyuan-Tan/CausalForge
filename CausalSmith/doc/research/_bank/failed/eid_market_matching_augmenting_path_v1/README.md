---
qid: eid_market_matching_augmenting_path
spec: v1
topic: "Marketplace matching exact-ID failure by augmenting-path certificate: four-node path b1-s1-b2-s2 separates focal match probability while one-hop buyer summary is unchanged."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - angle0_v1: "N-promissory-object: the flagship sufficiency frontier names A_b(M), but Section 9 only computes Delta_AP for the four-node alias and does not exhibit the frontier object."
  - angle0_v1: "N-thin-survey: missed Doudchenko et al. 2020, Causal Inference with Bipartite Designs, a closer bipartite marketplace exposure-design comparator."
  - angle0_v1: "C-wellposed: matching-relevant alternating-path indicator was partly circular because it was defined by whether it can change mu_b."
  - angle0_v1: "C-proof-sketch: exact mu_b under the uniform maximum-matching tie rule requires counting maximum matchings, not just max-flow."
  - angle1_v1: "N-promissory-object: the AP sufficiency frontier and positive-alias-diameter certificate were still promised but not computed beyond the four-node example."
  - angle1_v1: "C-wellposed: radius-one class and path-indicator change were not defined independently enough for an arbitrary finite buyer summary and market class."
reusable_artifacts:
  - eid_market_matching_augmenting_path_v1_proposal_angle0_rejected.tex: first four-node augmenting-path witness and failed AP/audit frontier.
  - eid_market_matching_augmenting_path_v1_proposal_angle1_rejected.tex: best pivot with AP_b, alias diameter, SC10 witness, and still-failed AP frontier.
  - eid_market_matching_augmenting_path_v1_reviews/angle0_v1.json: reviewer diagnosis for promissory audit and missing bipartite-design comparators.
  - eid_market_matching_augmenting_path_v1_reviews/angle1_v1.json: reviewer diagnosis that the AP frontier needs a worked certificate extraction object, not only a four-node witness.
seeds_burned:
  - four_node_matching_augmenting_path_alias
  - AP_b_matching_summary_frontier
  - matching_alias_diameter_certificate
proof_attempt_summary: |
  Attempted to use the augmenting path b1-s1-b2-s2 as a non-do-calculus marketplace-interference object: M_full gives focal buyer b1 match probability 1, while M_cut gives 1/2 under uniform maximum-match tie-breaking, despite the same one-hop buyer summary. Reviewers found the witness concrete but not flagship: the general AP sufficiency frontier, audit algorithm, and alias-diameter certificate were promissory or circular, and the only fully computed object was the four-node example. Reuse the witness as a sanity check, but do not relaunch a matching-summary topic without a non-circular graph class plus a complete AP/certificate extraction transcript.
banked_on: "2026-05-25"
---

# eid_market_matching_augmenting_path / v1 - Failed

**Topic.** Marketplace matching exact-ID failure by augmenting-path certificate: four-node path `b1-s1-b2-s2` separates focal match probability while one-hop buyer summary is unchanged.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after two D-0.5 field-tier rejections across matching augmenting-path angles: angle 0 had promissory/circular AP sufficiency and audit objects, and angle 1 still promised AP frontier/certificate extraction without computing the constructive object beyond the four-node witness.

## Key Files

- `eid_market_matching_augmenting_path_v1_state.json` - pipeline state at banking (`banked: true`).
- `eid_market_matching_augmenting_path_v1_proposal_angle0_rejected.tex` - first rejected angle.
- `eid_market_matching_augmenting_path_v1_proposal_angle1_rejected.tex` - second rejected angle.
- `eid_market_matching_augmenting_path_v1_reviews.jsonl` - per-round reviewer log.
- `eid_market_matching_augmenting_path_v1_reviews/` - per-version reviewer JSON files.

## Notes

Reflection:

- Pipeline bug: none during the meaningful run; the active process chain was inspected and stopped before banking.
- Topic choice: better than a plain exposure-count alias, but still did not supply a general nonroutine object beyond a small witness.
- Proposer angle quality: angle 1 improved definitions and SC10/SC11, but did not compute the promised AP frontier or certificate extraction on a generic worked instance.
- Reviewer strictness: appropriate; it accepted novelty adjacency while enforcing the exhibited-object rule.
- Solver/math weakness: not a D0 solver issue; failure happened at proposal novelty and object concreteness.
