---
qid: pid_network_exposure_aliasing_graphpair
spec: v1
topic: "Network exposure aliasing by finite graph-pair certificate: compare C6 with two disjoint triangles under iid Bernoulli treatment. Both graphs have identical one-hop treated-neighbor count law Binomial(2,p), but differ in triangle-closure exposure under a local quadratic spillover law."
novelty_target: flagship
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - angle0_v1: "N-no-comparator-chain: tier=field below novelty_target=flagship; the kernel is a single finite C6/2K3 alias class tied mainly to one rooted-configuration comparator, not a generic-class frontier or multi-comparator chain."
  - angle0_v1: "C-definitional-unfold: proof route is only adjacency enumeration plus E[Z_j Z_k]=p^2, so the finite separator is correct but too elementary for flagship tier."
  - angle0_v2: "N-comparator-drift: comparator_promise_table claims strict_tightening or iff_frontier, but no Section 8 headline is phrased as a strict tightening or iff frontier against any named published result."
  - angle0_v2: "C-coherence: the conjecture quantifies over every two-regular graph, but Assumption 1 fixes only the two candidate graphs C6 and 2K3."
  - angle0_v2: "C-definitional-unfold: mu_G depends on G only through the already-defined average closure count tau_cl; the proposed frontier is essentially linearity plus the definition of the quotient."
reusable_artifacts:
  - pid_network_exposure_aliasing_graphpair_v1_proposal.tex: finite C6 versus 2K3 closure witness, including degree-two one-hop count alias and Delta_cl(1/2)=1/4 calculation.
  - pid_network_exposure_aliasing_graphpair_v1_reviews/angle0_v1.json: reviewer checklist for why finite network-exposure witnesses stay field-tier without a generic comparator-anchored frontier.
  - pid_network_exposure_aliasing_graphpair_v1_reviews/angle0_v2.json: exact failure modes for tau_cl frontier attempts, especially comparator drift and definitional quotient collapse.
seeds_burned:
  - C6_vs_2K3_one_hop_count_alias
  - tau_cl_two_regular_closure_frontier
proof_attempt_summary: |
  Attempted a network-exposure graph-pair aliasing theorem: C6 and 2K3 have the same one-hop treated-neighbor count law Binomial(2,p), but differ in triangle-closure exposure under a local quadratic spillover law. The witness table was concrete and correct, but both novelty reviews classified the object as field-tier because the proof is adjacency enumeration plus E[Z_j Z_k]=p^2 and the attempted tau_cl frontier was a definitional quotient rather than a nonroutine published-result delta. Reuse the C6/2K3 table only as a sanity-check witness, not as a flagship topic unless a genuinely broader invariant/minimality theorem is hand-derived first.
banked_on: "2026-05-25"
---

# pid_network_exposure_aliasing_graphpair / v1 - Failed

**Topic.** Network exposure aliasing by finite graph-pair certificate: compare C6 with two disjoint triangles under iid Bernoulli treatment. Both graphs have identical one-hop treated-neighbor count law Binomial(2,p), but differ in triangle-closure exposure under a local quadratic spillover law.

**Novelty target.** flagship

**Stage -0.5 verdict.** REJECT

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after two D-0.5 novelty reviews on the same C6/2K3 closure-separator object: v1 was field-tier/revise and v2 was field-tier/reject because the finite separator was elementary, the comparator chain stayed thin, and the proposed closure frontier did not rise above routine rooted-configuration/network-exposure specialization.

## Key files

- `pid_network_exposure_aliasing_graphpair_v1_state.json` - pipeline state at banking (`banked: true`).
- `pid_network_exposure_aliasing_graphpair_v1_proposal.tex` - final proposal version.
- `pid_network_exposure_aliasing_graphpair_v1_reviews.jsonl` - per-round reviewer log.
- `pid_network_exposure_aliasing_graphpair_v1_reviews/` - per-version reviewer JSON files.

## Notes

Reflection:

- Pipeline bug: none during banking; the active qid process chain was inspected and stopped before bank_entry.ts.
- Topic choice: too weak for flagship; finite graph-pair exposure aliasing sounded concrete but lacked a hard theorem beyond the witness.
- Proposer angle quality: v2 improved wording and added tau_cl, but the underlying object stayed the same field-tier closure separator.
- Reviewer strictness: appropriate; the reviews separated a correct finite certificate from a flagship-level contribution.
- Solver/math weakness: not a D0 solver issue; the run failed at novelty/proposal strength before formal derivation.
