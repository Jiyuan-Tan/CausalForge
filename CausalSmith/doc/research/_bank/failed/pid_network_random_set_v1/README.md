---
qid: pid_network_random_set
spec: v1
topic: "Random-set sharp partial identification of direct and indirect treatment effects under sparse-network interference when the exposure mapping support is unknown but bounded in cardinality"
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Conjecture 1: strict-cellwise-frontier — refuted-with-counterexample: the stated K=2,n=4 witness law P-star has F_2(P-star)=empty, so the advertised finite compatibility gap Gamma_2(u;P-star) is not a well-defined sparse-versus-cellwise support-program comparison.'
  - 'Conjecture 2: joint-nonrectangular — refuted-with-counterexample: unit 2''s four neighbor-assignment means at a=0 are 0.33, 0.44, 0.40, 0.51; any K=2 exposure map must merge two distinct states, violating observed-law matching, so F_2(P-star) is empty and Delta_2 cannot satisfy the claimed >=1/40 margin.'
  - 'Theorem certificate: novelty — the endpoint-certificate result is a finite feasibility split obtained from finite-dimensional Farkas separation and exhaustive enumeration; it does not open a new identification regime, name a new random-set object, or provide an algorithmic identifiability result with complexity beyond brute-force enumeration — below the orchestrator''s flagship novelty floor.'
  - 'Main theorems: novelty — the accepted positive content is the endpoint-certificate theorem, not the strict-cellwise frontier or joint-nonrectangularity conjectures, and it is below the required flagship novelty floor.'
  - 'Novelty target: novelty — assessed tier is below flagship, violating the orchestrator-enforced novelty_target=flagship floor.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal targeted a flagship partial-identification result: a sharp joint direct/indirect decomposition set for sparse-K latent exposure networks, anchored by a strict shared-map cellwise-vs-network compatibility frontier (Conjecture 1) and a generic open-set joint nonrectangularity theorem (Conjecture 2). Both conjectures collapsed because the advertised K=2, n=4 witness law P-star has an empty K=2 sparse feasible class — unit 2's four distinct neighbor-state conditional means (0.33, 0.44, 0.40, 0.51 at a=0) cannot be represented by any two-label exposure map, so F_2(P-star) is empty and the claimed 1/40 gaps for Gamma_2 and Delta_2 are not valid. The only surviving positive result is Conjecture 3 (the endpoint-certificate Farkas/enumeration dichotomy), which reviewers unanimously classified as sub-flagship (finite LP infeasibility plus brute-force 0-1 enumeration, opening no new sharp-bound regime or named mathematical object); after five angles and exhausting the pivot budget, no angle produced a flagship-grade replacement.
banked_on: "2026-05-22"
---

# pid_network_random_set / v1 — Failed

**Topic.** Random-set sharp partial identification of direct and indirect treatment effects under sparse-network interference when the exposure mapping support is unknown but bounded in cardinality

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** REJECT

**Banking reason.** Stage -1.2 NO-PASS @ flagship (D-1.2 effort=high). 22 reviewer rounds across 4 angles; one angle cleared D-0.5 ACCEPT@flagship, then D-0.5→0 review fast-pathed REJECT (Case 6b kernel_substituted): the advertised P-star witness for K=2 sparse exposure had an empty feasible class — unit 2's four distinct a=0 neighbor-state means (0.33/0.44/0.40/0.51) cannot be represented by two exposure labels, so the claimed 1/40 sharp gaps are not valid. Surviving finite Farkas/enumeration certificate is sound but subfield/incremental. High-effort drafter wrote a more concrete witness (good), but the construction was self-refuting (caught by artifact audit, not concealed).

## Key files

- `pid_network_random_set_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_network_random_set_v1_proposal.tex` — final proposal version.
- `pid_network_random_set_v1.tex` — derivation note (if Stage 0 ran).
- `pid_network_random_set_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_network_random_set_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
