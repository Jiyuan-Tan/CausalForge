---
qid: eid_lp_svar_nonequiv
spec: v1
topic: "Sharp non-equivalence theorem for local-projection (LP) versus structural-vector-autoregression (SVAR) identification of structural impulse responses under non-Gaussian innovations and partial sign restrictions. Plagborg-Moller and Wolf (2021, Econometrica) established that LP and SVAR estimate the same population impulse response under finite-order linear VAR data-generating processes when both use the same identifying restrictions; Montiel Olea, Plagborg-Moller, Qian, and Wolf (Econometrica, forthcoming) extend the equivalence to local projections under misspecification of lag length. The flagship question: characterize the sharp boundary at which LP and SVAR identify distinct structural impulse responses when innovations are non-Gaussian with bounded higher-cumulant restrictions a la Gourieroux-Monfort-Renne (2017) and Lanne-Meitz-Saikkonen (2017), and when the structural impact matrix is restricted only by a partial sign/zero pattern. The kernel claim is a closed-form algebraic non-equivalence theorem: under non-Gaussian innovations with bounded fourth cumulant gap, the LP-IRF and SVAR-IRF identify distinct functionals of the structural-shock distribution unless a cumulant-matching restriction is jointly imposed, recovering Plagborg-Moller-Wolf equivalence at the Gaussian limit."
novelty_target: flagship
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: re-raise
gap_reasons:
  # Verbatim/near-verbatim reviewer phrases from eid_lp_svar_nonequiv_v1_reviews.jsonl
  # (Stage 0.5 rounds; correctness PASS/REVISE throughout, novelty REJECT throughout).
  - "novelty:reject — The strict gap is assumed through A-quant-margin and then transferred by containment; this is a conditional field-or-lower result, not the requested flagship primitive generic non-equivalence theorem."
  - "novelty:reject — The primitive generic open-class separation needed for flagship status remains an open conjecture, so the derivation cannot meet novelty_target=flagship."
  - "novelty:reject — The note explicitly does not prove the primitive generic strict-gap conjecture, does not name a specific published estimator/workflow as a refuted target, and makes the strict support gap depend on the user-approved A-quant-margin assumption."
  - "novelty:reject — The actual proved kernel is a deterministic containment/support-function comparison plus a two-shock trigonometric witness, which is at most subfield and plausibly incremental relative to standard set-inclusion and rotation geometry."
  - "correctness:revise — the claimed confirmation of Conjecture 1 is not proved: the positive strict margin is assumed, and the equality Delta=chi is essentially the envelope lemma plus the definition of chi."
  - "correctness:revise — The headline strict-gap theorem obtains strict positivity by assuming the positive support-loss margin in Assumption A-quant-margin rather than deriving it; this is mathematically valid as a conditional implication but not a substantive theorem-level strict-gap proof."
  - "novelty:reject — Proposition 2 two-shock witness is a single planar special case rather than the generic-class obstruction required for flagship novelty."
  - "split_collapsed (route=user) — after the prior split granted A-quant-margin (theorem_splits=1), Theorem 1's strict-gap kernel reduces to a one-line bookkeeping transfer via R_SVAR(P) ⊆ R_LP(P) ∩ C_eps(P); no further split is autonomous-safe."
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted the flagship kernel Conjecture 1: primitive non-Gaussian fourth-cumulant
  + partial sign/zero conditions generically force a strictly positive LP/sign vs
  SVAR/sign support-function gap (Plagborg-Moller-Wolf equivalence recovered at the
  Gaussian limit). The solver could not derive the strict gap from primitives, so it
  split the theorem — substituting the kernel by promoting the strict gap into the
  user-approved Assumption A-quant-margin (chi_w(P)>0) and proving only the conditional
  Theorem 1, where the gap transfers by set containment R_SVAR(P) ⊆ R_LP(P) ∩ C_eps(P),
  plus a single planar two-shock trigonometric witness (gap = 1 - sqrt(2)/2). Reviewers
  confirmed the containment algebra and witness are correct but rejected on novelty:
  the strict gap is assumed not derived, no named published estimator is targeted, and
  the witness is a special case not a generic-class obstruction — field tier, below the
  flagship floor. What remains open: prove the primitive generic fourth-cumulant
  strict-gap obstruction (the demoted Conjecture 1) from moment/sign-cone geometry.
banked_on: "2026-05-16"
---

# eid_lp_svar_nonequiv / v1 — Downgraded

**Topic.** Sharp non-equivalence theorem for local-projection (LP) versus structural-vector-autoregression (SVAR) identification of structural impulse responses under non-Gaussian innovations and partial sign restrictions. Plagborg-Moller and Wolf (2021, Econometrica) established that LP and SVAR estimate the same population impulse response under finite-order linear VAR data-generating processes when both use the same identifying restrictions; Montiel Olea, Plagborg-Moller, Qian, and Wolf (Econometrica, forthcoming) extend the equivalence to local projections under misspecification of lag length. The flagship question: characterize the sharp boundary at which LP and SVAR identify distinct structural impulse responses when innovations are non-Gaussian with bounded higher-cumulant restrictions a la Gourieroux-Monfort-Renne (2017) and Lanne-Meitz-Saikkonen (2017), and when the structural impact matrix is restricted only by a partial sign/zero pattern. The kernel claim is a closed-form algebraic non-equivalence theorem: under non-Gaussian innovations with bounded fourth cumulant gap, the LP-IRF and SVAR-IRF identify distinct functionals of the structural-shock distribution unless a cumulant-matching restriction is jointly imposed, recovering Plagborg-Moller-Wolf equivalence at the Gaussian limit.

**Novelty target.** flagship

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REJECT

**Banking reason.** Re-review under widened flagship rubric (axes b/c added) — D0.5 still REJECT (route=user, theorem_splits cap hit + split_collapsed). Derivation reduces to one-line bookkeeping transfer R_SVAR(P) ⊆ R_LP(P) ∩ C_eps(P) after granting A-quant-margin; no axis-b non-equivalence threshold derived in closed form, no axis-c strict extension of named published regime. Math sound at field tier; flagship floor still unattainable in this kernel.

## Key files

- `eid_lp_svar_nonequiv_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_lp_svar_nonequiv_v1_proposal.tex` — final proposal version.
- `eid_lp_svar_nonequiv_v1.tex` — derivation note (if D0 ran).
- `eid_lp_svar_nonequiv_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `eid_lp_svar_nonequiv_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
