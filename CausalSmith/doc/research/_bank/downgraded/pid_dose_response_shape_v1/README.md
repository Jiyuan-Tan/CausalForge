---
qid: pid_dose_response_shape
spec: v1
topic: "Sharp partial identification of continuous-treatment dose-response curves under monotone-and-concave shape restrictions and bounded unmeasured confounding, without an instrument"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: unknown  # was solver_blocked; corrected — no solver/F-phase ran, kernel was refuted at D0 math derivation, not blocked by a solver
reraise_status: true-negative
gap_reasons:
  # Verbatim / near-verbatim reviewer phrases (source: pid_dose_response_shape_v1_reviews.jsonl, D0.5 attempts 1-3).
  - "the only field-tier kernel (law-level joint sharpness) is refuted by the density-version obstruction, leaving only generic Manski-style outer containment"
  - "Lemma \\ref{lem:pasting} refutes the proposed law-level normalization-pasting sharpness claim; without that reverse inclusion, the kernel cannot reach the enforced field novelty floor"
  - "The flagship theorem proves only Theta_I(P) subset Theta_{Gamma,mc}(P), a routine outer containment once pointwise intervals and monotone-concavity are assumed"
  - "changing density values at finitely many continuous-dose points changes only representatives, not the conditional treatment law"
  - "The pointwise sharp sensitivity intervals are imported as a primitive rather than derived, so the theorem-level contribution is the finite-dimensional LP closure, not a new sensitivity-identification result"
  - "the kernel is generic finite-grid shape closure of assumed sharp pointwise intervals, not a field-level new bound or regime"
  - "to lift the note to field tier it would need either a new law-invariant sharpness theorem under the locked restrictions or a changed primitive ... which would materially alter the current locked law-level problem"
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The D-0.5 proposal headlined Conjecture 1 (finite-grid CMSM normalization-pasting / joint sharpness): the
  reverse inclusion that every shape-compatible vector in the pointwise sensitivity polytope is realizable by a
  single full-data hidden-confounding law, which was the only field-tier kernel. At D0 the producer's own Lemma
  (lem:pasting) refuted that kernel via a density-version obstruction — finite-point density-ratio changes alter
  only representatives, not the conditional treatment law — so the reverse inclusion fails. What survived and was
  delivered is the forward outer containment Theta_I(P) ⊆ Theta_{Gamma,mc}(P): generic Manski-style interval
  completion intersected with a monotone-concave LP projection, plus a correct three-dose concavity chord
  proposition. All three D0.5 reviews pass correctness but reject on novelty; the surviving result sits below the
  novelty_target=field floor. Run halted at the D0.5 review boundary (user intervention); no Lean / F-phase ran.
banked_on: "2026-05-14"
---

# pid_dose_response_shape / v1 — Downgraded

**Topic.** Sharp partial identification of continuous-treatment dose-response curves under monotone-and-concave shape restrictions and bounded unmeasured confounding, without an instrument

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REJECT

**Banking reason.** D-0.5 ACCEPT angle 0 v3 tier=field; D0.5 REJECT (novelty) — density-version obstruction collapses the only field-tier kernel; surviving result is generic Manski-style outer containment plus monotone-concave LP projection.

## Key files

- `pid_dose_response_shape_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_dose_response_shape_v1_proposal.tex` — final proposal version.
- `pid_dose_response_shape_v1.tex` — derivation note (if D0 ran).
- `pid_dose_response_shape_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_dose_response_shape_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
