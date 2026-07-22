---
qid: pid_mediation_proxy
spec: v1
topic: "Sharp partial identification of natural direct and indirect effects in mediation with unobserved post-treatment confounders, using negative-control proxies for the latent mediator-outcome confounder and a single binary treatment"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Proposition thm:outer-sharp: ''The proposition is correct but tautological once E(P), B_sh(P), and ass:latent-polytope are introduced; it does not deliver a field-level partial-identification theorem.'''
  - 'Main contribution / novelty tier: ''tier=subfield below novelty_target=field; the surviving positive result is generic finite-LP sharpness plus convex separation, while the rank-one zonotope result is a negative correction of the proposal rather than a field-level published contribution.'''
  - 'Proposition thm:sharp-fails: ''The counterexample is only schematic: it asserts E(P)={0} and [ell,u]=[-1,1] without constructing a finite shared-null mediation instance satisfying the bridge, proxy, and mean-kernel restrictions.'''
  - 'Theorem thm:lp-sharp: ''The equality Theta_I(P)=Theta_LP(P) mismatches the earlier definition of Theta_I(P), which requires bridge feasibility and rank assumptions that the theorem and LP do not impose.'''
  - 'Novelty tier floor: ''tier=incremental below novelty_target=field; the kernel needs a genuinely new sharp proxy-mediation bound, observable full-fiber criterion, or nontrivial impossibility theorem to clear the floor.'''
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal attempted to prove that rank-deficient negative-control proxies yield a sharp non-rectangular joint identified set for (PNDE, TNIE) as a line segment parameterized by a shared bridge-null coordinate. Across three angles and ten revision cycles the flagship sharpness conjecture (E(P)=[ell,u]) was refuted in-derivation: what survived was only the definitional projection identity Theta_I(P)=f(E(P)) (thm:outer-sharp) plus elementary two-point affine-slope bookkeeping (thm:total-effect), both rated tier=incremental/subfield. No angle delivered a field-level new observable criterion, sharp LP construction, or non-trivial impossibility theorem, and the pivot budget was exhausted with no re-derivable kernel remaining.
banked_on: "2026-05-15"
---

# pid_mediation_proxy / v1 — Failed

**Topic.** Sharp partial identification of natural direct and indirect effects in mediation with unobserved post-treatment confounders, using negative-control proxies for the latent mediator-outcome confounder and a single binary treatment

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** REJECT

**Banking reason.** D-0.5 ACCEPT angle 2 v5 tier=field; D0.5 REJECT (novelty, case 6b) — kernel collapsed to definitional projection identity Theta_I(P)=f(E(P)); pivot budget exhausted across angles 0/1/2.

## Key files

- `pid_mediation_proxy_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_mediation_proxy_v1_proposal.tex` — final proposal version.
- `pid_mediation_proxy_v1.tex` — derivation note (if D0 ran).
- `pid_mediation_proxy_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_mediation_proxy_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
