---
qid: eid_frontdoor_multi_mediator
spec: v1
topic: "Sharp partial identification of the natural direct effect through multiple sequential mediators with bounded mediator-outcome confounding via negative-control proxies, when only the marginal mediator distributions are observed and the joint mediator dependency structure is partially specified"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: ACCEPT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # NOTE: D0.5 attempt 2 returned ACCEPT@field, but the user manually re-tiered
  # candidates->downgraded (state.json banked_reason): "Stage 0.5 reviewer ACCEPT
  # was too lenient; user judgment is the kernel does not actually clear the
  # field-tier bar." The substantive objection is D0.5 attempt-1 (REVISE, mixed),
  # re-affirmed by the user over the lenient attempt-2 ACCEPT. Verbatim phrases:
  - "The derivation currently delivers at most a subfield-level finite LP formulation plus a useful rational counterexample to rectangularization, below novelty_target=field."
  - "Proposition 1 is essentially the standard fact that a linear functional over a finite feasible polytope gives an outer interval ... That is correct but generic Manski/Balke-Pearl LP machinery."
  - "The flagship theorem ... proves a rational counterexample ... That is a useful technical witness, but it does not give a general sharp/tighter bound, a new class of proxy-mediator reductions, or a theorem resolving a previously open regime. It is best assessed as subfield-level unless strengthened."
  - "Sharpness is invoked rather than derived." / "Assumption 5 ... effectively assumes the finite realization step needed for sharpness, so it both lowers the novelty tier and leaves the flagship sharpness claim conditional."
  - "the producer needs more than prose adjustment ... add a real realization theorem ... explicitly constructing the finite potential-outcome/proxy distribution and proving canonical sharpness rather than assuming it."
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed sharp partial ID of the PNDE through two marginally-observed binary
  mediators with negative-control proxy bounds, kernel = a "shared latent face"
  where proxy-bridge equations and the unknown mediator coupling fail to
  decouple, so the sharp LP lower bound is attained at an interior coupling
  value and the rectangular relaxation is strictly nonsharp (Thm 1 routine LP
  envelope, flagship Conjecture 1, Thm 2 no-interaction reduction). Reviewers
  confirmed the LP/witness arithmetic and structural completeness; D0.5 attempt 1
  flagged the kernel as below field tier (generic Manski/Balke-Pearl LP plus a
  single rational counterexample) and noted sharpness was invoked via Assumption 5
  rather than derived (no finite potential-outcome/proxy model constructed).
  D0.5 attempt 2 flipped to ACCEPT@field, but the user manually re-tiered to
  downgraded judging that ACCEPT too lenient — the kernel does not clear field
  tier. Remains: a real realization theorem constructing the finite PO/proxy law
  (proving, not assuming, canonical sharpness) and a general non-rectangularity
  family rather than one witness.
banked_on: "2026-05-15"
---

# eid_frontdoor_multi_mediator / v1 — Candidates

**Topic.** Sharp partial identification of the natural direct effect through multiple sequential mediators with bounded mediator-outcome confounding via negative-control proxies, when only the marginal mediator distributions are observed and the joint mediator dependency structure is partially specified

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D0.5 ACCEPT at novelty_target=field; parked pending tournament selection.

Re-tiered to `downgraded` before 2026-07-18; the `candidates` tier was retired 2026-07-18 (see the "Retired tier" note in `_bank/README.md`). The original parked-pending-tournament banking note has been removed because it pointed at `_bank/candidates/`, a path that no longer exists. To re-raise, move this directory into `doc/research/active/<qid>/`, clear `banked` in state.json, and run `/causalsmith research --resume <qid> <spec>`.

## Key files

- `eid_frontdoor_multi_mediator_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_frontdoor_multi_mediator_v1_proposal.tex` — final proposal version.
- `eid_frontdoor_multi_mediator_v1.tex` — derivation note (if D0 ran).
- `eid_frontdoor_multi_mediator_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `eid_frontdoor_multi_mediator_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
