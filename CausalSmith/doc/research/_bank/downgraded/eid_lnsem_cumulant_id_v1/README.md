---
qid: eid_lnsem_cumulant_id
spec: v1
topic: "Constructive identification in linear non-Gaussian SEMs under general non-factor confounding: for a direct-effect coefficient certified generically identifiable by the non-intersecting-path v-rank criterion of Tramontano-Drton-Etesami 2024 -- whose proof only produces a rank witness in the UNOBSERVED mixing matrix B_Lambda and yields no observable-side formula -- derive the EXPLICIT closed-form identifying functional expressing the coefficient as a rational function of OBSERVABLE higher-order cross-cumulants, via a cumulant-transfer that uses cumulant multilinearity and the bidirected connected-set vanishing pattern to cancel the general confounding at the cumulant order the graph dictates; this is the higher-cumulant generalization of the covariance IV ratio, valid precisely where second moments and linear-factor LiNGAM / over-complete-ICA identities fail once the parent edge carries a bow, with a consistent plug-in sample-cumulant estimator and delta-method inference as a plug-in corollary."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # D0.5 decision/rubric referee (verdict: revise), verbatim:
  - "novelty-floor-miss @ thm:closed-form-coefficient: The determinant-ratio theorem is conditional on choosing C in Mcal_m, where Mcal_m is defined by the same row-uniform transfer the theorem exploits, so this node reads as a packaging kernel rather than a field-level theorem against the cited literature."
  - "subclass-positioning @ thm:source-isolated-covariance-admissible: The strongest unconditional positive result is a covariance-order source-isolated subclass theorem that lands in the known IV/half-trek comparator class, and the note does not yet make the theorem-level case that this subclass opening clears the injected field novelty floor."
  # D0.5 math referee (verdict: revise) — mechanical, NON-load-bearing (proof already correct):
  - "setup @ thm:source-isolated-covariance-admissible: The source-isolation clause is stated too strongly: because each witness node i_r is an ancestor of p_r, requiring i_r to be bidirected-disconnected from every ancestor of P_v union {v} forces i_r to be disconnected from itself; the proof and supporting lemma use the distinct-ancestor version instead. (FIX: quantify over distinct t != i_r; proof unchanged.)"
  # Codex field-reachability adjudication (gpt-5.5) — WHY field is BLOCKED, not merely unproven:
  - "The field-clearing move is an UNCONDITIONAL higher-order (beyond covariance/IV/half-trek) existence theorem: a named graph class with a TDE-certified bowed edge u->v where covariances fail yet a finite m>2 admissible family exists. Codex showed the natural order-3 bowed-edge construction is BLOCKED: to make the row scalar A = kappa_X(u,u,c) generically nonzero the augmentation must be bidirected-connected to u, but because u<->v the contaminating cumulant kappa(eps_u,eps_v,X_c) is then also connected and generically nonzero (connected-set Markov does not kill it); disconnect the augmentation enough to kill the contamination and it kills A too. Bow contamination is MONOTONE under adding connected augmentation variables. The paper's own oeq:finite-order-transfer already resolves NEGATIVELY (explicit m_star=infinity witness), corroborating the block."
reusable_artifacts:
  # Sound, liftable math for a future subfield bank or a flagship re-raise that first cracks the higher-order-existence block:
  - "discovery/writeup.tex — full proved paper (conditional cumulant-transfer kernel + order-2 source-isolated unconditional subclass + both negative OEQ resolutions + plug-in delta-method inference)."
  - "discovery/core.json — all proofs (thm:cumulant-row-system, thm:closed-form-coefficient, prop:iv-reduction, thm:source-isolated-covariance-admissible + lemmas), status=proved."
  - "discovery/d0_escalation_log.jsonl — the maximality directive that added thm:source-isolated-covariance-admissible."
seeds_burned: []
proof_attempt_summary: |
  Attempted: an explicit observable identifying functional (Cramer determinant ratio of higher-order
  cumulants) for a TDE-2024-certified direct edge under general non-factor confounding — the observable
  analogue of TDE's hidden B_Lambda rank witness. PROVED (sound): the conditional row-system + determinant
  ratio GIVEN a cumulant-admissible family, its witness-invariance, plug-in delta-method inference, the
  order-2 collapse to the covariance IV ratio, an UNCONDITIONAL order-2 source-isolated subclass theorem,
  and NEGATIVE resolutions of both open questions (finite admissible family need not exist: m_star=infinity
  witness; m_star is not a sharp information frontier). COLLAPSED (for FIELD): no nonempty higher-order
  (beyond covariance/IV/half-trek) admissible class is proved — the main kernel is conditional "packaging"
  and the only unconditional result sits in the known IV/half-trek layer; codex showed the natural higher-order
  existence theorem is BLOCKED (monotone bow contamination), not merely missing. REMAINS (flagship re-raise):
  find a graph class + explicit m>2 augmentation that beats the monotone-bow block, or a general
  necessary-and-sufficient graph criterion for M_m nonemptiness — both genuine open-research problems.
banked_on: "2026-07-07"
---

# eid_lnsem_cumulant_id / v1 — Downgraded

**Topic.** Constructive identification in linear non-Gaussian SEMs under general non-factor confounding: for a direct-effect coefficient certified generically identifiable by the non-intersecting-path v-rank criterion of Tramontano-Drton-Etesami 2024 -- whose proof only produces a rank witness in the UNOBSERVED mixing matrix B_Lambda and yields no observable-side formula -- derive the EXPLICIT closed-form identifying functional expressing the coefficient as a rational function of OBSERVABLE higher-order cross-cumulants, via a cumulant-transfer that uses cumulant multilinearity and the bidirected connected-set vanishing pattern to cancel the general confounding at the cumulant order the graph dictates; this is the higher-cumulant generalization of the covariance IV ratio, valid precisely where second moments and linear-factor LiNGAM / over-complete-ICA identities fail once the parent edge carries a bow, with a consistent plug-in sample-cumulant estimator and delta-method inference as a plug-in corollary.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Math sound; the conditional cumulant-transfer determinant-ratio kernel is a valid observable identifying functional on the TDE frontier GIVEN an admissible family, but it does not clear the FIELD floor: no nonempty higher-order (beyond covariance/IV/half-trek) admissible class is proved, and codex showed the natural bowed-edge order-3 construction is BLOCKED (bow contamination is monotone under connected augmentation), so the only unconditional result is the order-2 source-isolated subclass which lands in the known IV/half-trek layer.

## Key files

- `eid_lnsem_cumulant_id_v1_state.json` — pipeline state at banking (`banked: true`).
- `eid_lnsem_cumulant_id_v1_proposal.tex` — final proposal version.
- `eid_lnsem_cumulant_id_v1.tex` — derivation note (if Stage 0 ran).
- `eid_lnsem_cumulant_id_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_lnsem_cumulant_id_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
