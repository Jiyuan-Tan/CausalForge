---
qid: eid_lp_svar_nonequiv
spec: upgrade2
topic: "Sharp non-equivalence theorem for local-projection (LP) versus structural-vector-autoregression (SVAR) identification of structural impulse responses under non-Gaussian innovations and partial sign restrictions. Plagborg-Moller and Wolf (2021, Econometrica) established that LP and SVAR estimate the same population impulse response under finite-order linear VAR data-generating processes when both use the same identifying restrictions; Montiel Olea, Plagborg-Moller, Qian, and Wolf (Econometrica, forthcoming) extend the equivalence to local projections under misspecification of lag length. The flagship question: characterize the sharp boundary at which LP and SVAR identify distinct structural impulse responses when innovations are non-Gaussian with bounded higher-cumulant restrictions a la Gourieroux-Monfort-Renne (2017) and Lanne-Meitz-Saikkonen (2017), and when the structural impact matrix is restricted only by a partial sign/zero pattern. The kernel claim is a closed-form algebraic non-equivalence theorem: under non-Gaussian innovations with bounded fourth cumulant gap, the LP-IRF and SVAR-IRF identify distinct functionals of the structural-shock distribution unless a cumulant-matching restriction is jointly imposed, recovering Plagborg-Moller-Wolf equivalence at the Gaussian limit."
novelty_target: flagship
supersedes:
  parent_qid: "eid_lp_svar_nonequiv"
  parent_spec: "v1"
  parent_tier: "downgraded"
  upgrade_axis: "generalization"
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - 'Theorem 1 (critical leakage frontier): ''The equality frontier is essentially the definition of eta_w^*(P) plus compactness of nested closed contact sets, so tier=field at best below novelty_target=flagship.'' (stage_0.5_to_0 attempt 2, dimension novelty)'
  - 'Theorem 1 / critical leakage frontier: ''The iff conclusion follows directly from defining eta_w^*(P) as the first leakage radius at which M_w(P) intersects Q_eta(P), so the headline theorem is tautological rather than an independent identification result.'' (stage_0.5_to_0 attempt 2, perItemFindings)'
  - 'Locked parameters: ''The run metadata declares exactid, but the note locks the theorem as a PartialID support-function structural time-series problem, changing the anchor cluster.'' (stage_0.5_to_0 attempt 2, perItemFindings)'
  - 'Theorem critical-leakage-frontier: ''The theorem proves the generic identity that support equality over a subset occurs iff a full-set support maximizer lies in the subset, with eta_w^* defined exactly as the first such intersection.'' (stage_0.5_to_0 angle 1 attempt 1, perItemFindings)'
  - 'Flagship tier floor: ''The assessed derivation tier is below flagship because the operational quantity is definitional and the theorem does not prove a new regime-opening identification, comparator frontier, strict class extension, or diagnose-then-correct result.'' (stage_0.5_to_0 angle 1 attempt 2, perItemFindings)'
  - 'Theorem 1: critical leakage support frontier: ''The equivalence h_LP=h_eta iff eta >= eta_w^*(P) follows almost immediately from defining eta_w^*(P) as the first leakage level at which the LP support face intersects Q_eta(P), so the current derivation is below the enforced flagship floor.'' (stage_0.5_to_0 angle 3 attempt 1, perItemFindings)'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  This run attempted to characterize a critical co-kurtosis leakage radius eta_w*(P) at which LP-sign and non-Gaussian SVAR identification coincide, upgrading the parent v1 from exact independence to bounded off-diagonal co-kurtosis leakage. Both conjectures were confirmed by D0 derivation, but D0.5 reviewers (across four independent angles, all reaching the same verdict) found the headline equivalence h_LP = h_eta iff eta >= eta_w*(P) to be a near-immediate unfold of the definition of eta_w*(P) itself — definitionally tautological rather than a flagship frontier. Compounding this, the locked-parameter block consistently anchored a PartialID support-function object while the run metadata declared the exactid cluster, a structural anchor drift that persisted unsalvaged across all pivot attempts; the pipeline was retired after exhausting its pivot budget with no angle clearing the flagship novelty floor.
banked_on: "2026-05-21"
---

# eid_lp_svar_nonequiv / upgrade2 — Failed

**Topic.** Sharp non-equivalence theorem for local-projection (LP) versus structural-vector-autoregression (SVAR) identification of structural impulse responses under non-Gaussian innovations and partial sign restrictions. Plagborg-Moller and Wolf (2021, Econometrica) established that LP and SVAR estimate the same population impulse response under finite-order linear VAR data-generating processes when both use the same identifying restrictions; Montiel Olea, Plagborg-Moller, Qian, and Wolf (Econometrica, forthcoming) extend the equivalence to local projections under misspecification of lag length. The flagship question: characterize the sharp boundary at which LP and SVAR identify distinct structural impulse responses when innovations are non-Gaussian with bounded higher-cumulant restrictions a la Gourieroux-Monfort-Renne (2017) and Lanne-Meitz-Saikkonen (2017), and when the structural impact matrix is restricted only by a partial sign/zero pattern. The kernel claim is a closed-form algebraic non-equivalence theorem: under non-Gaussian innovations with bounded fourth cumulant gap, the LP-IRF and SVAR-IRF identify distinct functionals of the structural-shock distribution unless a cumulant-matching restriction is jointly imposed, recovering Plagborg-Moller-Wolf equivalence at the Gaussian limit.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Flagship-generalization upgrade D0.5 REJECT (Case 6b unsalvageable conjecture): D-0.5 reached ACCEPT@flagship+clean_substance 4 times across angles 0/1/2/3; D0 honestly confirmed both conjectures (conj_1_verdict=confirmed, conj_2_verdict=confirmed); D0.5 rejected with proposal_promise_gap:tier_genuinely_below because the headline iff 'h_LP = h_eta iff eta >= eta_w*(P)' is a near-immediate support-function unfold of the very definition of eta_w*(P) — definitionally tautological, not a flagship frontier. Combined with the prior mechanism upgrade (D-0.5 NO-PASS, persistent C-* well-posedness flags on flagship drafts) and the original v1 + D0-retest (kernel_substituted both times), this kernel empirically tops out at field tier; the flagship framing of the LP-vs-single-law-non-Gaussian-SVAR strict-gap is structurally either tautological or refuted at the open-class scope. Banking decision: retire eid_lp_svar_nonequiv from flagship pursuit.

**Supersedes.** eid_lp_svar_nonequiv_v1 (tier=downgraded, upgrade_axis=generalization). The parent remains in _bank/downgraded/ as an independent reference; this entry is the flagship upgrade.

## Key files

- `eid_lp_svar_nonequiv_upgrade2_state.json` — pipeline state at banking (`banked: true`).
- `eid_lp_svar_nonequiv_upgrade2_proposal.tex` — final proposal version.
- `eid_lp_svar_nonequiv_upgrade2.tex` — derivation note (if Stage 0 ran).
- `eid_lp_svar_nonequiv_upgrade2_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_lp_svar_nonequiv_upgrade2_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
