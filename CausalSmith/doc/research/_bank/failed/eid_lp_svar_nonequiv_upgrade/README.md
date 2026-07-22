---
qid: eid_lp_svar_nonequiv
spec: upgrade
topic: "Sharp non-equivalence theorem for local-projection (LP) versus structural-vector-autoregression (SVAR) identification of structural impulse responses under non-Gaussian innovations and partial sign restrictions. Plagborg-Moller and Wolf (2021, Econometrica) established that LP and SVAR estimate the same population impulse response under finite-order linear VAR data-generating processes when both use the same identifying restrictions; Montiel Olea, Plagborg-Moller, Qian, and Wolf (Econometrica, forthcoming) extend the equivalence to local projections under misspecification of lag length. The flagship question: characterize the sharp boundary at which LP and SVAR identify distinct structural impulse responses when innovations are non-Gaussian with bounded higher-cumulant restrictions a la Gourieroux-Monfort-Renne (2017) and Lanne-Meitz-Saikkonen (2017), and when the structural impact matrix is restricted only by a partial sign/zero pattern. The kernel claim is a closed-form algebraic non-equivalence theorem: under non-Gaussian innovations with bounded fourth cumulant gap, the LP-IRF and SVAR-IRF identify distinct functionals of the structural-shock distribution unless a cumulant-matching restriction is jointly imposed, recovering Plagborg-Moller-Wolf equivalence at the Gaussian limit."
novelty_target: flagship
supersedes:
  parent_qid: "eid_lp_svar_nonequiv"
  parent_spec: "v1"
  parent_tier: "downgraded"
  upgrade_axis: "mechanism"
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "constructive_object_missing"
reusable: unknown
reraise_status: retry
gap_reasons:
  - 'Conjecture 1: C-wellposed — The advertised closed diagnostic tau_w^mech(P) depends on c_w(P), but Assumption curvature only asserts existence of some positive constant and does not define a unique or computable functional.'
  - 'Conjecture 2: C-coherence — E_w^sign(P)>0 is automatic under the current normalization/Assumption sign-cone, so the stated three-channel iff does not actually encode sign-channel positivity.'
  - 'Sanity-check corollaries: C-sanity — The PMW reduction sets R_HLP^common=R_CLP but then claims zero gap against h_SVAR when the fourth-cumulant label is imposed equally; unless the LP side is also restricted to R_SVAR, h_CLP-h_SVAR and overline Lambda need not vanish.'
  - 'Theorem 1 / setup: C-wellposed — L_delta4 is named a fourth-cumulant label residual but is defined as distance to X_SVAR; since X_SVAR is a diagonal common-SVAR set, L_delta4=0 already implies Pi=0, making Pi redundant in the zero-contact filter M_delta4.'
  - 'Conjecture 1: C-coherence — The claimed sharp iff frontier is mostly restating tau_w^*(P)=h_LP-h_0 and the setup assertion h_0=h_SVAR under Assumption mechanism-regularity, so the flagship statement does not yet add a non-tautological mechanism condition.'
  - 'upgrade delta: N-upgrade-thin — Mechanism rubric only partially delivered: delta_summary promises separate exposure, pasting, and cumulant-label channels, but L_delta4=dist(x,X_SVAR) already bundles pasting and cumulant feasibility, so the three mechanisms are not isolated.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Attempted a mechanism-axis upgrade of the banked parent eid_lp_svar_nonequiv/v1 by decomposing the single cumulant-envelope margin chi_w(P) into three named channels: sign-cone exposure E_w^sign(P), common-impact pasting Pi_w^paste(P), and cumulant-label residual L_delta4(P), with Theorem 1 (diagnostic tuple), Conjectures 1-2 (mechanism lower bound and iff frontier), and Theorem 2 (parent collapse). Five angles over 12 total review attempts reached publishability_tier:flagship with novelty-new verdicts on Conjectures 1 and 2, but each was blocked by statement-level well-posedness failures: c_w(P) undefined/non-computable in the closed-form diagnostic tau_w^mech(P), E_w^sign(P)>0 automatic under the sign-cone normalization making the iff tautological, and the PMW sanity corollary claiming zero gap without restricting the LP side to R_SVAR. The underlying math area and the three-channel decomposition idea are sound and novel; failure was purely a precision defect in the statement of the scalar curvature constant and the iff encoding, not a refutation of the kernel.
banked_on: "2026-05-21"
---

# eid_lp_svar_nonequiv / upgrade — Failed

**Topic.** Sharp non-equivalence theorem for local-projection (LP) versus structural-vector-autoregression (SVAR) identification of structural impulse responses under non-Gaussian innovations and partial sign restrictions. Plagborg-Moller and Wolf (2021, Econometrica) established that LP and SVAR estimate the same population impulse response under finite-order linear VAR data-generating processes when both use the same identifying restrictions; Montiel Olea, Plagborg-Moller, Qian, and Wolf (Econometrica, forthcoming) extend the equivalence to local projections under misspecification of lag length. The flagship question: characterize the sharp boundary at which LP and SVAR identify distinct structural impulse responses when innovations are non-Gaussian with bounded higher-cumulant restrictions a la Gourieroux-Monfort-Renne (2017) and Lanne-Meitz-Saikkonen (2017), and when the structural impact matrix is restricted only by a partial sign/zero pattern. The kernel claim is a closed-form algebraic non-equivalence theorem: under non-Gaussian innovations with bounded fourth cumulant gap, the LP-IRF and SVAR-IRF identify distinct functionals of the structural-shock distribution unless a cumulant-matching restriction is jointly imposed, recovering Plagborg-Moller-Wolf equivalence at the Gaussian limit.

**Novelty target.** flagship

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Flagship-mechanism upgrade D-0.5 NO-PASS after pivot budget exhausted (4/4); three distinct angles (2 v3, 3 v1, 4 v3) reached publishability_tier:flagship with upgrade_delta_verdict:delivered but each was killed by statement-level well-posedness flags (C-sanity tie-break in Theorem 1; C-wellposed scalar-curvature/sign-cone normalisation; C-coherence tautological iff) that the reviewer recommended patching and rerunning; the kernel survives but the pipeline's revise-cap + reject-on-soundness policies foreclosed iteration.

**Supersedes.** eid_lp_svar_nonequiv_v1 (tier=downgraded, upgrade_axis=mechanism). The parent remains in _bank/downgraded/ as an independent reference; this entry is the flagship upgrade.

## Key files

- `eid_lp_svar_nonequiv_upgrade_state.json` — pipeline state at banking (`banked: true`).
- `eid_lp_svar_nonequiv_upgrade_proposal.tex` — final proposal version.
- `eid_lp_svar_nonequiv_upgrade.tex` — derivation note (if Stage 0 ran).
- `eid_lp_svar_nonequiv_upgrade_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_lp_svar_nonequiv_upgrade_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
