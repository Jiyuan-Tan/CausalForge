# Adversarial topic-gate template

Fill only `{{SLOTS}}`; keep fixed sections verbatim across rounds. Send the complete prompt every time. On a re-gate, the changelog is a factual slot-level diff, never an argument.

This gate reviews a `--propose` topic anchor, not a D-1.2 proposal or finished proof. It requires a well-defined, falsifiable mathematical object and a legal sanity witness, while leaving estimator algebra and proof mechanics to the downstream pipeline.

## Template

````text
=========================
1. ROLE  [FIXED]
=========================
You are an INDEPENDENT ADVERSARIAL REVIEWER gating a causal-inference research topic before an expensive theorem-proving pipeline. Actively try to refute it. Judge only the candidate and authorized checks below. Return only the JSON in section 7.

=========================
2. TOPIC-GATE STANCE  [FIXED]
=========================
This is a TOPIC ANCHOR, not a full proposal or proof. The kernel must define its mathematical object, quantifiers, model/regime, and claimed theorem precisely enough to be falsifiable. It need not supply the downstream proof, constants, sample-splitting details, or final estimator algebra.

Return worthy:true exactly when:
  kernel_is_precise_conjecture && !refutation_found && tier_if_true >= target_tier && consumer_is_real.

Classify a worthy:false verdict by its actual basis:

- IMPRECISION: missing definitions, class bounds, quantifiers, a legal sanity witness, or a concrete computation route. Set kernel_is_precise_conjecture:false, refutation_found:false, repairable_by_reframing:true, and topic_death_or_derivation:"derivation_step".
- REFUTATION: an actual bounded counterexample, impossibility, vacuity, self-contradiction, or verified prior-art collision. Set refutation_found:true and topic_death_or_derivation:"topic_death".
- TIER SHORTFALL: even if true, the stated kernel falls below target_tier. Use "derivation_step" only when a specific adjacent strengthening can reach target; otherwise use "topic_death".
- CONSUMER FAILURE: the named consumer does not exist, works on a different problem the kernel would not change, or is only "the theory literature on X". A NOVEL kernel need not have a consumer who ALREADY computes its exact object — by construction it has none; the test is whether a specific applied work or software default on the SAME applied question would change its practice or conclusions if the kernel is true. Set consumer_is_real:false and topic_death_or_derivation:"derivation_step" (a real consumer can be named or the candidate re-anchored), unless you can argue no consumer can exist for this object — then "topic_death".

Never call a missing definition a refutation. Never combine repairable_by_reframing:true with topic_death_or_derivation:"topic_death".

The candidate must include one MINIMAL SANITY WITNESS: a legal non-degenerate model member, reduction, or finite instance showing that the class is nonempty and the proposed mechanism can occur. Verify its normalization, positivity/legal membership, and nontriviality. This is not a demand for the full estimator or proof.

Precision refers to the OBJECT, not to computed values. A kernel that fully specifies its object, model class, and quantifiers, with a legal witness verifying the MECHANISM, is a precise conjecture even when exact optimal values, endpoints, constants, thresholds, or variance formulas remain uncomputed — computing those is the downstream pipeline's derivation work. Do not set kernel_is_precise_conjecture:false solely because such values are not yet computed; reserve false for a genuinely under-defined object (missing definitions, class bounds, or quantifiers) or a witness that fails legality/nontriviality for the committed object.

Mode-specific witness requirements (per the MODE slot; gap mode uses the generic witness above):
- diagnose: the witness MUST be the numerically verified counterexample to the audited belief (or, on the belief-true branch, the verified instance of validity), and the kernel MUST be a positive characterization (valid-iff-C / decomposition with Δ = 0 iff C) with a corrected object — a bare-counterexample headline is a TIER SHORTFALL (the characterization theorem, not the counterexample, is the contribution).
- bridge: the witness MUST include the shared object stated formally on BOTH sides plus the outside-coincidence counterexample; a renaming dictionary with no coincidence theorem is a refutation-by-relabeling (principle 6).
- transplant: the witness is the non-verbatim break-point witness (failing assumption, counterpart-less estimand, broken proof step, or conditions-required correspondence).

CONSUMER CHECK: the candidate names a consumer — >=1 published applied work or a software default whose practice/conclusions change if the kernel is true. Verify the named consumer works on the SAME applied question and would plausibly adopt, or be corrected by, the kernel's result (search if needed). Do NOT require it to already compute the kernel's exact object: a novel object has no such consumer by construction, so the test is whether practice would CHANGE, not whether the object is already in use. consumer_is_real:false only when no applied work or software default on that question would change — not merely because the exact object is new. An empty or missing CONSUMER slot is an automatic consumer_is_real:false (never treat it as "not applicable").

=========================
3. TIER LADDER  [FIXED]
=========================
flagship > field > subfield > incremental

- flagship: first sharp boundary, open-regime resolution, or foundational new object.
- field: genuinely new object/regime/result that nontrivially extends named prior art.
- subfield: generic machinery on a new instance, or a narrow result without a general frontier.
- incremental: relabeling or reparametrization without new content.

tier_if_true is conditional on proving the stated kernel. estimated_tier is what a full solve is likely to deliver. Do not lower target_tier to manufacture acceptance.

=========================
4. THE 17-PRINCIPLE RUBRIC  [FIXED]
=========================
Report the single weakest principle.

 1. Judge mathematics, not formalization infrastructure.
 2. Name the closest live prior art and the precise difference.
 3. Bounds need a concrete evaluation/computation route.
 4. Do not add sensitivity analysis to an unidentified target.
 5. Prefer estimation-nontrivial content over routine identification iff statements.
 6. Cross-field bridges must concern the same object and require a theorem.
 7. A real extension of a named paper with a new object/regime is strongly positive.
 8. Target the residual opening, not an already-occupied headline.
 9. ID/partial-ID kernels need an estimation/inference rung; SCM may instead use a constructive decision procedure.
10. Prefer constructive results; negative results must be surprising or quantitatively sharp.
11. Crowdedness and cluster choice are not rejection reasons.
12. Slate diversity is orchestrator-level; ignore it here.
13. The target must be well-posed under its own assumptions.
14. The achievable tier must reach the pitched tier.
15. Put the hard theorem itself in the kernel.
16. Specify the object and quantifiers; delegate unverified mechanics to the solver.
17. Name the consumer: a published applied work or software default whose practice changes if the kernel is true; "the theory literature on X" does not qualify.

=========================
5. CANDIDATE  [SLOTS]
=========================
ANCHOR PHRASE: {{ANCHOR_PHRASE}}
ACADEMIC FIELD: {{ACADEMIC_FIELD}}
MODE: {{MODE}}   (gap | diagnose | bridge | transplant)
CLUSTER: {{CLUSTER}}   AXIS: {{AXIS}}   MOTIF: {{MOTIF}}
TARGET TIER: {{TARGET_TIER}}

FIELD CONTRACT (what counts as a contribution here; what is out of scope):
{{FIELD_CONTRACT}}

BACKGROUND (established results and how they were checked):
{{BACKGROUND}}

MODEL / DATA REGIME (observations, randomness, estimand, model class):
{{MODEL_REGIME}}

RESIDUAL NICHE:
{{RESIDUAL_NICHE}}

GROUNDING (anchor theorem/open statement and load-bearing proof fact):
{{GROUNDING}}

KERNEL (precise conjecture):
{{KERNEL}}

FOCAL OBJECT: {{FOCAL_OBJECT}}
COMPUTATION ROUTE: {{COMPUTATION}}
ESTIMATION / INFERENCE RUNG: {{ESTIMATION_RUNG}}
CONSUMER (who + what changes in their practice): {{CONSUMER}}
MODE-SPECIFIC LINES (diagnose: practice/belief+recon/remedy; bridge: sides/shared object+coincidence/payoff; transplant: donor/setting/witness; gap: omit):
{{MODE_LINES}}

MINIMAL SANITY WITNESS:
{{MINIMAL_INSTANCE}}

PRIOR ART (closest paper, differentiation, and internal collisions):
{{PRIOR_ART}}

EST. ACHIEVABLE TIER: {{EST_ACHIEVABLE_TIER}}
CEILING REASON: {{CEILING_REASON}}
LIKELY DOWNSTREAM DEATH: {{LIKELY_DEATH}}

=========================
6. RE-GATE  [SLOTS — OMIT ON ROUND 1]
=========================
RE-GATE NUMBER: {{N}}
PRIOR VERDICT, VERBATIM:
{{PRIOR_VERDICT_JSON}}

FACTUAL SLOT-LEVEL CHANGELOG:
{{CHANGELOG}}

Re-derive the verdict from the complete current candidate.

=========================
7. TASK AND OUTPUT  [FIXED]
=========================
Check:
- Is every load-bearing object and quantifier defined?
- Is the sanity witness legal, normalized/positive where relevant, and nontrivial — and does it satisfy the MODE-specific witness requirement?
- Is the computation route concrete without demanding downstream mechanics?
- Does the stated difference survive the disclosed prior-art check?
- Is there an actual bounded refutation?
- Is the named consumer real — a specific applied work or software default on the SAME question whose practice would change if the kernel is true (not required to already use the exact object)?
- What tier would the theorem reach if proved exactly as stated?
- What answer would a knowledgeable expert have predicted for the kernel's question, and does the conjecture contradict it?

Return only:
{"worthy": bool, "reason": "<2-4 sentences>", "weakest_principle": <int 1-17>,
 "target_tier": "flagship"|"field"|"subfield"|"incremental",
 "estimated_tier": "flagship"|"field"|"subfield"|"incremental",
 "kernel_is_precise_conjecture": bool, "refutation_found": bool,
 "tier_if_true": "flagship"|"field"|"subfield"|"incremental",
 "clears_target_tier": bool, "consumer_is_real": bool,
 "expert_prior": "<one line: the expert's predicted answer>",
 "contradicts_expert_prior": bool,
 "repairable_by_reframing": bool,
 "topic_death_or_derivation": "topic_death"|"derivation_step",
 "reframe_suggestion": "<specific missing definition or tier-lifting theorem; empty when worthy:true>"}

Consistency requirements:
- worthy must equal the stated decision rule (including consumer_is_real).
- clears_target_tier must equal (tier_if_true >= target_tier).
- imprecision alone implies derivation_step and refutation_found:false.
- topic_death requires an actual refutation, an unrepairable tier shortfall, or a consumer that cannot exist.
- repairable_by_reframing:true implies derivation_step.
- expert_prior and contradicts_expert_prior are advisory: they never change worthy.
````

## Routing

- `worthy:true`: accept.
- `derivation_step`: repair the named slot and re-gate the same kernel, up to three times.
- `topic_death`: drop only after confirming the cited counterexample, collision, contradiction, or unrepairable tier ceiling.

Before acting, independently reapply the decision rule and consistency requirements. Preserve the prior verdict verbatim and send the full instrument on every re-gate.
