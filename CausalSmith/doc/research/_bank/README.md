# CausalSmith Result Bank (thmsmith pipeline)

A persistent, queryable archive of every thmsmith run that completed Stage -0.5
(question proposal) and reached at least an attempted derivation. Banking
downgraded and failed runs is deliberate: negative results, burned seeds, and
reusable infrastructure all compound over time, and the proposal→derivation
tier drift is the most important calibration signal for the pipeline.

## Tiers

| Directory | Inclusion criterion | Primary use |
|-----------|--------------------|-------------|
| `accepted/`   | Stage -0.5 ACCEPT **and** Stage 0.5 ACCEPT at the requested `novelty_target`, **and** the run reached Stage 5 (Lean proof complete) | Publishable results; promotion candidates into AutoID |
| `downgraded/` | Stage -0.5 ACCEPT **but** Stage 0.5 falls below `novelty_target` (still mathematically sound) | Negative findings; reusable LP/operator/witness infrastructure; burned-seed manifests |
| `failed/`     | Stage -0.5 NO-PASS, or Stage 0.5 REJECT on correctness/structure | Pipeline-diagnostic only; usually low scientific value |
| `legacy/`     | Runs predating the Stage -0.5 / Stage 0.5 reviewer system (e.g. early Q1 outputs) | Held un-graded; see `legacy/README.md` for the regrade plan |

The four-bucket split is deliberate. `legacy/` is an administrative
holding bin, not a scientific tier — it holds results that cannot be
retroactively slotted without re-running the reviewers. The
proposal→derivation tier-drift statistic is computed only over
`accepted ∪ downgraded ∪ failed` (entries with both verdicts on file).

**Retired tier — `candidates/` (removed 2026-07-18).** `candidates/` parked
D0.5-ACCEPT runs pending tournament selection. It was retired because the
parking state it encoded was not load-bearing: an independent per-entry
re-grade of all 8 parked entries assessed every one of them **subfield**
against their banked `field` target, in agreement with objections already
recorded in each entry's own review log before the accepting round reversed
them. They were not "awaiting a verdict"; they were mis-tiered. All 8 were
re-banked into `downgraded/` with `reraise_status: re-raise` and a
`retiered_from: candidates` stamp. Do not reintroduce the tier: an entry
whose novelty framing outran its math belongs in `downgraded/`, and one
that has genuinely not been adjudicated should stay in
`doc/research/active/<qid>/`.

## Promotion / demotion between tiers

Re-entering the active pipeline is a deliberate re-raise, not a promotion:
move the entry's directory out of `_bank/<tier>/` back into
`doc/research/active/<qid>/`, clear `banked` (and `banked_tier`,
`banked_on`, `banked_reason`) in the state.json, then run
`/causalsmith research --resume <qid> <spec>`. For a `downgraded/` entry
consult its `reraise_status` first: `re-raise` means the math was sound and
only the novelty framing was too high — re-anchor at the corrected tier or
pivot to the kernel recorded under the entry's **Re-anchor path** heading;
`true-negative` means the kernel is refuted and should stay banked.

## Bank reads (load semantics)

- `loadBurnedSeeds` walks **all four** tiers. With `candidates/` retired
  there is no longer a tier whose seeds are exempt from burning.
- `loadReusableArtifacts` also walks **all four** tiers, attaching a
  per-tier trust label (`trustLabel` in `tools/src/discovery/bank.ts`).
  Re-tiered ex-candidate entries carry the `downgraded` label —
  "math-sound, novelty-biased": their `literature_map` artifacts are
  trusted, their novelty framing is not.

## Layout

    _bank/
      README.md                          ← this file
      accepted/<qid>_<spec>/             ← entry directory, one per accepted run
      downgraded/<qid>_<spec>/           ← entry directory, one per downgraded run
      failed/<qid>_<spec>/               ← entry directory, one per failed run
      legacy/<qid>_<spec>/               ← entry directory, one per legacy (pre-reviewer) run

Each entry directory contains the verbatim run artifacts (state.json,
proposal.tex, reviews/, derivation note, pipeline.jsonl, etc.) plus a
top-level `README.md` carrying the metadata block below.

## Banking and the guardrail

When an entry is banked, its `<qid>_<spec>_state.json` MUST carry:

    "banked": true,
    "banked_tier": "accepted" | "downgraded" | "failed" | "legacy",
    "banked_on": "<YYYY-MM-DD>",
    "banked_reason": "<one-sentence reason, verbatim verdict where possible>",

Banking moves `<qid>_<spec>_state.json` out of `formalization/<qid>/` into
`_bank/<tier>/<qid>_<spec>/`, so the `causalsmith-guardrail.sh` PreToolUse
hook's legacy state-file check (which scans `formalization/<qid>/*_state.json`
for `stage_completed != "5"`) never sees the banked file again. The
`banked: true` field is preserved as a frozen artifact, not a live signal —
the hook is path-scoped, so being out of the protected directory is what
makes a banked entry inert.

## Per-entry metadata (entry `README.md` frontmatter)

    ---
    qid: <question id>                   # e.g. flagship_explore, q1_minimal_basis
    spec: <specialization id>            # e.g. f1, p1_bernoulli
    topic: <one-line topic phrase>       # carried from state.json proposed_from.topic
    novelty_target: incremental | subfield | field | flagship
    banked_novelty_tier: incremental | subfield | field | flagship  # achieved tier; upgrade target must be strictly higher
    tier_at_proposal: ACCEPT | REVISE | REJECT   # Stage -0.5 final verdict
    tier_at_derivation: ACCEPT | REVISE | REJECT | NA  # Stage 0.5 final verdict; NA for legacy
    gap_reasons:                         # only meaningful for downgraded/failed
      - <verbatim reviewer phrase identifying which Conjecture collapsed and why>
    reusable_artifacts:                  # paths inside the entry dir worth lifting
      - path: <relative path>
        kind: lp_setup | operator | witness | literature_map | counterexample | other
        one_line: <plain-English description>
    seeds_burned:                        # seed indices that this run refuted
      - index: <int>
        one_liner: <verbatim from seed_list>
        reason: <short, verbatim or paraphrased from the kill review>
    proof_attempt_summary: |
      <2–3 sentence epitaph: what was attempted, what collapsed, what remains>
    banked_on: <ISO date>
    ---

The body of the entry README is free-form: usually a short pointer to the
key files inside the directory (proposal, derivation, latest review) and any
context not captured by the structured fields.

## Authoring conventions

- **Never delete a banked entry.** Move, downgrade, or re-tier; do not remove.
- **Keep the run artifacts verbatim.** The bank's value comes from being
  able to re-derive the tier drift; rewriting old derivations defeats that.
- **`burned: true` propagates to the global seed registry.** When `seeds_burned`
  lists a seed, future proposal runs on the same anchor topic should skip that
  seed unless explicitly unburned (with reason).
- **Promotion to AutoID** is a separate, manual step. Banking accepted ≠
  upstreamed; that happens only after a human review copies the Lean
  statement+proof into AutoID and confirms it builds.

## Tier-drift metric (planned)

    drift_rate(novelty_target) =
      |{downgraded entries with novelty_target = T}| /
      |{accepted ∪ downgraded entries proposed at T}|

Computed per `novelty_target` band. A rising drift rate at `field`/`flagship`
means Stage -0.5 is over-promising relative to Stage 0.5; a falling rate is
calibration. Both are useful — neither is visible if downgrades are deleted.
