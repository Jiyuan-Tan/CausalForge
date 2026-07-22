# qid / specialization naming convention

CausalSmith research pipeline runs are identified by `(qid, specialization)`. The pair
appears in every artifact path (`doc/research/active/<qid>/<qid>_<spec>_*`,
`_bank/<tier>/<qid>_<spec>/`, Lean output dirs) and in seed-burning /
reusable-artifact match keys. Drift here costs the team — a vague qid forces
a future reader to open the proposal before they can tell what a banked run
was about, and inconsistent cluster prefixes silently shrink bank-matching.

## Rules

1. **The qid encodes the topic, not the tier.** The novelty tier is a
   separate axis passed via the `--novelty` flag (`relative-to-repo` |
   `relative-to-literature` | `field` | `flagship`). Tier is not a topic
   property; it's an acceptance threshold. Do not put `flagship` or `field`
   in the qid.

2. **The qid leads with a cluster prefix.** The first underscore-delimited
   token must be one of:
   - `panel` — any panel / linear-projection paper or theorem (matches
     `Causalean/Panel/` and `CausalSmith/CausalSmith/Panel/`). This is a
     topical cluster, not a reference to a predefined question pool.
   - `eid` — exact identification.
   - `pid` — partial identification.
   - `stat` — estimation and inference theory.
   - `exp` — design-based / randomization inference.
   - `scm` — graphical identification and structural causal models.
   This prefix is what the bank uses as the "related" matching key — runs
   that share it can reuse each other's `literature_map` artifacts.

3. **The remainder of the qid is a short topic descriptor** in lowercase
   `snake_case`: 2–4 tokens, content-bearing, no filler words like
   `theorem`, `question`, `explore`. Examples:
   - `pid_dynamic_iv_compliance` ✓
   - `eid_backdoor_ate` ✓
   - `panel_spectral_threshold` ✓
   - `pid_late_bounded_defiers` ✓
   - `flagship_explore_f1` ✗ — no topic, no cluster
   - `pid_problem_v1` ✗ — empty descriptor
   - `pid_late_with_imperfect_compliance_and_assignment_under_dynamic_setup` ✗ — verbose

4. **The specialization is a version counter `vN`** (`v1`, `v2`, …) for
   sequential attempts on the same topic. Each pivot to a structurally
   different angle on the SAME anchor topic increments the version. A
   genuinely new topic gets a new qid, not a new spec. Older specs such as
   `p1_markov`, `p1_iid_bernoulli`, `f1` predate this convention and remain
   valid in the bank — do not retroactively rename them unless the topic is
   actively being reworked.

5. **A topic-pivot is a new qid; a sub-question of the same topic is a new
   spec.** Heuristic: if the burned-seed registry from run `pid_X v1` would
   apply to your new run, you're on the same topic — use `pid_X v2`. If the
   burned seeds are irrelevant, you're on a new topic — pick a new qid.

6. **Parallel alternatives: leave the run active, draft the sibling on a new
   spec or a new qid.** Different qids may run concurrently under the per-qid
   heartbeat, so generating alternatives needs no parking step: a run that has
   passed D0.5 but not yet committed to F1 stays in
   `doc/research/active/<qid>/`. Sibling runs on the same qid use the next spec
   (`v3`, `v4`); cross-topic alternatives use a fresh qid.

   The `candidates` bank tier that formerly parked such runs was retired
   2026-07-18 — see the "Retired tier" note in
   `doc/research/_bank/README.md`. Bank only on a terminal verdict: a run whose
   novelty framing outran its math belongs in `downgraded/`, not in a holding
   bin.

## Examples

| Topic | qid | spec |
|------|-----|------|
| Sharp partial ID of LATE under bounded defiers | `pid_late_bounded_defiers` | `v1` |
| Sharp partial ID of LATE under bounded defiers, second pivot | `pid_late_bounded_defiers` | `v2` |
| Sharp partial ID of dynamic LATEs under non-Markov compliance | `pid_dynamic_iv_compliance` | `v1` |
| Spectral phase transition for staggered TWFE | `panel_spectral_phase_transition` | `v1` |
| Backdoor identification of ATE on a DAG family | `eid_backdoor_ate` | `v1` |

## Why this matters

- **Greppability**: `ls _bank/downgraded/` should tell you what topics were
  tried, not what tier they targeted. Tier shows up via `banked_tier` and
  `proposed_from.novelty_target` in state.json.
- **Bank matching**: `loadReusableArtifacts` matches on cluster prefix. If
  every exploratory run sits in a `flagship_*` namespace, the matcher cannot
  tell them apart from any other cluster — defeating the purpose.
- **Cross-run literature reuse**: `pid_*` runs share the IV/compliance
  literature; `panel_*` runs share the panel-methods literature; `eid_*` runs share
  the graphical-ID literature. Topic-encoded qids let the proposer inherit
  the right prior-art substrate without re-doing Step 0a.
