# Next-action checkpoint for exp_bipartite_minimax_design_v1

Loop: research, lineage depth: 0

## What just finished

Research run exp_bipartite_minimax_design_v1 reached F5 cleanly.

## Proposed next actions

### Option 1 — Extend minimax design to weak-overlap policy regret

Why: Build directly on stat_policy_regret_margin_overlap_v1 and stat_ate_overlap_decay_v1 by asking whether a bipartite minimax design can attain policy-regret rates that adapt to overlap decay and margin conditions.

Command:
```bash
causalsmith research --id oq_bipartite_minimax_weak_overlap --question 'Can bipartite minimax experimental designs achieve overlap-adaptive policy-regret guarantees under margin conditions?'
```

### Option 2 — Stop

Why: Human pacing: take a break, review the just-completed run, or change direction.

Command:
```bash
# Stop — do not launch a follow-up run.
```
