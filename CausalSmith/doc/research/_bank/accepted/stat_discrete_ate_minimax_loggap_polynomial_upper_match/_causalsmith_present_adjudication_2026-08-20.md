# Presentation adjudication — 2026-08-20

Run: `stat_discrete_ate_minimax_loggap` / `polynomial_upper_match`, P1 statement-equivalence audit.
Context: editorial restructuring pass (synthesized-definition consolidation, 34 envs -> 7).

## Why these two re-flagged

Both envs are operator-frozen and were adjudicated in an earlier pass (their `review.note`
records it). Neither body was touched by this restructuring. They re-audited — and re-flagged —
because the token-economy change to the audit inputs altered the content keys, invalidating the
stored verdicts. So these are cache-invalidation re-flags of a known false-positive class, not
new drift. Verified decl-by-decl below rather than accepted on the strength of the prior note.

## Flag 1 — `ass:iid-sampling` (locked-env-drift)

Auditor: "The paper additionally introduces the derived quantities p_k, pi_k, and mu_ak, but the
listed Lean counterparts only deliver the observation alphabet, arbitrary one-unit law, and iid
product sample law."

Verdict: **FALSE POSITIVE — bundled env.** Two independent grounds.

1. Kind. p_k, pi_k, mu_ak are DEFINITIONS of derived functionals of P, not hypotheses. Writing
   `p_k = P(X=k)` places no restriction on P, so the audit rule (the paper may not carry a
   load-bearing hypothesis the Lean does not require) does not apply.
2. Backing. Each is Lean-realized and `@realizes`-tagged:
   - `p_k`      -> `cellMass`     (Basic.lean:74)   -- @realizes p_k(P(X=k); range [0,1])
   - `pi_k`     -> `propensity`   (Basic.lean:108)  -- @realizes pi_k(P(A=1|X=k))
   - `mu_{ak}`  -> `outcomeMean`  (Basic.lean:132)  -- @realizes mu_{ak}(E[Y|A=a,X=k])
   The mapped decl `IidSampling` delivers alphabet + one-unit law + iid product law.

The single-decl crosswalk mapping cannot express the bundle, so the auditor sees only
`IidSampling`. Mapping is correct and was NOT changed.

## Flag 2 — `def:sample-splits` (locked-env-drift)

Auditor: "The paper defines split sizes m_j and logarithmic scale L=log(en), but the listed Lean
counterpart splitCellCount only defines the split cell count using splitIndices and does not
deliver m_j or L."

Verdict: **FALSE POSITIVE — bundled env.** Every display is Lean-backed:
   - `I_0, I_1`        -> `splitIndices n j`                              (Helpers/Estimator.lean:14)
   - `m_j`             -> `splitSize n j := (splitIndices n j).card`      (Helpers/Estimator.lean:21)
   - `L = log(en)`     -> `logScale n := Real.log (Real.exp 1 * n)`       (Helpers/Estimator.lean:51)
   - `N^{(j)}_{aky}`   -> `splitCellCount`                                (Helpers/Estimator.lean:24)

`logScale` is literally log(e*n), matching the paper's `L=\log(en)` exactly. Mapping is correct
and was NOT changed.

## Action taken

- `equivalence_cache.json`: flipped `verdict` to `faithful` for these two obj_ids ONLY, one
  explicit edit per entry, stored `key` left untouched (valid while content is unchanged; any
  future content change re-audits automatically). Verified afterwards: 34 entries, both keys
  byte-identical to before, JSON valid.
- No frozen body was amended. No crosswalk mapping was repointed. No Lean was changed.
- No bank graph edit: the two `review.note` fields already record the decl-by-decl backing, and
  this file supersedes them as the durable record.

## Backups held

`graph.json.bak-20260820`, and in the bundle `p1_cache.json.bak-20260820`,
`outline.md.pre-regen-20260820`.
