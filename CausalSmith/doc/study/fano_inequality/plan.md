## Status ledger — Fano inequality (build round 2) — COMPLETE

Two files under `CausalSmith/Substrate/FanoInequality/` build clean (`lake build CausalSmith.Substrate.FanoInequality.Fano` exit 0; only linter warnings: unused `[DecidableEq α]`/`[Fintype β]` section vars and `unusedDecidableInType`). **Zero sorries** (grep clean). Both main theorems verified to depend only on `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no Fano gate axiom).

### Design (single-reference-distribution Gibbs proof)
The whole theorem is reduced to ONE information-theoretic inequality — the Gibbs/cross-entropy
bound `entropy_le_crossEntropy` — applied to an explicit reference distribution `fanoRef`.
`fanoRef (x,y) = yMarginal p y · (if x = decode y then 1−Pe else Pe/(card α−1))`. Its
cross-entropy against `p` computes exactly to `entropy(yMarginal p) + binEntropy Pe + Pe·log(card α−1)`;
subtracting `entropy(yMarginal p)` yields Fano. The `card α−1` (not `card α`) is genuine — it is
the error-block size in `fanoRef`. Decoder is deterministic `decode : β → α`; `[DecidableEq α]`
added (no weakening — every finite type has it) so the `if x = decode y` test elaborates.

### Done (all decls proven, no sorry)
**Basic.lean**: `yMarginal`, `condEntropy`, `errorProb` (+ rfl simp lemmas); `negMulLog_add_mul_log_le`
(per-coord Gibbs lever), `entropy_le_crossEntropy` (Gibbs, proven from the lever + `entropy_def`),
`yMarginal_sum`, `yMarginal_nonneg`, `le_yMarginal`, `errorProb_nonneg`, `errorProb_le_one`, `correctMass_eq`.
**Fano.lean**: `fanoRef` (+ rfl simp), `fanoRef_nonneg`, `fanoRef_sum_eq_one`, `fanoRef_ac`,
`neg_crossEntropy_fanoRef` (the algebraic computation), `fano_inequality`, `fano_error_lower_bound`.

### Statements (genuine, match Requirement, non-vacuous)
- `condEntropy p = entropy p − entropy (yMarginal p)` — the chain-rule definition the Requirement names.
- `fano_inequality : condEntropy p ≤ Real.binEntropy Pe + Pe·Real.log(card α−1)` with hyps exactly the
  MAY-assume set (`0 ≤ p`, `∑ p = 1`, `2 ≤ card α`, `decode`).
- `fano_error_lower_bound : (condEntropy p − Real.log 2)/Real.log(card α) ≤ Pe`.

### Remaining
None.

### Blocked
None.

### Decisions / rejected paths
- REJECTED: explicit (E,X,Y)-joint chain-rule decomposition + "conditioning reduces entropy" (needs
  mutual-info ≥ 0 = another Gibbs + multivariable plumbing). The single-reference Gibbs proof gives the
  SAME sharp bound with one inequality and elementary sum algebra. The Requirement explicitly leaves the
  encoding to the scaffolder; the `card−1` and chain-rule are PROVEN (not assumed as black-box hyps), so
  this is not laundering.
- REJECTED: conditioning on `X̂ = decode Y` (would need data-processing). Conditioning on full `Y`
  (= `condEntropy p`) is what the Requirement's `condEntropy` denotes; handled directly.

## Previous round report (round 1)
Build ok: true; sorries remaining: 0. Confirmed independently this round from ground truth
(build exit 0, grep clean, axiom check clean).