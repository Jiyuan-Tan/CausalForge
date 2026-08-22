# Presentation adjudication — 2026-08-21 (pipeline re-run)

Re-ran `present stat_transported_late_strength_frontier v1 --from P1 --refresh-frozen-bodies`
to carry the 2026-08-18..21 pipeline improvements into the 2026-08-17 bundle.

P1's notation loop converged (4 iterations, 4 advisories) and the statement audit passed on
all 39 environments. The POST-AUDIT notation re-review then failed with three blocking
findings, all repaired here. Backup: `graph.json.bak`.

## 1. `\mathcal G` used before its definition — node reorder

`def:admissible-geometry-class` sat AFTER `def:geometry-handle` and
`def:least-favorable-witness` in the graph node order, hence after them in the derived
formal layer, although the outline places it in an earlier section. The notation reviewer
reads the layer, so `\mathcal G` read as undefined at both use sites.

Edit: moved the `def:admissible-geometry-class` node immediately before
`def:geometry-handle`. No edge, statement, or body change; layer order now agrees with
paper order. Side effect: the outline structure key embeds node order, so P1 regenerated
the outline on re-entry (frozen bodies and audit verdicts were unaffected and cache-hit).

## 2. `def:geometry-handle` — cross-reference to a non-existent label

Body carried `\cref{def:least-favorable-witness}`; the paper defines the label
`obj:def:least-favorable-witness`. Would have emitted a broken reference in the PDF.

Edit (`nl.frozen_body`, 1 occurrence asserted):
`\cref{def:least-favorable-witness}` -> `\cref{obj:def:least-favorable-witness}`

## 3. `def:regular-cell-feasible-honesty` — `\ne` where an input belongs

The displayed argument list read
`C_n((O_i^S)_{i=1}^n,(X_j^T)_{j=1}^{N_n},(q_{x,n})_{x=1}^{k_n},\ne)`.
`\ne` is the not-equal macro; the definition's own closing prose states the inputs are
"the observed samples, the realized support, the known source-cell probability vector
\((q_{x,n})_{x=1}^{k_n}\), and the propensity values on that support". The intended input
is the already-defined source assignment propensity `e` (homed at `ass:instrument-overlap`),
so no new notation is introduced. The regular-cell class does not restrict the propensity
to a constant, so the procedure is given `e` itself rather than a constant.

Edit (`nl.frozen_body`, 1 occurrence asserted):
`(q_{x,n})_{x=1}^{k_n},\ne` -> `(q_{x,n})_{x=1}^{k_n},e`

## Not changed

The accepted note is untouched. No statement, hypothesis, or conclusion was altered; all
three edits are notation/reference/ordering repairs, and the two body edits re-enter the
statement audit on the next P1 (their audit keys moved).
