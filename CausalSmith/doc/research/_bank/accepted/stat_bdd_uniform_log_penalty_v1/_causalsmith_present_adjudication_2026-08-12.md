# PRESENT adjudication — 2026-08-12

## P1: `def:cty-stabilized-local-polynomial-estimator`

The P1 equivalence audit flagged the final sentence of the frozen P-14 definition: it specialized the generic estimator to the theorem bandwidth `h_n = a_n` and restated `B_n = a_n^{-1/3}`, while the declaration named by the crosswalk, `CausalSmith.Stat.BddUniformLogPenalty.stabilizedLocalPolynomial`, defines the estimator for arbitrary `h`.

Verdict: note-overstates-declaration packaging (case 2), not a wrong crosswalk. The specialization is separately machine-backed and remains in the mapped upper theorem `cty_a1_a2_winsorized_expected_outer_upper`, which explicitly uses `stabilizedLocalPolynomial ... (frontierRate n)` and documents `B_n = a_n^{-1/3}`.

Edits:

- Removed only the redundant theorem-bandwidth sentence from the frozen P-14 body in the bank graph and presentation formal layer.
- Recomputed the P-14 body hash and regenerated its derived TeX view.
- Kept the accepted note unchanged and kept the crosswalk target unchanged.
- Confirmed that no dependent prose artifact exists yet (P2 has not run); the theorem-level specialization remains present.

Backup: the accepted bank artifact before this presentation adjudication remains recoverable from the repository history/current pre-presentation checkpoint.
