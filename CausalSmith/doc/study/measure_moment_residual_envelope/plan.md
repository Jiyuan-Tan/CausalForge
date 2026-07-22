## Status: COMPLETE — ready for review

Verified from ground truth this turn:
- `lake build ...Envelope ...Attainment ...Bounds ...QuarticRoot` → success (8077 jobs).
- `grep -cw sorry` = 0 in all 5 Lean files; no `admit`.
- `#print axioms` on `rho_envelope_isLUB`, `rho_envelope_attained`, `interior_quartic_unique_root`
  → only `[propext, Classical.choice, Quot.sound]`; no `sorryAx` from ME/L2 deps.

## Done (full API contract)
- `rhoEnvelope v := momentEnvelope (maximizingRoot v) (v²)` (Defs).
- `rho_envelope_isLUB : IsLUB (residualSet v) (rhoEnvelope v)` (Envelope) — combines upper bound
  `l2ResidualQuadratic_le_rho` + attainment.
- `rho_envelope_attained` — extremal 3-pt law `w₀δ₀+w₁δ_{xᵥ}+w₂δ₁` is admissible & realizes ρ(v).
- `interior_quartic_unique_root : ∃! u ∈ Ioo (v²) v, envelopeQuartic u (v²)=0` (QuarticRoot).
- Support lemmas (Bounds/Attainment/QuarticRoot) all proven: moment inequalities, extremal moments
  1–4, isProb, supp⊆[0,1], quartic deriv/monotonicity.

## Integrity
- `Admissible` = prob measure + a.e. supp ⊆ [0,1] + ∫y²=v²; genuine, non-vacuous (extremalMeasure
  is a concrete witness). Upper bound bridges to `ME.momentResidual_le_envelope` — no weakening.

## Remaining / Blocked
- none.