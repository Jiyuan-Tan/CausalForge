# CausalSmith present adjudication — 2026-07-15

## Flagged statement

- `def:variance-scale` (`P-5`) was still classified as drift after two automatic P1 refinement rounds.
- The rendered definition asserted both `n Var_p(n⁻¹ ∑ᵢ ηᵢ)` and the raw second-moment expansion `n⁻¹ ∑ᵢⱼ E_p[ηᵢηⱼ]`.

## Verdict

This was note-overstates-Lean, not a wrong crosswalk mapping. The mapped declaration
`BipartiteExperiment.varScale` in `Basic.lean` defines only the scaled design variance.
The raw second-moment expansion additionally needs centering under the heterogeneous
Bernoulli design; that fact is supplied by the later variance theorem and is not part
of this unconditional definition.

## Edits

- Tightened `graph.json`'s frozen body for `def:variance-scale` to the scaled-variance definition.
- Updated the graph review note to record the boundary.
- Left the accepted discovery note unchanged as a historical artifact; future note maintenance should separate the conditional second-moment identity from the definition.
- Added the adjudication to the presentation paper-state notes.

The first tightened body still wrote the design variance as `Var_p`. A follow-up
equivalence audit correctly noted that Lean accepts an arbitrary finite design `D`.
The final body therefore defines the `D`-parameterized variance scale and introduces
the paper's `p`-indexed symbol only as the heterogeneous-Bernoulli abbreviation.

No crosswalk mapping changed, so no backup file was required.
