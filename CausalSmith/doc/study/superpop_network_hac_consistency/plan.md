## Status: COMPLETE — both required APIs proven, zero sorries, zero errors (ground-truth verified this turn)

### Ground-truth check (this turn)
- `grep -rn sorry` over the substrate dir: **no matches**.
- `lean_diagnostic_messages` on both files: empty (no errors, no warnings).
- `lake env lean Consistency.lean`: **EXIT=0**, no output (transitively builds VarianceBound.lean).
- `lean_verify` axiom check on all 4 theorems (`netHACVarEst_variance_le`, `netHACVarEst_variance_tendsto_zero`, `netHACVarEst_memLp`, `netHAC_consistent`): axioms = `{propext, Classical.choice, Quot.sound}` only — **no sorryAx**, including no sorryAx leaking from the transitive `var_nbhd_prod_le` dependency in the sibling Causalean pkg.

## Done (compile + axiom verified)
File `VarianceBound.lean`:
- `netHACVarEst_eq_locProd` — `V̂ ω = ∑ᵢ Xᵢ·(∑_{k∈Nᵢ}Xₖ)` (Finset.mul_sum rewrite).
- `netHACVarEst_variance_le` (**milestone 1**) — `variance(V̂) ≤ 2·m⁵·card(V)·B⁴`, derived from `F.toDepGraph.var_nbhd_prod_le`. Minimal hyps: `0≤B`, `|Xᵢ|≤B`, degree `≤m`.
- `netHACVarEst_variance_tendsto_zero` (**milestone 2 — REQUIRED API**) — sequence version → 0 under `B n→0`, `card·B³→0`, via squeeze (`card·B⁴=(card·B³)·B`).

File `Consistency.lean`:
- `netHACVarEst_memLp` — `MemLp V̂ 2 μ` from pointwise bound `|V̂|≤card·m·B²` (Chebyshev moment anchor).
- `netHAC_consistent` (**milestone 3 — REQUIRED API**) — for `ε>0`, `Tendsto (fun n => (μ n).real {ω | ε ≤ |V̂ − variance(depSum X)|}) atTop (𝓝 0)`. Genuinely derived: Chebyshev `meas_ge_le_variance_div_sq` + unbiasedness `netHACVarEst_integral_eq_variance` (gives E[V̂]=variance(depSum X)) + milestone 2 + `squeeze_zero`.

## Remaining
- None. Both REQUIRED APIs from the Requirement's "Provides" contract are present and proven.

## Blocked
- Nothing.

## Decisions
- Module under `CausalSmith.Substrate.SuperpopNetworkHacConsistency.{VarianceBound,Consistency}`; building blocks live in sibling `Causalean` pkg (one-way dep CausalSmith→Causalean), so we extend its `NetworkDependence` API from CausalSmith side.
- **Milestone-1 simplification (genuine, not laundering):** `netHACVarEst` rewritten via `Finset.mul_sum` IS literally `∑ᵢ Xᵢ·Tᵢ`, exactly the object `var_nbhd_prod_le` bounds. So the "one order up" lemma the Requirement anticipated reduces to a direct application — the statement remains the genuine `variance(V̂) ≤ poly(m)·card(V)·B⁴`, and the m-dependence/degree-counting content is carried (not bypassed) by `var_nbhd_prod_le`. Axiom check confirms no sorry hides there.
- Variance-bound lemmas kept minimal-hypothesis (no mean-zero/unit-variance) — strictly more general & reusable; `netHAC_consistent` adds mean-zero+L² only where unbiasedness needs them. Not laundering (no hypothesis added to dodge a hard case; the extra generality is a strengthening).
- Consistency stated with `Measure.real` + `Tendsto (𝓝 0)` to match `networkSum_clt`'s `.real` convention and let `squeeze_zero` apply (equiv to the `≥ε`-prob `→0` phrasing in the Requirement).
- **Optional `studentized_wald_coverage` (Slutsky corollary) deliberately NOT built:** the library's only Slutsky (`InProb.lean`) is finite-design-specific, not the general-measure setting here; a general-measure Slutsky is scope creep beyond the two REQUIRED APIs. Marked optional in the Requirement; deferred.

## Verdict
Ready for review: both required deliverables proven, build & axioms clean, statements genuine/non-vacuous.