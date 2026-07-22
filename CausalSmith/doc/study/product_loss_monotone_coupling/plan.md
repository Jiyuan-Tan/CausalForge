## Module: product_loss_monotone_coupling
Path `CausalSmith/Substrate/ProductLossMonotoneCoupling/`, prefix `CausalSmith.Substrate.ProductLossMonotoneCoupling`.

**Round-4 ground-truth verification (this turn, not inherited):**
- `lake build ...Optimality` → **Build completed successfully (2621 jobs)**, exit 0. Zero errors; only style/unusedVariable lint warnings (`FrechetHoeffding.lean` multiGoal, `Optimality.lean:107` unused `hμ hν` on the optional closed-form lemma).
- `grep -nE '\b(sorry|admit|axiom|native_decide|implemented_by|extern|sorryAx)\b' *.lean` → **NONE** across all 8 files.
- `#print axioms` on every contract declaration → all report exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no custom axiom.

Files (bottom-up): `PIT` → `Coupling` → `FrechetHoeffding` → {`Survival`, `TailIntegral`} → `HoeffdingFubini` → `Hoeffding` → `Optimality`.

## Done (all proven; no sorry, no axiom)
- **PIT.lean**: `unifOI`, `instIsProbabilityMeasure_unifOI`, `monotoneOn_quantile`, `aemeasurable_quantile_unifOI`, `quantile_map_uniform`.
- **Coupling.lean**: `IsCoupling` (structure: prob. measure + `map_fst = μ` + `map_snd = ν`), `comonotoneCoupling`, `countermonotoneCoupling`, `map_one_sub_unifOI`, `isCoupling_comonotoneCoupling`, `isCoupling_countermonotoneCoupling`.
- **FrechetHoeffding.lean**: `jointCdf`, `frechet_hoeffding_upper` (`≤ min F G`), `frechet_hoeffding_lower` (`max (F+G-1) 0 ≤`), `jointCdf_comonotoneCoupling` (`= min F G`, bound attained), `jointCdf_countermonotoneCoupling` (`= max (F+G-1) 0`, bound attained), `jointCdf_le_comonotone`, `countermonotone_le_jointCdf`.
- **TailIntegral.lean**: `tailInd`, `signedTail`, `signedTail_eq_indicator_sub`, `measurable_signedTail(_uncurry)`, `abs_signedTail_le_one`, `integrable_signedTail`, `integral_signedTail` (`= a`), `integral_abs_signedTail` (`= |a|`), `integrable_signedTail_prod`, `integral_signedTail_prod` (`= x*y`), `integral_norm_signedTail_prod`.
- **Survival.lean**: `survFst`, `survSnd`, `jointSurv`, `survFst_eq` (`= 1-F`), `survSnd_eq`, `jointSurv_eq` (incl–excl), `surv_gap_eq` (`S - SX·SY = H - F·G`).
- **HoeffdingFubini.lean**: `coupling_fst/snd_memLp`, `coupling_integral_fst/snd`, `coupling_integrable_mul` (Cauchy–Schwarz), `integral_signedTail_fst/snd`, `fiber_integral_pi`, `integrable_tail_fst/snd_prod`, `integrable_bigPhi`, `integral_prod_eq_integral_fiber` (the Fubini swap), `mean_fst/snd_tail`, `integrable_survFst/survSnd_sub`, `integrable_fiber`.
- **Hoeffding.lean**: `fiber_sub_mean_prod`, `integrable_frechet_gap`, `hoeffding_cov_identity_prod`, `hoeffding_cov_identity`.
- **Optimality.lean** (capstone): `product_expectation_le_comonotone`, `countermonotone_le_product_expectation`, `product_expectation_comonotoneCoupling` (closed form `= ∫_(0,1) quantile μ · quantile ν`).

Every item of the Requirement's "Provides" contract is present and proven, with the general hypotheses (`IsCoupling π μ ν`, `MemLp id 2` marginals) intact. `IsCoupling` is inhabited (witnessed by `isCoupling_comonotoneCoupling`), and `MemLp id 2 μ` is satisfiable (e.g. Dirac), so no statement is vacuous.

## Remaining
- None. Zero open sorries.

## Blocked
- None.

## Decisions (kept so a future turn does not repeat dead ends)
- **Round-2 route ABANDONED**: the "independent copy on `π.prod π`" (Lehmann) argument, requiring `covariance_fst_snd_prod`. Replaced entirely.
- **Adopted route**: signed-tail representation `x·y = ∫∫ (𝟙{s<x}−𝟙{s<0})(𝟙{t<y}−𝟙{t<0}) ds dt`; one Fubini swap on `(volume⊗volume)⊗π`; mean tail formula `E[X] = ∫(SX(s)−𝟙{s<0})ds`. The `𝟙{s<0}`,`𝟙{t<0}` constants cancel identically (`fiber_sub_mean_prod`), leaving the survival gap `S − SX·SY`, converted to `H − F·G` by `surv_gap_eq`.
- **Orientation convention (do not flip)**: product measures are *tail variables first* (`(volume.prod volume).prod π`), so `Integrable.integral_prod_left` directly yields integrability of the fibre `q ↦ ∫ Φ q p ∂π` against Lebesgue².
- **Fubini domination**: `∫∫‖Φ q p‖ dq = |p.1|·|p.2|`, `π`-integrable by Cauchy–Schwarz (`MemLp.integrable_mul` on the two `L²` marginals) — this is where `MemLp 2` is used, exactly once.
- **Round-3 restructure** (retained): the monolithic `hoeffding_analytic_core` conjunction was split into a 4-file chain of small independently-fillable lemmas rather than laundered into a private sorry.
- Mathlib anchors confirmed: `integral_prod_mul`, `integral_integral_swap`, `Integrable.integral_prod_left`, `Integrable.mul_prod` (NOT `Integrable.prod_mul` — no such name), `integrable_prod_iff'`, `MemLp.integrable_mul`, `integral_prod`, `Measure.ext_of_Iic`, `measureReal_union_add_inter`.
- Extra `[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]` instance args on `jointCdf_le_comonotone` / the optimality theorems are implied by `IsCoupling` and are convenience only — not a hypothesis strengthening.

## Optional polish (non-blocking, cosmetic only)
- `Optimality.lean:107` `product_expectation_comonotoneCoupling` does not use `hμ hν` (the closed form needs no moment condition). Harmless; could be dropped to silence the lint.
- `FrechetHoeffding.lean` multiGoal style warnings at lines 72, 92, 126, 136.

## Reference
Hoeffding (1940); Lehmann, "Some Concepts of Dependence" (Ann. Math. Statist. 1966); Nelsen, *An Introduction to Copulas* §2.4–2.5. Mathlib has `ProbabilityTheory.covariance` but no cdf identity — this module supplies it.
