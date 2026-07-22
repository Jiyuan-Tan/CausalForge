# Substrate debt (disclosed gates)

  oeq:feasible-upper, lem:crude-localized-master-bound. Bochner integrability + BddAbove of
  the localized/offset empirical-process suprema over the policy class, previously assumed as
  `hBochner`. **Now proved**, not assumed: `hBochner` was removed from `feasible_upper`
  (`T_feasible_upper.lean`) and from `crude_localized_master_bound` (`Helpers/MasterBound.lean`,
  which now takes `hbn : BoundedCrossfitNuisances` instead and derives the side conditions
  internally). Discharge lemma `bochner_discharge` (`Helpers/BochnerIntegrability.lean`) proves
  all four conjuncts: the sup measurability over the uncountable policy class is reduced to the
  countable `PolicyClassVC` pointwise-dense skeleton `Π₀` via the paper-agnostic Causalean
  substrate `Causalean.Mathlib.MeasureTheory.integrable_sSup_image_of_countable_dense`
  (`Causalean/Mathlib/MeasureTheory/SupCountableDense.lean`), fed by the dominated-convergence
  skeleton-continuity lemmas (`lawRegret_tendsto_of_skeleton`,
  `pooledCrossfitProcess_tendsto_of_skeleton`, `foldSubCentered_tendsto_of_skeleton`); the
  untruncated process is handled via the `*_trunc_eq_original_ae_36` a.e.-equalities and the
  truncated envelope `36/q`. Verified axiom-clean: `#print axioms feasible_upper =
  [propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axioms). Full chain builds
  green.
